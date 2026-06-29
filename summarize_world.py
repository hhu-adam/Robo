#!/usr/bin/env python3
import argparse
import os
import re
import sys



BULLET_HINT_JOIN_RE = re.compile(
      r'^(?P<prefix>[ \t]*·[ \t]*)Hint'
      r'(?:[ \t]*\([^()\n]*\))?[ \t]*'
      r'"[^"]*"[^\n]*\n'      # Hint line through its newline
      r'[ \t]*(?P<next>[^\n]*)',
      re.MULTILINE
  )
PLAIN_HINT_RE = re.compile(
      r'^[ \t]*Hint(?:[ \t]*\([^()\n]*\))?[ \t]*"[^"]*"[^\n]*\n?',
      re.MULTILINE
  )


def collect_lean_files(subdir):
    """Return a list of (path, name, stem) for all .lean files in subdir, sorted by name."""
    try:
        entries = os.listdir(subdir)
    except FileNotFoundError:
        sys.stderr.write(f"Error: directory not found: {subdir}\n")
        sys.exit(1)
    except NotADirectoryError:
        sys.stderr.write(f"Error: not a directory: {subdir}\n")
        sys.exit(1)

    files = []
    for name in entries:
        path = os.path.join(subdir, name)
        if not os.path.isfile(path):
            continue
        if not name.lower().endswith('.lean'):
            continue
        if name.lower() == 'summary.lean':
            continue
        stem, _ = os.path.splitext(name)
        files.append((path, name, stem))

    files.sort(key=lambda t: t[1].lower())
    return files

def remove_hints(text: str) -> str:
    """
    Remove Hints, handling the bullet form '· Hint ...' by splicing the next line’s code
    immediately after the bullet prefix so that the next line’s first non-space character
    appears exactly where 'Hint' started.
    """
    text = BULLET_HINT_JOIN_RE.sub(r'\g<prefix>\g<next>', text)
    text = PLAIN_HINT_RE.sub('', text)
    return text

def strip_block_comments(text: str) -> str:
    """
    Remove Lean block comments '/- ... -/' (nestable) from `text`.
    Single-line comments '-- ...' are left in place. '/-', '-/' occurring inside
    string literals ("..."), character literals ('c') or single-line comments are
    NOT treated as block-comment delimiters (these regions are copied verbatim, so
    a '/-' inside them cannot accidentally open a block comment).
    """
    out = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]

        # String literal: copy verbatim, honouring backslash escapes.
        if c == '"':
            out.append(c)
            i += 1
            while i < n:
                d = text[i]
                out.append(d)
                i += 1
                if d == '\\' and i < n:
                    out.append(text[i])
                    i += 1
                elif d == '"':
                    break
            continue

        # Character literal: 'c' or '\e'. A leading quote only starts a char
        # literal when it is not a prime attached to an identifier (e.g. x').
        if c == "'":
            prev = text[i - 1] if i > 0 else ''
            if not (prev.isalnum() or prev in "_'"):
                j = i + 1
                if j < n and text[j] == '\\':
                    j += 2
                elif j < n:
                    j += 1
                if j < n and text[j] == "'":
                    out.append(text[i:j + 1])
                    i = j + 1
                    continue
            # otherwise fall through and treat ' as an ordinary character

        # Single-line comment: copy verbatim through end of line (so a '/-'
        # inside it cannot open a block comment).
        if c == '-' and i + 1 < n and text[i + 1] == '-':
            j = i + 2
            while j < n and text[j] != '\n':
                j += 1
            out.append(text[i:j])
            i = j
            continue

        # Block comment (nested): drop everything up to the matching '-/'.
        if c == '/' and i + 1 < n and text[i + 1] == '-':
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == '/' and i + 1 < n and text[i + 1] == '-':
                    depth += 1
                    i += 2
                elif text[i] == '-' and i + 1 < n and text[i + 1] == '/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
            # If the comment occupied whole lines (only whitespace before '/-' on
            # its first line and only whitespace after '-/' on its last line),
            # remove that surrounding whitespace and the trailing newline too, so
            # the removal does not leave a blank line behind. Such a stray blank
            # line would otherwise prematurely terminate the Statement block.
            k = len(out)
            while k > 0 and out[k - 1] in (' ', '\t'):
                k -= 1
            at_line_start = (k == 0) or (out[k - 1] == '\n')
            m = i
            while m < n and text[m] in (' ', '\t'):
                m += 1
            at_line_end = (m >= n) or (text[m] == '\n')
            if at_line_start and at_line_end:
                del out[k:]
                i = m + 1 if (m < n and text[m] == '\n') else m
            continue

        out.append(c)
        i += 1

    return ''.join(out)

def extract_statement_block_from_text(text: str):
    """
    From preprocessed text, extract the first block that starts with a line beginning
    with 'Statement' (ignoring indentation) and ends before the next blank line.
    Replace the leading 'Statement' with 'lemma'. Return the block (ending with '\n')
    or None if not found.
    """
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(r'^\s*Statement\b', line):
            start = i
            break
    if start is None:
        return None

    block_lines = []
    for j in range(start, len(lines)):
        if j > start and lines[j].strip() == '':
            break
        block_lines.append(lines[j])

    if not block_lines:
        return None

    block_lines[0] = re.sub(r'^(\s*)Statement\b', r'\1lemma', block_lines[0])
    return '\n'.join(block_lines) + '\n'

def main():
    parser = argparse.ArgumentParser(description="Summarize Lean 'Statement' blocks into summary.lean")
    parser.add_argument('subdir', nargs='?', help="Subdirectory containing .lean files")
    args = parser.parse_args()

    subdir = args.subdir
    if not subdir:
        try:
            subdir = input("Enter subdirectory (relative or absolute path): ").strip() or '.'
        except EOFError:
            sys.stderr.write("No input provided.\n")
            sys.exit(1)

    files = collect_lean_files(subdir)
    if not files:
        sys.stderr.write(f"No .lean files found in {subdir}\n")
        sys.exit(1)

    out_path = os.path.join(subdir, 'summary.lean')
    skipped = 0
    with open(out_path, 'w', encoding='utf-8') as out:
        for path, name, stem in files:
            with open(path, 'r', encoding='utf-8') as f:
                original = f.read()

            preprocessed = remove_hints(original)
            preprocessed = strip_block_comments(preprocessed)

            block = extract_statement_block_from_text(preprocessed)
            if block is None:
                sys.stderr.write(f"Warning: no Statement block found in {name}; skipping\n")
                skipped += 1
                continue

            out.write(f"\n\n/- {stem} -/\n")
            out.write(block)

    print(f"Wrote summary to {out_path}")
    if skipped:
        print(f"Skipped {skipped} file(s) without a Statement block.", file=sys.stderr)

if __name__ == '__main__':
    main()

# What the script currently does:
# - Prompts for a subdirectory if none is given on the command line
# - Collects all lean files from that subdirectory
# - Within each file, removes all Hints
#   The form '· Hint ...' is handled by splicing the next line’s code immediately after
#   the bullet prefix so that the next line’s first non-space character appears exactly
#   where 'Hint' started.
# - Within each file, removes all block comments (delimited by “/- … -/”).
# - Extracts the first block that starts with a line beginning with “Statement …” and
#   continues up to (but not including) the next blank line
# - Writes each extracted block to summary.lean (in the same subdirectory), preceded by
#   a header line “/- {filename} -/”, ordered alphabetically by file name
    
# How to use:
# - Run either:
#   - python3 summarize_world.py path/to/subdirectory
#   - or just python3 summarize_world.py and type the subdirectory when prompted
# - The script writes path/to/subdirectory/summary.lean
