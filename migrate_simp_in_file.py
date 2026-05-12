#!/usr/bin/env python3
"""Per-file migration from `true_simp?` to `simp` + `attribute [game_simp] ...`.

Workflow:
  1. Run `lake build` (with `true_simp?` still in place) so each call emits
     a `Try this: [apply] simp (config✝ := { }) only [...]` suggestion.
     Save the output, e.g.  `lake build 2>&1 | tee /tmp/lake-build.log`.
  2. Run this script on the level file:
        python3 migrate_simp_in_file.py Game/Levels/Foo/L01.lean
     It reads /tmp/lake-build.log, extracts the suggestions for that file,
     dedups the lemma list, inserts an `attribute [game_simp] ...` line just
     before `Statement`, and replaces every `true_simp?` with `simp`.
  3. Re-run `lake build`. If you get `Unknown constant` errors at the
     attribute line (typically because a local hypothesis or `let`-bound
     name leaked in), re-run with --prune:
        python3 migrate_simp_in_file.py Game/Levels/Foo/L01.lean --prune
     which reads the latest build log and removes any flagged names from
     this file's attribute line.

Use --log to point at a different build log.
"""
import argparse
import re
import sys
from pathlib import Path

HEADER = re.compile(r"^info: (Game/Levels/[^:]+\.lean):\d+:\d+: Try this:$")
CONTENT_START = re.compile(
    r"^\s*\[apply\] simp \(config✝ := \{ \}\) only(?: \[(?P<body>.*))?$"
)
CONT = re.compile(r"^    (.*)$")
ATTR_RE = re.compile(r"^attribute \[game_simp\] (.*)$")
STATEMENT_RE = re.compile(r"^Statement(\s|\b)")
UNKNOWN_RE = re.compile(
    r"^error: (Game/Levels/[^:]+\.lean):\d+:\d+: Unknown constant `([^`]+)`$"
)

def parse_suggestions(log_path: Path, target: str) -> list[str]:
    """Return a deduplicated list of lemma names from `Try this:` lines for `target`."""
    lines = log_path.read_text().splitlines()
    lemmas: list[str] = []
    seen: set[str] = set()
    i = 0
    while i < len(lines):
        m = HEADER.match(lines[i])
        if not m or m.group(1) != target:
            i += 1
            continue
        i += 1
        if i >= len(lines):
            break
        cm = CONTENT_START.match(lines[i])
        if not cm:
            i += 1
            continue
        body = cm.group("body")
        i += 1
        if body is None:
            continue
        buf = body
        while "]" not in buf:
            if i >= len(lines):
                break
            cm2 = CONT.match(lines[i])
            if not cm2:
                break
            buf += " " + cm2.group(1).strip()
            i += 1
        buf = buf.split("]", 1)[0]
        for raw in buf.split(","):
            name = raw.strip().lstrip("↓").lstrip("↑")
            if name and name not in seen:
                seen.add(name)
                lemmas.append(name)
    return lemmas

def collect_unknowns(log_path: Path, target: str) -> set[str]:
    """Return the set of names flagged as `Unknown constant` for `target`."""
    bad = set()
    for line in log_path.read_text().splitlines():
        m = UNKNOWN_RE.match(line)
        if m and m.group(1) == target:
            bad.add(m.group(2))
    return bad

def insert_or_update_attr(file_path: Path, lemmas: list[str]) -> str:
    """Insert or replace the file's `attribute [game_simp]` line."""
    text = file_path.read_text()
    lines = text.splitlines()
    # If an attribute line already exists, replace it.
    for i, line in enumerate(lines):
        if ATTR_RE.match(line):
            new = "attribute [game_simp] " + " ".join(lemmas) if lemmas else None
            if new is None:
                # remove the line and an immediately-following blank
                del lines[i]
                if i < len(lines) and lines[i].strip() == "":
                    del lines[i]
            else:
                lines[i] = new
            file_path.write_text("\n".join(lines) + "\n")
            return "updated existing attribute line"
    # Otherwise insert before Statement, with one blank line separating.
    if not lemmas:
        return "no lemmas; nothing to insert"
    stmt_idx = next((i for i, l in enumerate(lines) if STATEMENT_RE.match(l)), None)
    if stmt_idx is None:
        return "no Statement line found; not inserting"
    new_attr = "attribute [game_simp] " + " ".join(lemmas)
    if stmt_idx > 0 and lines[stmt_idx - 1].strip() == "":
        new_lines = lines[:stmt_idx - 1] + [new_attr, ""] + lines[stmt_idx:]
    else:
        new_lines = lines[:stmt_idx] + [new_attr, ""] + lines[stmt_idx:]
    file_path.write_text("\n".join(new_lines) + "\n")
    return "inserted new attribute line"

def replace_true_simp(file_path: Path) -> int:
    text = file_path.read_text()
    n = text.count("true_simp?")
    if n:
        file_path.write_text(text.replace("true_simp?", "simp"))
    return n

def prune_unknowns(file_path: Path, bad: set[str]) -> bool:
    """Remove flagged names from the file's attribute line."""
    text = file_path.read_text()
    lines = text.splitlines()
    for i, line in enumerate(lines):
        m = ATTR_RE.match(line)
        if not m:
            continue
        names = [n for n in m.group(1).split() if n not in bad]
        # also strip ↓ / ↑ defensively
        names = [n.lstrip("↓").lstrip("↑") for n in names]
        if not names:
            del lines[i]
            if i < len(lines) and lines[i].strip() == "":
                del lines[i]
        else:
            lines[i] = "attribute [game_simp] " + " ".join(names)
        file_path.write_text("\n".join(lines) + "\n")
        return True
    return False

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file", help="path to the level .lean file")
    ap.add_argument("--log", default="/tmp/lake-build.log",
                    help="path to lake build log (default /tmp/lake-build.log)")
    ap.add_argument("--prune", action="store_true",
                    help="prune Unknown-constant names from existing attribute line")
    args = ap.parse_args()
    file_path = Path(args.file)
    if not file_path.exists():
        sys.exit(f"file not found: {file_path}")
    log_path = Path(args.log)
    if not log_path.exists():
        sys.exit(f"build log not found: {log_path}")
    # Path inside the repo, used to filter the log
    target = str(file_path).removeprefix("./")
    if args.prune:
        bad = collect_unknowns(log_path, target)
        if not bad:
            print(f"no Unknown-constant errors for {target}")
            return
        ok = prune_unknowns(file_path, bad)
        print(f"pruned {sorted(bad)} from {target}: {'ok' if ok else 'no attribute line found'}")
        return
    lemmas = parse_suggestions(log_path, target)
    print(f"found {len(lemmas)} unique lemma(s) in suggestions for {target}")
    if lemmas:
        print(f"  {' '.join(lemmas)}")
    msg = insert_or_update_attr(file_path, lemmas)
    print(f"attribute line: {msg}")
    n = replace_true_simp(file_path)
    print(f"replaced {n} occurrence(s) of true_simp? with simp")

if __name__ == "__main__":
    main()
