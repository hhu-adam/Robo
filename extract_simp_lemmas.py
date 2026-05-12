#!/usr/bin/env python3
"""
Extract `simp only [...]` suggestions from a build log and write them
as `attribute [game_simp]` lines into Game/Metadata/Tactic/simp_list.lean.

Usage: python3 extract_simp_lemmas.py [LOGFILE]
       python3 extract_simp_lemmas.py -            # read from stdin
       lake build | python3 extract_simp_lemmas.py # read from stdin (auto)
       (with no arg and a tty, defaults to simp.log)
"""

import re
import sys
from collections import OrderedDict
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "Game" / "Metadata" / "Tactic" / "simp_list.lean"

ENTRY_RE = re.compile(
    r"^info:\s+Game/Levels/(?P<folder>[^/]+)/(?P<file>[^/]+)\.lean:\d+:\d+:\s*\[simp_log\]\s+(?P<lemma>\S+)\s*$"
)
HEADER_RE = re.compile(r"^--\s*([^,]+),\s*(\S+):\s*$")
ATTR_RE = re.compile(r"^attribute\s+\[game_simp\]\s+(.*)$")


def parse_existing(out_path: Path):
    """Read existing simp_list.lean into the same OrderedDict shape as parse()."""
    results: "OrderedDict[tuple[str,str], OrderedDict[str,None]]" = OrderedDict()
    if not out_path.exists():
        return results
    lines = out_path.read_text().splitlines()
    i = 0
    while i < len(lines):
        hm = HEADER_RE.match(lines[i])
        if not hm:
            i += 1
            continue
        folder, fname = hm.group(1).strip(), hm.group(2).strip()
        i += 1
        if i < len(lines):
            am = ATTR_RE.match(lines[i].strip())
            if am:
                bucket: "OrderedDict[str,None]" = OrderedDict()
                for l in am.group(1).split():
                    if l:
                        bucket.setdefault(l, None)
                results[(folder, fname)] = bucket
                i += 1
    return results


def parse(text: str):
    """Each `[simp_log] <name>` line emits one lemma for one (folder, file)."""
    results: "OrderedDict[tuple[str,str], OrderedDict[str,None]]" = OrderedDict()
    for line in text.splitlines():
        m = ENTRY_RE.match(line)
        if not m:
            continue
        folder, fname, lemma = m.group("folder"), m.group("file"), m.group("lemma")
        results.setdefault((folder, fname), OrderedDict()).setdefault(lemma, None)
    return results


HEADER = "import Game.Metadata.Tactic.Simp\nimport Game.Metadata.FromMathlib\n"


def write_output(results, out_path: Path):
    out_path.parent.mkdir(parents=True, exist_ok=True)
    chunks = []
    for (folder, fname), lemmas in sorted(results.items()):
        if not lemmas:
            continue
        chunks.append(f"-- {folder}, {fname}:\nattribute [game_simp] {' '.join(lemmas)}\n")
    out_path.write_text(HEADER + "\n" + "\n".join(chunks))


def main():
    arg = sys.argv[1] if len(sys.argv) > 1 else None
    if arg == "-" or (arg is None and not sys.stdin.isatty()):
        text = sys.stdin.read()
        source = "<stdin>"
    else:
        log = Path(arg) if arg else ROOT / "simp.log"
        if not log.exists():
            sys.exit(f"Log file not found: {log}")
        text = log.read_text()
        source = str(log)
    new_results = parse(text)
    merged = parse_existing(OUT)
    updated = added = 0
    for key, lemmas in new_results.items():
        if not lemmas:
            continue
        if key in merged:
            updated += 1
        else:
            added += 1
        merged[key] = lemmas
    write_output(merged, OUT)
    print(f"{added} added, {updated} updated, {len(merged)} total entries in {OUT} (from {source})")


if __name__ == "__main__":
    main()
