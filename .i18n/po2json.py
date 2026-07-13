#!/usr/bin/env python3
"""Regenera .i18n/<lang>/Game.json a partir de .i18n/<lang>/Game.po.

Uso:  python3 .i18n/po2json.py es

Sin dependencias externas (solo Python 3). El JSON resultante replica el
formato de los existentes: {msgid: msgstr} con las claves en orden
descendente.
"""
import json
import os
import re
import sys

_ESC = {'\\n': '\n', '\\t': '\t', '\\"': '"', '\\\\': '\\'}


def unescape(s):
    return re.sub(r'\\[nt"\\]', lambda m: _ESC[m.group(0)], s)


def parse_po(path):
    """Devuelve {msgid: msgstr}, ignorando la cabecera y las entradas obsoletas."""
    text = open(path, encoding='utf-8').read()
    result = {}
    for block in re.split(r'\n\s*\n', text):
        lines = block.strip('\n').split('\n')
        if not any(l.startswith('msgid') for l in lines):
            continue
        if any(l.startswith('#~') for l in lines):
            continue
        msgid_parts, msgstr_parts, mode = [], [], None
        for l in lines:
            if l.startswith('#'):
                continue
            if l.startswith('msgid '):
                mode, rest = 'id', l[len('msgid '):].strip()
            elif l.startswith('msgstr '):
                mode, rest = 'str', l[len('msgstr '):].strip()
            elif l.strip().startswith('"'):
                rest = l.strip()
            else:
                continue
            if not (rest.startswith('"') and rest.endswith('"')):
                raise SystemExit(f'línea .po no reconocida: {l!r}')
            (msgid_parts if mode == 'id' else msgstr_parts).append(unescape(rest[1:-1]))
        msgid, msgstr = ''.join(msgid_parts), ''.join(msgstr_parts)
        if msgid:  # la cabecera tiene msgid vacío
            result[msgid] = msgstr
    return result


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    lang = sys.argv[1]
    base = os.path.join(os.path.dirname(os.path.abspath(__file__)), lang)
    po_path = os.path.join(base, 'Game.po')
    json_path = os.path.join(base, 'Game.json')

    data = parse_po(po_path)
    vacias = sum(1 for v in data.values() if not v)
    with open(json_path, 'w', encoding='utf-8') as f:
        json.dump(dict(sorted(data.items(), reverse=True)), f, ensure_ascii=False, indent=1)
        f.write('\n')
    print(f'{json_path}: {len(data)} entradas escritas'
          + (f' (¡OJO: {vacias} sin traducir!)' if vacias else ''))


if __name__ == '__main__':
    main()
