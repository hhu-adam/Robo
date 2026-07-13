#!/usr/bin/env python3
"""Comprueba la salud de una traducción .i18n/<lang>/Game.po.

Uso:  python3 .i18n/check_po.py es

Verifica, entrada por entrada:
  1. que no haya traducciones vacías;
  2. que el multiconjunto de placeholders §n del msgstr coincida con el del
     msgid o, en su defecto, con el de la traducción alemana (el original del
     juego a veces omite o repite placeholders deliberadamente).

Termina con código 1 si encuentra problemas (pensado para CI).
"""
import os
import re
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from po2json import parse_po

PH = re.compile(r'§\d+')


def main():
    if len(sys.argv) != 2:
        raise SystemExit(__doc__)
    lang = sys.argv[1]
    base = os.path.dirname(os.path.abspath(__file__))
    target = parse_po(os.path.join(base, lang, 'Game.po'))
    de = parse_po(os.path.join(base, 'de', 'Game.po')) if lang != 'de' else {}

    problemas = []
    for msgid, msgstr in target.items():
        resumen = msgid.replace('\n', '¶')[:60]
        if not msgstr and msgid.strip():
            problemas.append(f'VACÍA: «{resumen}»')
            continue
        c_tr = Counter(PH.findall(msgstr))
        c_id = Counter(PH.findall(msgid))
        c_de = Counter(PH.findall(de.get(msgid, ''))) if msgid in de else None
        if c_tr != c_id and (c_de is None or c_tr != c_de):
            esperado = f'{sorted(c_id.items())}' + (f' o {sorted(c_de.items())}' if c_de is not None else '')
            problemas.append(f'PLACEHOLDERS: «{resumen}» tiene {sorted(c_tr.items())}, se esperaba {esperado}')

    print(f'{lang}/Game.po: {len(target)} entradas comprobadas')
    if problemas:
        print(f'\n{len(problemas)} problema(s):')
        for p in problemas:
            print(' -', p)
        sys.exit(1)
    print('todo correcto ✓')


if __name__ == '__main__':
    main()
