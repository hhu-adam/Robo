import topology.basic
import analysis.normed_space.basic

/-
Ziel dieser Übung wird es sein,
die folgenden Theoreme aus der Topologie zu zeigen:

1. $S^2$ ist einfach-zusammenhängend.
2. Jeder zusammenziehbare Raum ist einfach-zusammenhängend

Hierfür werden wir folgendermaßen vorgehen:
1. Einleitung
  1.1. Was ist ein topologischer Raum? [./s01.lean]
    1.1.1. Beispiel: $S^2$ [./s02.lean]
    1.1.2. Beispiel: $[0,1]$ [./s02.lean]
    1.1.3. Beispiel: $S^1 + S^1$ [./s02.lean]
  1.2. Wann ist ein topologischer Raum (weg-)zusammenhängend? [./s03.lean]
  1.3. Wann ist ein topologischer Raum einfach-zusammenhängend? [./s04.lean]
2. Beweis der Theoreme
  2.1. $S^2$ ist einfach-zusammenhängend. [./s05.lean]
  2.2. Jeder zusammenziehbare Raum ist einfach-zusammenhängend [./s06.lean]
-/
