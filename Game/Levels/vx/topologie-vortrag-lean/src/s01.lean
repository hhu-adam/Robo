import topology.basic
import topology.path_connected
import analysis.normed_space.basic
import data.set.basic

/-
## 1.1. Was ist ein topologischer Raum?

Ein topologischer Raum ist eine Menge, auf der eine Topologie definiert ist, wobei
eine Topologie eine Menge von Teilmengen ist, welche die folgenden Bedingungen erfüllt:
- Die leere Menge und die gesamte Menge sind in der Topologie enthalten.
- Der Durchschnitt zweier Mengen in der Topologie ist ebenfalls in der Topologie enthalten.
- Die Vereinigung einer beliebigen Anzahl von Mengen in der Topologie ist ebenfalls in der Topologie enthalten.

In Lean verwenden wir dazu folgende Definition:
> Gegeben einen Typen α, so ist `topological_space α` die Klasse von Typen, welche
> Topologische Räume repräsentieren, parametriert über α. In Lean werden offene Mengen,
> abgeschlossene Mengen, das Innere, Äußere und der Rand für Typen dieser Klasse durch
> die Prädikate `is_open`, `is_closed`, `interior`, `closure` und `frontier`
> definiert.

Die Grundbegriffe der Topologie werden in dem Package 
```
import topology.basic
```
definiert.
-/

#check topological_space
--      ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑
-- hier kann durch rechtsclick auf `topological_space` und `go to definition`
-- die Definition angezeigt werden. (in VIM mit `gd`)

