# Language

* Anreden klein (du, ihr, euch)
* Format für direkte Rede:
  ```
  **Robo**:
  **Robo** *(flüsternd)*:
  ```
* Okay (nicht Ok, nicht OK, nicht Oke, nicht O.K. …)
* Doppel-S (ß) nach Deutscher Grammatik, nicht Schweizer🥲.

# Tactics 
  
* We don't use `rcases` but rather `obtain`.
  - `obtain` is more pronouncable and more of a word
  - `obtain` seems to be encouraged over `rcases` in mathlib
* In general, we want to advertise automation, not hide it.  Therefore:
  - `tauto` is allowed (except on the first few planets, were we want to introduce a few other basic tactics in an elementary setting)
  - We won't employ `linear_combination`.  We would rather want to use `polyrith`, but that would require some engineering and might create security issues.
* We try not to introduce too many tactics.
  - we use `let` but not `set` tactic
    - we don't currently need `set`
    - `set` does not operate on sets the way `ring` operates on rings, which might be confusing don't need it
    - we believe `let` is more common in mathlib than `set` 

# Inventory Doc

## Taktiken

* Haben zuerst eine Kurzbeschreibung
* Gefolgt von folgenden h2 (##) headers:
  - "Details": optional, genauere Beschreibung
  - "Beispiel": pflicht! mindestens ein Beispiel
  - "Hilfreiche Resultate": optional, verwandte Taktiken/Definitionen/Theoreme

 
