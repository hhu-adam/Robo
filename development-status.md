
| Level                  | new name   | levels         | tried? | hints  | story  | summary    | picture     | optional changes                                                      |
|:-----------------------|:-----------|:---------------|:-------|:-------|:-------|:-----------|:------------|:----------------------------------------------------------------------|
| Proposition            | Logos      | +++            | +++    | +++    | +++    | +          | +++         |                                                                       |
| Implication            | Implis     | +++            | +++    | +++    | ++     | o (update) | +++         | (check trans tactic for implications? -- Jon has added it to level 9) |
| Predicate              | Quantus    | +++            | +++    | +++    | +++    | +          | +++         |                                                                       |
| Contradiction          | Spinoza    | ++             | ++     | ++     | ++     |            | +++         | add WLOG tactic?  ad TFAE tactics?                                    |
| Inequality             | Luna       | +              | +++    | +++    | +++    |            | +++         | add some help for Analysis-level                                      |
| Sum                    | Babylon    | +              | +++    | +++    | +++    |            | +++         | TODO: add sum over zeroes, adding over singleton                      |
| FunctionBij            | Isos?      | +              | TODO   |        | TODO   |            | TODO        | remove linear_combination                                             |
| FunctionInj            | Monos?     | +              | TODO   |        | TODO   |            | TODO        |                                                                       |
| FunctionSurj           | Epos?      | +              | TODO   |        | TODO   |            | TODO        |                                                                       |
| Cantor                 | ==         | ++             | +      | +      | +      |            | +++         | move first problem somewhere else                                     |
| MatrixSpan             | TODO       | o TODO: sorrys | TODO   | TODO   | TODO   |            | TODO        |                                                                       |
| MatrixTrace            | Robotswana | ++             | +      | update | update |            | +++         |                                                                       |
| SetTheory              | Synolos    | TODO           |        |        |        |            | ??          | (add intervals?? -- only necessary for analysis)                      |
| ~FiniteSetTheory       | TODO       | TODO           |        |        |        |            | TODO        |                                                                       |
| SymmSquare             | TODO       | o TODO: L08    | TODO   | TODO   | TODO   |            | TODO        |                                                                       |
| Quotient               | TODO       | 7-?            | TODO   |        | TODO   |            | TODO        |                                                                       |
| Prime                  | TODO       | +              | TODO   | TODO   | TODO   |            | TODO        |                                                                       |
| ? RealUncountable      | TODO       | TODO .         |        |        |        |            |             |                                                                       |
| GoodByePlanet          |            | TODO (.)       |        |        |        |            | Spacecraft? |                                                                       |
|                        |            |                |        |        |        |            |             |                                                                       |
| [[[Continuity]]]       |            |                |        |        |        |            |             |                                                                       |
| [[ContinuousFunction]] |            | TODO ..        |        |        |        |            |             |                                                                       |
| [[CosExtInequality]]   |            | TODO ...       |        |        |        |            |             |                                                                       |
|                        |            |                |        |        |        |            |             |                                                                       |
| [[Tmp]]                |            |                |        |        |        |            |             |                                                                       |
| [[VectorSpan]]         |            |                |        |        |        |            |             |                                                                       |
| [[NewStuff]]           |            |                |        |        |        |            |             |                                                                       |
| [[Quantum]]            |            |                |        |        |        |            |             |                                                                       |

### Tactics

- replace rcases by obtain
- recursive constructor -- some version of refine??


### FunctionSurj
````
L03: Hint "Fallunterscheidung" does not trigger after "simp[g,f]" in place of "simp"
  
L04:     
     DOCUMENTATION
        Namespaces: Function.RightInverse
        move congr_fun to Function tab
        move congr_arg to Function tab
        
     Current solution uses “trick”:   
        simp [h x]
     rather than
        apply h 
     (is that more intuitive??) or
        specialize h x 
        assumption
     (more intuitive, but `specialize` has not been introduced)
     
L05 (NEW): just add hint to try tauto
    
L06 (NEW):
     REWRITE:
     remove "linear_combination"
     still need to introduce
     `set` and `injection`  (do we need `set`?)
     
L07 (NEW)
     FIX:
       does not compile in game nor in web editor:
          `simp [g, f]` throws error “invalid argument, variable is not a proposition or let-declaration”
       remove "match" from pretty printer!
     
     HINTS:  notation ⟨x, y⟩ in step `intro ⟨x, y⟩` (if we need this; not sure we do)

     DOCUMENTATION
        Namespaces: Function.HasRightInverse
   

L08: introduces `Surjective` 
     [earlier, before RightInverse? -- probably not, see L09]

L09 (NEW): semi-boss level for "surjective"
     does *not* need `RightInverse` or `HasRightInverse`
     but uses `congr_fun` and `comp_apply` (my solution below only uses `congr_fun`), and level that introduces `congr_fun` is about `RightInverse`

    HINTS
      A is of type Sort u_1 
      explain `succ`

    my solution:
       intro n
       induction n with m hm
       assumption
       obtain ⟨ a, ha⟩ := hm
       use g a
       rw [← ha]
       apply congr_fun hs

L10 (NEW):
     HINTS
     Here's the solution:
     
       constructor
       intro h
       ext
       constructor
       intro hx
       tauto
       intro hx
       --rw [mem_range]
       apply h
       intro h
       intro y
       rw [← mem_range]
       rw [h]
       tauto

    I added the line rw [mem_range], but it's not needed.
    The line rw [← mem_range], on the other hand, is needed.
    There's a hint about mem_range only in this line, which is weird if mem_range has already been used.
     
L11 (NEW): introduces `choose` and `preimage`

     FIX
     anonymous object α✝: Type u_2
     “tactic `using` is not available”
     
     STORY, HINTS
     Do we need to mention `surjective_iff_hasRightInverse` (as is currently the case)?  I think not.

L12 (NEW): good recap of previous level! 

     level silently introduces `Function.HasRightInverse.surjective` in the inventory, but this is only used in a Branch
     -- do we need/want to introduce this?  

     STORY

     uses `TFAE` -- shouldn't this be introduced separately (boss level should be without hints)
     
     tfae_have tfae_finish
     
     
     
````
