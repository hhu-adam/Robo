

| Planet                          | new name  | levels         | tried? | hints        | story  | summary | picture                    | desirable changes                                                                          |
|:--------------------------------|:----------|:---------------|:-------|:-------------|:-------|:--------|:---------------------------|:-------------------------------------------------------------------------------------------|
| **Version 1.0:**                |           |                |        |              |        |         |                            |                                                                                            |
| Logo                            | ==        | +++            | +++    | +++          | +++    | +       | +++                        |                                                                                            |
| Implis                          | ==        | +++            | +++    | +++          | ++     | +       | +++                        |                                                                                            |
| Quantus                         | ==        | +++            | +++    | +++          | +++    | +       | +++                        |                                                                                            |
| Spinoza                         | ==        | ++             | ++     | ++           | ++     |         | +++                        |                                                                                            |
| Luna                            | ==        | +              | +++    | +++          | update |         | +++                        |                                                                                            |
| Babylon                         | ==        | +              | +++    | +++          | +++    |         | +++                        |                                                                                            |
| Prado (Primes)                  | ==        | +              | TODO   | +            | +++    |         | +++                        |                                                                                            |
| SetTheory                       | Piazza    | TODO           |        |              |        |         | (market)                   | TODO: see below                                                                            |
| Vieta (Function Basics)         | ==        | ++             | TODO   | +            | +      |         | +++                        |                                                                                            |
| Epo                             | ==        | +              | +      |              | TODO   |         | +++                        |                                                                                            |
| Mono                            | ==        | +              | TODO   |              | TODO   |         | +++                        |                                                                                            |
| Iso                             | ==        | +              | TODO   |              | TODO   |         | +++                        |                                                                                            |
| Samarkand                       | ==        | +              |        |              |        |         | +++                        |                                                                                            |
| Cantor                          | ==        | ++             | +      | +            | +      |         | +++                        |                                                                                            |
| Robotswana                      | ==        | ++             | +      | update (L05) | update |         | +++                        |                                                                                            |
| Ciao                            | ==        | +              | +      | +            | +      |         | +++                        |                                                                                            |
|                                 |           |                |        |              |        |         |                            |                                                                                            |
| **Version 2.0:**                |           |                |        |              |        |         |                            |                                                                                            |
| SymmSquare                      | TODO      | o TODO: L08    | TODO   | TODO         | TODO   |         | TODO                       |                                                                                            |
| Quotient                        | TODO      | 7-?            | TODO   | TODO         | TODO   |         | TODO                       |                                                                                            |
| MatrixSpan                      | TODO      | o TODO: sorrys | TODO   | TODO         | TODO   |         | TODO                       |                                                                                            |
| RealUncountable                 | TODO      | TODO .         | TODO   | TODO         | TODO   |         | TODO                       |                                                                                            |
|                                 |           |                |        |              |        |         |                            |                                                                                            |
| **Possible future versions:**   |           |                |        |              |        |         |                            |                                                                                            |
| ???                             |           |                |        |              |        |         | +++ (librarian)            |                                                                                            |
| Lineare Independence            |           |                |        |              |        |         | +++ (mushrooms with flags) |                                                                                            |
| Intervals                       |           |                |        |              |        |         |                            |                                                                                            |
| Continuity                      |           |                |        |              |        |         |                            |                                                                                            |
| Epsilon-Delta-Differentiability |           |                |        |              |        |         | +++ (ants)                 |                                                                                            |
| Differentiability               |           |                |        |              |        |         | +++ (snail)                |                                                                                            |
| ContinuousFunction              |           | TODO ..        |        |              |        |         |                            |                                                                                            |
| CosExtInequality                |           | TODO ...       |        |              |        |         |                            |                                                                                            |
|                                 |           |                |        |              |        |         |                            |                                                                                            |
| **Trash:**                      |           |                |        |              |        |         |                            |                                                                                            |
| [[Tmp]]                         |           |                |        |              |        |         |                            |                                                                                            |
| [[VectorSpan]]                  |           |                |        |              |        |         |                            |                                                                                            |
| [[NewStuff]]                    |           |                |        |              |        |         |                            |                                                                                            |
| [[Quantum]]                     |           |                |        |              |        |         |                            |                                                                                            |
|                                 |           |                |        |              |        |         |                            |                                                                                            |

#### TODO SetTheory:

- use set of primes in examples
- introduce Fin n (currently in Babylon)
- introduce Finite
- new Boss: set of primes is infinite
- warnings:

    ./././Game.lean:121:0: warning: No world introducing Set.mem_inter_iff,     but required by SetTheory
    ./././Game.lean:121:0: warning: No world introducing Set.mem_union,         but required by SetTheory
    ./././Game.lean:121:0: warning: No world introducing Set.mem_setOf,         but required by Cantor
    ./././Game.lean:121:0: warning: No world introducing Set.mem_singleton_iff, but required by Cantor
    ./././Game.lean:121:0: warning: No world introducing Finset.sum_subset,     but required by Robotswana (L05)
    ./././Game.lean:121:0: warning: No world introducing Finset.univ,           but required by Robotswana


## Strategic decisions regarding Tactics

- recursive `constructor` -- some version of `refine`??
- we've thrown out `injection` tactic
- use `choose` instead of `obtain` for existential hypotheses


# Ideas for missing stories and pictures in v1.0

# Prado (only even prime is 2)

**intro**
You land next to a magnificent building in neo-classical style.
An elegant penguin-like figure is waiting for you at the grand entrance.
He bows deeply.  He is very happy to see you.  You are the first visitors to the newly built Prado, the Prime-Adoration museum.

The main hall is massive, but completely empty apart from a pillar with two small marbles on it.
The prime two, as the penguin explains.
When you ask for further exhibits, he apologizes. This is currently the only one.
The museum is very new.

He wants to take you on a tour of the empty rooms, and you agree.

**in between the questions**
You discuss how formalosophers think about primes.

Eventually, it transpires that the museum is supposed to be reserved for the most honourable primes only: the even ones.

You and Robo try to figure out a way to convince the penguin that other primes should also be considered.

**picture**
The penguin-like formalosopher proudly presenting the marble pedastal with two small marbles on it.
Robo looking up at it, not terribly impressed.


# Piazza (set of primes is infinite)

**intro**
You land on a planet that is bustling with life.
It appears you are in the middle of some market place.
There are traders in all shapes and sizes, and they each have baskets fill with little “things” of all shapes and sizes.
You can’t make out what these “things” are, but it’s notable that everything looks very much sorted.  There are baskets of small round red “things”, baskets of small flat green “things”, baskets of small star-shaped dark blue “things” and so on.
The traders all appear to be busy trading with each other.
A group of childern approaches you.

**in between questions**
The childern have some homework to do.
You try to help them.

(**picture** already exists)

# FunctionBasics = Vieta

Named after [Franciscus Vieta](https://en.wikipedia.org/wiki/Fran%C3%A7ois_Vi%C3%A8te), who apparently invented variables. He was also a code-breaker for the king, and had to navigate difficult and dangerous political situations.

**intro**:
You land on a planet that appears to be in a state of civil war.
Every now and then arrows whiz past.  You cannot make out where they come from or who's shooting, and there's nowhere to take cover.
Your impuls us to go straight back into the spaceship, but then you see Vieta, standing alone, out there in the open, seemingly untroubled, reading something.
He greets you warmly.  He explains you do not need to be afraid.  You just has to stand in the right place at the right moment.  He will take care of you.

**in between questions**
Vieta cannot share what he is reading.
But he can entertain you with some questions.
Every now and then, Vieta asks to walk with him over here or over there.

**end**
At the end, he says actually right now would be a good time to leave. He will be alright.

**picture**
Robo looking up at Vieta.  Vieta very elegantly dressed in 16th century style, calm and authorative.  Arrows whizzing right and left, missing Vieta and Robo only narrowly.


# FunctionSurj = Epo

**intro**
You approach a planet that is dominated by two skyscrapers, which are connected by tubes.
One is tall and thin, the other a bit fatter and smaller.
You carefully land on top of the tall one. The spaceship only just fits in the landing area.
As it turns out, this was the wrong choice.  A lone concierge greets you and explains that everyone else is eagerly awaitiing you at the other skyscraper.
This skyscraper, tower A, is where they all sleep (in English: our “domain”, though unfortunately that won't work in German). The other skyscraper, tower B, is where they spend the day (in English: our “codomain”).  But it's ok.  The tubes are there to quickly get from A to B.  He takes you downstairs to one of the tubes.  You take a seat in a transport capsule that will take you through the tube. Concierge:  “It’s good that every one is already in B.  That way, we won't crash on arrival.”

**in between questions**
You each sit in a transport capsule and glide over to the other side, where you are greeted.
The locals are very proud that every single floor of tower B has an incoming tube.
As the conversation continues, it transpires that most floors have several incoming tubes, and that's why they frequently have crashes.

**end**
When you want to leave, it turns out you have to go down and walk back to tower A.  The tubes only work in one direction.

**picture**

A view of the two towers and the tubes, either as a “realistic” image or as a tube map (cf. London underground).  Tall and thin tower with the dormitories on the left, smaller fatter tower with offices, shops or amusement park features on the right.

# FunctionInj = Mono

**intro**
This planet again has two towers, one tall, one fat, again connected by tubes.
You land on the fat one this time.  Again, it's the wrong choice.
A lone concierge greets you and explains that everyone else is eagerly awaiting you at the top level of the other skyscraper.
On this planet, they all sleep in the smaller tower, and spend the day in the higher one.
He takes you downstairs to one of the tubes. You ask about crashes, but he ensures you their system is very safe.

**in between questions**
When you get to the other tower, you still have to ascend ten floors on the stairs to get to the top.  Obviously, not every floor is accessible by a tube.  In particular, not the top floor, where you are expected.

**end**
To go back, you again have to walk.

**picture**
As for Epo.  Smaller fatter tower with dormitories on the left, tall thin tower with offices, shops or amusement park features on the right.

# FunctionBij = Iso

**intro**
Again a planet with two skyscrapers connected by tubes.  This time, they appear equally high, so you really don't have any clue where to land.  You choose one of them randomly.  You made the right choice, hurray!

**in between questions/end**
Though you landed in the right place, the inhabitants are keen to show off their transport capsule system.  You can each have your own capsule.

And it turns out you can go back and forth!

But this also means you have to be careful.  They do have rather a lot of crashes.

**picture**
Robo enjoying a ride in a transport capsule.

# FunctionImage = Samarkand

**intro**
Already from afar, this planet looks very colourful.  As you come closer, you see that most of the surface is covered in intricated geometric patterns.  But there are still some white spots, and you land in one of the them.  First, it seems the planet is completely empty and uninhabited.  Then, in the distance, in a colourful area, you notice something.  A bump in the flat landscape.  You are a bit hesitant to walk over the colour, but it appears to be dry and firm.  As you draw closer, you notice that the bump is a creature ressembling a tortoise.  It's lying, completely motionless, but when you approach it greets you in a friendly tone.
The tortoise explains that by lying in the same place for long enough she will create a copy of the pattern on the surface underneath on her belly.
She will then move to the edge of the white area and lie down there to transfer the colour to the white area.

She needs to stay lying, but she wants to entertain you with some questions.

**in between questions**
She needed centuries of training to do this correctly.  The most difficult part is to find the right part of the existing pattern (the correct preimage) to continue.
Most of the planet was decorated by her ancestors.

**end**
It is no longer known where the intial pattern(s) came from.

**picture**
The turtle lying on an [islamic geometric pattern](https://duckduckgo.com/?t=ffab&q=islamic+geometric+pattern&iax=images&ia=images), seen from above.









# Technical notes from testing various planets

## FunctionBasics

#### L??: succ has left inverse, using if … then … else
Defining the left inverse as n ↦ n-1 (now in branch) looks ill-defined to a mathematician, so requires some explanation.

#### L?? BOSS: function which semiconjugates to successor function is surjective

**need to introduced `succ` here or elsewhere, or reformulate**

## FunctionSurj

Remove `NewTheorem congr_fun` from end of file.

#### L?? BOSS: TFAE definitions of surjectivity

**Remove TFAE and reference to image/preimage**


## FunctionImagePreimage

#### L??: injective → fibres are singletons
- ∃! needs to be explained -- perhaps already in Quantus? (see table above)
- Add hidden hint for `obtain`
- Add hint regarding overly complicated goal after `use a`:

  `(fun a => f a = b) a ∧ ∀ (y : A), (fun a => f a = b) y → y = a`

  `simp` turns this into

  `f a = b ∧ ∀ (y : A), f y = b → y = a`

  **Or can mathlib's `use` be improved??**

## FunctionBij

#### L02 BOSS: inverse of a bijection

Update hint on choose -- we should have already seen exactly how to do this in FunctionSurj.

My solution:
````
constructor
intro h
obtain ⟨ h_inj, h_surj⟩ := h
choose g hg using h_surj
use g
have h_r : RightInverse g f
assumption
constructor
unfold LeftInverse
intro a
apply h_inj
rw [hg]
assumption
intro h
obtain ⟨ g, hL, hR ⟩ := h
unfold RightInverse at hR
unfold LeftInverse at *
constructor
intro a a' h
apply congr_arg g at h
rw [hL] at h
rw [hL] at h
assumption
intro b
use (g b)
apply hR
````

# Potential Future Levels

#### Bij Future L03: A × A × A = (Fin 3 → A)

**currently unplayable (too many new concepts/too much new notation)**

#### Bij Future L04: Equiv (how to use it)

Need to discuss structures here, and explain what the different fields of Equiv are.

My solution:
````
rw [bijective_iff_has_inverse]  -- already known from L02
use f.invFun
constructor
apply f.left_inv
apply f.right_inv
````
This solution avoids introducing the new theorem `Equiv.injective`, and recycles L02.


#### Bij Future L05: Equiv (how to construct it)

Should come before L04, as it necessarily explains what the fields of Equiv are.

My solution:
````
rw [bijective_iff_has_inverse] at h
  choose g hL hR using h
  constructor
  · use f
  · use g
  · use hL
  · use hR
````

Note that we cannot start with:
````
rw [bijective_iff_has_inverse] at h
obtain ⟨g, hL, hR⟩ := h
````
But this fails, as explained [here](https://leanprover-community.github.io/mathlib4_docs//Init/Core.html#Exists).
