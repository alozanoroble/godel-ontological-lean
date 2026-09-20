import Godel.Modal

/-
# Gödel's original (1970) axioms are inconsistent

Gödel's ontological argument, in the form of his 1970 notes, rests on a
primitive `P φ` ("the property `φ` is *positive*") together with three
definitions and five axioms.  This file formalises the 1970 version and
derives `False` from it.

The inconsistency was discovered in 2013 by the higher-order theorem prover
Leo-II and reported by Christoph Benzmüller and Bruno Woltzenlogel Paleo,
*The inconsistency in Gödel's ontological argument: a success story for AI in
metaphysics*, IJCAI-16, pp. 936–942.  What is formalised below is their informal
argument (their §4.1), which they also reconstructed in Isabelle/HOL.  It is
their result, not a new one; this is a Lean 4 rendering of it.

## Where the argument breaks

Gödel defines

    φ ess x  :=  ∀ψ (ψ(x) → □∀y (φ(y) → ψ(y)))

— "everything x has, φ necessarily carries with it".  Note what is *absent*:
there is no requirement that `x` actually have `φ`.

Consider then the **empty property** `e`, had by nothing in any world.  The
implication `e(y) → ψ(y)` is vacuously true at every world, for every `ψ`.  So
`□∀y (e(y) → ψ(y))` holds outright, and therefore

    e ess x    for every individual x whatsoever.

This is the Empty Essence Lemma (`emptyProperty_ess` below).

Now Axiom 5 says necessary existence is positive, so by Gödel's Theorem 1 it
is possibly exemplified: some accessible world holds an `x` with

    NE(x)  =  ∀φ (φ ess x → □∃y φ(y)).

Instantiating at `φ := e` gives `□∃y e(y)` — necessarily, something has the
empty property.  Since nothing does, at any world, this says exactly that *no
world at all is accessible from* `v`.  But Axiom 5 and Theorem 1 hold at `v`
too, and together they produce an accessible world.  Contradiction.

Scott's variant (c. 1972) adds the single conjunct `φ(x)` to the definition of
essence.  That one conjunct is exactly what blocks this: see
`empty_not_scottEss` at the end of the file.

## What the derivation uses

Only `A1` (one half of it), `A2` and `A5`, plus the existence of at least one
world.  In particular **`A3` and `A4` are not used at all**, and *no frame
condition whatsoever* is imposed on the accessibility relation — not
seriality, not reflexivity, not symmetry.  The axioms are already inconsistent
in `K`, the weakest normal modal logic.

The last step is what buys this.  A cruder argument cashes `□∃y e(y)` into a
witness using seriality, which costs the logic `D`.  Here instead we use that
the axioms hold at *every* world, `v` included, so Theorem 1 applied at `v`
supplies the accessible world that `□∃y e(y)` has just ruled out.
-/

namespace Godel

universe u v

variable {W : Type u} {I : Type v}
variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-- `G x`: `x` has every positive property.  ("x is God-like".) -/
def God (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, P φ w → φ x w

/-- **Gödel's** definition of essence, from the 1970 notes.

`φ ess x` iff every property of `x` is necessarily entailed by `φ`.  There is
deliberately no conjunct `φ x w` here — that is Scott's later emendation, and
its absence is what makes the system inconsistent. -/
def Ess (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => ∀ ψ : Property I W, ψ x w → box r (fun v => ∀ y, φ y v → ψ y v) w

/-- **Scott's** definition of essence: Gödel's, with the conjunct `φ x w`
restored. -/
def ScottEss (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => φ x w ∧ ∀ ψ : Property I W, ψ x w → box r (fun v => ∀ y, φ y v → ψ y v) w

/-- `NE x`: every essence of `x` is necessarily instantiated.
("x has necessary existence".) -/
def NE (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, Ess r φ x w → box r (fun v => ∃ y, φ y v) w

/-! ### The axioms, stated individually

Each is asserted to hold at *every* world.  They are named so that the
hypotheses of each theorem below say exactly which of Gödel's axioms it
consumes. -/

/-- **A1**, in the half that the derivation uses.  Gödel's A1 is the
biconditional `P(¬φ) ↔ ¬P(φ)`, which is stronger, so an inconsistency here is
an inconsistency there. -/
abbrev AxiomA1 (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), P (pneg φ) w → ¬ P φ w

/-- **A2.** Positivity is closed under necessary entailment. -/
abbrev AxiomA2 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ ψ : Property I W),
    P φ w → box r (fun v => ∀ x, φ x v → ψ x v) w → P ψ w

/-- **A3.** Being God-like is a positive property.  *Not used below.* -/
abbrev AxiomA3 (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (God P) w

/-- **A4.** Positivity is necessary.  *Not used below.* -/
abbrev AxiomA4 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w

/-- **A5.** Necessary existence is a positive property. -/
abbrev AxiomA5 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (NE r) w

/-- Gödel's axioms as of the 1970 notes, bundled.  All five are included, for
faithfulness; the derivation uses only `A1`, `A2` and `A5`. -/
structure Godel1970 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1 : AxiomA1 P
  A2 : AxiomA2 r P
  A3 : AxiomA3 P
  A4 : AxiomA4 r P
  A5 : AxiomA5 r P

/-- **Theorem 1.** A positive property is possibly instantiated.

If `φ` were necessarily empty then `□∀x (φ x → ψ x)` would hold vacuously for
*every* `ψ`, so by `A2` every property would be positive — including both `ψ`
and `¬ψ`, contradicting `A1`.

Uses `A1` and `A2` only; no frame conditions. -/
theorem possibly_exists (hA1 : AxiomA1 P) (hA2 : AxiomA2 r P)
    (φ : Property I W) (w : W) (hφ : P φ w) : ∃ v, r w v ∧ ∃ x, φ x v :=
  Classical.byContradiction fun hc =>
    have key : ∀ ψ : Property I W, P ψ w := fun ψ =>
      hA2 w φ ψ hφ (fun v hv x hx => absurd ⟨v, hv, x, hx⟩ hc)
    hA1 w φ (key (pneg φ)) (key φ)

/-- The property had by nothing, at any world. -/
def emptyProperty (I : Type v) (W : Type u) : Property I W := fun _ _ => False

/-- **Empty Essence Lemma.**  On Gödel's definition of essence, the empty
property is an essence of *every* individual — vacuously, since `e y v → ψ y v`
has a false antecedent everywhere.

No axiom, no frame condition, no classical reasoning. -/
theorem emptyProperty_ess (x : I) (w : W) :
    Ess r (emptyProperty I W) x w := by
  intro _ψ _hψ _v _hv _y hy
  exact hy.elim

/-- **Gödel's 1970 axioms are inconsistent**, from `A1`, `A2` and `A5` alone.

No frame condition is assumed on `r`, so this is already a refutation in the
modal logic `K`.  The only other hypothesis is that there is at least one
world, without which every axiom is vacuous. -/
theorem inconsistent_of_A1_A2_A5 [Nonempty W]
    (hA1 : AxiomA1 P) (hA2 : AxiomA2 r P) (hA5 : AxiomA5 r P) : False := by
  -- A5 and Theorem 1 together: at *every* world, necessary existence is
  -- possibly exemplified.
  have key : ∀ w : W, ∃ v, r w v ∧ ∃ x, NE r x v :=
    fun w => possibly_exists hA1 hA2 (NE r) w (hA5 w)
  obtain ⟨w₀⟩ := ‹Nonempty W›
  obtain ⟨v, _, x, hx⟩ := key w₀
  -- The empty property is an essence of `x`, so `NE x` makes it necessarily
  -- instantiated.  Nothing instantiates it anywhere, so this says precisely
  -- that no world is accessible from `v`.
  have dead : ∀ u, r v u → False := by
    intro u hu
    obtain ⟨_y, hy⟩ := hx (emptyProperty I W) (emptyProperty_ess x v) u hu
    exact hy
  -- But the axioms hold at `v` too, and hand us an accessible world.
  obtain ⟨v', hv', _⟩ := key v
  exact dead v' hv'

/-- **Gödel's 1970 axioms are inconsistent.**  Over an arbitrary frame; `A3`
and `A4` are carried by the structure but never used. -/
theorem godel_1970_inconsistent [Nonempty W] (h : Godel1970 r P) : False :=
  inconsistent_of_A1_A2_A5 h.A1 h.A2 h.A5

/-- The same in the usual `S5` reading, with `□` as "at every world".  A
special case, since no frame condition was needed in the first place. -/
theorem godel_1970_inconsistent_S5 [Nonempty W]
    (h : Godel1970 (univ : W → W → Prop) P) : False :=
  godel_1970_inconsistent h

/-- **Scott's emendation blocks the derivation.**  With the conjunct `φ x w`
restored, the empty property is an essence of nothing, so the Empty Essence
Lemma — and with it the contradiction above — is unavailable. -/
theorem empty_not_scottEss (x : I) (w : W) :
    ¬ ScottEss r (emptyProperty I W) x w :=
  fun h => h.1

end Godel
