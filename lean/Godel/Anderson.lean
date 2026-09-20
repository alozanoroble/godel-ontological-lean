import Godel.Original

/-
# Anderson's variant (1990)

Anderson's emendation starts from a different complaint. Scott's `A1` is the
biconditional `P(¬φ) ↔ ¬P(φ)`, which says that of every property exactly one
of it and its negation is positive — an implausibly strong claim, and the
half that Gödel's refutation does *not* need. Anderson keeps only

    A1*.  P(φ) → ¬P(¬φ)

and drops `A1b`. (`Godel.AxiomA1`, which the other systems here share, is
written the other way round, `P(¬φ) → ¬P(φ)`. The two are equivalent by
contraposition alone — see `axiomA1_iff_A1star`, which checks it. Anderson's
own orientation is the one displayed above, and the one used in the 2017
computational study.) That alone would break the argument, so he strengthens the
two definitions to compensate:

    Gᴬ(x)      :=  ∀φ ( P(φ) ↔ □φ(x) )
    φ essᴬ x   :=  ∀ψ ( □ψ(x) ↔ □∀y(φ(y) → ψ(y)) )

God-likeness becomes a biconditional — the positive properties are *exactly*
the ones `x` has necessarily — and essence likewise. Necessary existence is
unchanged except for using `essᴬ`.

## What this buys

The biconditional in `Gᴬ` makes God-like individuals unique (`monotheism`
below) by a particularly direct route, and makes God-likeness *stable* across
accessible worlds (`god_transfers`), which is what carries the essence
argument.

Uniqueness is **not** peculiar to Anderson: `Godel.scott_monotheism` proves it
for Scott's system from `A1b` alone, with no frame condition at all. An earlier
version of this file claimed otherwise, and was wrong.

What Anderson avoids is modal collapse: `noCollapse` gives a two-world `S5`
model of all the axioms in which collapse fails. The reason is that `Gᴬ` and
`essᴬ` speak only of what holds *necessarily*, so the essence clause never gets
a grip on a merely contingent sentence.

## A warning about the frame hypotheses below

The derivations in this file assume reflexivity, transitivity **and** symmetry.
**Those hypotheses are not minimal, and nothing here shows that they are.**

- Anderson himself (1990, footnote 5) notes that the weaker logic `B` suffices
  for Theorem 3.
- Benzmüller, Weber and Woltzenlogel Paleo (*Logica Universalis* 11, 2017)
  report `T3` automated in `KB` for Anderson's emendation, and further report
  `A4` and `A5` to be **redundant** there — derivable from the rest, `A4` in
  `K4B` and `A5` already in `K`. That holds under the constant- and
  varying-domain readings they analyse. Under the **mixed** reading Anderson
  himself floats (actualist quantifiers only in `T3` and in the definition of
  essence), the same study finds `A4` still redundant but `A5` independent —
  and reports a countermodel to `T3` itself. Domain choice is not a free
  parameter here.

So the right reading of every hypothesis below is *"what this particular Lean
derivation consumes"*, never *"what Anderson's system requires"*. Tightening
these proofs towards `KB`, and deriving `A4`/`A5` rather than postulating them,
is open work in this development.

## Simplification

This file uses constant domains (possibilist quantifiers), where Anderson's
argument is normally presented with an existence predicate. That is a
substantive choice, not a free one: domain semantics was itself a central point
in the Anderson–Hájek dispute, and the 2017 study finds that redundancy results
and even the validity of `T3` in a mixed variant depend on it. Read this file
as one reconstruction among several, not as evidence that the choice does not
matter.

Following Benzmüller and Fuenmayor, arXiv:1910.08955, and the AFP entry
*Types, Tableaus and Gödel's God in Isabelle/HOL*, which in turn follow
Fitting's presentation of Anderson's argument.
-/

namespace Godel.Anderson

open Godel

universe u v

variable {W : Type u} {I : Type v}

/-- **Anderson's God-likeness**: the positive properties are exactly those `x`
has necessarily. -/
def God (r : W → W → Prop) (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, P φ w ↔ box r (φ x) w

/-- **Anderson's essence**: `φ` necessarily entails exactly the properties `x`
has necessarily. -/
def Ess (r : W → W → Prop) (φ : Property I W) (x : I) : Sentence W :=
  fun w => ∀ ψ : Property I W,
    box r (ψ x) w ↔ box r (fun v => ∀ y, φ y v → ψ y v) w

/-- **Anderson's necessary existence.** -/
def NE (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, Ess r φ x w → box r (fun v => ∃ y, φ y v) w

/-- Anderson's axioms.  `A1b` is gone; Gödel's `A3` is replaced by `A3p`,
which **postulates** that the revised God-likeness `Gᴬ` is positive.

A note on the name.  Anderson's own paper numbers this Axiom 3*; Fitting's
presentation — which the AFP development and this file follow — reaches it as
Proposition 11.16 and labels the corresponding Isabelle field `T2`.  It is
postulated here, not derived, so `T2` would be actively misleading and `A3p`
is used instead. -/
structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1a : AxiomA1 P
  A2  : AxiomA2 r P
  A3p : ∀ w : W, P (God r P) w
  A4  : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  A5  : ∀ w : W, P (NE r) w

variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-- **Anderson's A1\* and the shared `AxiomA1` are the same axiom.**

Anderson writes the retained half of A1 as `P(φ) → ¬P(¬φ)`; `Godel.AxiomA1`,
shared with Gödel's, Scott's and Hájek's systems here, is written
`P(¬φ) → ¬P(φ)`.  Both say "not both `φ` and `¬φ` are positive", and each is
the contraposition of the other — no substitution and no double negation of
properties is involved, so nothing turns on which is displayed. -/
theorem axiomA1_iff_A1star :
    AxiomA1 P ↔ ∀ (w : W) (φ : Property I W), P φ w → ¬ P (pneg φ) w :=
  ⟨fun h w φ hp hn => h w φ hn hp, fun h w φ hn hp => h w φ hp hn⟩

/-- **Theorem 1.**  A positive property is possibly instantiated.  This is
Gödel's Theorem 1 unchanged — `Godel.possibly_exists` needs only `A1a` and
`A2`, both of which Anderson keeps. -/
theorem T1 (h : Ax r P) (φ : Property I W) (w : W) (hφ : P φ w) :
    ∃ v, r w v ∧ ∃ x, φ x v :=
  possibly_exists h.A1a h.A2 φ w hφ

/-- **Monotheism.**  Anderson's biconditional makes God-like individuals
unique at a world.  Take the property of being identical to `x`: `x` has it
necessarily, so it is positive, so any God-like `y` has it necessarily too,
and reflexivity brings that down to the world itself.

Uniqueness is *not* peculiar to Anderson — see `Godel.scott_monotheism`, which
gets it for Scott's system from `A1b` alone and needs no frame condition.  What
Anderson's biconditional buys is directness, not the result.  Reflexivity here
is what *this* proof uses; it is not shown to be necessary. -/
theorem monotheism (hrefl : ∀ w : W, r w w) {x y : I} {w : W}
    (hx : God r P x w) (hy : God r P y w) : y = x :=
  ((hy (fun z _ => z = x)).1
    ((hx (fun z _ => z = x)).2 (fun _ _ => rfl))) w (hrefl w)

/-- **God-likeness is stable.**  If `x` is God-like at `w` then it is God-like
at every accessible world.  This is where symmetry and transitivity are used,
together with `A4`. -/
theorem god_transfers (hsymm : Symm r) (htrans : ∀ a b c : W, r a b → r b c → r a c)
    (h : Ax r P) {x : I} {w v : W} (hwv : r w v) (hx : God r P x w) :
    God r P x v := by
  intro φ
  constructor
  · -- `P φ v` travels back to `w` along symmetry, then out again by transitivity
    intro hPv
    intro u hvu
    exact (hx φ).1 (h.A4 v φ hPv w (hsymm w v hwv)) u (htrans w v u hwv hvu)
  · -- and conversely
    intro hbox
    exact h.A4 w φ ((hx φ).2 (fun u hwu => hbox u (htrans v w u (hsymm w v hwv) hwu)))
      v hwv

/-- **God-likeness is an essence of any God-like individual.**

The forward direction uses `A4` and reflexivity; the backward direction uses
`god_transfers`, hence the rest of `S5`. -/
theorem god_essential (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P)
    {x : I} {w : W} (hx : God r P x w) : Ess r (God r P) x w := by
  intro ψ
  constructor
  · intro hbox v hwv y hy
    exact (hy ψ).1 (h.A4 w ψ ((hx ψ).2 hbox) v hwv) v (hrefl v)
  · intro hent v hwv
    exact hent v hwv x (god_transfers hsymm htrans h hwv hx)

/-- A God-like individual makes God-like existence necessary.  This is the
step that uses `A5`. -/
theorem box_exists_of_god (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P)
    {g : I} {w : W} (hg : God r P g w) :
    box r (fun v => ∃ y, God r P y v) w :=
  ((hg (NE r)).1 (h.A5 w) w (hrefl w)) (God r P)
    (god_essential hrefl hsymm htrans h hg)

/-- **Theorem 3.**  Necessarily, a God-like individual exists.

**This derivation** assumes reflexivity, transitivity and symmetry.  Those are
the hypotheses *this proof* consumes — they are **not** minimal and are not a
property of Anderson's system.  Anderson (1990, fn. 5) notes that `B` suffices;
Benzmüller, Weber and Woltzenlogel Paleo (2017) report `T3` automated in `KB`
and `A4`, `A5` redundant.  Reaching `KB` here would need a different route:
`god_transfers` uses transitivity and `box_exists_of_god` uses reflexivity, and
neither is avoidable in the present argument.  Open work. -/
theorem T3 (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w := by
  obtain ⟨v, hwv, g, hg⟩ := T1 h (God r P) w (h.A3p w)
  intro u hwu
  exact box_exists_of_god hrefl hsymm htrans h hg u
    (htrans v w u (hsymm w v hwv) hwu)

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual, and a property is positive exactly when the
individual has it at *every* world.  All of Anderson's axioms hold over the
universal relation, and modal collapse does not.

The mechanism: `Gᴬ` and `essᴬ` are stated entirely in terms of `□`, so a
merely contingent sentence never satisfies the antecedent of the essence
clause, and the collapse derivation of `Godel.modal_collapse` has no
counterpart. -/

section NoCollapse

/-- Positivity: the sole individual has the property at every world. -/
def cP : Property Unit Bool → Sentence Bool := fun φ _ => ∀ v, φ () v

theorem noCollapse_axioms : Ax (univ : Bool → Bool → Prop) cP where
  A1a := fun _w _φ hn hp => (hn false) (hp false)
  A2  := fun _w _φ _ψ hφ hb v => hb v trivial () (hφ v)
  A3p := fun _w _v _φ => ⟨fun h u _ => h u, fun h u => h u trivial⟩
  A4  := fun _w _φ h _v _hv => h
  A5  := by
    intro _w _v φ hess u _hu
    exact ⟨(), ((hess φ).2 (fun _u _h _y hy => hy)) u trivial⟩

theorem noCollapse :
    ¬ ∀ (p : Sentence Bool) (w : Bool), p w → box univ p w := by
  intro h
  exact Bool.noConfusion (h (fun u => u = false) false rfl true trivial)

end NoCollapse

end Godel.Anderson
