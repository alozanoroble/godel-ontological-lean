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

## What the biconditional buys, and how cheaply

Feed `Gᴬ` its own defining property. `A3*` says `P(Gᴬ)`, so the biconditional
converts that directly into `□Gᴬ(x)`: **a God-like individual is necessarily
God-like**, with no essence argument, no `A4` and no `A5` (`box_god`). Symmetry
then pulls a God-like individual back from the accessible world that `T1`
produces to the world of evaluation (`god_back`), and one more application of
`box_god` pushes it out to every accessible world. That is all of `T3`:

    T3 needs `A1a`, `A2`, `A3*` and symmetry — the logic `KB`.

`A1a` and `A2` enter only through `Godel.possibly_exists`, and only to supply
*some* world accessible from `w`.

This reproduces in Lean what Benzmüller, Weber and Woltzenlogel Paleo report
from automated analysis (*Logica Universalis* 11, 2017): `T3` in `KB`, with
`A4` and `A5` redundant. **Nothing here is new mathematics**; what changes is
that the frame condition and the axiom list are now enforced by Lean's type
checker rather than recorded in a comment. An earlier version of this file
derived `T3` from reflexivity, transitivity *and* symmetry and flagged the gap
to `KB` as open work; `T3_viaEssence` preserves that route for comparison.

## The two redundancy results

Both are now proved rather than cited.

- **`A5` is derivable in `K`** (`A5_of_A2_A3p`). The reason is stronger than
  redundancy: with Anderson's biconditional essence, `NEᴬ` holds of *every*
  individual at *every* world (`ne_universal`). Put `ψ := φ` in `φ essᴬ x` and
  the right-hand side becomes `□∀y(φ(y) → φ(y))`, a validity, so `□φ(x)` — an
  essence is automatically had, necessarily, so its instantiation is automatic.
  `A2` and `A3*` then lift that to `P(NEᴬ)`.
- **`A4` is derivable in `K4B`** (`A4_of_core`). Given `P(φ)` at `w` and
  `r w u`, the God-like `g` supplied at `w` is God-like at `u` too, so `P(φ)`
  at `u` amounts to `□φ(g)` at `u` — and transitivity carries the witnesses of
  `□φ(g)` at `w` to every world accessible from `u`.

So `Ax` below is stated in full for faithfulness to Anderson, but `AxCore` is
what the mathematics consumes, and `A4_of_core` / `A5_of_A2_A3p` show the
remaining two are not independent additions.

## Uniqueness

`monotheism` needs `AxCore` and **no frame condition** — `A1a`, `A2` and `A3*`
already guarantee that `w` has a successor, which is the only thing the argument
needs beyond the biconditional. Uniqueness is not peculiar to Anderson:
`Godel.scott_monotheism` proves it for Scott's system from `A1b` alone. An
earlier version of this file claimed otherwise, and was wrong.

## Modal collapse

`noCollapse` gives a two-world `S5` model of all the axioms in which collapse
fails. The reason is that `Gᴬ` and `essᴬ` speak only of what holds
*necessarily*, so the essence clause never gets a grip on a merely contingent
sentence.

## Simplification

This file uses constant domains (possibilist quantifiers), where Anderson's
argument is normally presented with an existence predicate. That is a
substantive choice, not a free one: domain semantics was itself a central point
in the Anderson–Hájek dispute. The 2017 study finds `A4` redundant but `A5`
**independent** under the mixed reading Anderson himself floats — actualist
quantifiers only in `T3` and in the definition of essence — and reports a
countermodel to `T3` itself there. Everything below is for the constant-domain
reading, and none of it transfers to the mixed one.

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

/-- The part of Anderson's system that the mathematics below actually uses.

`A3p` **postulates** that the revised God-likeness `Gᴬ` is positive.  A note on
the name: Anderson's own paper numbers this Axiom 3*; Fitting's presentation —
which the AFP development and this file follow — reaches it as Proposition
11.16 and labels the corresponding Isabelle field `T2`.  It is postulated here,
not derived, so `T2` would be actively misleading and `A3p` is used instead. -/
structure AxCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  /-- **A1\*.**  Anderson's retained half of Gödel's `A1`; `A1b` is dropped. -/
  A1a : AxiomA1 P
  /-- **A2.**  Positivity is closed under necessary entailment. -/
  A2 : AxiomA2 r P
  /-- **A3\*.**  The revised God-likeness is positive. -/
  A3p : ∀ w : W, P (God r P) w

/-- Anderson's system in full.  `A4` and `A5` are stated for faithfulness and
are never used: see `T3`, and `A4_of_core` / `A5_of_A2_A3p` for the two
published redundancy results. -/
structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends AxCore r P where
  /-- **A4.**  Positive properties are necessarily positive. -/
  A4 : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  /-- **A5\*.**  Necessary existence is positive. -/
  A5 : ∀ w : W, P (NE r) w

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
theorem T1 (h : AxCore r P) (φ : Property I W) (w : W) (hφ : P φ w) :
    ∃ v, r w v ∧ ∃ x, φ x v :=
  possibly_exists h.A1a h.A2 φ w hφ

/-! ### The direct route to `T3`

Three short lemmas, no frame condition until the last step, and `A4`/`A5`
nowhere. -/

/-- **A God-like individual is necessarily God-like.**

Instantiate the biconditional in `Gᴬ` at `Gᴬ` itself: `A3*` supplies `P(Gᴬ)`,
and the biconditional turns it straight into `□Gᴬ(x)`.  This is the step that
Gödel's and Scott's systems have to reach through essence and `A5`.

No frame condition; `A1a`, `A2`, `A4`, `A5` all unused. -/
theorem box_god (hA3p : ∀ w : W, P (God r P) w) {x : I} {w : W}
    (hx : God r P x w) : box r (God r P x) w :=
  (hx (God r P)).1 (hA3p w)

/-- **God-likeness reaches back along symmetry.**  If `x` is God-like at some
world accessible from `w`, it is God-like at `w`.  Symmetry only. -/
theorem god_back (hsymm : Symm r) (hA3p : ∀ w : W, P (God r P) w) {x : I}
    {w v : W} (hwv : r w v) (hx : God r P x v) : God r P x w :=
  box_god hA3p hx w (hsymm w v hwv)

/-- **A God-like individual exists at every world.**

`T1` applied to `Gᴬ` produces one at *some* accessible world; `god_back` brings
it home.  Logic `KB`. -/
theorem exists_god (hsymm : Symm r) (h : AxCore r P) (w : W) :
    ∃ x, God r P x w := by
  obtain ⟨v, hwv, g, hg⟩ := T1 h (God r P) w (h.A3p w)
  exact ⟨g, god_back hsymm h.A3p hwv hg⟩

/-- **Theorem 3.**  Necessarily, a God-like individual exists.

**In `KB`, from `A1a`, `A2` and `A3*` alone.**  `exists_god` produces a God-like
`g` at `w`; `box_god` makes it God-like at every world accessible from `w`.
`A4` and `A5` are not hypotheses of this theorem, which is why it takes `AxCore`
rather than `Ax` — the type checker now enforces what a comment used to assert.

This matches the `KB` result reported by Benzmüller, Weber and Woltzenlogel
Paleo (2017) from automated analysis, and Anderson's own footnote 5 that the
logic `B` suffices.  `T3_viaEssence` below reconstructs the essence route and
records what it costs. -/
theorem T3 (hsymm : Symm r) (h : AxCore r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w := by
  obtain ⟨g, hg⟩ := exists_god hsymm h w
  exact fun u hwu => ⟨g, box_god h.A3p hg u hwu⟩

/-- **Monotheism.**  Anderson's biconditional makes God-like individuals unique.

Take the property of being identical to `x`: `x` has it necessarily, so it is
positive, so any God-like `y` has it necessarily too.  To bring that down to an
actual identity we need one world accessible from `w` — and `T1` supplies one,
so **no frame condition is required**.  (An earlier version of this proof used
reflexivity for that step.)

Uniqueness is *not* peculiar to Anderson — see `Godel.scott_monotheism`, which
gets it for Scott's system from `A1b` alone.  What Anderson's biconditional
buys is directness, not the result. -/
theorem monotheism (h : AxCore r P) {x y : I} {w : W}
    (hx : God r P x w) (hy : God r P y w) : y = x := by
  obtain ⟨v, hwv, _⟩ := T1 h (God r P) w (h.A3p w)
  exact ((hy (fun z _ => z = x)).1
    ((hx (fun z _ => z = x)).2 (fun _ _ => rfl))) v hwv

/-! ### `A4` and `A5` are redundant

Benzmüller, Weber and Woltzenlogel Paleo (2017) report both as redundant for
Anderson's emendation under the constant-domain reading — `A5` already in `K`,
`A4` in `K4B`.  Both are proved here. -/

/-- **Anderson's necessary existence is satisfied by everything.**

Put `ψ := φ` in `φ essᴬ x`.  The right-hand side is `□∀y(φ(y) → φ(y))`, a
validity, so the biconditional yields `□φ(x)`: anything that is an essence of
`x` is necessarily had by `x`, hence necessarily instantiated — by `x`.

No axioms and no frame condition whatsoever.  This is why `A5` carries no
content in Anderson's system: `NEᴬ` is the universally true property. -/
theorem ne_universal (x : I) (w : W) : NE r x w := by
  intro φ hess u hwu
  exact ⟨x, ((hess φ).2 (fun _v _hv _y hy => hy)) u hwu⟩

/-- **`A5` is derivable in `K`, from `A2` and `A3*`.**

`Gᴬ` is positive by `A3*`, and necessarily entails `NEᴬ` because
`ne_universal` makes `NEᴬ` true outright.  `A2` then transfers positivity. -/
theorem A5_of_A2_A3p (hA2 : AxiomA2 r P) (hA3p : ∀ w : W, P (God r P) w)
    (w : W) : P (NE r) w :=
  hA2 w (God r P) (NE r) (hA3p w) (fun v _hv x _hx => ne_universal x v)

/-- **`A4` is derivable in `K4B`, from `AxCore`.**

Let `P(φ)` hold at `w` and let `r w u`.  `exists_god` gives a God-like `g` at
`w` (symmetry), and `box_god` makes it God-like at `u` as well, so `P(φ)` at `u`
is equivalent to `□φ(g)` at `u`.  The God-likeness of `g` at `w` turns the
hypothesis into `□φ(g)` at `w`, and transitivity carries that to every world
accessible from `u`. -/
theorem A4_of_core (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : AxCore r P) :
    AxiomA4 r P := by
  intro w φ hφ u hwu
  obtain ⟨g, hg⟩ := exists_god hsymm h w
  exact ((box_god h.A3p hg u hwu) φ).2
    (fun u' huu' => (hg φ).1 hφ u' (htrans w u u' hwu huu'))

/-! ### Anderson's own route, for comparison

The essence argument reconstructed.  It reaches the same `T3` but consumes
reflexivity and transitivity on top of symmetry, and uses `A4` and `A5`.  Kept
because the contrast is the point: the cost is in the route, not in Anderson's
system. -/

/-- **God-likeness is stable.**  If `x` is God-like at `w` then it is God-like
at every accessible world.  Uses symmetry, transitivity and `A4`.

Superseded by `box_god`, which gets the same conclusion from `A3*` alone. -/
theorem god_transfers (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P) {x : I}
    {w v : W} (hwv : r w v) (hx : God r P x w) : God r P x v := by
  intro φ
  constructor
  · intro hPv u hvu
    exact (hx φ).1 (h.A4 v φ hPv w (hsymm w v hwv)) u (htrans w v u hwv hvu)
  · intro hbox
    exact h.A4 w φ
      ((hx φ).2 (fun u hwu => hbox u (htrans v w u (hsymm w v hwv) hwu))) v hwv

/-- **God-likeness is an essence of any God-like individual.**  Forward
direction uses `A4` and reflexivity; backward uses `god_transfers`. -/
theorem god_essential (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P)
    {x : I} {w : W} (hx : God r P x w) : Ess r (God r P) x w := by
  intro ψ
  constructor
  · intro hbox v hwv y hy
    exact (hy ψ).1 (h.A4 w ψ ((hx ψ).2 hbox) v hwv) v (hrefl v)
  · intro hent v hwv
    exact hent v hwv x (god_transfers hsymm htrans h hwv hx)

/-- A God-like individual makes God-like existence necessary, via `A5`. -/
theorem box_exists_of_god (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P)
    {g : I} {w : W} (hg : God r P g w) :
    box r (fun v => ∃ y, God r P y v) w :=
  ((hg (NE r)).1 (h.A5 w) w (hrefl w)) (God r P)
    (god_essential hrefl hsymm htrans h hg)

/-- **Theorem 3 by Anderson's essence route.**  Same conclusion as `T3`, but
consuming reflexivity, transitivity, `A4` and `A5` on top of symmetry — an
artefact of this argument, not of Anderson's system.  Compare `T3`. -/
theorem T3_viaEssence (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w := by
  obtain ⟨v, hwv, g, hg⟩ := T1 h.toAxCore (God r P) w (h.A3p w)
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

theorem noCollapse_A2 : AxiomA2 (univ : Bool → Bool → Prop) cP :=
  fun _w _φ _ψ hφ hb v => hb v trivial () (hφ v)

theorem noCollapse_A3p : ∀ w : Bool, cP (God (univ : Bool → Bool → Prop) cP) w :=
  fun _w _v _φ => ⟨fun h u _ => h u, fun h u => h u trivial⟩

/-- `A5` is *not* checked by hand here: `A5_of_A2_A3p` derives it from the two
above, which is the redundancy result doing visible work. -/
theorem noCollapse_axioms : Ax (univ : Bool → Bool → Prop) cP where
  A1a := fun _w _φ hn hp => (hn false) (hp false)
  A2 := noCollapse_A2
  A3p := noCollapse_A3p
  A4 := fun _w _φ h _v _hv => h
  A5 := A5_of_A2_A3p noCollapse_A2 noCollapse_A3p

theorem noCollapse :
    ¬ ∀ (p : Sentence Bool) (w : Bool), p w → box univ p w := by
  intro h
  exact Bool.noConfusion (h (fun u => u = false) false rfl true trivial)

end NoCollapse

end Godel.Anderson
