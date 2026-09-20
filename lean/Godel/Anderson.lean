import Godel.Original

/-
# Anderson's variant (1990)

Anderson's emendation starts from a different complaint. Scott's `A1` is the
biconditional `P(¬φ) ↔ ¬P(φ)`, which says that of every property exactly one
of it and its negation is positive — an implausibly strong claim, and the
half that Gödel's refutation does *not* need. Anderson keeps only

    A1a.  P(¬φ) → ¬P(φ)

and drops `A1b`. That alone would break the argument, so he strengthens the
two definitions to compensate:

    Gᴬ(x)      :=  ∀φ ( P(φ) ↔ □φ(x) )
    φ essᴬ x   :=  ∀ψ ( □ψ(x) ↔ □∀y(φ(y) → ψ(y)) )

God-likeness becomes a biconditional — the positive properties are *exactly*
the ones `x` has necessarily — and essence likewise. Necessary existence is
unchanged except for using `essᴬ`.

## What this buys, and what it costs

The biconditional in `Gᴬ` is strong enough to make God-like individuals
unique (`monotheism` below), which is not a theorem of Scott's system. It also
makes God-likeness *stable* across accessible worlds (`god_transfers`), and
that is what carries the essence argument.

The cost is the frame: unlike Fitting's variant, which runs in `K`, Anderson's
needs the full `S5` package — reflexivity, transitivity and symmetry are all
used, exactly as in the Isabelle formalization this follows.

What it avoids is modal collapse: `noCollapse` gives a two-world `S5` model of
all the axioms in which collapse fails. The reason is that `Gᴬ` and `essᴬ`
speak only of what holds *necessarily*, so the essence clause never gets a
grip on a merely contingent sentence.

## Simplification

This file uses constant domains (possibilist quantifiers), where Anderson's
argument is normally presented with an existence predicate. For Anderson —
unlike Fitting, see `Godel.Fitting` — that costs nothing structural, because
his God-likeness is intensional: `∃x Gᴬ(x)` still varies from world to world,
so Theorem 1 still delivers merely possible existence and `A5` still does real
work.

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

/-- Anderson's axioms.  `A1b` is gone; `A3` is replaced by `T2`, which
postulates that God-likeness is positive. -/
structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1a : AxiomA1 P
  A2  : AxiomA2 r P
  T2  : ∀ w : W, P (God r P) w
  A4  : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  A5  : ∀ w : W, P (NE r) w

variable {r : W → W → Prop} {P : Property I W → Sentence W}

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

This is not a theorem of Scott's system. -/
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

Needs the full `S5` package, unlike Fitting's variant
(`Godel.Fitting.T3`), which needs no frame condition at all. -/
theorem T3 (hrefl : ∀ w : W, r w w) (hsymm : Symm r)
    (htrans : ∀ a b c : W, r a b → r b c → r a c) (h : Ax r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w := by
  obtain ⟨v, hwv, g, hg⟩ := T1 h (God r P) w (h.T2 w)
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
  T2  := fun _w _v _φ => ⟨fun h u _ => h u, fun h u => h u trivial⟩
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
