import Godel.Anderson

/-
# Hájek's first emendation (AOE)

Hájek's route is different again from Anderson's and Fitting's. Where Anderson
weakens Axiom 1 and strengthens the definitions, and Fitting changes what
positivity applies to, Hájek **merges A1 and A2 into a single weaker axiom**
and rebuilds God-likeness on top of it.

    H:A12   ( P(φ) ∧ □∀x(φ x → ψ x) )  →  ¬ P(¬ψ)

"The negation of a property necessarily implied by a positive property is not
positive." Anderson's A1a is the case `ψ := φ`, and A2 is *not* assumed — the
conclusion is only that `¬ψ` fails to be positive, not that `ψ` is positive.

God-likeness is then defined through the derived notion

    P#(φ)   :=  ∃ψ ( P(ψ) ∧ □∀y(ψ y → φ y) )     -- `Pstar` below

of a property *necessarily implied by* a positive one:

    Gᴴ(x)   :=  ∀φ ( □φ(x) ↔ P#(φ) )

— a God-like being necessarily possesses those and only those properties that
are necessarily implied by a positive property. Essence and necessary
existence are Anderson's, reused verbatim from `Godel.Anderson`.

## A4 and A5 are superfluous

This is the striking part, and it is visible in the type of `T3` below: the
theorem takes `AxCore`, which contains only `H:A12` and `A3`. Neither `A4`
(positivity is necessary) nor `A5` (necessary existence is positive) is used
anywhere in the derivation.

Benzmüller, Weber and Woltzenlogel Paleo report exactly this, and add that
`A4` and `A5` are nonetheless *independent* of the rest — superfluous without
being redundant. We formalize the superfluousness; the independence would need
a further pair of models and is not done here.

The mechanism is `box_exists_of_god`. Hájek's biconditional lets a God-like
individual be fed its *own* God-likeness: `Gᴴ` is positive by `A3`, hence
trivially `P#(Gᴴ)`, hence `□Gᴴ(g)` — the God-like individual is necessarily
God-like, immediately. Where Scott needs `A5` and an essence argument to make
God-like existence necessary, Hájek's definition delivers it outright, and with
no frame condition at all.

## Frame conditions

`T3` needs **symmetry** and nothing else, for the same reason as Scott's:
carrying the conclusion from a merely possible world back to the actual one.
Everything before that step is frame-free.

Following Benzmüller, Weber and Woltzenlogel Paleo, *Computer-Assisted
Analysis of the Anderson–Hájek Ontological Controversy*, Logica Universalis 11
(2017), pp. 139–151, Figure 3.
-/

namespace Godel.Hajek

open Godel

universe u v

variable {W : Type u} {I : Type v}

/-- `P# φ` — `φ` is necessarily implied by some positive property.  Hájek's
`D4`, inlined into the definition of God-likeness in this emendation. -/
def Pstar (r : W → W → Prop) (P : Property I W → Sentence W)
    (φ : Property I W) : Sentence W :=
  fun w => ∃ ψ : Property I W, P ψ w ∧ box r (fun v => ∀ y, ψ y v → φ y v) w

/-- **Hájek's God-likeness**: `x` necessarily has exactly the properties that
are necessarily implied by a positive property. -/
def God (r : W → W → Prop) (P : Property I W → Sentence W) : Property I W :=
  fun x w => ∀ φ : Property I W, box r (φ x) w ↔ Pstar r P φ w

/-- **The core axioms**: `H:A12` and `A3`.  This is all `T3` needs. -/
structure AxCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  /-- **H:A12.**  Merges Anderson's `A1a` and `A2` into one weaker axiom. -/
  A12 : ∀ (w : W) (φ ψ : Property I W),
    P φ w → box r (fun v => ∀ x, φ x v → ψ x v) w → ¬ P (pneg ψ) w
  /-- **A3.**  Being God-like is positive. -/
  A3 : ∀ w : W, P (God r P) w

/-- Hájek's `AOE` in full.  `A4` and `A5` are stated for faithfulness and are
never used: see `T3`. -/
structure Ax (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends AxCore r P where
  /-- **A4.**  Positive properties are necessarily positive. -/
  A4 : ∀ (w : W) (φ : Property I W), P φ w → box r (P φ) w
  /-- **A5.**  Necessary existence — Anderson's — is positive. -/
  A5 : ∀ w : W, P (Anderson.NE r) w

variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-- Double complement of a property is the property itself.  Classical, via
propositional extensionality. -/
theorem pneg_pneg (φ : Property I W) : pneg (pneg φ) = φ := by
  funext x w
  show (¬ ¬ φ x w) = φ x w
  exact propext ⟨fun h => Classical.byContradiction h, fun h hn => hn h⟩

/-- **Anderson's A1a is derived**, as the case `ψ := φ` of `H:A12`. -/
theorem A1a_of_A12 (h : AxCore r P) (w : W) (φ : Property I W)
    (hφ : P φ w) : ¬ P (pneg φ) w :=
  h.A12 w φ φ hφ (fun _v _hv _x hx => hx)

/-- **Theorem 1.**  A positive property is possibly instantiated.

If `φ` were necessarily empty, the entailment hypothesis of `H:A12` would hold
vacuously for every `ψ`; taking `ψ := ¬φ` makes its conclusion say that `φ`
itself is not positive.  No frame condition. -/
theorem T1 (h : AxCore r P) (φ : Property I W) (w : W) (hφ : P φ w) :
    ∃ v, r w v ∧ ∃ x, φ x v :=
  Classical.byContradiction fun hc =>
    have hno : ¬ P (pneg (pneg φ)) w :=
      h.A12 w φ (pneg φ) hφ (fun v hv x hx => absurd ⟨v, hv, x, hx⟩ hc)
    hno (by rw [pneg_pneg]; exact hφ)

/-- **A God-like individual is necessarily God-like**, and so makes God-like
existence necessary.

This is where Hájek's definition earns its keep. `Gᴴ` is positive by `A3`, so
it is trivially necessarily implied by a positive property — itself. The
biconditional in `Gᴴ(g)` then converts that directly into `□Gᴴ(g)`.

Uses `A3` only.  **No `A4`, no `A5`, and no frame condition.** -/
theorem box_exists_of_god (h : AxCore r P) {g : I} {w : W}
    (hg : God r P g w) : box r (fun v => ∃ x, God r P x v) w := by
  have hstar : Pstar r P (God r P) w :=
    ⟨God r P, h.A3 w, fun _v _hv _y hy => hy⟩
  intro u hu
  exact ⟨g, (hg (God r P)).2 hstar u hu⟩

/-- **C.**  Possibly, a God-like being exists.  From `A3` and Theorem 1. -/
theorem possibly_god (h : AxCore r P) (w : W) :
    ∃ v, r w v ∧ ∃ x, God r P x v :=
  T1 h (God r P) w (h.A3 w)

/-- **Theorem 3.**  Necessarily, a God-like being exists.

Note the hypothesis: `AxCore`, not `Ax`.  **`A4` and `A5` are superfluous** —
they appear nowhere in the derivation. The only frame condition is symmetry,
used once, to carry the conclusion back from a merely possible world. -/
theorem T3 (hs : Symm r) (h : AxCore r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w := by
  obtain ⟨v, hwv, g, hg⟩ := possibly_god h w
  obtain ⟨x, hx⟩ := box_exists_of_god h hg w (hs w v hwv)
  exact box_exists_of_god h hx

/-- The same, stated against the full axiom set, for the record. -/
theorem T3_full (hs : Symm r) (h : Ax r P) (w : W) :
    box r (fun v => ∃ x, God r P x v) w :=
  T3 hs h.toAxCore w

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual; a property is positive exactly when the individual
has it at *every* world.  All of `AOE` holds — including `A4` and `A5`, so this
also certifies the consistency of the full axiom set — and modal collapse does
not.

As with Anderson's variant, the reason is that `Gᴴ` is stated entirely in terms
of `□`: a merely contingent sentence never reaches the biconditional. -/

section NoCollapse

/-- Positivity: the sole individual has the property at every world. -/
def hP : Property Unit Bool → Sentence Bool := fun φ _ => ∀ v, φ () v

theorem noCollapse_axioms : Ax (univ : Bool → Bool → Prop) hP where
  A12 := fun _w _φ _ψ hφ hb hn => hn false (hb false trivial () (hφ false))
  A3  := fun _w _v φ =>
    ⟨fun hb => ⟨φ, fun u => hb u trivial, fun _u _h _y hy => hy⟩,
     fun ⟨_ψ, hψ, hb⟩ u _ => hb u trivial () (hψ u)⟩
  A4  := fun _w _φ h _v _hv => h
  A5  := by
    intro _w _v φ hess u _hu
    exact ⟨(), ((hess φ).2 (fun _u _h _y hy => hy)) u trivial⟩

theorem noCollapse :
    ¬ ∀ (p : Sentence Bool) (w : Bool), p w → box univ p w := by
  intro h
  exact Bool.noConfusion (h (fun u => u = false) false rfl true trivial)

end NoCollapse

end Godel.Hajek
