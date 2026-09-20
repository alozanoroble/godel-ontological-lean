import Godel.Original

/-
# Scott's 1987 variant: the positive argument, and its price

Dana Scott's version of Gödel's argument differs in exactly one conjunct: his
definition of essence requires that `x` actually have `φ`.  That single change
blocks the refutation of `Godel.Original` (see `empty_not_scottEss` there), and
this file carries out the argument that Gödel intended:

* `scott_T2` — God-likeness is an essence of any God-like individual;
* `scott_T3` — necessarily, a God-like individual exists;

and then the objection that the argument has never shaken off:

* `modal_collapse` — every truth is a necessary truth, `p → □p`;
* `s5_unique_world` — under the `S5` reading, there is only one world.

## Reading these theorems correctly

Every result below is a *conditional*: it takes a `Scott1987 r P` hypothesis
and derives something from it.  `scott_T3` is not a proof that God exists.  It
is a proof that *if* one grants Scott's five axioms, then `□∃x G(x)` follows —
which is exactly the claim the ontological argument makes, and exactly as much
as a formalization can settle.  Whether the axioms should be granted is not a
question Lean can answer.

`modal_collapse` is the reason this matters.  From the same axioms one derives
that nothing is contingent: every truth whatsoever is necessary.  That is a
consequence most people are unwilling to accept, so the argument's soundness is
bought at a price that is usually judged too high.  `s5_unique_world` makes the
price vivid: under the usual `S5` reading the axioms force the space of
possible worlds to be a single point.

## Frame conditions

The positive argument needs **symmetry** of the accessibility relation, and
nothing else — no reflexivity, no transitivity.  That is the modal logic `B`,
weaker than the `S5` in which the argument is usually presented.  Symmetry is
used in exactly one place, `exists_god`.
-/

namespace Godel

universe u v

variable {W : Type u} {I : Type v}
variable {r : W → W → Prop} {P : Property I W → Sentence W}

/-- **Scott's** necessary existence: every *Scott*-essence of `x` is
necessarily instantiated.  Identical to Gödel's `NE` except that it is built
on `ScottEss` rather than `Ess`. -/
def NES (r : W → W → Prop) : Property I W :=
  fun x w => ∀ φ : Property I W, ScottEss r φ x w → box r (fun v => ∃ y, φ y v) w

/-- **A1**, the converse half.  Gödel's and Scott's A1 is the biconditional
`P(¬φ) ↔ ¬P(φ)`; the refutation in `Godel.Original` needed only `AxiomA1`,
but the positive argument needs this direction too. -/
abbrev AxiomA1b (P : Property I W → Sentence W) : Prop :=
  ∀ (w : W) (φ : Property I W), ¬ P φ w → P (pneg φ) w

/-- **A5**, in Scott's form: *Scott*-necessary existence is a positive
property. -/
abbrev AxiomA5S (r : W → W → Prop) (P : Property I W → Sentence W) : Prop :=
  ∀ w : W, P (NES r) w

/-- Scott's axioms.  `A1a` and `A1b` are the two halves of the biconditional
A1; `A2`, `A3` and `A4` are as in Gödel's system; `A5` is stated with Scott's
necessary existence. -/
structure Scott1987 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1a : AxiomA1 P
  A1b : AxiomA1b P
  A2  : AxiomA2 r P
  A3  : AxiomA3 P
  A4  : AxiomA4 r P
  A5  : AxiomA5S r P

/-- Anything a God-like individual has is positive.

If `ψ` were not positive then `¬ψ` would be, by `A1b`, and a God-like `x` would
have `¬ψ` — contradicting `ψ(x)`. -/
theorem positive_of_god (hA1b : AxiomA1b P) {x : I} {w : W}
    (hg : God P x w) (ψ : Property I W) (hψ : ψ x w) : P ψ w :=
  Classical.byContradiction fun hnp => hg (pneg ψ) (hA1b w ψ hnp) hψ

/-- **Theorem 2.**  God-likeness is an essence, in Scott's sense, of any
God-like individual.

Uses `A1b` and `A4`.  No frame condition. -/
theorem scott_T2 (hA1b : AxiomA1b P) (hA4 : AxiomA4 r P) {x : I} {w : W}
    (hg : God P x w) : ScottEss r (God P) x w := by
  refine ⟨hg, ?_⟩
  intro ψ hψ v hv y hy
  exact hy ψ (hA4 w ψ (positive_of_god hA1b hg ψ hψ) v hv)

/-- A God-like individual makes the existence of a God-like individual
necessary: `G(g) → □∃y G(y)`.

This is the step that uses `A5`.  Note that it needs `ScottEss`, which is
exactly what Gödel's definition failed to supply. -/
theorem box_exists_god_of_god (hA1b : AxiomA1b P) (hA4 : AxiomA4 r P)
    (hA5 : AxiomA5S r P) {g : I} {w : W} (hg : God P g w) :
    box r (fun v => ∃ y, God P y v) w :=
  hg (NES r) (hA5 w) (God P) (scott_T2 hA1b hA4 hg)

/-- A God-like individual exists at *every* world.

Theorem 1 applied to `A3` puts one at some accessible world `v`; the previous
lemma makes its existence necessary *at `v`*; symmetry brings that back to `w`.
This is the only place symmetry is used. -/
theorem exists_god (hs : Symm r) (h : Scott1987 r P) (w : W) :
    ∃ x, God P x w := by
  obtain ⟨v, hwv, g, hg⟩ := possibly_exists h.A1a h.A2 (God P) w (h.A3 w)
  exact box_exists_god_of_god h.A1b h.A4 h.A5 hg w (hs w v hwv)

/-- **Theorem 3.**  Necessarily, a God-like individual exists.

This is the conclusion of the ontological argument.  It is a conditional: it
says that Scott's axioms entail `□∃x G(x)`, not that `□∃x G(x)`. -/
theorem scott_T3 (hs : Symm r) (h : Scott1987 r P) (w : W) :
    box r (fun v => ∃ x, God P x v) w := by
  obtain ⟨g, hg⟩ := exists_god hs h w
  exact box_exists_god_of_god h.A1b h.A4 h.A5 hg

/-- **Modal collapse.**  Every truth is a necessary truth.

Take any sentence `p` true at `w`, and regard "being such that `p`" as a
property.  A God-like `g` has it, so by Theorem 2 God-likeness necessarily
entails it; and by Theorem 3 there is a God-like individual at every
accessible world.  So `p` holds at every accessible world.

Nothing is contingent.  This is the standard objection to the argument, due to
Sobel, and it applies to Scott's consistent version, not only to Gödel's. -/
theorem modal_collapse (hs : Symm r) (h : Scott1987 r P)
    (p : Sentence W) (w : W) (hp : p w) : box r p w := by
  obtain ⟨g, hg⟩ := exists_god hs h w
  have hbox := (scott_T2 h.A1b h.A4 hg).2 (fun _ v => p v) hp
  intro v hv
  obtain ⟨y, hy⟩ := scott_T3 hs h w v hv
  exact hbox v hv y hy

/-- Under a reflexive frame, modal collapse is an equivalence: `p ↔ □p`.  The
distinction between truth and necessary truth disappears entirely. -/
theorem modal_collapse_iff (hs : Symm r) (hrefl : ∀ w : W, r w w)
    (h : Scott1987 r P) (p : Sentence W) (w : W) : p w ↔ box r p w :=
  ⟨modal_collapse hs h p w, fun hb => hb w (hrefl w)⟩

/-- **Under the `S5` reading, Scott's axioms force a single world.**

With `□` read as "at every world whatsoever", modal collapse applied to the
sentence "being the world `w`" says that every world *is* `w`.  So the space of
possible worlds collapses to a point, and with it every modal distinction the
argument was stated in. -/
theorem s5_unique_world (h : Scott1987 (univ : W → W → Prop) P) (v w : W) :
    v = w :=
  modal_collapse symm_univ h (fun u => u = w) w rfl v trivial

/-! ### What modal collapse does to the frame

Modal collapse is usually stated as a fact about sentences: every truth is
necessary.  Read semantically it is a fact about the *accessibility relation*,
and a drastic one.  Applying collapse to the sentence "being the world `w`"
shows that `w` sees nothing but itself; Theorem 1 applied to `A3` shows it does
see itself.  So `r` is forced to be equality, and every world is an isolated
point.

This is the standard semantic reading of modal collapse — Benzmüller and
others state `MC` directly as `∀x ∀y (r x y → y = x)` — not something new.
What it settles is a question about *models*: Scott's axioms are consistent
with `W` of any size, but never with a frame that has any modal structure. -/

/-- Scott's axioms make the frame **serial**: `A3` and Theorem 1 put an
accessible world under every world.  No frame hypothesis needed. -/
theorem serial_of_scott (h : Scott1987 r P) (w : W) : ∃ v, r w v :=
  let ⟨v, hv, _⟩ := possibly_exists h.A1a h.A2 (God P) w (h.A3 w)
  ⟨v, hv⟩

/-- Scott's axioms make the frame **reflexive**.  Note this is *derived*, not
assumed: the axioms do not merely hold in reflexive frames, they force
reflexivity. -/
theorem refl_of_scott (hs : Symm r) (h : Scott1987 r P) (w : W) : r w w := by
  obtain ⟨v, hv⟩ := serial_of_scott h w
  obtain rfl : v = w := modal_collapse hs h (fun u => u = w) w rfl v hv
  exact hv

/-- **The accessibility relation is forced to be equality.**

Every world sees itself and nothing else.  This is modal collapse read as a
condition on the frame, and it is the sharpest statement of what Scott's axioms
cost: not that there is only one world, but that no world can see another, so
there is no modality left anywhere in the structure. -/
theorem accessibility_eq (hs : Symm r) (h : Scott1987 r P) (w v : W) :
    r w v ↔ v = w := by
  constructor
  · exact fun hrv => modal_collapse hs h (fun u => u = w) w rfl v hrv
  · rintro rfl
    exact refl_of_scott hs h v

/-- With the frame forced to equality, `□` is the identity operation: `□p` and
`p` say the same thing at every world.  The modal language has no content
left. -/
theorem box_iff (hs : Symm r) (h : Scott1987 r P) (p : Sentence W) (w : W) :
    box r p w ↔ p w :=
  ⟨fun hb => hb w (refl_of_scott hs h w), modal_collapse hs h p w⟩

/-- `◇` likewise. -/
theorem dia_iff (hs : Symm r) (h : Scott1987 r P) (p : Sentence W) (w : W) :
    dia r p w ↔ p w :=
  ⟨fun ⟨v, hv, hpv⟩ => ((accessibility_eq hs h w v).1 hv) ▸ hpv,
   fun hp => ⟨w, refl_of_scott hs h w, hp⟩⟩

end Godel
