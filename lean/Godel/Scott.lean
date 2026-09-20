import Godel.Original

/-
# Scott's variant (c. 1972; published via Sobel 1987)

The positive argument, and its price.

Dana Scott's version of Gödel's argument differs in exactly one conjunct: his
definition of essence requires that `x` actually have `φ`.  That single change
blocks the refutation of `Godel.Original` (see `empty_not_scottEss` there), and
this file carries out the argument that Gödel intended:

* `scott_T2` — God-likeness is an essence of any God-like individual;
* `scott_T3` — necessarily, a God-like individual exists;

and then the objection that the argument has never shaken off:

* `modal_collapse` — every truth is a necessary truth, `p → □p`;
* `s5_unique_world` — under the *universal-accessibility* presentation of `S5`,
  there is only one world.  (An arbitrary `S5` frame is an equivalence relation
  and may have several classes; the theorem is about a single cluster.)

## Reading these theorems correctly

Every result below is a *conditional*: it takes a `Scott1987 r P` hypothesis
and derives something from it.  `scott_T3` is not a proof that God exists.  It
is a proof that *if* one grants Scott's five axioms, then `□∃x G(x)` follows —
which is exactly the claim the ontological argument makes, and exactly as much
as a formalization can settle.  Whether the axioms should be granted is not a
question Lean can answer.

`modal_collapse` is the reason this matters.  From the same axioms one derives
that nothing is contingent: every truth whatsoever is necessary.  Modal
collapse is widely discussed as an objection to the Gödel/Scott system, though
readings of its philosophical significance differ -- Kovač, among others, has
argued that Gödel would not have regarded it as a defect.  `s5_unique_world`
makes the consequence vivid: over the universal relation the axioms force the
space of possible worlds to be a single point.

Note also that consistency is not soundness.  Blocking Gödel's contradiction
makes the derivation non-trivial; it says nothing about whether the axioms are
true.

## Frame conditions

The positive argument needs **symmetry** of the accessibility relation, and
nothing else — no reflexivity, no transitivity.  That is the modal logic `KB`:
K plus the symmetry axiom B.  (The system conventionally named `B` is `KTB`,
which adds reflexivity; both are weaker than the `S5` in which the argument is
usually presented, and `KB` is weaker than `KTB`.)  Symmetry is
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

/-- The **positive-existence core**: the three axioms that make a positive
property possibly instantiated and apply that to God-likeness.  Everything
that only needs "some accessible world holds a God-like individual" takes
this, not the full system — see `serial_of_scott` and `exists_god`. -/
structure ScottCore (r : W → W → Prop) (P : Property I W → Sentence W) : Prop where
  A1a : AxiomA1 P
  A2  : AxiomA2 r P
  A3  : AxiomA3 P

/-- Scott's axioms.  `A1a` and `A1b` are the two halves of the biconditional
A1; `A2`, `A3` and `A4` are as in Gödel's system; `A5` is stated with Scott's
necessary existence. -/
structure Scott1987 (r : W → W → Prop) (P : Property I W → Sentence W) : Prop
    extends ScottCore r P where
  A1b : AxiomA1b P
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

/-- **Monotheism.**  God-like individuals are unique at a world.

Being identical to a God-like `x` is a positive property — otherwise its
negation would be positive by `A1b`, and `x`, having every positive property,
would fail to be self-identical.  Any God-like `y` therefore has it.

Uses `A1b` alone: no frame condition, no `A4`, no `A5`.

**Uniqueness is not special to Anderson's variant.**  An earlier version of
this development claimed in a comment that Scott's system could not prove it;
that was false, and this theorem is the refutation.  Benzmüller and Scott
(*Monatshefte für Mathematik* 208, 2025) likewise list monotheism as a
consequence of the Gödel/Scott setting. -/
theorem scott_monotheism (hA1b : AxiomA1b P) {x y : I} {w : W}
    (hx : God P x w) (hy : God P y w) : y = x :=
  hy (fun z _ => z = x) (positive_of_god hA1b hx (fun z _ => z = x) rfl)

/-- A God-like individual makes the existence of a God-like individual
necessary: `G(g) → □∃y G(y)`.

This is the step that uses `A5`.  Note that it needs `ScottEss`, which is
exactly what Gödel's definition failed to supply. -/
theorem box_exists_god_of_god (hA1b : AxiomA1b P) (hA4 : AxiomA4 r P)
    (hA5 : AxiomA5S r P) {g : I} {w : W} (hg : God P g w) :
    box r (fun v => ∃ y, God P y v) w :=
  hg (NES r) (hA5 w) (God P) (scott_T2 hA1b hA4 hg)

/-! ### A shorter route, and a warning about it

Everything above follows Scott's own argument.  The encoded system also admits
a much shorter route to the same conclusions, which uses neither `A1b` nor
`A4`.  It is recorded here because it is a genuine theorem of the encoding and
because the gap between it and Scott's argument is itself informative — but
read the caveat on `hae_scottEss` before drawing conclusions about Scott's
system as he intended it. -/

/-- **The world-indexed haecceity is a Scott-essence, for free.**

Fix `g` and `v` and take the property "being `g`, at `v`".  Scott's essence
clause asks that the property necessarily entail every property its bearer has
at `v`; the only way to bear this one at an accessible world `u` is to be `g`
with `u = v`, at which point the entailed property is being asked for at `v`
itself, where it holds by hypothesis.  **No axioms, no frame condition.**

⚠ *This is where the encoding may outrun the source.*  Whether Scott's system
licenses a property that mentions a particular world is a question about the
comprehension principle of his higher-order language, not about his axioms.
The shallow embedding here makes every function `I → W → Prop` a property, so
it is available.  The published dependency analyses reach Theorem 3 through
Theorem 2, and hence through `A4`; the results below bypass that, and the
divergence most likely lives in exactly this lemma.  Treat what follows as a
fact about *this formalization*.

Fitting's `Fitting.singleton_ess` is the same idea without the caveat: his
essences are plain sets, so the bare singleton `{g}` suffices and no world is
mentioned. -/
theorem hae_scottEss (g : I) (v : W) :
    ScottEss r (fun z u => z = g ∧ u = v) g v :=
  ⟨⟨rfl, rfl⟩, by
    intro ψ hψ u _hvu y hy
    obtain ⟨rfl, rfl⟩ := hy
    exact hψ⟩

/-- **`A5` alone isolates the world of a God-like individual.**

If `g` is God-like at `v` then `A5` gives it Scott-necessary existence, and
applying that to the haecceity of `hae_scottEss` says every world accessible
from `v` *is* `v`.

Uses `A5` and `D1` only: no `A1b`, no `A4`, no `A2`, no frame condition.  This
is `accessibility_eq` in miniature, and it is what makes the rest collapse. -/
theorem blind_of_god (hA5 : AxiomA5S r P) {g : I} {v : W}
    (hg : God P g v) : ∀ u, r v u → u = v := by
  intro u hvu
  obtain ⟨_y, _hy1, hy2⟩ := hg (NES r) (hA5 v) _ (hae_scottEss _ _) u hvu
  exact hy2

/-- A God-like individual exists at *every* world.

Theorem 1 applied to `A3` puts one at some accessible world `v`; `blind_of_god`
then shows `v` sees only itself, and symmetry makes `w` one of the worlds it
sees — so `v` *is* `w`.

Needs `ScottCore`, `A5` and symmetry.  **Scott's own route** to this used
`A1b` and `A4` as well, via `box_exists_god_of_god`; that version is
`exists_god_viaT2`. -/
theorem exists_god (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (w : W) : ∃ x, God P x w := by
  obtain ⟨v, hwv, g, hg⟩ := possibly_exists h.A1a h.A2 (God P) w (h.A3 w)
  obtain rfl : w = v := blind_of_god hA5 hg w (hs w v hwv)
  exact ⟨g, hg⟩

/-- Scott's own route to `exists_god`, using Theorem 2. -/
theorem exists_god_viaT2 (hs : Symm r) (h : Scott1987 r P) (w : W) :
    ∃ x, God P x w := by
  obtain ⟨v, hwv, g, hg⟩ := possibly_exists h.A1a h.A2 (God P) w (h.A3 w)
  exact box_exists_god_of_god h.A1b h.A4 h.A5 hg w (hs w v hwv)

/-- **Theorem 3.**  Necessarily, a God-like individual exists.

This is the conclusion of the ontological argument.  It is a conditional: it
says that Scott's axioms entail `□∃x G(x)`, not that `□∃x G(x)`.

Stated over `ScottCore` plus `A5` and symmetry — so **neither `A1b` nor `A4`
is a hypothesis.**  See the caveat on `hae_scottEss`: this is a dependency
fact about the encoding, and the published analyses, which go through Theorem
2, list `A4`.  `scott_T3_viaT2` is Scott's own route. -/
theorem scott_T3 (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (w : W) : box r (fun v => ∃ x, God P x v) w := by
  obtain ⟨g, hg⟩ := exists_god hs h hA5 w
  intro u hwu
  obtain rfl : u = w := blind_of_god hA5 hg u hwu
  exact ⟨g, hg⟩

/-- **Theorem 3 by Scott's own route**, through Theorem 2 — hence using `A1b`
and `A4`.  Same conclusion as `scott_T3`. -/
theorem scott_T3_viaT2 (hs : Symm r) (h : Scott1987 r P) (w : W) :
    box r (fun v => ∃ x, God P x v) w := by
  obtain ⟨g, hg⟩ := exists_god_viaT2 hs h w
  exact box_exists_god_of_god h.A1b h.A4 h.A5 hg

/-- **Modal collapse.**  Every truth is a necessary truth.

Take any sentence `p` true at `w`, and regard "being such that `p`" as a
property.  A God-like `g` has it, so by Theorem 2 God-likeness necessarily
entails it; and by Theorem 3 there is a God-like individual at every
accessible world.  So `p` holds at every accessible world.

Nothing is contingent.  This is the standard objection to the argument, due to
Sobel, and it applies to Scott's consistent version, not only to Gödel's. -/
theorem modal_collapse (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (p : Sentence W) (w : W) (hp : p w) : box r p w := by
  obtain ⟨g, hg⟩ := exists_god hs h hA5 w
  intro u hwu
  obtain rfl : u = w := blind_of_god hA5 hg u hwu
  exact hp

/-- **Modal collapse relative to Theorem 3.**

The dependency question "what does collapse need?" has two different answers
depending on whether Theorem 3 is taken as given or expanded, and conflating
them is easy.  This is the *relative* statement: given necessary God-like
existence as a hypothesis, collapse follows from `A1b`, `A4`, seriality and
symmetry — and from **no** other axiom.  `A1a`, `A2`, `A3` and `A5` appear
only inside the proof of `T3` itself.

This is the route the published dependency summaries describe (collapse from
`A1`, `A4`, `B`, `D1`, `T3`), and it is *not* how `modal_collapse` above is
proved — that one short-circuits through `blind_of_god`. -/
theorem modal_collapse_of_T3 (hs : Symm r) (hserial : ∀ u : W, ∃ v, r u v)
    (hA1b : AxiomA1b P) (hA4 : AxiomA4 r P)
    (hT3 : ∀ u : W, box r (fun v => ∃ x, God P x v) u)
    (p : Sentence W) (w : W) (hp : p w) : box r p w := by
  obtain ⟨v, hwv⟩ := hserial w
  obtain ⟨g, hg⟩ := hT3 v w (hs w v hwv)
  have hbox := (scott_T2 hA1b hA4 hg).2 (fun _ u => p u) hp
  intro u hwu
  obtain ⟨y, hy⟩ := hT3 w u hwu
  exact hbox u hwu y hy

/-- Under a reflexive frame, modal collapse is an equivalence: `p ↔ □p`.  The
distinction between truth and necessary truth disappears entirely. -/
theorem modal_collapse_iff (hs : Symm r) (hrefl : ∀ w : W, r w w)
    (h : ScottCore r P) (hA5 : AxiomA5S r P) (p : Sentence W) (w : W) :
    p w ↔ box r p w :=
  ⟨modal_collapse hs h hA5 p w, fun hb => hb w (hrefl w)⟩

/-- **Over the universal relation, Scott's axioms force a single world.**

With `□` read as "at every world whatsoever", modal collapse applied to the
sentence "being the world `w`" says that every world *is* `w`.  So the space of
possible worlds collapses to a point, and with it every modal distinction the
argument was stated in.

`S5` is named loosely here and in the literature.  An arbitrary `S5` frame is
an equivalence relation and may have many classes; this theorem assumes the
*universal* relation, i.e. a single cluster.  The general statement is
`accessibility_eq` below, which needs only symmetry. -/
theorem s5_unique_world (h : ScottCore (univ : W → W → Prop) P)
    (hA5 : AxiomA5S (univ : W → W → Prop) P) (v w : W) : v = w :=
  modal_collapse symm_univ h hA5 (fun u => u = w) w rfl v trivial

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
theorem serial_of_scott (h : ScottCore r P) (w : W) : ∃ v, r w v :=
  let ⟨v, hv, _⟩ := possibly_exists h.A1a h.A2 (God P) w (h.A3 w)
  ⟨v, hv⟩

/-- Scott's axioms make the frame **reflexive**.  Note this is *derived*, not
assumed: the axioms do not merely hold in reflexive frames, they force
reflexivity.

Needs `ScottCore`, `A5` and symmetry — seriality supplies a world, and
collapse identifies it with `w`. -/
theorem refl_of_scott (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (w : W) : r w w := by
  obtain ⟨v, hv⟩ := serial_of_scott h w
  obtain rfl : v = w := modal_collapse hs h hA5 (fun u => u = w) w rfl v hv
  exact hv

/-- **The accessibility relation is forced to be equality.**

Every world sees itself and nothing else.  This is modal collapse read as a
condition on the frame, and it is the sharpest statement of what Scott's axioms
cost: not that there is only one world, but that no world can see another, so
there is no modality left anywhere in the structure. -/
theorem accessibility_eq (hs : Symm r) (h : ScottCore r P)
    (hA5 : AxiomA5S r P) (w v : W) : r w v ↔ v = w := by
  constructor
  · exact fun hrv => modal_collapse hs h hA5 (fun u => u = w) w rfl v hrv
  · rintro rfl
    exact refl_of_scott hs h hA5 v

/-- With the frame forced to equality, `□` is the identity operation: `□p` and
`p` say the same thing at every world.  The modal language has no content
left. -/
theorem box_iff (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (p : Sentence W) (w : W) : box r p w ↔ p w :=
  ⟨fun hb => hb w (refl_of_scott hs h hA5 w), modal_collapse hs h hA5 p w⟩

/-- `◇` likewise. -/
theorem dia_iff (hs : Symm r) (h : ScottCore r P) (hA5 : AxiomA5S r P)
    (p : Sentence W) (w : W) : dia r p w ↔ p w :=
  ⟨fun ⟨v, hv, hpv⟩ => ((accessibility_eq hs h hA5 w v).1 hv) ▸ hpv,
   fun hp => ⟨w, refl_of_scott hs h hA5 w, hp⟩⟩

end Godel
