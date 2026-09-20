import Godel.Scott

/-
# One model, doing two jobs

Take one world and one individual, and call a property positive exactly when
the individual has it.  This tiny structure settles two quite different
questions.

**1. The encoding of Gödel's axioms is not vacuously contradictory.**  A proof
of `False` from a set of hypotheses is only informative if the hypotheses have
not been mis-stated into absurdity.  Nothing in
`Godel.inconsistent_of_A1_A2_A5` would look any different if, say, `A2` had
been encoded in a form nothing could satisfy.  Here `A1`, `A2`, `A3` and `A4`
all hold, so the contradiction is not coming from them, and `A5` is exactly
what tips the system over (`toy_not_A5`).

**2. Scott's system is consistent.**  The same model, with the same `P`,
satisfies *all* of Scott's axioms (`toy_satisfies_scott`) — including his `A5`,
which is the one Gödel's version fails.  So the inconsistency of the 1970
axioms really is specific to Gödel's definition of essence, and not a defect of
the surrounding axioms or of this encoding of them.

The contrast between `toy_not_A5` and `toy_A5S` is the sharpest statement of
what the missing conjunct costs: one model, one notion of positivity, and the
two readings of "necessary existence" come apart.

**A caveat on job 2.**  This model is degenerate: it has a single world, so
`□` is trivial and modal collapse holds vacuously.  That is not laziness.
`Godel.s5_unique_world` shows that under the `S5` reading Scott's axioms *force*
a one-world model, so no richer one is available there.  What remains open is
whether a non-degenerate model exists over a merely symmetric frame; nothing
here settles that.
-/

namespace Godel

universe u

/-- One world, one individual; a property is positive iff the individual
has it. -/
def toyP : Property Unit Unit → Sentence Unit := fun φ _ => φ () ()

theorem toy_A1 : AxiomA1 toyP :=
  fun _w _φ h => h

theorem toy_A1b : AxiomA1b toyP :=
  fun _w _φ h => h

theorem toy_A2 : AxiomA2 (univ : Unit → Unit → Prop) toyP :=
  fun _w _φ _ψ hφ hb => hb () trivial () hφ

theorem toy_A3 : AxiomA3 toyP :=
  fun _w _φ h => h

theorem toy_A4 : AxiomA4 (univ : Unit → Unit → Prop) toyP :=
  fun _w _φ h _v _hv => h

/-! ### Gödel's A5 fails here -/

/-- `A5` in Gödel's form fails in the toy model — as it must, given
`inconsistent_of_A1_A2_A5`.  The empty property is a Gödel-essence of the
unique individual, but is instantiated nowhere. -/
theorem toy_not_A5 : ¬ AxiomA5 (univ : Unit → Unit → Prop) toyP := by
  intro h
  obtain ⟨_y, hy⟩ :=
    h () (emptyProperty Unit Unit) (emptyProperty_ess () ()) () trivial
  exact hy

/-- `A1`, `A2`, `A3` and `A4` are jointly satisfiable: the encoding of Gödel's
axioms is not vacuously contradictory. -/
theorem toy_satisfies_A1_A2_A3_A4 :
    AxiomA1 toyP ∧
    AxiomA2 (univ : Unit → Unit → Prop) toyP ∧
    AxiomA3 toyP ∧
    AxiomA4 (univ : Unit → Unit → Prop) toyP :=
  ⟨toy_A1, toy_A2, toy_A3, toy_A4⟩

/-! ### Scott's A5 holds here -/

/-- `A5` in Scott's form *does* hold in the toy model.  Scott's essence
requires `φ ()  ()`, so the empty property is not one, and the only properties
whose necessary instantiation is demanded are those the individual actually
has. -/
theorem toy_A5S : AxiomA5S (univ : Unit → Unit → Prop) toyP := by
  intro _w φ hess v _hv
  exact ⟨(), hess.1⟩

/-- **Scott's system is consistent**: all six axioms hold in the toy model. -/
theorem toy_satisfies_scott : Scott1987 (univ : Unit → Unit → Prop) toyP :=
  { A1a := toy_A1, A1b := toy_A1b, A2 := toy_A2
    A3 := toy_A3, A4 := toy_A4, A5 := toy_A5S }

/-! ## Models with as many worlds as you like

`Godel.accessibility_eq` says Scott's axioms force `r` to be equality.  That
leaves an obvious question: is such a frame satisfiable with more than one
world, or does something else collapse the world set too?

It is satisfiable, for `W` of any size whatsoever.  Take equality as the
accessibility relation and one individual, and let a property be positive at a
world exactly when that individual has it there.  Each world is then an
isolated copy of the toy model, with its own God-like individual, seeing
nothing but itself.

So the answer to "does Scott's system have a non-degenerate model?" is: yes in
cardinality, no in modal structure.  `W` may be a proper class of worlds; none
of them can see another, so `□` and `◇` are inert (`box_iff`, `dia_iff`) and
nothing modal is being said.  The one-world model above is not forced — but
nothing better than a disjoint heap of one-world models is available either. -/

section Isolated

variable (V : Type u)

/-- Accessibility by equality: every world sees itself and nothing else. -/
def isoR : V → V → Prop := fun w v => v = w

theorem symm_isoR : Symm (isoR V) := fun _ _ h => Eq.symm h

/-- Positivity in the isolated-worlds model: positive at `w` iff the sole
individual has it at `w`. -/
def isoP : Property Unit V → Sentence V := fun φ w => φ () w

/-- **Scott's axioms hold over a world set of arbitrary size.**  No hypothesis
on `V` at all — it may have one element, two, or a proper class of them. -/
theorem iso_satisfies_scott : Scott1987 (isoR V) (isoP V) where
  A1a := fun _w _φ h => h
  A1b := fun _w _φ h => h
  A2  := fun w _φ _ψ hφ hb => hb w rfl () hφ
  A3  := fun _w _φ h => h
  A4  := by intro w φ h v hv; subst hv; exact h
  A5  := by
    intro w φ hess v hv
    subst hv
    exact ⟨(), hess.1⟩

end Isolated

/-- Two distinct worlds, satisfying Scott's axioms. -/
theorem scott_two_worlds : Scott1987 (isoR Bool) (isoP Bool) :=
  iso_satisfies_scott Bool

/-! ## Symmetry cannot be traded for `S4`

`exists_god` is the only place the positive argument uses a frame condition,
and it uses symmetry: it needs to carry `□∃x G(x)`, established at some
*possible* world, back to the actual one.  That is the `B` schema
`◇□p → p`.  Could the other two `S5` conditions do the job instead?

No.  The model below is **reflexive and transitive** — an `S4` frame —
satisfies all of Scott's axioms, and refutes Theorem 3, modal collapse and
`accessibility_eq` outright.

**Be careful what this shows.**  It shows the symmetry hypothesis cannot be
deleted from the `KB` results in favour of reflexivity and transitivity.  It
does **not** show that symmetry is necessary in the absolute sense: some frame
condition weaker than, or incomparable with, symmetry might still suffice, and
no correspondence or minimality theorem here excludes that.  An earlier
version of this file said "symmetry is really needed", which claimed more than
the countermodel delivers.

Two worlds, `false` and `true`.  `false` sees both; `true` sees only itself.
One individual.  A property is positive, at either world, exactly when the
individual has it **at `true`**.  So `true` is a world where the toy model of
`toy_satisfies_scott` lives, and `false` is a world that can see it but is not
seen by it.  All the positivity facts are imported from `true`, which is what
keeps the axioms true at `false`; but God-likeness is not, because being
God-like at `false` would require having there every property one has at
`true`, and "being the world `true`" is such a property.

The moral: Scott's axioms do not entail modal collapse on their own.  They
entail it *in `B` and `S5`*, which is where the argument is always presented.
-/

section NoSymmetry

/-- `false` sees both worlds; `true` sees only itself. -/
def nsR : Bool → Bool → Prop := fun w v => w = true → v = true

/-- Positivity: what the sole individual has at the world `true`. -/
def nsP : Property Unit Bool → Sentence Bool := fun φ _ => φ () true

theorem nsR_refl (w : Bool) : nsR w w := fun h => h

theorem nsR_trans {a b c : Bool} : nsR a b → nsR b c → nsR a c :=
  fun hab hbc ha => hbc (hab ha)

/-- The frame is **not** symmetric: `false` sees `true` but not conversely. -/
theorem nsR_not_symm : ¬ Symm nsR := by
  intro h
  exact Bool.noConfusion (h false true (fun _ => rfl) rfl)

/-- **Scott's axioms hold in this `S4` frame.** -/
theorem ns_satisfies_scott : Scott1987 nsR nsP where
  A1a := fun _w _φ h => h
  A1b := fun _w _φ h => h
  A2  := fun _w _φ _ψ hφ hb => hb true (fun _ => rfl) () hφ
  A3  := fun _w _φ h => h
  A4  := fun _w _φ h _v _hv => h
  A5  := by
    intro _w φ hess v hv
    obtain rfl : v = true := hv rfl
    exact ⟨(), hess.1⟩

/-- There is no God-like individual at the world `false`: being God-like there
would mean having, at `false`, every property one has at `true` — and "being
the world `true`" is one of those. -/
theorem ns_no_god_at_false : ¬ ∃ x, God nsP x false := by
  rintro ⟨x, hx⟩
  exact Bool.noConfusion (hx (fun _ w => w = true) rfl)

/-- **Theorem 3 fails** without symmetry. -/
theorem ns_not_T3 : ¬ box nsR (fun v => ∃ x, God nsP x v) false := by
  intro h
  exact ns_no_god_at_false (h false (nsR_refl false))

/-- **Modal collapse fails** without symmetry. -/
theorem ns_not_modal_collapse :
    ¬ ∀ (p : Sentence Bool) (w : Bool), p w → box nsR p w := by
  intro h
  exact Bool.noConfusion (h (fun u => u = false) false rfl true (fun _ => rfl))

/-- **The frame is not equality**, so `accessibility_eq` fails too. -/
theorem ns_not_accessibility_eq : ¬ ∀ w v : Bool, nsR w v ↔ v = w := by
  intro h
  exact Bool.noConfusion ((h false true).1 (fun _ => rfl))

end NoSymmetry

end Godel
