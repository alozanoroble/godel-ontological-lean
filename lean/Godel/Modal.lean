/-
# A shallow embedding of quantified modal logic

Worlds are a type `W`; a modal sentence is a predicate on worlds, and a
property of individuals is a predicate on individuals *and* worlds, so that
its extension may vary from world to world.

The embedding is *shallow*: modal connectives are Lean functions on
`W → Prop` rather than a datatype of formulas with a separate satisfaction
relation.  Nothing below is specific to Gödel's argument.

The accessibility relation `r` is kept explicit and unconstrained, so that
every frame condition a result consumes appears as a named hypothesis of that
result rather than being baked into the semantics.

This pays off twice.  The refutation of Gödel's 1970 axioms (`Godel.Original`)
takes *no* frame hypothesis at all, so it lives in `K`; the positive argument
for Scott's system (`Godel.Scott`) takes exactly one, `Symm`, so it lives in
`B`.  Neither needs the full strength of `S5`.
-/

namespace Godel

universe u v

/-- A modal sentence: its truth value varies from world to world. -/
abbrev Sentence (W : Type u) : Type u := W → Prop

/-- A property of individuals, whose extension varies from world to world. -/
abbrev Property (I : Type v) (W : Type u) : Type (max u v) := I → W → Prop

variable {W : Type u} {I : Type v}

/-- Pointwise negation of a property. -/
def pneg (φ : Property I W) : Property I W := fun x w => ¬ φ x w

/-- `□p` holds at `w` when `p` holds at every world accessible from `w`. -/
def box (r : W → W → Prop) (p : Sentence W) : Sentence W :=
  fun w => ∀ v, r w v → p v

/-- `◇p` holds at `w` when `p` holds at some world accessible from `w`. -/
def dia (r : W → W → Prop) (p : Sentence W) : Sentence W :=
  fun w => ∃ v, r w v ∧ p v

/-- Symmetry of the accessibility relation: the frame condition for the modal
logic `B` (and hence for `S5`).  This is the one frame condition the positive
argument of `Godel.Scott` actually needs. -/
def Symm (r : W → W → Prop) : Prop := ∀ w v, r w v → r v w

/-- The universal relation, giving the `S5` reading of `□` as "at every world
whatsoever".  Provided only so that the `S5` case can be stated explicitly;
nothing in the development needs it. -/
def univ : W → W → Prop := fun _ _ => True

theorem symm_univ : Symm (univ : W → W → Prop) := fun _ _ _ => trivial

end Godel
