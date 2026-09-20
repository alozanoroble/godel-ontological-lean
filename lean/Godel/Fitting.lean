import Godel.Modal

/-
# Fitting's variant (2002)

Fitting's emendation attacks modal collapse at its root. In Gödel's and
Scott's systems, positivity is a predicate on *intensional* properties
`I → W → Prop`, whose extension may vary from world to world. Fitting makes it
a predicate on **extensions** — plain, world-independent sets of individuals,
`I → Prop`. God-likeness, essence and necessary existence are all re-read
accordingly.

    Scott:    G(x)  :=  ∀ φ : I → W → Prop,  P φ → φ(x)
    Fitting:  G(x)  :=  ∀ S : I → Prop,      P S → S x

## Why that blocks modal collapse

The collapse proof for Scott's system takes an arbitrary sentence `p` and
smuggles it in as the constant *intensional* property `λ y w. p w`. That
property tracks `p` from world to world, which is exactly what makes the
essence clause carry `p` along the accessibility relation.

An extension cannot do this. `S : I → Prop` has no world argument, so there is
no extension that varies with `p`. The step has no counterpart, and the
collapse proof simply has nothing to substitute. `noCollapse_axioms` below
exhibits a two-world `S5` model of all of Fitting's axioms in which collapse
fails.

## De re and de dicto

`God P z w` mentions two worlds' worth of information: the individual `z`, and
the world `w` at which positivity is read off. That makes two readings of any
claim about God-like existence available, and this file states both:

    de re     ∀ v, r w v → ∃ z, Ex z v ∧ God P z w   -- frozen at `w`
    de dicto  ∀ v, r w v → ∃ z, Ex z v ∧ God P z v   -- re-read at each `v`

With the full axiom set **both are theorems** (`T3` and `T3_deDicto`); the
bridge is `god_stable`, which needs `A4`. Following the Isabelle development,
the axioms are therefore split into two bundles: `AxI`, the Part I axioms, and
`Ax`, which adds `A4` and `A5`.

The split matters, because the two readings *do* come apart on `AxI` alone.
Section `DeDicto` at the end gives a two-world, two-individual model of `AxI`
in which God-like existence is de re possible but not de dicto possible. This
is the countermodel Benzmüller and Fuenmayor report for their `T3-deDicto`.
Note what it is and is not: it refutes the de dicto *possibility* statement
before `A4` is available, not the de dicto reading of the conclusion, which
their `GodNecExists-v1` proves.

## Actualist quantifiers

Unlike the rest of this development, this file uses an explicit existence
predicate `Ex : I → W → Prop` and quantifies only over individuals that exist
at the world in question. That is not decoration. Because a Fitting extension
is world-independent, "S is empty" would otherwise be a world-independent
statement, Theorem 1 would deliver *actual* rather than merely possible
exemplification, and `T3` would follow without ever using `A5` — which is not
Fitting's argument. It is also what makes the `DeDicto` countermodel possible:
the room for the two readings to separate is an individual that is God-like as
read off at `w` but does not *exist* at `v`.

## Frame conditions

None. Fitting's argument goes through in `K`, and the reason is visible in the
proof: `God P z w` freezes the positivity facts at `w`, so a witness found at
an accessible world is a witness full stop. There is no need to travel back,
which is exactly what symmetry was buying in `Godel.exists_god`.

Following Benzmüller and Fuenmayor, *Computer-supported analysis of positive
properties, ultrafilters and modal collapse in variants of Gödel's ontological
argument*, arXiv:1910.08955, and the AFP entry *Types, Tableaus and Gödel's
God in Isabelle/HOL*.
-/

namespace Godel.Fitting

universe u v

/-- An **extension**: a world-independent set of individuals.  This is what
Fitting's positivity predicate applies to. -/
abbrev Ext (I : Type v) : Type v := I → Prop

variable {W : Type u} {I : Type v}

/-- Complement of an extension. -/
def enot (S : Ext I) : Ext I := fun x => ¬ S x

/-- `S ⇒ T` at `w`: necessarily, every existing member of `S` is a `T`. -/
def Entails (r : W → W → Prop) (Ex : I → W → Prop) (S T : Ext I) : Sentence W :=
  fun w => ∀ v, r w v → ∀ z, Ex z v → S z → T z

/-- **Fitting's God-likeness**: `x` lies in every positive extension. -/
def God (P : Ext I → Sentence W) : I → Sentence W :=
  fun x w => ∀ S : Ext I, P S w → S x

/-- The extension of God-likeness at a given world. -/
def godExt (P : Ext I → Sentence W) (w : W) : Ext I := fun x => God P x w

/-- **Fitting's essence**, quantifying over extensions. -/
def Ess (r : W → W → Prop) (Ex : I → W → Prop) (S : Ext I) (x : I) : Sentence W :=
  fun w => S x ∧ ∀ T : Ext I, T x → Entails r Ex S T w

/-- **Fitting's necessary existence.** -/
def NE (r : W → W → Prop) (Ex : I → W → Prop) : I → Sentence W :=
  fun x w => ∀ S : Ext I, Ess r Ex S x w → ∀ v, r w v → ∃ z, Ex z v ∧ S z

/-- The extension of necessary existence at a given world. -/
def neExt (r : W → W → Prop) (Ex : I → W → Prop) (w : W) : Ext I :=
  fun x => NE r Ex x w

/-- **Part I axioms.**  Enough for Theorem 1 and for the de re possibility of
God-like existence, and no more. -/
structure AxI (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop where
  A1a : ∀ (w : W) (S : Ext I), P (enot S) w → ¬ P S w
  A1b : ∀ (w : W) (S : Ext I), ¬ P S w → P (enot S) w
  A2  : ∀ (w : W) (S T : Ext I), P S w → Entails r Ex S T w → P T w
  T2  : ∀ w : W, P (godExt P w) w

/-- **The full axiom set**, adding `A4` and `A5`. -/
structure Ax (r : W → W → Prop) (Ex : I → W → Prop)
    (P : Ext I → Sentence W) : Prop extends AxI r Ex P where
  A4 : ∀ (w : W) (S : Ext I), P S w → ∀ v, r w v → P S v
  A5 : ∀ w : W, P (neExt r Ex w) w

variable {r : W → W → Prop} {Ex : I → W → Prop} {P : Ext I → Sentence W}

/-- **Theorem 1.**  A positive extension is possibly exemplified.

Uses `A1a` and `A2`; no frame condition. -/
theorem T1 (h : AxI r Ex P) (S : Ext I) (w : W) (hS : P S w) :
    ∃ v, r w v ∧ ∃ z, Ex z v ∧ S z :=
  Classical.byContradiction fun hc =>
    have key : ∀ T : Ext I, P T w := fun T =>
      h.A2 w S T hS (fun v hv z hz hSz => absurd ⟨v, hv, z, hz, hSz⟩ hc)
    h.A1a w S (key (enot S)) (key S)

/-- Anything a God-like individual has is positive.  Uses `A1b`. -/
theorem positive_of_god (h : AxI r Ex P) {x : I} {w : W}
    (hg : God P x w) (T : Ext I) (hT : T x) : P T w :=
  Classical.byContradiction fun hnp => hg (enot T) (h.A1b w T hnp) hT

/-- **Monotheism.**  God-like individuals are unique at a world.

Being identical to a God-like `x` is a positive extension — otherwise its
complement would be, by `A1b`, and `x` would fail to be self-identical. -/
theorem monotheism (h : AxI r Ex P) {x y : I} {w : W}
    (hx : God P x w) (hy : God P y w) : y = x :=
  hy (fun u => u = x) (positive_of_god h hx (fun u => u = x) rfl)

/-- **God-likeness is an essence of any God-like individual.**

No frame condition, and `A4` is not needed. -/
theorem god_essential (h : AxI r Ex P) {x : I} {w : W} (hg : God P x w) :
    Ess r Ex (godExt P w) x w :=
  ⟨hg, fun T hT _v _hv _z _hz hgz => hgz T (positive_of_god h hg T hT)⟩

/-- **De re possibility.**  Some accessible world holds an existing individual
that is God-like *as read off at `w`*.  Part I only. -/
theorem possible_deRe (h : AxI r Ex P) (w : W) :
    ∃ v, r w v ∧ ∃ z, Ex z v ∧ God P z w :=
  T1 h (godExt P w) w (h.T2 w)

/-- A God-like individual makes God-like existence necessary.  This is the
step that uses `A5`. -/
theorem box_exists_of_god (h : Ax r Ex P) {g : I} {w : W} (hg : God P g w) :
    ∀ v, r w v → ∃ z, Ex z v ∧ God P z w :=
  hg (neExt r Ex w) (h.A5 w) (godExt P w) (god_essential h.toAxI hg)

/-- **Theorem 3, de re.**  Necessarily, an individual God-like at `w` exists —
*in `K`*.

No frame condition whatsoever, in contrast with Scott's variant, which needs
symmetry (`Godel.exists_god`).  The reason is structural: `God P z w` freezes
positivity at `w`, so the witness Theorem 1 produces at an accessible world is
a witness simpliciter, and nothing has to be carried back. -/
theorem T3 (h : Ax r Ex P) (w : W) :
    ∀ v, r w v → ∃ z, Ex z v ∧ God P z w := by
  obtain ⟨_v, _hv, g, _hEg, hg⟩ := possible_deRe h.toAxI w
  exact box_exists_of_god h hg

/-! ### From de re to de dicto

`A4` propagates positivity forward along `r`, which is enough to make
God-likeness itself stable, and with it to upgrade `T3` to the de dicto
reading. -/

/-- God-likeness at an accessible world implies God-likeness here: `A4` carries
the extension `godExt P w` forward, and a God-like `z` at `v` must lie in it. -/
theorem god_from_accessible (h : Ax r Ex P) {z : I} {w v : W} (hwv : r w v)
    (hz : God P z v) : God P z w :=
  hz (godExt P w) (h.A4 w (godExt P w) (h.T2 w) v hwv)

/-- Every world has a God-like individual (not necessarily an existing one). -/
theorem exists_god_at (h : AxI r Ex P) (v : W) : ∃ z, God P z v := by
  obtain ⟨_u, _hu, z, _hz, hg⟩ := possible_deRe h v
  exact ⟨z, hg⟩

/-- **God-likeness is stable** along accessibility.  Uses `A4` and monotheism. -/
theorem god_stable (h : Ax r Ex P) {x : I} {w v : W} (hwv : r w v)
    (hx : God P x w) : God P x v := by
  obtain ⟨z, hz⟩ := exists_god_at h.toAxI v
  obtain rfl : z = x := monotheism h.toAxI hx (god_from_accessible h hwv hz)
  exact hz

/-- **Theorem 3, de dicto.**  Necessarily, an individual God-like *there*
exists.  Also in `K`; the extra ingredient over `T3` is `A4`, not a frame
condition. -/
theorem T3_deDicto (h : Ax r Ex P) (w : W) :
    ∀ v, r w v → ∃ z, Ex z v ∧ God P z v := by
  intro v hv
  obtain ⟨z, hEz, hz⟩ := T3 h w v hv
  exact ⟨z, hEz, god_stable h hv hz⟩

/-! ### Modal collapse fails, even in `S5`

Two worlds, one individual existing at both, and a set is positive exactly
when the individual belongs to it.  All of Fitting's axioms hold and modal
collapse does not — over the universal relation, so this is an `S5` frame.

The contrast with `Godel.modal_collapse` is the whole point of the variant:
there, the sentence `p` entered as the constant intensional property
`λ y w. p w`; here the essence clause admits only extensions, and no extension
tracks `p`. -/

section NoCollapse

/-- Positivity: the sole individual belongs to the set. -/
def cP : Ext Unit → Sentence Bool := fun S _ => S ()

/-- Everything exists at every world. -/
def cEx : Unit → Bool → Prop := fun _ _ => True

theorem noCollapse_axioms : Ax (univ : Bool → Bool → Prop) cEx cP where
  A1a := fun _w _S h => h
  A1b := fun _w _S h => h
  A2  := fun w _S _T hS hEnt => hEnt w trivial () trivial hS
  T2  := fun _w _S h => h
  A4  := fun _w _S h _v _hv => h
  A5  := fun _w _S hess _v _hv => ⟨(), trivial, hess.1⟩

/-- **Modal collapse fails** in that model. -/
theorem noCollapse : ¬ ∀ (p : Sentence Bool) (w : Bool), p w → box univ p w := by
  intro h
  exact Bool.noConfusion (h (fun u => u = false) false rfl true trivial)

end NoCollapse

/-! ### The two readings come apart on the Part I axioms

Two worlds and two individuals.  Each world sees only the *other* world, and
the individual existing at a world is the *other* one.  A set is positive at
`w` exactly when it contains `w`'s own individual — so the God-like individual
at each world is the one that does *not* exist there.

On `AxI` this is a model. God-like existence is de re possible
(`dd_possible_deRe`) and de dicto impossible (`dd_not_possible_deDicto`): at
the accessible world there is an existing individual God-like *as read off
here*, but the individual God-like *there* is not one that exists there.

`A4` necessarily fails (`dd_not_A4`) — it has to, since `T3_deDicto` is a
theorem once `A4` is available. -/

section DeDicto

/-- Each world sees only the other. -/
def ddR : Bool → Bool → Prop := fun w v => w ≠ v

/-- The individual existing at a world is the other one. -/
def ddEx : Bool → Bool → Prop := fun z v => z ≠ v

/-- A set is positive at `w` iff it contains `w`'s own individual. -/
def ddP : Ext Bool → Sentence Bool := fun S w => S w

theorem bool_ne_not : ∀ w : Bool, w ≠ !w
  | false => fun h => Bool.noConfusion h
  | true  => fun h => Bool.noConfusion h

theorem dd_axioms : AxI ddR ddEx ddP where
  A1a := fun _w _S h => h
  A1b := fun _w _S h => h
  A2  := fun w _S _T hS hEnt => hEnt (!w) (bool_ne_not w) w (bool_ne_not w) hS
  T2  := fun _w _S h => h

/-- God-like existence is **de re possible**: the accessible world holds an
existing individual that is God-like as read off here. -/
theorem dd_possible_deRe (w : Bool) :
    ∃ v, ddR w v ∧ ∃ z, ddEx z v ∧ God ddP z w :=
  ⟨!w, bool_ne_not w, w, bool_ne_not w, fun _S h => h⟩

/-- God-like existence is **not de dicto possible**: the individual God-like at
a world is precisely the one that does not exist there. -/
theorem dd_not_possible_deDicto (w : Bool) :
    ¬ ∃ v, ddR w v ∧ ∃ z, ddEx z v ∧ God ddP z v := by
  rintro ⟨v, _, z, hz, hg⟩
  exact hz (hg (fun u => u = v) rfl)

/-- `A4` fails here, as it must. -/
theorem dd_not_A4 :
    ¬ ∀ (w : Bool) (S : Ext Bool), ddP S w → ∀ v, ddR w v → ddP S v := by
  intro h
  exact Bool.noConfusion (h false (fun u => u = false) rfl true (bool_ne_not false))

end DeDicto

end Godel.Fitting
