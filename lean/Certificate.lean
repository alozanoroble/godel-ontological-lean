import Godel

/-
Run with `lake env lean Certificate.lean` and keep the output in `results/`.

`#print axioms` lists what each theorem ultimately rests on.  Gödel's and
Scott's axioms do not appear: they are hypotheses of the theorems, discharged
by whoever supplies them.  What appears is only Lean's own foundations.
-/

-- Gödel 1970: the refutation
#print axioms Godel.possibly_exists
#print axioms Godel.emptyProperty_ess
#print axioms Godel.inconsistent_of_A1_A2_A5
#print axioms Godel.godel_1970_inconsistent
#print axioms Godel.godel_1970_inconsistent_S5
#print axioms Godel.empty_not_scottEss

-- Scott 1987: the positive argument
#print axioms Godel.positive_of_god
#print axioms Godel.scott_T2
#print axioms Godel.exists_god
#print axioms Godel.scott_T3

-- The price: modal collapse and what it does to the frame
#print axioms Godel.scott_monotheism
#print axioms Godel.modal_collapse
#print axioms Godel.modal_collapse_iff
#print axioms Godel.s5_unique_world
#print axioms Godel.serial_of_scott
#print axioms Godel.refl_of_scott
#print axioms Godel.accessibility_eq
#print axioms Godel.box_iff
#print axioms Godel.dia_iff

-- Models
#print axioms Godel.toy_satisfies_A1_A2_A3_A4
#print axioms Godel.toy_not_A5
#print axioms Godel.toy_satisfies_scott
#print axioms Godel.iso_satisfies_scott
#print axioms Godel.scott_two_worlds

-- Symmetry is necessary: an S4 countermodel
#print axioms Godel.ns_satisfies_scott
#print axioms Godel.nsR_not_symm
#print axioms Godel.ns_no_god_at_false
#print axioms Godel.ns_not_T3
#print axioms Godel.ns_not_modal_collapse
#print axioms Godel.ns_not_accessibility_eq

-- Fitting's variant (2002): positivity over extensions
#print axioms Godel.Fitting.T1
#print axioms Godel.Fitting.positive_of_god
#print axioms Godel.Fitting.god_essential
#print axioms Godel.Fitting.box_exists_of_god
#print axioms Godel.Fitting.possible_deRe
#print axioms Godel.Fitting.monotheism
#print axioms Godel.Fitting.T3
#print axioms Godel.Fitting.god_stable
#print axioms Godel.Fitting.T3_deDicto
#print axioms Godel.Fitting.noCollapse_axioms
#print axioms Godel.Fitting.noCollapse

-- Anderson's variant (1990): biconditional God-likeness and essence
#print axioms Godel.Anderson.T1
#print axioms Godel.Anderson.monotheism
#print axioms Godel.Anderson.god_transfers
#print axioms Godel.Anderson.god_essential
#print axioms Godel.Anderson.box_exists_of_god
#print axioms Godel.Anderson.T3
#print axioms Godel.Anderson.noCollapse_axioms
#print axioms Godel.Anderson.noCollapse

-- Fitting: de re vs de dicto on the Part I axioms
#print axioms Godel.Fitting.dd_axioms
#print axioms Godel.Fitting.dd_possible_deRe
#print axioms Godel.Fitting.dd_not_possible_deDicto
#print axioms Godel.Fitting.dd_not_A4

-- Hájek's first emendation (AOE, 2002): A4 and A5 superfluous
#print axioms Godel.Hajek.A1a_of_A12
#print axioms Godel.Hajek.T1
#print axioms Godel.Hajek.box_exists_of_god
#print axioms Godel.Hajek.possibly_god
#print axioms Godel.Hajek.T3
#print axioms Godel.Hajek.noCollapse_axioms
#print axioms Godel.Hajek.noCollapse
