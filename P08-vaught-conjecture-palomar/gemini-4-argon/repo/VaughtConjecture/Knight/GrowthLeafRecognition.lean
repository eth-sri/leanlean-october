/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthPaddedSuccessor
public import VaughtConjecture.Knight.GrowthFiniteReflection
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.SupportLadderBottomReflection

/-! # Complete-field recognition from the maximal leaf chart on the growth successor rows

On the actual one-scope grade-two growth rows (`GrowthPaddedSuccessor`), an **arbitrary** lawful
section `p` below `(A, 2)` is recognized by the chart of its maximal ceiling leaf.  No admission,
selected display, bottom-pattern class or hidden-original completion of `p` is assumed, and no
probe interface is introduced: the chart is extracted from lawfulness alone
(`AmbientGradeCharts.exists_chart`), and its owner is necessarily a leaf.

Write `B_p f` for the finite maximum of `p` over the shadows of the complete field `f`
(`shadowSup`), `M₂ p` for its maximum over the ceiling leaves (`leafSup`) and `M₁ p` for its
maximum over the spare rungs (`spareSup`).  With `a` the maximal leaf and `σ` its chart:

* **Complete-field recognition** (`recognition`): `σ (a f) = min (B_p f) (M₂ p)` for **every**
  complete field `f`, present, hidden or future — the shadows of every field are installed —
  because the native row reads the field as the finite maximum of its shadow columns
  (`source_shadow_sup`) and a monotone bottom-preserving chart commutes with finite maxima.
* **Finite bottom reflection** (`bottom_reflection`): when `M₂ p ≠ ⊥`, `σ (a f) = ⊥` forces
  `a f = ⊥`, on the ladder's tracked values only (`SupportLadderRows.bottom_reflection_image`
  on the actual ladder restriction of `p`, whose lawfulness is derived in `ladder_lawful`, with
  the spare rung reading the ceiling).  Nothing global about `σ` is asserted.
* **The reconstructed complete vector is admitted** (`exists_admitted`): the transported
  state `(state a).map σ` is `Growth.Admitted X 2` by `Admitted.map_on_profile`, and its
  profile is `f ↦ min (B_p f) (M₂ p)`; at `M₂ p = ⊥` it is the zero state.
* **Readouts** (`present_readback`, `present_readback_of_grade_two`, `leafSup_le_spareSup`):
  every present original cell reads `min (B_p (field d)) (M₂ p)` below `M₂ p`, exactly so at
  grade two, and `M₂ p ≤ M₁ p` through the maximal leaf's birth spare.

Grade one (the uncapped values `B_p f` themselves and the grade-one original vector) needs the
maximal spare chart of the checked base and is not treated here.  Mixed scopes are not treated
here. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.GrowthLeafRecognition

open Transform Value ExtOrd Growth GrowthHigherSources GrowthPaddedSuccessor SupportLadderRows LadderScalarRendering SharpWitnessComposition

theorem card_pos {ι : Type*} {A : Finset ι} (h : 2 ≤ A.card) : 0 < A.card := by omega

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : RelativeData I.right.scheme I.right.rows I.left.scheme I.left.rows)
  (T : RootAttachment I.common I.commonLeft I.visibleLeft I.faceLeft
    I.commonRight I.visibleRight I.faceRight X)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

local notation "Fld" => Field I.right.scheme I.left.scheme
local notation "Ωc" => carrier I X T hA hB hC
local notation "Occ" => CellScheme.below (carrier I X T hA hB hC) (A, 2)
local notation "cellΩ" => CellScheme.cell (carrier I X T hA hB hC)
local notation "gradeΩ" => CellScheme.grade (carrier I X T hA hB hC)
local notation "Eρ" => Semantics.E (rows I X T hA hB hC)
local notation "Rows" => rows I X T hA hB hC
local notation "src" => source I X T hA hB hC
local notation "Pt" => RelativeLadderLayer.Point (X := Fld) (Q := Catalogue X 1)
local notation "ranks₁" => RelativeLadderLayer.ranks (fields X 1)
local notation "rungs" => RelativeLadderLayer.rungs (X := Fld)
local notation "ceil" => RecursiveRungRendering.ceiling Fld 2
local notation "lowerΩ" => LadderWeightedSuccessor.Input.lower (input I X T hA hB hC)

theorem rungs_pos : 0 < rungs := Nat.succ_pos _

/-! ## Occurrences below `(A, 2)` -/

/-! ## The finite maxima -/

variable (p : CellScheme.below (carrier I X T hA hB hC) (A, 2) → ExtOrd)

/-- Finite maxima commute with capping. -/
theorem cap_sup {Y : Type*} [Fintype Y] (g : Y → ExtOrd) (h : ExtOrd) :
    min (Finset.univ.sup g) h = Finset.univ.sup fun y => min (g y) h :=
  Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x => min x h)
    (fun _ _ hxy => min_le_min_right _ hxy) (min_bot_left _)

/-! ## The native rows on the padded base -/

theorem rank_le_rungs (a : Catalogue X 1) (f : Fld) : ranks₁ a f ≤ rungs :=
  (RelativeLadderLayer.rank_bound (fields X 1) a f).le

/-- The birth anchor's own shadow of `f` is indexed by the rank of `f`. -/
theorem index_shadow_self (a : Catalogue X 1) (f : Fld) :
    SupportLadderRows.index (H := rungs) ranks₁ a (shadow a f) = ranks₁ a f := by
  change min (FiniteProfileControllers.cut rungs (ranks₁ a) (ranks₁ a)) (ranks₁ a f) = _
  rw [FiniteProfileControllers.cut_refl]
  exact min_eq_right (rank_le_rungs I X a f)

/-! ## The ladder restriction of an arbitrary lawful section -/

variable {p}

/-! ## The maximal leaf chart -/

/-- The catalogue is nonempty: the zero state is admitted and canonical. -/
def zeroMember (j : ℕ) (hj : 1 ≤ j) : Catalogue X j :=
  Growth.zeroMember X j hj

/-! ## Recognition and finite bottom reflection -/
