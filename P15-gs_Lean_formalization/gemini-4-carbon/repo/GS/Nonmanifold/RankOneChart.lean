module

public import GS.Nonmanifold.RankOneGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Explicit charts on the nonzero rank-one stratum

On the open patch W[0,j] != 0, a 2 x k rank-one matrix is uniquely represented
by its first row x and the scalar a=W[1,j]/W[0,j]. Its inverse is [x;a*x].
The coordinate domain x[j] != 0 is open. Swapping the two rows covers every
remaining nonzero point. These are actual homeomorphisms, not dimension counts
inferred merely from a redundant parameter space.
-/
noncomputable section
open Matrix GS GS.GlobalGeometry
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

abbrev RankOnePivot (j : κ) :=
  {W : Matrix (Fin 2) κ ℝ // W.rank ≤ 1 ∧ W 0 j ≠ 0}

abbrev PivotCoordinates (j : κ) := {x : κ → ℝ // x j ≠ 0} × ℝ

def pivotEncode (j : κ) (W : RankOnePivot j) : PivotCoordinates j :=
  (⟨W.val 0,W.property.2⟩,W.val 1 j / W.val 0 j)

def pivotDecode (j : κ) (p : PivotCoordinates j) : RankOnePivot j :=
  ⟨outer ![1,p.2] p.1.val, rank_outer_le_one _ _, by
    simpa [outer] using p.1.property⟩

theorem pivotDecode_encode (j : κ) (W : RankOnePivot j) :
    pivotDecode j (pivotEncode j W) = W := by
  apply Subtype.ext
  ext i k
  fin_cases i
  · simp [pivotDecode, pivotEncode, outer]
  · have hm := rank_le_one_two_column_minor W.val W.property.1 j k
    change (W.val 1 j / W.val 0 j) * W.val 0 k = W.val 1 k
    field_simp [W.property.2]
    nlinarith [hm]

theorem pivotEncode_decode (j : κ) (p : PivotCoordinates j) :
    pivotEncode j (pivotDecode j p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    funext k
    simp [pivotDecode, pivotEncode, outer]
  · change (p.2*p.1.val j)/(1*p.1.val j)=p.2
    field_simp [p.1.property]

theorem continuous_pivotEncode (j : κ) : Continuous (pivotEncode j) := by
  unfold pivotEncode
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact (continuous_apply 0).comp continuous_subtype_val
  · have h₀ : Continuous (fun W : RankOnePivot j => W.val 0 j) :=
      (continuous_apply j).comp ((continuous_apply 0).comp continuous_subtype_val)
    have h₁ : Continuous (fun W : RankOnePivot j => W.val 1 j) :=
      (continuous_apply j).comp ((continuous_apply 1).comp continuous_subtype_val)
    exact h₁.div h₀ (fun W => W.property.2)

theorem continuous_pivotDecode (j : κ) : Continuous (pivotDecode j) := by
  unfold pivotDecode
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro k
  fin_cases i <;> simp [outer]
  · exact (continuous_apply k).comp (continuous_subtype_val.comp continuous_fst)
  · exact continuous_snd.mul
      ((continuous_apply k).comp (continuous_subtype_val.comp continuous_fst))

def rankOnePivotHomeomorph (j : κ) : RankOnePivot j ≃ₜ PivotCoordinates j where
  toFun := pivotEncode j
  invFun := pivotDecode j
  left_inv := pivotDecode_encode j
  right_inv := pivotEncode_decode j
  continuous_toFun := continuous_pivotEncode j
  continuous_invFun := continuous_pivotDecode j

end GS.Nonmanifold
