module

public import NearlyMinimax.FinePairResponseGeometry
public import NearlyMinimax.CardinalCoefficientBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Nondegeneracy of the genuine fine-pair response matrices. -/
𝚪
𝚨
𝚩
𝚱

𝗇 𝔄 𝖢
theorem spatial_matrix_l1_eq_zero_iff
    (A : HighFrameIndex d F → 𝖲) :
    spatialMatrixL1 A = 0 ↔ ∀ β β', A β β' = 0 := by
  constructor
  · intro h β β'
    have hentry : |A β β'| ≤ spatialMatrixL1 A := by
      calc
        _ ≤ ∑ γ, |A β γ| := Finset.single_le_sum 𝔄 $ Finset.mem_univ β'
        𝖦 := Finset.single_le_sum (f := fun β => ∑ γ, |A β γ|)
            (fun _ _ => Finset.sum_nonneg 𝔄)
            $ Finset.mem_univ β
    simp_all
  · intro h
    simp [spatialMatrixL1, h]

𝗇 𝔅 (spatial_matrix_l1_eq_zero_iff _).mp he.symm
theorem finePairUnitMatrix_l1_pos d F :
    0 < spatialMatrixL1 (finePairUnitMatrix d F) := by
  apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
  intro he
  have hk := finePairUnitMatrix_kernel (F := F)
     (fun _ => (0 : Covariate d)) (0 : Fin 1) 0
  simp only [spatialFrameCovariance, 𝔅] at hk
  norm_num at hk

theorem finePairDistanceMatrix_l1_pos (d F : ℕ) [NeZero d] (hF : 3 ≤ F) :
    0 < spatialMatrixL1 𝖺₂ := by
  apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
  intro he
  let U : 𝖿₁ := fun i _ => if i = 0 then 0 else 1
  have hk := finePairDistanceMatrix_kernel hF U 0 1
  simp only [spatialFrameCovariance, 𝔅, mul_zero, Finset.sum_const_zero] at hk
  have heU : 𝘘₂ = d := by simp [U, spatialSquaredDistance]
  rw [heU] at hk
  exact NeZero.ne d $ Nat.cast_eq_zero.mp $ neg_eq_zero.mp hk.symm
