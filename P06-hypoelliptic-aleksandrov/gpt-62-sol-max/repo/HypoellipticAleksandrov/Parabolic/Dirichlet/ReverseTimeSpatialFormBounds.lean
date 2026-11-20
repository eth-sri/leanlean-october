module
import Mathlib.Tactic.FunProp

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormRealization
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Ring

/-!
# Bounds for the reverse-time spatial form

This module proves boundedness and a Gårding lower estimate for the literal
reverse-time spatial form, always through its explicitly evidenced `L²`
multiplier representation.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem norm_hilbertVectorLpCoord_le (i : Fin d)
    (G : PDE.HilbertVectorLp Ω (2 : ℝ≥0∞)) :
    ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G‖ ≤ ‖G‖ := by
  rw [PDE.hilbertVectorLpCoord]
  calc
    ‖(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL
        (2 : ℝ≥0∞) (PDE.volumeOn Ω) G‖ ≤
        ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i‖ * ‖G‖ := ContinuousLinearMap.norm_compLp_le _ _
    _ ≤ 1 * ‖G‖ := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      simpa only [ContinuousLinearMap.coe_coe, Function.comp_apply, one_mul, PiLp.proj_apply] using
        PiLp.norm_apply_le x i
    _ = ‖G‖ := one_mul _

/-- Bounded slice multipliers yield one spatial-form bound on the entire time interval. -/
theorem reverseTimeSpatialForm_bounded_of_sliceMultiplierBounds {r₀ r₁ : ℝ} (hΩ : IsOpen Ω)
    {a : CoefficientField d} {b : ℝ → PDE.Vec d → PDE.Vec d} {c : ℝ → PDE.Vec d → ℝ}
    (e : ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Icc 0 (r₁ - r₀), ∀ u v : H10HilbertGraph hΩ,
        |reverseTimeSpatialForm hΩ r₁ τ a b c u v| ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := e.exists_operator_bound hΩ
  refine ⟨C, hC, fun τ hτ u v => ?_⟩
  rw [← e.operator_apply hΩ ⟨τ,hτ⟩ u v, ← Real.norm_eq_abs]
  exact ((e.operator hΩ ⟨τ,hτ⟩ u).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (((e.operator hΩ ⟨τ,hτ⟩).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hb ⟨τ,hτ⟩) (norm_nonneg _))) (norm_nonneg _))

private theorem principal_lower_of_loewner
    (r₀ r₁ lam τ : ℝ) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (u : H10HilbertGraph hΩ)
    (Ca : Fin d → Fin d → ℝ) (hCa : ∀ i j, 0 ≤ Ca i j)
    (hAMeas : ∀ i j, AEStronglyMeasurable (fun y : PDE.Vec d => a (r₁ - τ) y i j)
      (PDE.volumeOn Ω))
    (hABound : ∀ i j, ∀ᵐ y ∂PDE.volumeOn Ω, ‖a (r₁ - τ) y i j‖ ≤ Ca i j)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) :
    lam * ‖gradientCLM hΩ u‖ ^ 2 ≤
      ∑ i : Fin d, ∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier (fun y : PDE.Vec d => a (r₁ - τ) y i j)
            (hAMeas i j) (Ca i j) (hCa i j) (hABound i j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i (gradientCLM hΩ u)) := by
  let G := gradientCLM hΩ u
  have hcoord (i : Fin d) : MemLp (fun y : PDE.Vec d => G y i) (2 : ℝ≥0∞)
      (PDE.volumeOn Ω) :=
    MeasureTheory.MemLp.ae_eq (PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G)
      (Lp.memLp _)
  have hterm (i j : Fin d) : Integrable
      (fun y : PDE.Vec d => a (r₁ - τ) y i j * G y j * G y i) (PDE.volumeOn Ω) := by
    have hprod := (hcoord j).integrable_mul (hcoord i)
    have hbounded := hprod.mul_bdd (hAMeas i j) (hABound i j)
    convert hbounded using 1
    ext y
    simp only [Pi.mul_apply]
    ring
  have hsum : Integrable (fun y : PDE.Vec d => ∑ i : Fin d, ∑ j : Fin d,
      a (r₁ - τ) y i j * G y j * G y i) (PDE.volumeOn Ω) := by
    apply integrable_finset_sum
    intro i _
    apply integrable_finset_sum
    intro j _
    exact hterm i j
  have hgrad : Integrable (fun y : PDE.Vec d => lam * ‖G y‖ ^ 2)
      (PDE.volumeOn Ω) := by
    have hinner := L2.integrable_inner (𝕜 := ℝ) G G
    have : Integrable (fun y : PDE.Vec d => ‖G y‖ ^ 2) (PDE.volumeOn Ω) := by
      simpa only [real_inner_self_eq_norm_sq] using hinner
    exact this.const_mul lam
  have hpoint : ∀ y : PDE.Vec d, y ∈ Ω →
      lam * ‖G y‖ ^ 2 ≤ ∑ i : Fin d, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i := by
    intro y hy
    have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
      constructor <;> linarith [hτ.1, hτ.2]
    have hlo := hLower (r₁ - τ, y) ⟨htime, subset_closure hy⟩
    have hgap : (a (r₁ - τ) y - lam • (1 : PDE.Mat d)).PosSemidef := Matrix.le_iff.mp hlo
    have hquad := hgap.dotProduct_mulVec_nonneg (G y).toVec
    have hquad' : lam * PDE.vecNormSq (G y).toVec ≤
        PDE.vecDot (G y).toVec (Matrix.mulVec (a (r₁ - τ) y) (G y).toVec) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul] at hquad
      simpa [PDE.vecNormSq, HypoellipticAleksandrov.vecDot_eq_dotProduct,
        sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using sub_nonneg.mp hquad
    simpa [PDE.HilbertVec.norm_eq_vecEuclideanNorm, PDE.vecEuclideanNorm_sq,
      PDE.vecNormSq_eq_sum_sq, PDE.vecDot, dotProduct, Matrix.mulVec, Finset.mul_sum,
      PDE.HilbertVec.toVec_apply, mul_comm, mul_left_comm, mul_assoc] using hquad'
  have hmono : (∫ y, lam * ‖G y‖ ^ 2 ∂PDE.volumeOn Ω) ≤
      ∫ y, ∑ i : Fin d, ∑ j : Fin d, a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
    apply integral_mono_ae hgrad hsum
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    exact hpoint y hy
  have hgrad_eq : (∫ y, lam * ‖G y‖ ^ 2 ∂PDE.volumeOn Ω) = lam * ‖G‖ ^ 2 := by
    rw [integral_const_mul, ← real_inner_self_eq_norm_sq G, L2.inner_def]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    exact (real_inner_self_eq_norm_sq (G y)).symm
  rw [← hgrad_eq]
  refine hmono.trans_eq ?_
  calc
    (∫ y, ∑ i : Fin d, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω) =
      ∑ i : Fin d, ∫ y, ∑ j : Fin d,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
          apply integral_finset_sum
          intro i _
          apply integrable_finset_sum
          intro j _
          exact hterm i j
    _ = ∑ i : Fin d, ∑ j : Fin d, ∫ y,
        a (r₁ - τ) y i j * G y j * G y i ∂PDE.volumeOn Ω := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_finset_sum _ (fun j _ => hterm i j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [scalarL2Multiplier_apply_ae _ _ _ _ _ _,
        PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G,
        PDE.coeFn_hilbertVectorLpCoord Ω (2 : ℝ≥0∞) i G] with y hm hj hi
      rw [hm, hj, hi]
      simp only [RCLike.inner_apply, conj_trivial]
      ring

private theorem abs_scalarL2Multiplier_inner_le
    (q : PDE.Vec d → ℝ)
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω))
    (C : ℝ) (hC : 0 ≤ C)
    (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ C)
    (f g : PDE.ScalarLp Ω (2 : ℝ≥0∞)) :
    |inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g| ≤ C * ‖f‖ * ‖g‖ := by
  calc
    |inner ℝ (scalarL2Multiplier q hq C hC hqBound f) g| ≤
        ‖scalarL2Multiplier q hq C hC hqBound f‖ * ‖g‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (C * ‖f‖) * ‖g‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_scalarL2Multiplier_apply_le q hq C hC hqBound f) (norm_nonneg _)

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

private theorem drift_lower_of_sliceMultiplierBounds
    (hΩ : IsOpen Ω) (r₁ τ : ℝ) (a : CoefficientField d)
    (b : ℝ → PDE.Vec d → PDE.Vec d)
    (Cd : Fin d → ℝ) (hCd : ∀ j, 0 ≤ Cd j)
    (hDriftMeas : ∀ j, AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
      (PDE.volumeOn Ω))
    (hDriftBound : ∀ j, ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeDivergenceDrift r₁ a b τ y j‖ ≤ Cd j)
    (u : H10HilbertGraph hΩ) :
    -((∑ j : Fin d, Cd j) * ‖gradientCLM hΩ u‖ * ‖valueCLM hΩ u‖) ≤
      ∑ j : Fin d,
        inner ℝ
          (scalarL2Multiplier
            (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
            (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
            (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j (gradientCLM hΩ u)))
          (valueCLM hΩ u) := by
  let G := gradientCLM hΩ u
  let U := valueCLM hΩ u
  have hcoord (j : Fin d) : ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ ≤ ‖G‖ :=
    norm_hilbertVectorLpCoord_le j G
  have hterm (j : Fin d) :
      |inner ℝ
        (scalarL2Multiplier
          (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
          (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
          (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U| ≤
        Cd j * ‖G‖ * ‖U‖ := by
    calc
      _ ≤ Cd j * ‖PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G‖ * ‖U‖ :=
        abs_scalarL2Multiplier_inner_le _ _ _ _ _ _ _
      _ ≤ Cd j * ‖G‖ * ‖U‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hcoord j) (hCd j)) (norm_nonneg _)
  let B := ∑ j : Fin d,
    inner ℝ
      (scalarL2Multiplier
        (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
        (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
        (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U
  have habs : |B| ≤ (∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖ := by
    calc
      |B| ≤ ∑ j : Fin d,
          |inner ℝ
            (scalarL2Multiplier
              (fun y : PDE.Vec d => reverseTimeDivergenceDrift r₁ a b τ y j)
              (hDriftMeas j) (Cd j) (hCd j) (hDriftBound j)
              (PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j G)) U| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, Cd j * ‖G‖ * ‖U‖ := Finset.sum_le_sum fun j _ => hterm j
      _ = (∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖ := by
        simp_rw [← Finset.sum_mul]
  change -((∑ j : Fin d, Cd j) * ‖G‖ * ‖U‖) ≤ B
  exact (neg_le_neg habs).trans (neg_abs_le B)

private theorem scalar_multiplierInner_nonpos_of_nonpos
    (r₀ r₁ τ : ℝ) (hΩ : IsOpen Ω) (c : ℝ → PDE.Vec d → ℝ)
    (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hScalarMeas : AEStronglyMeasurable
      (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
      (PDE.volumeOn Ω))
    (hScalarBound : ∀ᵐ y ∂PDE.volumeOn Ω,
      ‖reverseTimeScalarCoefficient r₁ c τ y‖ ≤ Cc)
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (u : H10HilbertGraph hΩ) :
    inner ℝ
      (scalarL2Multiplier (fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y)
        hScalarMeas Cc hCc hScalarBound (valueCLM hΩ u))
      (valueCLM hΩ u) ≤ 0 := by
  let U := valueCLM hΩ u
  let q := fun y : PDE.Vec d => reverseTimeScalarCoefficient r₁ c τ y
  have htime : r₀ ≤ r₁ - τ ∧ r₁ - τ ≤ r₁ := by
    constructor <;> linarith [hτ.1, hτ.2]
  have hq : ∀ᵐ y ∂PDE.volumeOn Ω, q y ≤ 0 := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with y hy
    exact id (hcNonpos (r₁ - τ, y) ⟨htime, subset_closure hy⟩)
  have hint : Integrable (fun y : PDE.Vec d => q y * U y * U y) (PDE.volumeOn Ω) := by
    refine (L2.integrable_inner (𝕜 := ℝ)
      (scalarL2Multiplier q hScalarMeas Cc hCc hScalarBound U) U).congr ?_
    filter_upwards [scalarL2Multiplier_apply_ae q hScalarMeas Cc hCc hScalarBound U] with y hy
    rw [hy]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hnonpos : (∫ y, q y * U y * U y ∂PDE.volumeOn Ω) ≤ 0 := by
    rw [← integral_zero]
    apply integral_mono_ae hint (integrable_zero (PDE.Vec d) ℝ (PDE.volumeOn Ω))
    filter_upwards [hq] with y hy
    simpa only [pow_two, mul_assoc, Pi.zero_apply] using (mul_nonpos_of_nonpos_of_nonneg hy (sq_nonneg (U y)))
  rw [L2.inner_def]
  calc
    (∫ y, inner ℝ
        ((scalarL2Multiplier q hScalarMeas Cc hCc hScalarBound U) y) (U y)
        ∂PDE.volumeOn Ω) = ∫ y, q y * U y * U y ∂PDE.volumeOn Ω := by
          apply integral_congr_ae
          filter_upwards [scalarL2Multiplier_apply_ae q hScalarMeas Cc hCc hScalarBound U] with y hy
          rw [hy]
          simp only [RCLike.inner_apply, conj_trivial]
          ring
    _ ≤ 0 := hnonpos

end

private theorem garding_young
    (lam D G U : ℝ) (hlam : 0 < lam) :
    (lam / 2) * G ^ 2 - (D ^ 2 / (2 * lam)) * U ^ 2 ≤
      lam * G ^ 2 - D * G * U := by
  field_simp
  nlinarith [sq_nonneg (lam * G - D * U)]

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- Explicit slice multiplier evidence and a local Loewner lower bound give a
uniform reverse-time spatial Gårding estimate. -/
theorem reverseTimeSpatialForm_garding_of_sliceMultiplierBounds
    (r₀ r₁ lam : ℝ) (hlam : 0 < lam) (hΩ : IsOpen Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (e : ReverseTimeSpatialFormEvidence r₀ r₁ Ω a b c)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
          K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u := by
  let Ca i j := (e.principal i j).bound
  let Cd j := (e.drift j).bound
  let Cc := e.scalar.bound
  have hCa i j := (e.principal i j).bound_nonneg
  have hCd j := (e.drift j).bound_nonneg
  have hCc := e.scalar.bound_nonneg
  let D : ℝ := ∑ j : Fin d, Cd j
  refine ⟨D ^ 2 / (2 * lam), div_nonneg (sq_nonneg _) (by positivity), ?_⟩
  intro τ hτ u
  let t : Icc 0 (r₁ - r₀) := ⟨τ,hτ⟩
  have hAMeas i j := (e.principal i j).measurable t
  have hABound i j := (e.principal i j).ae_le t
  have hDriftMeas j := (e.drift j).measurable t
  have hDriftBound j := (e.drift j).ae_le t
  have hScalarMeas := e.scalar.measurable t
  have hScalarBound := e.scalar.ae_le t
  have hp := principal_lower_of_loewner r₀ r₁ lam τ hΩ a u Ca hCa hAMeas hABound hLower hτ
  have hd := drift_lower_of_sliceMultiplierBounds hΩ r₁ τ a b Cd hCd hDriftMeas hDriftBound u
  have hc := scalar_multiplierInner_nonpos_of_nonpos r₀ r₁ τ hΩ c Cc hCc hScalarMeas hScalarBound hcNonpos hτ u
  rw [reverseTimeSpatialForm_eq_multiplierInner_of_sliceEvidence hΩ r₁ τ a b c u u
    Ca hCa hAMeas hABound Cd hCd hDriftMeas hDriftBound Cc hCc hScalarMeas hScalarBound]
  have hyoung := garding_young lam D ‖gradientCLM hΩ u‖ ‖valueCLM hΩ u‖ hlam
  change (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
      (D ^ 2 / (2 * lam)) * ‖valueCLM hΩ u‖ ^ 2 ≤ _
  linarith

/-- Smooth coefficients on a bounded closed cylinder give a bounded reverse-time
spatial form. -/
theorem reverseTimeSpatialForm_bounded_of_smoothOnNeighborhood
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u v : H10HilbertGraph hΩ,
        |reverseTimeSpatialForm hΩ r₁ τ a b c u v| ≤ C * ‖u‖ * ‖v‖ :=
  reverseTimeSpatialForm_bounded_of_sliceMultiplierBounds hΩ
    (ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth)

/-- Smooth coefficients on a bounded closed cylinder and a local lower
Loewner bound give a reverse-time spatial Gårding estimate. -/
theorem reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
    (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (c : ℝ → PDE.Vec d → ℝ)
    (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcNonpos : ∀ z : TimeVelocity d,
      z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ τ, τ ∈ Set.Icc 0 (r₁ - r₀) →
      ∀ u : H10HilbertGraph hΩ,
        (lam / 2) * ‖gradientCLM hΩ u‖ ^ 2 -
          K * ‖valueCLM hΩ u‖ ^ 2 ≤
        reverseTimeSpatialForm hΩ r₁ τ a b c u u :=
  reverseTimeSpatialForm_garding_of_sliceMultiplierBounds r₀ r₁ lam hlam hΩ a b c
    (ReverseTimeSpatialFormEvidence.ofSmooth hΩ hΩbounded haSmooth hbSmooth hcSmooth) hLower hcNonpos

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
