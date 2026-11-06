module

public import PDEFoundation.Sobolev.WeakDerivative
import Aesop
import Mathlib.Tactic.Ring



/-!
# Linear algebra for weak first derivatives

The Bochner integral is not additive on arbitrary non-integrable functions.
Accordingly, the raw addition and subtraction lemmas below explicitly require
local integrability, with respect to the restricted measure, of both value
representatives and both weak-derivative representatives.

Negation and real scalar multiplication need no such hypotheses: the total
Bochner integral commutes with these operations without an integrability
assumption. These raw lemmas are the analytic input for the
representative-level `W^{1,p}` module structure when `1 ≤ p`.
-/

 public section

namespace PDE

namespace HasWeakPartialDerivOn

/-- Zero has zero weak partial derivative. -/
theorem zero {d : ℕ} {U : Set (Vec d)} {i : Fin d} :
    HasWeakPartialDerivOn U i (0 ) 0 := by
  intro φ _hφSmooth _hφCompact _hφSupport
  simp only [Pi.zero_apply, zero_mul, MeasureTheory.integral_zero, neg_zero]

variable {d : ℕ} {U : Set (Vec d)} {i : Fin d}

/-- Weak partial differentiation commutes with addition.

The four local-integrability assumptions are needed to apply additivity of the
Bochner integral to the two test-function pairings.
-/
theorem add
    {u v gi hi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    (hv : HasWeakPartialDerivOn U i v hi)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hgiLoc : MeasureTheory.LocallyIntegrable gi (volumeOn U))
    (hhiLoc : MeasureTheory.LocallyIntegrable hi (volumeOn U)) :
    HasWeakPartialDerivOn U i (u + v) (gi + hi) := by
  intro φ hφSmooth hφCompact hφSupport
  let dφ  :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  have hdφContinuous : Continuous dφ := by
    simpa only [dφ] using
      (hφSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφCompact : HasCompactSupport dφ := by
    simpa only [dφ] using
      hφCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)




  have huWeak := hu φ hφSmooth hφCompact hφSupport
  have hvWeak := hv φ hφSmooth hφCompact hφSupport
  change
    (∫ x, u x * dφ x ∂(volumeOn U)) =
      -(∫ x, gi x * φ x ∂(volumeOn U)) at huWeak
  change
    (∫ x, v x * dφ x ∂(volumeOn U)) =
      -(∫ x, hi x * φ x ∂(volumeOn U)) at hvWeak
  change
    (∫ x, (u + v) x * dφ x ∂(volumeOn U)) =
      -(∫ x, (gi + hi) x * φ x ∂(volumeOn U))
  calc
    (∫ x, (u + v) x * dφ x ∂(volumeOn U)) =
        ∫ x, u x * dφ x + v x * dφ x ∂(volumeOn U) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.add_apply, add_mul]
    _ = (∫ x, u x * dφ x ∂(volumeOn U)) +
          ∫ x, v x * dφ x ∂(volumeOn U) := by
            rw [MeasureTheory.integral_add (by
                simpa only [smul_eq_mul] using
                  huLoc.integrable_smul_right_of_hasCompactSupport
                    hdφContinuous hdφCompact) (by
                simpa only [smul_eq_mul] using
                  hvLoc.integrable_smul_right_of_hasCompactSupport
                    hdφContinuous hdφCompact)]
    _ = (-(∫ x, gi x * φ x ∂(volumeOn U))) +
          (-(∫ x, hi x * φ x ∂(volumeOn U))) := by
            rw [huWeak, hvWeak]
    _ = -((∫ x, gi x * φ x ∂(volumeOn U)) +
          ∫ x, hi x * φ x ∂(volumeOn U)) :=
      (neg_add _ _).symm
    _ = -(∫ x, gi x * φ x + hi x * φ x ∂(volumeOn U)) := by
          rw [MeasureTheory.integral_add (by
              simpa only [smul_eq_mul] using
                hgiLoc.integrable_smul_right_of_hasCompactSupport
                  hφSmooth.continuous hφCompact) (by
              simpa only [smul_eq_mul] using
                hhiLoc.integrable_smul_right_of_hasCompactSupport
                  hφSmooth.continuous hφCompact)]
    _ = -(∫ x, (gi + hi) x * φ x ∂(volumeOn U)) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.add_apply, add_mul]

section
variable {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi)

include h
/-- Weak partial differentiation commutes with real scalar multiplication. -/
theorem smul
     (c : ℝ) :
    HasWeakPartialDerivOn U i (c • u) (c • gi) := by
  intro φ hφSmooth hφCompact hφSupport
  let dφ  :=
    fun x => (fderiv ℝ φ x) (basisVec i)
  have hWeak := h φ hφSmooth hφCompact hφSupport
  change
    (∫ x, u x * dφ x ∂(volumeOn U)) =
      -(∫ x, gi x * φ x ∂(volumeOn U)) at hWeak
  change
    (∫ x, (c • u) x * dφ x ∂(volumeOn U)) =
      -(∫ x, (c • gi) x * φ x ∂(volumeOn U))
  calc
    (∫ x, (c • u) x * dφ x ∂(volumeOn U)) =
        ∫ x, c * (u x * dφ x) ∂(volumeOn U) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = c * ∫ x, u x * dφ x ∂(volumeOn U) := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * (-(∫ x, gi x * φ x ∂(volumeOn U))) := by
          rw [hWeak]
    _ = -(c * ∫ x, gi x * φ x ∂(volumeOn U)) := by
          ring
    _ = -(∫ x, c * (gi x * φ x) ∂(volumeOn U)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = -(∫ x, (c • gi) x * φ x ∂(volumeOn U)) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Weak partial differentiation commutes with negation. -/
theorem neg
     :
    HasWeakPartialDerivOn U i (-u) (-gi) := by
  change HasWeakPartialDerivOn U i
    (fun x => -u x) (fun x => -gi x)
  have hs := h.smul (-1)
  aesop
end


/-- Weak partial differentiation commutes with subtraction.

As for addition, local integrability of both values and both weak partial
representatives is essential.
-/
theorem sub
    {u v gi hi : Vec d → ℝ}
    (hu : HasWeakPartialDerivOn U i u gi)
    (hv : HasWeakPartialDerivOn U i v hi)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hgiLoc : MeasureTheory.LocallyIntegrable gi (volumeOn U))
    (hhiLoc : MeasureTheory.LocallyIntegrable hi (volumeOn U)) :
    HasWeakPartialDerivOn U i (u - v) (gi - hi) := by
  simpa only [sub_eq_add_neg] using
    hu.add hv.neg huLoc hvLoc.neg hgiLoc hhiLoc.neg

end HasWeakPartialDerivOn

namespace HasWeakGradientOn

/-- The zero vector field is a weak gradient of the zero function. -/
theorem zero {d : ℕ} {U : Set (Vec d)} :
    HasWeakGradientOn U (0 ) 0 := by
  intro i
  exact HasWeakPartialDerivOn.zero

variable {d : ℕ} {U : Set (Vec d)}

/-- Weak gradients commute with addition under the local-integrability
hypotheses needed coordinatewise by the raw Bochner identities. -/
theorem add
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    (hv : HasWeakGradientOn U v Dv)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hDuLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Du x i) (volumeOn U))
    (hDvLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Dv x i) (volumeOn U)) :
    HasWeakGradientOn U (u + v) (Du + Dv) := (fun i => id (HasWeakPartialDerivOn.add (hu i) (hv i) huLoc hvLoc (hDuLoc i) (hDvLoc i)))

section
variable {u : Vec d → ℝ} {Du : Vec d → Vec d} (h : HasWeakGradientOn U u Du)

include h
/-- Weak gradients commute with real scalar multiplication. -/
theorem smul
     (c : ℝ) :
    HasWeakGradientOn U (c • u) (c • Du) := (fun i => id (HasWeakPartialDerivOn.smul (h i) c))

/-- Weak gradients commute with negation. -/
theorem neg
     :
    HasWeakGradientOn U (-u) (-Du) := (fun i => id (HasWeakPartialDerivOn.neg (h i)))
end


/-- Weak gradients commute with subtraction under the local-integrability
hypotheses needed coordinatewise by the raw Bochner identities. -/
theorem sub
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : HasWeakGradientOn U u Du)
    (hv : HasWeakGradientOn U v Dv)
    (huLoc : MeasureTheory.LocallyIntegrable u (volumeOn U))
    (hvLoc : MeasureTheory.LocallyIntegrable v (volumeOn U))
    (hDuLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Du x i) (volumeOn U))
    (hDvLoc : ∀ i, MeasureTheory.LocallyIntegrable
      (fun x => Dv x i) (volumeOn U)) :
    HasWeakGradientOn U (u - v) (Du - Dv) := (fun i => id (HasWeakPartialDerivOn.sub (hu i) (hv i) huLoc hvLoc (hDuLoc i) (hDvLoc i)))

end HasWeakGradientOn

end PDE
