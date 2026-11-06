module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullCutoffRawHessian
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.NearFullDensity
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic
public import PDEFoundation.Calculus.RegularityOrder


/-! # Uniform almost-everywhere operator bound for the physical near-full cutoff -/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Holder

open Set MeasureTheory
open scoped MatrixOrder

variable {d : ℕ} {f : ℝ × (PDE.Vec d × PDE.Vec d) → ℝ} (hf : ContDiff ℝ PDE.smoothOrder f)

include hf in
/-- The unit jet expression is jointly continuous in point and matrix entries. -/
theorem continuous_unitCutoffJet  :
    Continuous (fun z : KineticPoint d × PDE.Mat d =>
      fderiv ℝ f (KineticPoint.equivProd d z.1) (1, (z.1.velocity, 0)) -
        matrixContraction z.2 (sliceHessian (unitCutoffVelocitySlice f z.1) z.1.velocity)) := (Continuous.sub (Continuous.comp (continuous_unitCutoffTransport hf) continuous_fst)
  (id
    (continuous_finsetSum Finset.univ fun i a =>
      continuous_finsetSum Finset.univ fun j a =>
        Continuous.mul (Continuous.comp (continuous_apply j) (Continuous.comp (continuous_apply i) continuous_snd))
          (Continuous.comp (continuous_apply j)
            (Continuous.comp (continuous_apply i)
              (Continuous.comp (continuous_unitCutoffVelocityHessian hf) continuous_fst))))))

variable (Lam : ℝ)

include hf
/-- Compact unit geometry gives a matrix-entry-uniform bound on the cutoff jet. -/
theorem exists_unitCutoffJet_bound   :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ Q ∈ closure
      (backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1),
      ∀ B : PDE.Mat d, (∀ i j, |B i j| ≤ |Lam|) →
        |fderiv ℝ f (KineticPoint.equivProd d Q) (1, (Q.velocity, 0)) -
          matrixContraction B (sliceHessian (unitCutoffVelocitySlice f Q) Q.velocity)| ≤ C₀ := (Exists.casesOn
  (IsCompact.exists_bound_of_continuousOn
    (IsCompact.prod
      (isCompact_closure_backwardCylinder { time := 0, position := 0, velocity := 0 } 1
        (Mathlib.Meta.NormNum.isNat_lt_true (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_zero)
          (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one) (Eq.refl false)))
      (isCompact_pi_infinite fun x => isCompact_pi_infinite fun x => isCompact_Icc))
    (Continuous.continuousOn (continuous_unitCutoffJet hf)))
  fun M hM =>
  Exists.intro (max M 0)
    ⟨le_max_right M 0, fun Q hQ B hB => LE.le.trans (hM (Q, B) ⟨hQ, fun i j => abs_le.mp (hB i j)⟩) (le_max_left M 0)⟩)

/-- Ellipticity and exact affine jets yield the source cutoff bound with uniform constants. -/
theorem exists_scaledUnitCutoff_operator_bound   :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ lam : ℝ, 0 < lam →
      ∀ A : FullKineticCoefficient d, FullElliptic lam Lam A →
      ∀ (P₀ : KineticPoint d) (R ell : ℝ), 0 < R → 0 ≤ ell →
      ∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
        |backwardOperator A (scaledUnitCutoff f P₀ R ell) P| ≤ C₀ * ell * (R ^ 2)⁻¹ := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_unitCutoffJet_bound hf Lam
  refine ⟨C₀, hC₀, fun lam hlam A hA P₀ R ell hR hell => ?_⟩

  filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet,
    ae_restrict_of_ae hA.2.2.1, ae_restrict_of_ae hA.2.2.2] with P hP hl hu

  have hB  :=
    fun i j =>
      (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam hl hu i j).trans (le_abs_self Lam)

  rw [scaledUnitCutoff_backwardOperator hf, abs_mul,
    abs_of_nonneg (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))]
  calc
    _ ≤ ell * (R ^ 2)⁻¹ * C₀ :=
      mul_le_mul_of_nonneg_left (hbound _ (subset_closure (show kineticAffineInverse P₀ R P ∈
      backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1 by
          apply (kineticAffine_mem_cylinder P₀ _ hR).mp
          simpa only [kineticAffine_apply_inverse P₀ hR.ne' P] using hP)) _ hB) (mul_nonneg hell (inv_nonneg.mpr (sq_nonneg R)))
    _ = C₀ * ell * (R ^ 2)⁻¹ := by ring

end HypoellipticAleksandrov.KineticAleksandrov.Holder
