module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.KineticPullbackJets
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Setting
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateEllipticity
public import HypoellipticAleksandrov.Parabolic.Scaling
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! # Kinetic affine normalization of supplied classical solutions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set MeasureTheory Parabolic Holder
open scoped MatrixOrder ContDiff Matrix.Norms.Elementwise

variable {d : ℕ}

/-- The time--velocity coefficient in the normalized physical coordinates. -/
def kineticPullbackCoefficient  (A : CoefficientField d)
    (P₀ : KineticPoint d) (R : ℝ) : CoefficientField d :=
  fun t v => A (P₀.time + R ^ 2 * t) (P₀.velocity + R • v)

variable {A : CoefficientField d}

/-- Normalization preserves smoothness of the time--velocity coefficient. -/
theorem kineticPullbackCoefficient_smooth
    (hA : IsSmoothCoefficient A) (P₀ : KineticPoint d) (R : ℝ) :
    IsSmoothCoefficient (kineticPullbackCoefficient A P₀ R) := hA.comp (show ContDiff ℝ ∞ (fun z : TimeVelocity d =>
    (P₀.time + R ^ 2 * z.1, P₀.velocity + R • z.2)) by fun_prop)

/-- Normalization preserves the symmetry and the literal ellipticity constants. -/
theorem kineticPullbackCoefficient_bounds
    {lam Lam : ℝ} (hs : IsSymmetricCoefficient A)
    (hlo : HasLowerEllipticity lam A) (hhi : HasUpperEllipticity Lam A)
    (P₀ : KineticPoint d) (R : ℝ) :
    IsSymmetricCoefficient (kineticPullbackCoefficient A P₀ R) ∧
    HasLowerEllipticity lam (kineticPullbackCoefficient A P₀ R) ∧
    HasUpperEllipticity Lam (kineticPullbackCoefficient A P₀ R) :=
  ⟨fun t v => hs _ _,
    fun t v => hlo _ _,
    fun t v => hhi _ _⟩

variable {u : KineticPoint d → ℝ}

variable {D : Set (KineticPoint d)}

section
variable (hD : IsOpen D) (hu : IsKineticC112On u D)

include hD hu
/-- The anisotropic classical class is preserved by the moving affine pullback. -/
theorem kineticPullback_C112

    (P₀ : KineticPoint d) (R : ℝ) :
    IsKineticC112On (kineticPullback u P₀ R) (kineticAffine P₀ R ⁻¹' D) := by
  let E := kineticAffine P₀ R ⁻¹' D
  have hc := (continuous_kineticAffine P₀ R).continuousOn (s := E)
  have hmap : ∀ P ∈ E, kineticAffine P₀ R P ∈ D := fun _ h => h

  have hx := hu.continuousOn_kineticPositionGradient.comp hc hmap


  refine ⟨hu.continuousOn.comp hc hmap, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hp
    exact (kineticPullback_time_hasDerivAt hD hu P₀ R P hp).differentiableAt
  · intro P hp
    let a := P₀.position + (R ^ 2 * P.time) • P₀.velocity
    have hs := hu.positionSlice_contDiffAt hp
    have he : (kineticAffine P₀ R P).position = a + R ^ 3 • P.position := by
      dsimp [kineticAffine, a]
      abel_nf
    rw [he] at hs
    have h := hs.comp P.position
      (show ContDiffAt ℝ 1 (fun x : PDE.Vec d => a + R ^ 3 • x) P.position by fun_prop)
    convert h using 1
    funext x
    simp only [kineticPullback, Function.comp_def, kineticAffine, a]
    congr 1
    abel_nf
  · intro P hp
    change ContDiffAt ℝ 2
      (fun v => u ⟨P₀.time + R ^ 2 * P.time,
        (kineticAffine P₀ R P).position, P₀.velocity + R • v⟩) P.velocity
    have h := (hu.velocitySlice_contDiffAt hp).comp P.velocity
      (show ContDiffAt ℝ 2 (fun v  => P₀.velocity + R • v)
        P.velocity by fun_prop)
    exact h
  ·
    exact (((hu.continuousOn_kineticTimeDerivative.comp hc hmap).add (by
        unfold PDE.vecDot
        apply continuousOn_finsetSum
        intro i _
        exact continuousOn_const.mul ((continuous_apply i).comp_continuousOn hx))).const_smul (R ^ 2)).congr
      ((kineticPullback_timeDerivative hD hu P₀ R))
  · exact (hx.const_smul (R ^ 3)).congr
      ((kineticPullback_positionGradient hu P₀ R))
  · exact ((hu.continuousOn_kineticVelocityGradient.comp hc hmap).const_smul R).congr
      ((kineticPullback_velocityGradient hu P₀ R))
  · exact ((hu.continuousOn_kineticVelocityHessian.comp hc hmap).const_smul (R ^ 2)).congr
      ((kineticPullback_velocityHessian hu P₀ R))

/-- The normalized operator is the original operator multiplied by the time dilation. -/
theorem kineticPullback_operator

    (A : CoefficientField d) (P₀ : KineticPoint d) (R : ℝ) (P : KineticPoint d)
    (hp : kineticAffine P₀ R P ∈ D) :
    backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
      (kineticPullback u P₀ R) P =
    R ^ 2 * backwardOperatorOfTimeVelocityCoefficient A u (kineticAffine P₀ R P) := by
  rw [backwardOperatorOfTimeVelocityCoefficient_apply,
    kineticPullback_timeDerivative hD hu P₀ R P hp,
    kineticPullback_positionGradient hu P₀ R P hp,
    kineticPullback_velocityHessian hu P₀ R P hp,
    matrixContraction_smul_right, backwardOperatorOfTimeVelocityCoefficient_apply]
  have hd₁ : ∀ (c : ℝ) (v g : PDE.Vec d),
      PDE.vecDot v (c • g) = c * PDE.vecDot v g := by
    intro c v g
    simp only [PDE.vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd₂ : ∀ (c : ℝ) (v w g : PDE.Vec d),
      PDE.vecDot (v + c • w) g = PDE.vecDot v g + c * PDE.vecDot w g := by
    intro c v w g
    simp only [PDE.vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hd₁, kineticAffine_velocity, hd₂]
  simp only [kineticPullbackCoefficient, kineticAffine_time]
  ring
end


/-- The classical kinetic operator is continuous on its open solution domain. -/
theorem continuousOn_backwardOperator
     (hu : IsKineticC112On u D)
    {A : CoefficientField d} (hA : IsContinuousCoefficient A) :
    ContinuousOn (backwardOperatorOfTimeVelocityCoefficient A u) D := (id
  (ContinuousOn.sub
    (ContinuousOn.add (IsKineticC112On.continuousOn_kineticTimeDerivative hu)
      (continuousOn_finsetSum Finset.univ fun i a =>
        ContinuousOn.mul (Continuous.continuousOn (Continuous.comp (continuous_apply i) continuous_velocity))
          (Continuous.comp_continuousOn (continuous_apply i)
            (IsKineticC112On.continuousOn_kineticPositionGradient hu))))
    (continuousOn_finsetSum Finset.univ fun i a =>
      continuousOn_finsetSum Finset.univ fun j a =>
        ContinuousOn.mul
          (Continuous.comp_continuousOn (continuous_apply j)
            (Continuous.comp_continuousOn (continuous_apply i)
              (Continuous.continuousOn (Continuous.comp hA (Continuous.prodMk continuous_time continuous_velocity)))))
          (Continuous.comp_continuousOn (continuous_apply j)
            (Continuous.comp_continuousOn (continuous_apply i)
              (IsKineticC112On.continuousOn_kineticVelocityHessian hu))))))

/-- A continuous classical equation holding almost everywhere holds at every interior point. -/
theorem backwardEquation_pointwise
     (hD : IsOpen D) (hu : IsKineticC112On u D)
    {A : CoefficientField d} (hA : IsContinuousCoefficient A)
    (he : ∀ᵐ P ∂volume.restrict D, backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    ∀ P ∈ D, backwardOperatorOfTimeVelocityCoefficient A u P = 0 :=
  Evolution.eqOn_of_ae_eq_of_continuousOn_kinetic hD
    ((continuousOn_backwardOperator hu hA).comp
      (Evolution.evolutionHomeomorph d).continuous.continuousOn (fun _ h => h))
    continuousOn_const he

/-- Normalization supplies the pointwise homogeneous equation on the unit cylinder. -/
theorem kineticPullback_normalized
    (P₀ : KineticPoint d) {R : ℝ} (hR : 0 < R)
    (hu : IsKineticC112On u (backwardCylinder P₀ R))
    {A : CoefficientField d} (hA : IsSmoothCoefficient A)
    (he : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
      backwardOperatorOfTimeVelocityCoefficient A u P = 0) :
    IsKineticC112On (kineticPullback u P₀ R)
      (backwardCylinder (⟨0, 0, 0⟩ ) 1) ∧
    ∀ P ∈ backwardCylinder (⟨0, 0, 0⟩ : KineticPoint d) 1,
      backwardOperatorOfTimeVelocityCoefficient (kineticPullbackCoefficient A P₀ R)
        (kineticPullback u P₀ R) P = 0 := by
  have hD := isOpen_backwardCylinder P₀ R hR
  have hp  :=
    fun P h => (kineticAffine_mem_cylinder P₀ P hR).mpr h
  have hreg := kineticPullback_C112 hD hu P₀ R

  refine ⟨(⟨hreg.1.mono hp, fun P h => hreg.2.1 P (hp P h),
        fun P h => hreg.2.2.1 P (hp P h), fun P h => hreg.2.2.2.1 P (hp P h),
        hreg.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.1.mono hp,
        hreg.2.2.2.2.2.2.1.mono hp, hreg.2.2.2.2.2.2.2.mono hp⟩), ?_⟩
  intro P hP
  rw [kineticPullback_operator hD hu A P₀ R P (hp P hP),
    backwardEquation_pointwise hD hu hA.continuous he _ (hp P hP), mul_zero]

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
