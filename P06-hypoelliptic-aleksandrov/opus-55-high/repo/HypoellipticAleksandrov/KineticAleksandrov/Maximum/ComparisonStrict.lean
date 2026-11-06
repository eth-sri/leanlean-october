module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry

/-! # Strictification by the source terminal-time tilt -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

variable {d : ℕ} (A : FullKineticCoefficient d) (T : ℝ) (P : KineticPoint d)

/-- The terminal-time affine function has unit time derivative and zero spatial derivatives. -/
theorem comparison_time_sub_formulas  :
    kineticTimeDerivative (fun Q : KineticPoint d => Q.time - T) P = 1 ∧
    kineticPositionGradient (fun Q : KineticPoint d => Q.time - T) P = 0 ∧
    kineticVelocityGradient (fun Q : KineticPoint d => Q.time - T) P = 0 ∧
    kineticVelocityHessian (fun Q : KineticPoint d => Q.time - T) P = 0 := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [kineticTimeDerivative]
    simp
  · ext i
    simp [kineticPositionGradient]
  · ext i
    simp [kineticVelocityGradient]
  · have hg : (fun v : PDE.Vec d =>
        PDE.classicalGradient (fun _ : PDE.Vec d => P.time - T) v) = fun _ => 0 := by
      aesop
    unfold kineticVelocityHessian
    aesop

/-- The time-affine function is in the source classical class on every set. -/
theorem comparison_regular_time_sub  (D : Set (KineticPoint d)) :
    IsKineticC112On (fun Q : KineticPoint d => Q.time - T) D := by
  refine ⟨(continuous_time.sub continuous_const).continuousOn,
    fun _ _ => differentiableAt_id.sub_const T,
    fun P _ => (show ContDiffAt ℝ 1 (fun _ : PDE.Vec d => P.time - T) P.position from
      contDiffAt_const),
    fun P _ => (show ContDiffAt ℝ 2 (fun _ : PDE.Vec d => P.time - T) P.velocity from
      contDiffAt_const),?_,?_,?_,?_⟩
  · have h : kineticTimeDerivative (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 1 := funext fun P => (comparison_time_sub_formulas T P).1
    rw [h]
    fun_prop
  · have h : kineticPositionGradient (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.1
    rw [h]
    fun_prop
  · have h : kineticVelocityGradient (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.2.1
    rw [h]
    fun_prop
  · have h : kineticVelocityHessian (fun Q : KineticPoint d => Q.time - T) =
        fun _ => 0 := funext fun P => (comparison_time_sub_formulas T P).2.2.2
    rw [h]
    fun_prop

/-- The forward operator of the terminal-time affine function equals one. -/
theorem comparison_forwardOperator_time_sub  :
    forwardKineticOperator A (fun Q : KineticPoint d => Q.time - T) P = 1 := by
  obtain ⟨ht,hx,_,hv⟩ := comparison_time_sub_formulas T P
  rw [forwardKineticOperator_apply,ht,hx,hv]
  simp [PDE.vecDot]

/-- The exact source tilt preserves regularity and is a strict subsolution at positive points. -/
theorem comparison_strictification 
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u : KineticPoint d → ℝ)
    (hu : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hsub : ∀ P ∈ forwardCylinder Z₀ R hR, 0 < u P →
      0 ≤ forwardKineticOperator A u P) (ε : ℝ) (hε : 0 < ε) :
    let w := fun P : KineticPoint d => u P + ε * (P.time - Z₀.time - R ^ 2)
    (∀ P ∈ closure (forwardCylinder Z₀ R hR), w P ≤ u P) ∧
      IsKineticC112On w (forwardCylinder Z₀ R hR) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR, 0 < w P →
        ε ≤ forwardKineticOperator A w P) := by
  let T := Z₀.time + R ^ 2
  simp only [sub_sub]
  have ht := comparison_regular_time_sub (d := d) T (forwardCylinder Z₀ R hR)
  have hle : ∀ P ∈ closure (forwardCylinder Z₀ R hR),
      u P + ε * (P.time - T) ≤ u P := by
    intro P hP
    have hp := (closure_forwardCylinder_bounds Z₀ R hR hP).1.2
    change P.time ≤ T at hp
    have hm := mul_nonpos_of_nonneg_of_nonpos hε.le (sub_nonpos.mpr hp)
    simp_all
  refine ⟨hle,comparison_regular_add hu (comparison_regular_const_mul ht ε),?_⟩
  intro P hP hpos
  rw [comparison_forwardOperator_add hu (comparison_regular_const_mul ht ε) A hP,
    comparison_forwardOperator_const_mul ht ε A hP,comparison_forwardOperator_time_sub]
  have hup : 0 < u P := lt_of_lt_of_le hpos (hle P (subset_closure hP))
  simp_all

end HypoellipticAleksandrov.KineticAleksandrov
