module
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.WholeSpaceCoefficient
public import HypoellipticAleksandrov.KineticAleksandrov.SourceProblem.InteriorEstimate

/-! # The backward estimate on a ball by reflection and parabolic scaling

Only an interior differential inequality and a sign on the backward boundary are needed;
there is no local boundary value problem to solve. -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open Parabolic MeasureTheory Set Filter SectionTwo
open scoped Topology MatrixOrder Matrix.Norms.Elementwise ENNReal
variable {d : ℕ}

theorem backward_ball_estimate (hd : 0 < d) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {B : CoefficientField d}, IsSectionTwoCoefficient lam Lam B →
    ∀ {F : TimeVelocity d → ℝ}, Continuous F → MemLp F (parabolicExponent d) volume →
    ∀ {α R : ℝ}, 0 ≤ α → α < 1 → 1 ≤ R → ∀ (v : PDE.Vec d) (V : TimeVelocity d → ℝ),
    let Ω := PDE.euclideanBall v R
    ContinuousOn V (scalarParabolicClosedCylinder α 1 Ω) → IsScalarC12On V (scalarParabolicOpenCylinder α 1 Ω) →
    (∀ z ∈ scalarParabolicOpenCylinder α 1 Ω, -F z ≤ scalarParabolicOperator B (fun _ _ => 0) V z) →
    (∀ z ∈ scalarParabolicTerminalFace 1 Ω ∪ scalarParabolicLateralFace α 1 Ω, V z ≤ 0) →
    ∀ z ∈ scalarParabolicClosedCylinder α 1 Ω, V z ≤ C * R ^ ((d : ℝ) / (d+1 : ℝ)) * parabolicLpNorm d F := by
  obtain ⟨C,hC,K⟩ := LsuFree.parabolic_aleksandrov_direct d hd lam Lam hlam hLam
  refine ⟨C,hC,?_⟩
  intro B hB F hF hm α R ha ht hR1 v V Ω hVc hV hop hb
  have hR := zero_lt_one.trans_le hR1
  let Q := scalarParabolicOpenCylinder α 1 Ω
  have ho : IsOpen Q := isOpen_Ioo.prod (PDE.isOpen_euclideanBall v R)
  let k := localHeight α R
  let m := reflectScale R v
  have hsub : krylovCylinder k k 0 ⊆ m ⁻¹' Q := fun z hz => (mem_krylovCylinder_iff_reflectScale hR z).1 hz
  obtain ⟨reg,_⟩ := isScalarC12On_reflectScale ho hV hR v
  have est := K k 0 k (localHeight_pos ht hR) (localHeight_le_one ha hR1)
    (coefficientAt B ∘ m) (localizedSource R v F) (V ∘ m)
    ((sectionTwoCoefficient_smooth hB).continuous.comp (continuous_reflectScale R v)).continuousOn
    (fun z _ => hB.2.2.2.1 _ _) (fun z _ => ⟨hB.2.2.2.2.1 _ _, hB.2.2.2.2.2 _ _⟩)
    (memLp_localizedSource hR hF hm)
    ⟨reg.1.mono hsub, fun z hz => reg.timeSlice_differentiableAt (hsub hz),
      fun z hz => reg.spatialSlice_contDiffAt (hsub hz), reg.continuousOn_scalarTimeDerivative.mono hsub,
      reg.continuousOn_scalarSpatialGradient.mono hsub, reg.continuousOn_scalarSpatialHessian.mono hsub⟩
    (hVc.comp (continuous_reflectScale R v).continuousOn (krylovClosedCylinder_subset_preimage hR))
    (ae_restrict_of_forall_mem (isOpen_krylovCylinder _ _ _).measurableSet fun z hz => by
      change scalarTimeDerivative (fun z => V (m z)) z - matrixContraction (coefficientAt B (m z)) _ ≤ R^2 * F (m z)
      simp only [m, Function.comp_def]; rw [scaled_operator_eq ho hV hR v B (hsub hz)]
      have e := hop (m z) (hsub hz)
      simp [scalarParabolicOperator, PDE.vecDot, coefficientAt, m] at e ⊢
      nlinarith only [mul_le_mul_of_nonneg_left e (sq_nonneg R)])
    (fun z hz => hb _ (krylovParabolicBoundary_subset_preimage hR hz))
  have hi : ∀ w ∈ Q, V w ≤ C * R ^ ((d : ℝ) / (d+1 : ℝ)) * parabolicLpNorm d F := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := exists_mem_krylovCylinder hR hw
    have hz' := est z hz
    rw [parabolicLpNormOn_localizedSource hR hF] at hz'
    rw [mul_assoc]; apply hz'.trans; gcongr
    exact ENNReal.toReal_mono hm.ne (eLpNorm_mono_measure F Measure.restrict_le_self)
  have eq : closure Q = scalarParabolicClosedCylinder α 1 Ω := by dsimp only [Q]; rw [scalarParabolicOpenCylinder, closure_prod_eq, closure_Ioo ht.ne]; rfl
  intro w hw
  exact ContinuousWithinAt.closure_le (eq.symm ▸ hw) ((hVc w hw).mono (subset_closure.trans eq.le)) continuousWithinAt_const hi

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
