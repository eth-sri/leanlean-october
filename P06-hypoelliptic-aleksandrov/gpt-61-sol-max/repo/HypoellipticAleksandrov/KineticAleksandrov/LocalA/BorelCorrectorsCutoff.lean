module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BorelCorrectorWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelInnerError
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import PDEFoundation.Calculus.RegularityOrder


/-! # Compact collars and actual cutoff residuals for Borel correctors -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open Set Parabolic
open scoped Topology Matrix.Norms.Elementwise

variable {d : ℕ}

/-- Compact interior sets have a compact collar and a physical smooth cutoff. -/
theorem exists_borelCorrector_cutoff  {D K : Set (KineticPoint d)}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ (O : Set (KineticPoint d)) (χ : HypoellipticAleksandrov.KineticScalarField d),
      IsOpen O ∧ K ⊆ O ∧ closure O ⊆ D ∧ IsCompact (closure O) ∧
      ContDiff ℝ PDE.smoothOrder (χ ∘ (KineticPoint.equivProd d).symm) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ D ∧
      (∀ P, 0 ≤ χ P ∧ χ P ≤ 1) ∧ (∀ P ∈ closure O, χ P = 1) := by
  let e := KineticPoint.homeomorphProd d
  obtain ⟨V, hV, hKV, hVD, hVc⟩ := exists_open_between_and_isCompact_closure
    (hK.image e.continuous) (e.isOpenMap _ hD) (image_mono hKD)
  obtain ⟨φ, hφ, hφc, hφD, hφb, hφone⟩ := SectionTwo.exists_smooth_cutoff
    hVc (e.isOpenMap _ hD) hVD


  have hclosure  := e.preimage_closure V |>.symm
  refine ⟨(e ⁻¹' V), (φ ∘ e), hV.preimage e.continuous, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P hP
    exact hKV (mem_image_of_mem e hP)
  · rw [hclosure]
    intro P hP
    obtain ⟨Q, hQ, hQP⟩ := hVD hP
    exact e.injective hQP ▸ hQ
  · rw [hclosure]
    exact e.isCompact_preimage.mpr hVc
  · assumption
  · exact hφc.comp_homeomorph e
  ·
    rw [(tsupport_comp_eq_preimage φ e)]
    intro P hP
    obtain ⟨Q, hQ, hQP⟩ := hφD hP
    exact e.injective hQP ▸ hQ
  · exact fun P => hφb (e P)
  · intro P hP
    exact hφone (e P) (by rwa [hclosure] at hP)

/-- Multiplication by a cutoff supported in the domain gives a globally continuous function. -/
theorem borelCorrector_cutoff_continuous  {D : Set (KineticPoint d)}
    (hD : IsOpen D) (χ f : HypoellipticAleksandrov.KineticScalarField d) (hχ : Continuous χ)
    (hs : tsupport χ ⊆ D) (hf : ContinuousOn f D) :
    Continuous (fun P => χ P * f P) := by
  apply continuous_iff_continuousAt.mpr
  intro P
  by_cases hP : P ∈ D
  · exact (hχ.continuousAt.mul (hf.continuousAt (hD.mem_nhds hP)))
  ·

    exact continuousAt_const.congr (show (fun Q => χ Q * f Q) =ᶠ[𝓝 P] (fun _ => 0) by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds (fun h => hP (hs h))] with Q hQ
        rw [image_eq_zero_of_notMem_tsupport hQ, zero_mul]).symm

/-- The actual cutoff source uses the smooth coefficient's classical residual. -/
def borelCorrectorSource  (χ : HypoellipticAleksandrov.KineticScalarField d)
    (B : CoefficientField d) (U : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d) : ℝ :=
  χ P * forwardKineticOperator (ofTimeVelocityCoefficient B) U P

/-- C112 jets make each cutoff residual continuous and compactly supported. -/
theorem borelCorrectorSource_continuous_compact  {D : Set (KineticPoint d)}
    (hD : IsOpen D) (χ : HypoellipticAleksandrov.KineticScalarField d) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hs : tsupport χ ⊆ D)
    (B : CoefficientField d) (hB : IsSmoothCoefficient B)
    (U : HypoellipticAleksandrov.KineticScalarField d) (hu : IsKineticC112On U D) :
    Continuous (borelCorrectorSource χ B U) ∧
      HasCompactSupport (borelCorrectorSource χ B U) := by
  refine ⟨borelCorrector_cutoff_continuous hD χ _ hχ hs ?_, hχc.mul_right⟩
  exact continuousOn_forwardKineticOperator hu (ofTimeVelocityCoefficient B)
    (hB.continuous.comp (continuous_time.prodMk continuous_velocity)).continuousOn

/-- The forward operator change is exactly the coefficient-Hessian contraction. -/
theorem borelCorrector_operator_sub  (B A : CoefficientField d)
    (U : HypoellipticAleksandrov.KineticScalarField d) (P : KineticPoint d) :
    forwardKineticOperator (ofTimeVelocityCoefficient B) U P -
      forwardKineticOperator (ofTimeVelocityCoefficient A) U P =
      matrixContraction (B P.time P.velocity - A P.time P.velocity)
        (kineticVelocityHessian U P) := by
  simp only [forwardKineticOperator_apply, ofTimeVelocityCoefficient, matrixContraction,
    Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
