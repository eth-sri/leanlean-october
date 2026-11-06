module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Smoothness and the classical source equation for the parabolic Duhamel potential

The packed function `(σ, v, z) ↦ W(σ, v)` is a distributional solution of `Lop u = -g` on the
preimage of `U₀`, so Hörmander's theorem (taken as the explicit hypothesis `hH`) gives a smooth
representative, which equals the continuous `W` pointwise.  The weak equation then becomes the
classical equation `∂_σ W + B : D_v² W = -g` in `U₀`.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped MatrixOrder

variable {n : ℕ}

/-- Hörmander regularity for a distributional solution of `Lop u = g` with smooth `g`
(packed coordinates), with Hörmander's theorem as the explicit hypothesis `hH`. -/
theorem exists_smooth_representative_transported_source
    (hH : HormanderHypoellipticityStatement) {lam Lam m : ℝ}
    {B : FullKineticCoefficient n} {b : PDE.VectorField n} (hlam : 0 < lam)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
    (hm : 0 < m) (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    {U : Set (EvolutionVec n)} (hU : IsOpen U) {u g : EvolutionVec n → ℝ}
    (hu : IsWeakTransportedSolution B b U u g) (hg : ContDiffOn ℝ PDE.smoothOrder g U) :
    ∃ f : EvolutionVec n → ℝ, ContDiffOn ℝ PDE.smoothOrder f U ∧
      u =ᵐ[volume.restrict U] f := by
  obtain ⟨hX, hspan⟩ :=
    hormander_hypotheses_transportedFields hlam hB_smooth hB_ell hb_smooth hm hb_coercive U

  exact hH hU _ _ _ _ hX hspan contDiffOn_const (hasWeakHormanderEquation_transportedFields hlam hB_smooth hB_ell hb_smooth hu hg)

section Potential

variable {d : ℕ} {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d}
variable (K : MovingFiberKernel Ω γ)

/-- The parabolic operator of a smooth function with continuous coefficient is continuous. -/
theorem continuousOn_scalarParabolicOperator_of_contDiffOn {B' : CoefficientField d}
    (hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B' p.1 p.2 i j))
    {D : HypoellipticAleksandrov.Parabolic.Region d} (hD : IsOpen D) {w : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hw : ContDiffOn ℝ PDE.smoothOrder w D) :
    ContinuousOn (scalarParabolicOperator B' (fun _ _ => 0) w) D := by
  have hu : IsScalarC12On w D :=
    isScalarC12On_of_isOpen_contDiffOn_two hD (hw.of_le (by norm_num))
  have hfun : scalarParabolicOperator B' (fun _ _ => 0) w = fun p =>
      scalarTimeDerivative w p + ∑ i, ∑ j, B' p.1 p.2 i j * scalarSpatialHessian w p i j := by
    funext p
    simp [scalarParabolicOperator_apply, matrixContraction, PDE.vecDot]
  rw [hfun]
  refine hu.continuousOn_scalarTimeDerivative.add (continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => (hBc i j).continuousOn.mul ?_)
  exact (show Continuous (fun A : PDE.Mat d => A i j) from
    (continuous_apply j).comp (continuous_apply i)).comp_continuousOn
      hu.continuousOn_scalarSpatialHessian

/-- The lift `(σ, v) ↦ (σ, v, 0)` is smooth. -/
theorem contDiff_zeroLift : ContDiff ℝ PDE.smoothOrder (fun p : TimeVelocity d =>
    packPoint p.1 p.2 (0 ) ) := (Eq.mpr (id (congrArg (fun _a => ContDiff ℝ (↑PDE.smoothOrder) _a) (funext fun p => Eq.refl (packPoint p.1 p.2 0))))
  (ContDiff.comp (ContinuousLinearEquiv.contDiff (evolutionProdCLE d).symm)
    (ContDiff.prodMk contDiff_fst (ContDiff.prodMk contDiff_snd contDiff_const))))

/-- **Smoothness and the source equation.**  Under Hörmander's theorem (`hH`), the Duhamel
potential is smooth in `U₀` and satisfies `∂_σ W + B : D_v² W = -g` there. -/
theorem duhamel_smooth_equation (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hγ : Continuous γ) {lam Lam : ℝ}
    {B : CoefficientField d} (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩa) (zIndependentCoefficient B) K)
    (g : HypoellipticAleksandrov.Parabolic.ScalarField d) (hgn : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ PDE.smoothOrder g)
    (hgc : HasCompactSupport g) (T : ℝ) (hgU : tsupport g ⊆ duhamelFiber Ω γ T) :
    ContDiffOn ℝ PDE.smoothOrder
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
        (duhamelFiber Ω γ T) ∧
      ∀ p ∈ duhamelFiber Ω γ T,
        scalarParabolicOperator B (fun _ _ => 0)
          (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g)
          p = -g p := by

  set W := parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩa) T g with hW
  obtain ⟨hsm, hsymm, hell⟩ := SectionTwo.sectionTwoCoefficient_fullBounds lam Lam B hB
  have hlam  := hB.1
  have hb  := SectionTwo.identityDrift_smooth d
  have hcoerc := (SectionTwo.identityDrift_bounds d).2
  set Qp := evolutionToTimeVelocity d with hQp
  have hU₀  :=
    isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ T
  have hU  := hU₀.preimage Qp.continuous
  have hWc : ContinuousOn W (duhamelFiber Ω γ T) :=
    (continuousOn_duhamelPotential K hΩa hγ hP g hgn hgs hgc T hgU).mono
      (duhamelFiber_subset_closedFiber T)
  have hWQ : ContinuousOn (fun x => W (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) :=
    hWc.comp Qp.continuous.continuousOn (fun x hx => hx)
  -- the weak equation on the packed set
  have hweak : IsWeakTransportedSolution (zIndependentCoefficient B) (SectionTwo.identityDrift d)
      (Qp ⁻¹' duhamelFiber Ω γ T) (fun x => W (Qp x)) (fun x => -g (Qp x)) := by
    refine ⟨hWQ.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
    have hfull := duhamel_weak_identity K hΩa hγ hP hsm hb g hgn hgs hgc T hgU hψ hc hs
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [neg_mul, integral_neg]
      exact hfull
    · intro x hx
      have : x ∉ tsupport ψ := fun h => hx (hs h)
      rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
    · intro x hx
      have : x ∉ tsupport ψ := fun h => hx (hs h)
      rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ this, mul_zero]
  have hg' : ContDiffOn ℝ PDE.smoothOrder (fun x => -g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) :=
    ((hgs.comp Qp.contDiff).neg).contDiffOn
  obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hlam hsm hell hb
    one_pos hcoerc hU hweak hg'
  have heq  :=
    Measure.eqOn_open_of_ae_eq hae hU hWQ hf.continuousOn
  -- smoothness of `W`
  have hι : ∀ p : TimeVelocity d, Qp (packPoint p.1 p.2 (0 )) = p := fun p => by
    simp [hQp]
  have hmaps : MapsTo (fun p : TimeVelocity d => packPoint p.1 p.2 (0 ))
      (duhamelFiber Ω γ T) (Qp ⁻¹' duhamelFiber Ω γ T) := fun p hp => by
    simpa only [mem_preimage, hι] using hp
  have hsmooth : ContDiffOn ℝ PDE.smoothOrder W (duhamelFiber Ω γ T) := by
    have h1 : ContDiffOn ℝ PDE.smoothOrder (f ∘ fun p : TimeVelocity d =>
        packPoint p.1 p.2 (0 )) (duhamelFiber Ω γ T) :=
      hf.comp contDiff_zeroLift.contDiffOn hmaps
    refine h1.congr fun p hp => ?_
    have := heq (hmaps hp)
    simpa only [hι, Function.comp_apply] using this
  refine ⟨hsmooth, ?_⟩
  -- the classical equation
  have hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B p.1 p.2 i j) := fun i j =>
    (hsm i j).continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk
      (continuous_const : Continuous fun _ : TimeVelocity d => (0 : PDE.Vec d))))
  have hopc := continuousOn_scalarParabolicOperator_of_contDiffOn hBc hU₀ hsmooth
  have hopQ : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x))
      (Qp ⁻¹' duhamelFiber Ω γ T) := hopc.comp Qp.continuous.continuousOn (fun x hx => hx)
  have hgQ : Continuous (fun x => g (Qp x)) := hgs.continuous.comp Qp.continuous

  intro p hp
  have := (show ∀ x ∈ Qp ⁻¹' duhamelFiber Ω γ T,
      scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x) = 0 by
      have hcont : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) +
          g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) := hopQ.add hgQ.continuousOn
      have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
          let sharedTerm_a763e5fa95 := (∫ x, scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x)
          have h1 := integral_transportedAdjoint_zIndep hsm hb hU₀ hsmooth hψ hc hs
          have h2 := hweak.2 ψ hψ hc hs
          have iA := integrable_evolution_mul_test hopQ hψ.continuous hc hs
          have iG := integrable_evolution_mul_test hgQ.continuousOn hψ.continuous hc hs
          have hAeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T,
              scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x) =
              sharedTerm_a763e5fa95 :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
              rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
          have hGeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T, -g (Qp x) * ψ x) =
              -∫ x, g (Qp x) * ψ x := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
              rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])]
            simp only [neg_mul, integral_neg]
          rw [hAeq] at h1
          have h3 : (sharedTerm_a763e5fa95) +
              ∫ x, g (Qp x) * ψ x = 0 := by
            have := h1.symm.trans h2
            rw [hGeq] at this
            linarith
          have : (fun x => ψ x • (scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x))) =
              fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x + g (Qp x) * ψ x := by
            funext x; simp only [smul_eq_mul]; ring
          rw [this, integral_add iA iG, h3])

      exact Measure.eqOn_open_of_ae_eq (show (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x))
          =ᵐ[volume.restrict (Qp ⁻¹' duhamelFiber Ω γ T)] fun _ => (0 ) from (ae_restrict_iff' hU.measurableSet).2 hae0) hU hcont continuousOn_const) _ (hmaps hp)
  rw [hι] at this
  linarith

end Potential

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
