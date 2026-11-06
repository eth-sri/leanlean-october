module

public import
  HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothRepresentation
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyWeakTest
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialBounds
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientIntegration
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds

open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_reverseTimeDivergenceDriftEntry_slice_of_smoothOnNeighborhood from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds
open private HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_reverseTimeCoefficientEntry_slice_of_smoothOnNeighborhood from HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormBounds


/-!
# Smooth fixed-time localized commutator

This module proves the exact fixed-time smooth localized source-minus-form
spatial difference-quotient commutator identity. It does not state an estimate.
-/

 public section


open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem cont_mul_local
    {X : Type*} [TopologicalSpace X] {U : Set X} {p q : X → ℝ}
    (hU : IsOpen U) (hp : Continuous p) (hps : tsupport p ⊆ U)
    (hq : ContinuousOn q U) : Continuous (fun x => p x * q x) := by
  refine (hp.continuousOn.mul hq).continuous_of_tsupport_subset hU ?_
  exact (tsupport_mul_subset_left (f := p) (g := q)).trans hps

variable {d : ℕ}

private theorem local_transpose
     (Ω : PDE.VelocityRegion d)
    (hΩ : IsOpen Ω)
    (k : Fin d) (h : ℝ) (f g : PDE.ScalarField d)
    (hf : ContinuousOn f Ω) (hg : Continuous g)
    (hgcompact : HasCompactSupport g)
    (hgΩ : tsupport g ⊆ Ω)
    (hgshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport g) Ω) :
    (∫ y in Ω, f y *
      ((g (y + (-h) • PDE.basisVec k) - g y) / h)) =
      ∫ y in Ω,
        ((f (y + h • PDE.basisVec k) - f y) / h) * g y := by
  let z  := h • PDE.basisVec k
  let F  := fun y => f (y + z) * g y
  let G  := fun y => f y * g y
  have hFcont : Continuous F := by
    have hU : IsOpen ((fun y  => y + z) ⁻¹' Ω) :=
      (continuous_id.add continuous_const).isOpen_preimage Ω hΩ
    have hq : ContinuousOn (fun y  => f (y + z))
        ((fun y  => y + z) ⁻¹' Ω) := by
      exact hf.comp (continuous_id.add continuous_const).continuousOn (by
        intro y hy
        exact hy)
    simpa only [F, mul_comm] using
      cont_mul_local hU hg (hgshift) hq
  have hGcont : Continuous G := by
    simpa only [G, mul_comm] using cont_mul_local hΩ hg hgΩ hf
  have hFsupport : HasCompactSupport F := by
    change HasCompactSupport ((fun y => f (y + z)) * g)
    exact hgcompact.mul_left
  have hGsupport : HasCompactSupport G := by
    change HasCompactSupport (f * g)
    exact hgcompact.mul_left
  have hF : Integrable F  := hFcont.integrable_of_hasCompactSupport hFsupport
  have hG : Integrable G  := hGcont.integrable_of_hasCompactSupport hGsupport
  have hFshift : Integrable (fun y => F (y - z))  := by
    exact (hFcont.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hFsupport.comp_homeomorph (Homeomorph.subRight z))
  have hshift : (∫ y, F (y - z)) = ∫ y, F y := by
    let hμ  :=
      measurePreserving_add_right volume (-z)
    simpa [sub_eq_add_neg] using
      hμ.integral_comp (Homeomorph.addRight (-z)).measurableEmbedding F
  calc
    (∫ y in Ω, f y * ((g (y + (-h) • PDE.basisVec k) - g y) / h)) =
        ∫ y, (F (y - z) - G y) / h := by
      rw [show (fun y => f y * ((g (y + (-h) • PDE.basisVec k) - g y) / h)) =
          fun y => (F (y - z) - G y) / h by
        funext y
        dsimp [F, G, z]
        rw [neg_smul]
        simp only [sub_eq_add_neg]
        ring_nf]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnot : y - z ∉ tsupport g := by
        intro hsupport
        apply hy
        have := hgshift hsupport
        simpa [z, sub_eq_add_neg, add_assoc] using this
      have hnot' : y ∉ tsupport g := by
        intro hsupport
        exact hy (hgΩ hsupport)
      dsimp [F, G, z]
      rw [image_eq_zero_of_notMem_tsupport hnot]
      rw [image_eq_zero_of_notMem_tsupport hnot']
      ring

    _ = ((∫ y, F (y - z)) - ∫ y, G y) / h := by
      rw [integral_div, integral_sub hFshift hG]
    _ = ((∫ y, F y) - ∫ y, G y) / h := by rw [hshift]
    _ = ∫ y, (F y - G y) / h := by
      rw [← integral_sub hF hG, ← integral_div]
    _ = ∫ y in Ω, ((f (y + h • PDE.basisVec k) - f y) / h) * g y := by
      rw [show (fun y => ((f (y + h • PDE.basisVec k) - f y) / h) * g y) =
          fun y => (F y - G y) / h by
        funext y
        dsimp [F, G, z]
        ring]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hnot : y ∉ tsupport g := by
        intro hsupport
        exact hy (hgΩ hsupport)
      dsimp [F, G]
      rw [image_eq_zero_of_notMem_tsupport hnot]
      ring

variable {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω) (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

private theorem energy_value_eq_backward

    (y : PDE.Vec d) :
    localizedSpatialDifferenceQuotientEnergyWeakTest
      η k h φ φ.contDiff hηΩ hηshift y =
      ((fun x => η x ^ 2 * ((φ (x + h • PDE.basisVec k) - φ x) / h))
        (y + (-h) • PDE.basisVec k) -
        (fun x => η x ^ 2 * ((φ (x + h • PDE.basisVec k) - φ x) / h)) y) / h := by
  change localizedSpatialDifferenceQuotientEnergyTest η k h φ y = _
  rw [localizedSpatialDifferenceQuotientEnergyTest_apply]
  simp only [localizedSpatialDifferenceQuotient_apply]
  rw [neg_smul]
  rw [sub_eq_add_neg]
  have hcancel : y + -(h • PDE.basisVec k) + h • PDE.basisVec k = y := by
    module
  rw [hcancel]
  ring_nf

private theorem energy_deriv_eq_backward

    (i : Fin d) (y : PDE.Vec d) :
    (localizedSpatialDifferenceQuotientEnergyWeakTest
      η k h φ φ.contDiff hηΩ hηshift).partialDeriv i y =
      ((fun x =>
        2 * η x * PDE.classicalGradient η.toFun x i *
            ((φ (x + h • PDE.basisVec k) - φ x) / h) +
          η x ^ 2 *
            ((φ.partialDeriv i (x + h • PDE.basisVec k) - φ.partialDeriv i x) / h))
        (y + (-h) • PDE.basisVec k) -
        (fun x =>
          2 * η x * PDE.classicalGradient η.toFun x i *
              ((φ (x + h • PDE.basisVec k) - φ x) / h) +
            η x ^ 2 *
              ((φ.partialDeriv i (x + h • PDE.basisVec k) - φ.partialDeriv i x) / h)) y) / h := by
  rw [localizedSpatialDifferenceQuotientEnergyWeakTest_partialDeriv
    η k h φ hηΩ hηshift i y]







/-- The fixed-time smooth localized energy test satisfies the literal
source-minus-form spatial difference-quotient commutator identity. -/
theorem reverseTimeSource_sub_reverseTimeSpatialForm_smooth_energyTest_eq_commutator
     {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d)
    (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    let e : PDE.Vec d := h • PDE.basisVec k
    let T : (PDE.ScalarField d) → PDE.ScalarField d :=
      fun q y => q (y + e)
    let D : (PDE.ScalarField d) → PDE.ScalarField d :=
      fun q y => (q (y + e) - q y) / h
    let u : H10HilbertGraph hΩ :=
      smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ
    let B : H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h hηΩ hηshift u
    let source : PDE.ScalarField d := (F (r₁ - τ))
    let sourceSlice : PDE.ScalarLp Ω (2 ) :=
      reverseTimeSourceSlice r₁ τ F
        (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
          r₀ r₁ hΩ hΩbounded F hFSmooth τ hτ)
    let α : Fin d → Fin d → PDE.ScalarField d :=
      fun i j y => a (r₁ - τ) y i j
    let drift : Fin d → PDE.ScalarField d :=
      fun j y => reverseTimeDivergenceDrift r₁ a b τ y j
    let γ : PDE.ScalarField d :=
      (reverseTimeScalarCoefficient r₁ c τ)
    let Q : PDE.ScalarField d :=
      fun y => η y ^ 2 * D φ y
    let R : Fin d → PDE.ScalarField d :=
      fun i y =>
        2 * η y * PDE.classicalGradient η.toFun y i * D φ y +
          η y ^ 2 * D ((φ.partialDeriv i)) y
    reverseTimeSourceFunctional hΩ sourceSlice B -
        reverseTimeSpatialForm hΩ r₁ τ a b c u B =
      -(∫ y in Ω, D source y * Q y) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          (T (α i j) y * D ((φ.partialDeriv j)) y +
            D (α i j) y * φ.partialDeriv j y) *
              R i y) -
        (∑ j : Fin d, ∫ y in Ω,
          (T (drift j) y * D ((φ.partialDeriv j)) y +
            D (drift j) y * φ.partialDeriv j y) *
              Q y) +
        ∫ y in Ω,
          (T γ y * D φ y + D γ y * φ y) * Q y := by
  dsimp only
  rw [reverseTimeSourceFunctional_apply_smooth_localizedSpatialDifferenceQuotientEnergyTest_eq
    hΩ r₁ τ F
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood
      r₀ r₁ hΩ hΩbounded F hFSmooth τ hτ)
    η k h φ hηΩ hηshift,
    reverseTimeSpatialForm_apply_smooth_localizedSpatialDifferenceQuotientEnergyTest_eq
      hΩ r₁ τ a b c η k h φ hηΩ hηshift]
  let Q  := fun y =>
    η y ^ 2 * ((φ (y + h • PDE.basisVec k) - φ y) / h)
  let R  := fun i y =>
    2 * η y * PDE.classicalGradient η.toFun y i *
        ((φ (y + h • PDE.basisVec k) - φ y) / h) +
      η y ^ 2 *
        ((φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h)
  have hBvalue (y : PDE.Vec d) :
      localizedSpatialDifferenceQuotientEnergyWeakTest
        η k h φ φ.contDiff hηΩ hηshift y =
        (Q (y + (-h) • PDE.basisVec k) - Q y) / h := energy_value_eq_backward η k h φ hηΩ hηshift y
  have hBderiv (i : Fin d) (y : PDE.Vec d) :
      (localizedSpatialDifferenceQuotientEnergyWeakTest
        η k h φ φ.contDiff hηΩ hηshift).partialDeriv i y =
        (R i (y + (-h) • PDE.basisVec k) - R i y) / h := energy_deriv_eq_backward η k h φ hηΩ hηshift i y
  simp_rw [hBvalue, hBderiv]
  have hDφcont : Continuous (fun y  =>
      (φ (y + h • PDE.basisVec k) - φ y) / h) :=
    ((φ.contDiff.continuous.comp (continuous_id.add continuous_const)).sub
      φ.contDiff.continuous).div_const h
  have hQcont : Continuous Q := by
    dsimp only [Q]
    exact (η.smooth.continuous.pow 2).mul hDφcont
  have hQcompact : HasCompactSupport Q := by
    have hrewrite : Q = η.toFun *
        (η.toFun * fun y => (φ (y + h • PDE.basisVec k) - φ y) / h) := by
      funext y
      dsimp only [Q, Pi.mul_apply]
      ring
    rw [hrewrite]
    exact η.hasCompactSupport.mul_right
  have hQsupport : tsupport Q ⊆ tsupport η.toFun := by
    dsimp only [Q]
    refine (tsupport_mul_subset_left (f := fun y => η y ^ 2)
      (g := fun y => (φ (y + h • PDE.basisVec k) - φ y) / h)).trans ?_
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := η.toFun) (g := η.toFun))
  have hQshift  :=
    hηshift.mono_left hQsupport
  have hgradηcont (i : Fin d) : Continuous
      (fun y  => PDE.classicalGradient η.toFun y i) := by
    rw [show (fun y  => PDE.classicalGradient η.toFun y i) =
        fun y => (fderiv ℝ η.toFun y) (PDE.basisVec i) by
      funext y
      exact PDE.classicalGradient_apply η.toFun y i]
    exact (η.smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hpartialcont (i : Fin d) : Continuous
      ((φ.partialDeriv i)) := by
    unfold PDE.WeakTestFunction.partialDeriv
    exact (φ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hRcont (i : Fin d) : Continuous (R i) := by
    dsimp only [R]
    exact ((continuous_const.mul η.smooth.continuous).mul (hgradηcont i)).mul hDφcont |>.add
      ((η.smooth.continuous.pow 2).mul
        (((hpartialcont i).comp (continuous_id.add continuous_const)).sub
          (hpartialcont i) |>.div_const h))
  have hRcompact (i : Fin d) : HasCompactSupport (R i) := by
    dsimp only [R]
    apply HasCompactSupport.add
    · rw [show (fun y : PDE.Vec d =>
          2 * η y * PDE.classicalGradient η.toFun y i *
            ((φ (y + h • PDE.basisVec k) - φ y) / h)) = η.toFun *
          (fun y => 2 * PDE.classicalGradient η.toFun y i *
            ((φ (y + h • PDE.basisVec k) - φ y) / h)) by
          funext y
          simp only [Pi.mul_apply]
          ring]
      exact η.hasCompactSupport.mul_right
    · rw [show (fun y : PDE.Vec d => η y ^ 2 *
          ((φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h)) =
          η.toFun * (η.toFun * fun y =>
            (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h) by
          funext y
          simp only [Pi.mul_apply]
          ring]
      exact η.hasCompactSupport.mul_right
  have hRsupport (i : Fin d) : tsupport (R i) ⊆ tsupport η.toFun := by
    dsimp only [R]
    refine (tsupport_add _ _).trans ?_
    intro y hy
    rcases hy with hy | hy
    · have hrewrite : (fun y : PDE.Vec d =>
          2 * η y * PDE.classicalGradient η.toFun y i *
            ((φ (y + h • PDE.basisVec k) - φ y) / h)) =
      η.toFun * (fun y => 2 * PDE.classicalGradient η.toFun y i *
            ((φ (y + h • PDE.basisVec k) - φ y) / h)) := by
        funext x
        simp only [Pi.mul_apply]
        rw [add_comm x]
        ring
      rw [hrewrite] at hy
      exact (tsupport_mul_subset_left
         hy)
    · have hrewrite : (fun y : PDE.Vec d =>
          η y ^ 2 * ((φ.partialDeriv i (y + h • PDE.basisVec k) -
            φ.partialDeriv i y) / h)) = η.toFun * (η.toFun * fun y =>
          (φ.partialDeriv i (y + h • PDE.basisVec k) - φ.partialDeriv i y) / h) := by
        funext x
        simp only [Pi.mul_apply]
        rw [add_comm x]
        ring
      rw [hrewrite] at hy
      exact (tsupport_mul_subset_left
         hy)

  have hαcont (i j : Fin d)  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_reverseTimeCoefficientEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a i j haSmooth hτ
  have hdriftcont (j : Fin d)  :=
    _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.continuousOn_reverseTimeDivergenceDriftEntry_slice_of_smoothOnNeighborhood r₀ r₁ τ a b j haSmooth hbSmooth hτ
  have hγcont  :=
    continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
      r₀ r₁ τ c hcSmooth hτ
  have hsourceTranspose := local_transpose Ω hΩ k h
    ((F (r₁ - τ))) Q ((continuousOn_reverseTimeScalarCoefficient_slice_of_smoothOnNeighborhood
            r₀ r₁ τ F hFSmooth hτ)) hQcont hQcompact
      (hQsupport.trans hηΩ) hQshift
  have hprincipalTranspose (i j : Fin d) := local_transpose Ω hΩ k h
    (fun y  => a (r₁ - τ) y i j * φ.partialDeriv j y) (R i)
    ((hαcont i j).mul (hpartialcont j).continuousOn) (hRcont i) (hRcompact i)
    ((hRsupport i).trans hηΩ) (hηshift.mono_left (hRsupport i))
  have hdriftTranspose (j : Fin d) := local_transpose Ω hΩ k h
    (fun y  => reverseTimeDivergenceDrift r₁ a b τ y j * φ.partialDeriv j y) Q
    ((hdriftcont j).mul (hpartialcont j).continuousOn) hQcont hQcompact
    (hQsupport.trans hηΩ) hQshift
  have hscalarTranspose := local_transpose Ω hΩ k h
    (fun y  => reverseTimeScalarCoefficient r₁ c τ y * φ y) Q
    (hγcont.mul φ.contDiff.continuous.continuousOn) hQcont hQcompact
    (hQsupport.trans hηΩ) hQshift
  rw [hsourceTranspose]
  simp_rw [hprincipalTranspose, hdriftTranspose, hscalarTranspose]
  have hproduct (f g : PDE.ScalarField d) (y : PDE.Vec d) :
      (f (y + h • PDE.basisVec k) * g (y + h • PDE.basisVec k) - f y * g y) / h =
        f (y + h • PDE.basisVec k) *
            ((g (y + h • PDE.basisVec k) - g y) / h) +
          ((f (y + h • PDE.basisVec k) - f y) / h) * g y := by
    ring
  simp_rw [hproduct]
  have hprincipalProduct (i j : Fin d) (y : PDE.Vec d) :
      (a (r₁ - τ) (y + h • PDE.basisVec k) i j *
          φ.partialDeriv j (y + h • PDE.basisVec k) -
        a (r₁ - τ) y i j * φ.partialDeriv j y) / h =
      a (r₁ - τ) (y + h • PDE.basisVec k) i j *
          ((φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y) / h) +
        (a (r₁ - τ) (y + h • PDE.basisVec k) i j - a (r₁ - τ) y i j) / h *
          φ.partialDeriv j y := by
    ring
  have hdriftProduct (j : Fin d) (y : PDE.Vec d) :
      (reverseTimeDivergenceDrift r₁ a b τ (y + h • PDE.basisVec k) j *
          φ.partialDeriv j (y + h • PDE.basisVec k) -
        reverseTimeDivergenceDrift r₁ a b τ y j * φ.partialDeriv j y) / h =
      reverseTimeDivergenceDrift r₁ a b τ (y + h • PDE.basisVec k) j *
          ((φ.partialDeriv j (y + h • PDE.basisVec k) - φ.partialDeriv j y) / h) +
        (reverseTimeDivergenceDrift r₁ a b τ (y + h • PDE.basisVec k) j -
          reverseTimeDivergenceDrift r₁ a b τ y j) / h * φ.partialDeriv j y := by
    ring
  simp_rw [hprincipalProduct, hdriftProduct]
  abel

end HypoellipticAleksandrov.Parabolic.Dirichlet
