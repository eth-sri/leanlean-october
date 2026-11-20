module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.VariationalEnergy
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentativeAlgebra
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourcePositivePartOrder
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormPositivePart
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase

/-! # Weak comparison for reverse-time variational energy solutions -/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise MatrixOrder
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet

local instance comparisonModule {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) :
    Module ℝ (ReverseTimeL2VStar hΩ T) := MeasureTheory.Lp.instModule

private theorem comparison_scalar_energy
    (g₁ g₂ B₁ B₂ Bw Bp S₁ S₂ G V lam K : ℝ)
    (h₁ : g₁ + B₁ = S₁) (h₂ : g₂ + B₂ = S₂)
    (hBsub : B₁ - B₂ = Bw) (hBpos : Bw = Bp) (hS : S₁ - S₂ ≤ 0)
    (hG : (lam / 2) * G - K * V ≤ Bp) :
    2 * (g₁ - g₂) + lam * G ≤ 2 * K * V := by
  linarith

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)

private theorem comparison_initialTrace_sub
    (u₁ u₂ : ReverseTimeL2V hΩ T) (g₁ g₂ : ReverseTimeL2VStar hΩ T)
    (hd₁ : HasGelfandWeakTimeDerivative hΩ T hT u₁ g₁)
    (hd₂ : HasGelfandWeakTimeDerivative hΩ T hT u₂ g₂)
    (hd : HasGelfandWeakTimeDerivative hΩ T hT (u₁-u₂) (g₁-g₂)) :
    reverseTimeInitialTrace hΩ T hT (u₁-u₂) (g₁-g₂) hd =
      reverseTimeInitialTrace hΩ T hT u₁ g₁ hd₁ -
        reverseTimeInitialTrace hΩ T hT u₂ g₂ hd₂ := by
  have hr := reverseTimeHilbertRepresentative_sub_eq hΩ T hT
    u₁ g₁ hd₁ u₂ g₂ hd₂ hd
  have he := congrArg (fun Q : C(Icc 0 T, PDE.ScalarLp Ω (2 : ℝ≥0∞)) =>
    Q ⟨0,⟨le_rfl,hT.le⟩⟩) hr
  convert he using 1 <;> rfl

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (w : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hd : HasGelfandWeakTimeDerivative hΩ T hT w g)

private theorem comparison_posPart_zero (K : ℝ) (hK : 0 ≤ K)
    (hrate : ∀ᵐ τ ∂reverseTimeVolume T,
      2 * (g τ) (h10PositivePart hΩ (w τ)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2 * 0 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (w τ))‖ ^ 2)
    (hW0 : Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd
      ⟨0,⟨le_rfl,hT.le⟩⟩) = 0) :
    ∀ t : ℝ, ∀ ht : t ∈ Icc 0 T,
      Lp.posPart (reverseTimeHilbertRepresentative hΩ T hT w g hd ⟨t,ht⟩) = 0 := by
  let W := reverseTimeHilbertRepresentative hΩ T hT w g hd
  let F := Lp.posPart ∘ IccExtend hT.le W
  have hW := (reverseTimeHilbertRepresentative_spec hΩ T hT w g hd).1
  have hEle : ∀ t ∈ Icc 0 T, ‖F t‖ ^ 2 ≤ 2 * K * ∫ r in Ioc 0 t, ‖F r‖ ^ 2 := by
    intro t ht
    have hi := (reverseTimeHilbertRepresentative_posPart_norm_sq_increment hΩ T hT w g hd 0 t ⟨le_rfl, hT.le⟩ ht ht.1)
    have hpair : Integrable (fun r => (g r) (h10PositivePart hΩ (w r)))
        (reverseTimeVolume T) :=
      (integrable_reverseTimeDualPairing hΩ T (reverseTimePositivePart hΩ T w) g).congr (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
        rw [hr])
    have hm := (Lp.memLp (reverseTimePositivePart hΩ T w)).continuousLinearMap_comp
      (valueCLM hΩ)
    have hv : Integrable (fun r => ‖valueCLM hΩ (h10PositivePart hΩ (w r))‖^2)
        (reverseTimeVolume T) :=
      ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm).congr (by
        filter_upwards [coeFn_reverseTimePositivePart hΩ T w] with r hr
        rw [hr])
    have hint : (∫ r in Ioc 0 t, 2 * (g r) (h10PositivePart hΩ (w r))
        ∂reverseTimeVolume T) ≤
        ∫ r in Ioc 0 t, 2*K*‖valueCLM hΩ (h10PositivePart hΩ (w r))‖^2
          ∂reverseTimeVolume T :=
      setIntegral_mono_ae_restrict (hpair.const_mul 2).integrableOn
      (hv.const_mul (2*K)).integrableOn (ae_restrict_of_ae (by
        filter_upwards [hrate] with r hr
        simpa only [mul_zero, add_zero] using hr))
    rw [integral_const_mul, integral_const_mul] at hint
    have hval := reverseTime_integral_representative hT.le ht hW (fun _ x => ‖Lp.posPart x‖ ^ 2)
    rw [hW0, norm_zero, zero_pow (by decide), sub_zero] at hi
    simp only [F, Function.comp_apply, IccExtend_of_mem hT.le W ht]
    rw [← hval]
    simp only [← valueCLM_h10PositivePart]
    exact hi.le.trans hint
  have hz := eq_zero_on_Icc_of_norm_sq_le_mul_integral hT
    (mul_nonneg (by norm_num) hK) F (Lp.continuous_posPart.comp W.continuous.Icc_extend') hEle
  intro t ht
  simpa only [F, Function.comp_apply, IccExtend_of_mem hT.le W ht] using hz t ht

end

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (r₀ r₁ lam : ℝ) (h₀₁ : r₀ < r₁) (hlam : 0 < lam)
  (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) (a : CoefficientField d)
  (b : ℝ → PDE.Vec d → PDE.Vec d) (c F₁ F₂ : ℝ → PDE.Vec d → ℝ)
  (haSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω a) (hbSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
  (hcSmooth : IsSmoothOnClosedCylinder r₀ r₁ Ω c) (hF₁Smooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F₁)
  (hF₂Smooth : IsSmoothOnClosedCylinder r₀ r₁ Ω F₂)
  (hLower : HasLowerEllipticityOn lam a (scalarParabolicClosedCylinder r₀ r₁ Ω))
  (hcNonpos : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → c z.1 z.2 ≤ 0)
  (hF₂leF₁ : ∀ z : TimeVelocity d, z ∈ scalarParabolicClosedCylinder r₀ r₁ Ω → F₂ z.1 z.2 ≤ F₁ z.1 z.2)
  (initial₁ initial₂ : PDE.ScalarLp Ω (2 : ℝ≥0∞))
include lam hlam haSmooth hbSmooth hcSmooth hLower hcNonpos hF₂leF₁

private theorem comparison_ae_rate
    (u₁ : ReverseTimeL2V hΩ (r₁-r₀)) (g₁ : ReverseTimeL2VStar hΩ (r₁-r₀))
    (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₁ g₁)
    (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁)
    (u₂ : ReverseTimeL2V hΩ (r₁-r₀)) (g₂ : ReverseTimeL2VStar hΩ (r₁-r₀))
    (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) (sub_pos.mpr h₀₁) u₂ g₂)
    (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * ((g₁-g₂) τ) (h10PositivePart hΩ ((u₁-u₂) τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ ((u₁-u₂) τ))‖^2 := by
  obtain ⟨K,hK,hGard⟩ := reverseTimeSpatialForm_garding_of_smoothOnNeighborhood
    r₀ r₁ lam h₀₁ hlam hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth hLower hcNonpos
  refine ⟨K,hK,?_⟩
  rcases hu₁ with ⟨_,heq₁⟩
  rcases hu₂ with ⟨_,heq₂⟩
  filter_upwards [heq₁,heq₂,Lp.coeFn_sub u₁ u₂,Lp.coeFn_sub g₁ g₂,
    ae_restrict_mem measurableSet_Ioo] with τ heq₁τ heq₂τ huτ hgτ hτ
  have hτcc : τ ∈ Icc 0 (r₁-r₀) := ⟨hτ.1.le,hτ.2.le⟩
  let w := u₁ τ-u₂ τ
  let wp := h10PositivePart hΩ w
  let f₁ := reverseTimeSourceSlice r₁ τ F₁
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₁ hF₁Smooth τ hτcc)
  let f₂ := reverseTimeSourceSlice r₁ τ F₂
    (reverseTimeSourceSlice_memLp_of_smoothOnNeighborhood r₀ r₁ hΩ hΩbounded F₂ hF₂Smooth τ hτcc)
  have hs : ∀ᵐ y ∂PDE.volumeOn Ω, f₂ y ≤ f₁ y := by
    filter_upwards [coeFn_reverseTimeSourceSlice r₁ τ F₁ _,
      coeFn_reverseTimeSourceSlice r₁ τ F₂ _,ae_restrict_mem hΩ.measurableSet]
      with y h1 h2 hy
    rw [h1,h2]
    exact hF₂leF₁ (r₁-τ,y) ⟨⟨by linarith [h₀₁,hτ.2],by linarith [hτ.1]⟩,
      subset_closure hy⟩
  have hS := reverseTimeSourceFunctional_sub_nonpos_of_ae_le hΩ f₁ f₂ hs w
  have e₁ : (g₁ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp =
      reverseTimeSourceFunctional hΩ f₁ wp := heq₁τ hτ wp
  have e₂ : (g₂ τ) wp + reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
      reverseTimeSourceFunctional hΩ f₂ wp := heq₂τ hτ wp
  let B := reverseTimeSpatialFormOperator r₀ r₁ h₀₁ hΩ hΩbounded a b c
    haSmooth hbSmooth hcSmooth ⟨τ,hτcc⟩
  have hB : reverseTimeSpatialForm hΩ r₁ τ a b c (u₁ τ) wp -
      reverseTimeSpatialForm hΩ r₁ τ a b c (u₂ τ) wp =
      reverseTimeSpatialForm hΩ r₁ τ a b c w wp := by
    have hm := congrArg (fun q : H10HilbertGraphDual hΩ => q wp)
      (B.map_sub (u₁ τ) (u₂ τ))
    simpa only [B,reverseTimeSpatialFormOperator_apply,ContinuousLinearMap.sub_apply,w]
      using hm.symm
  have hBp := reverseTimeSpatialForm_apply_positivePart_eq hΩ r₁ τ a b c w
  have hG := hGard τ hτcc wp
  rw [huτ,hgτ]
  change 2*((g₁ τ) wp-(g₂ τ) wp)+lam*‖gradientCLM hΩ wp‖^2 ≤
    2*K*‖valueCLM hΩ wp‖^2
  exact comparison_scalar_energy _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ hB hBp hS hG

/-- Reverse-time variational comparison: ordered initial data and the original-source
orientation `F₂ ≤ F₁` imply spatial almost-everywhere order at every closed time. -/
theorem reverseTimeVariationalEnergySolution_le
    (hinitial : ∀ᵐ y ∂PDE.volumeOn Ω, initial₁ y ≤ initial₂ y)
    (u₁ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₁ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₁ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₁ g₁)
    (hu₁ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₁ hF₁Smooth initial₁ u₁ g₁ hdu₁)
    (u₂ : ReverseTimeL2V hΩ (r₁ - r₀))
    (g₂ : ReverseTimeL2VStar hΩ (r₁ - r₀))
    (hdu₂ : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁) u₂ g₂)
    (hu₂ : IsReverseTimeVariationalEnergySolution r₀ r₁ h₀₁ hΩ hΩbounded
      a b c F₂ hF₂Smooth initial₂ u₂ g₂ hdu₂) :
    ∀ τ : ℝ, ∀ hτ : τ ∈ Set.Icc 0 (r₁ - r₀),
      ∀ᵐ y ∂PDE.volumeOn Ω,
        reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₁ g₁ hdu₁ ⟨τ, hτ⟩ y ≤
          reverseTimeHilbertRepresentative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
            u₂ g₂ hdu₂ ⟨τ, hτ⟩ y := by
  let hT : 0 < r₁ - r₀ := sub_pos.mpr h₀₁
  let hd : HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) hT
      (u₁ - u₂) (g₁ - g₂) := by
    change HasGelfandWeakTimeDerivative hΩ (r₁ - r₀) (sub_pos.mpr h₀₁)
      (u₁ - u₂) (g₁ - g₂)
    simpa [sub_eq_add_neg] using hdu₁.add (hdu₂.smul (-1 : ℝ))
  obtain ⟨K,hK,hrate⟩ := comparison_ae_rate r₀ r₁ lam h₀₁ hlam hΩ hΩbounded
    a b c F₁ F₂ haSmooth hbSmooth hcSmooth hF₁Smooth hF₂Smooth hLower hcNonpos
    hF₂leF₁ initial₁ initial₂ u₁ g₁ hdu₁ hu₁ u₂ g₂ hdu₂ hu₂
  let wd : ReverseTimeL2V hΩ (r₁-r₀) := u₁-u₂
  let gd : ReverseTimeL2VStar hΩ (r₁-r₀) := g₁-g₂
  let hdd : HasGelfandWeakTimeDerivative hΩ (r₁-r₀) hT wd gd := hd
  have hrate' : ∀ᵐ τ ∂reverseTimeVolume (r₁-r₀),
      2 * (gd τ) (h10PositivePart hΩ (wd τ)) +
        lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 ≤
      2 * K * ‖valueCLM hΩ (h10PositivePart hΩ (wd τ))‖ ^ 2 := by
    simpa only [wd, gd] using hrate
  let W := reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT wd gd hdd
  have hrep := reverseTimeHilbertRepresentative_sub_eq hΩ (r₁-r₀) hT
    u₁ g₁ hdu₁ u₂ g₂ hdu₂ hd
  have hW0 : Lp.posPart (W ⟨0,⟨le_rfl,hT.le⟩⟩) = 0 := by
    have ht1 := hu₁.1
    have ht2 := hu₂.1
    change Lp.posPart (reverseTimeInitialTrace hΩ (r₁-r₀) hT (u₁-u₂) (g₁-g₂) hd) = 0
    have htrace := comparison_initialTrace_sub hΩ (r₁-r₀) hT
      u₁ u₂ g₁ g₂ hdu₁ hdu₂ hd
    rw [htrace, ht1, ht2]
    apply Lp.ext
    filter_upwards [Lp.coeFn_posPart (initial₁-initial₂), Lp.coeFn_sub initial₁ initial₂,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω), hinitial]
      with y hp hs hz hi
    rw [hp, hs, hz]
    simp only [Pi.sub_apply]
    exact max_eq_right (sub_nonpos.mpr hi)
  intro τ hτ
  have hrate0 : ∀ᵐ r ∂reverseTimeVolume (r₁-r₀),
      2 * (gd r) (h10PositivePart hΩ (wd r)) +
        ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 * 0 ≤
      2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 := by
    filter_upwards [hrate'] with r hr
    have hg : 0 ≤ lam * ‖gradientCLM hΩ (h10PositivePart hΩ (wd r))‖^2 :=
      mul_nonneg hlam.le (sq_nonneg _)
    simpa only [mul_zero, add_zero] using (show
      2 * (gd r) (h10PositivePart hΩ (wd r)) ≤
        2*K*‖valueCLM hΩ (h10PositivePart hΩ (wd r))‖^2 by linarith)
  have hp := comparison_posPart_zero hΩ (r₁-r₀) hT wd gd hdd K hK hrate0 hW0 τ hτ
  have hw : ∀ᵐ y ∂PDE.volumeOn Ω, W ⟨τ,hτ⟩ y ≤ 0 := by
    filter_upwards [Lp.ext_iff.mp hp, Lp.coeFn_posPart (W ⟨τ,hτ⟩),
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (PDE.volumeOn Ω)] with y hy hpy hz
    rw [hpy, hz] at hy
    exact max_eq_right_iff.mp hy
  have hrepW : W = reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ -
      reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ := by
    dsimp only [W, wd, gd, hdd]
    exact hrep
  rw [hrepW] at hw
  filter_upwards [hw, Lp.coeFn_sub
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩)
    (reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩)] with y hy hsy
  change ((reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₁ g₁ hdu₁ ⟨τ,hτ⟩ -
    reverseTimeHilbertRepresentative hΩ (r₁-r₀) hT u₂ g₂ hdu₂ ⟨τ,hτ⟩) y) ≤ 0 at hy
  rw [hsy] at hy
  exact sub_nonpos.mp hy

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
