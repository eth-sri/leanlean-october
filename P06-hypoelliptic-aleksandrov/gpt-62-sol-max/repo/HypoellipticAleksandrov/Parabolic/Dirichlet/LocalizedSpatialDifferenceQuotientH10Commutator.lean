module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeCutoffSlice
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTime
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientBound
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.Cutoff.Basic
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialRawAmplitudeMajorant
public import HypoellipticAleksandrov.Topology.Support

/-! # Extension of the fixed-slice commutator identity to `H¹₀` -/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem continuous_reverseTimeSpatialForm_apply_energyTest {d : ℕ} {Ω : Set (PDE.Vec d)}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    Continuous (fun u => reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) := by
  let O := reverseTimeSpatialFormOperator
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc ⟨τ, hτ⟩
  have hO : Continuous (fun u => O u (B u)) := O.continuous.clm_apply B.continuous
  convert hO using 1
  funext u
  exact (reverseTimeSpatialFormOperator_apply
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc ⟨τ, hτ⟩ u (B u)).symm

private theorem continuous_weighted_pairing
    {X : Type*} [TopologicalSpace X] {d : ℕ} {Ω : Set (PDE.Vec d)}
    {p q : PDE.Vec d → ℝ} (hp : Continuous p ∧ HasCompactSupport p)
    (hq : Continuous q ∧ HasCompactSupport q)
    {F G H : X → PDE.ScalarLp Ω 2} (hF : Continuous F) (hG : Continuous G) (hH : Continuous H)
    {f g h : X → PDE.Vec d → ℝ}
    (hf : ∀ x, f x =ᵐ[PDE.volumeOn Ω] F x) (hg : ∀ x, g x =ᵐ[PDE.volumeOn Ω] G x)
    (hh : ∀ x, h x =ᵐ[PDE.volumeOn Ω] H x) :
    Continuous (fun x => ∫ y in Ω, (p y * f x y + q y * g x y) * h x y) := by
  obtain ⟨P, hpP⟩ := hp.2.exists_bound_of_continuous hp.1
  obtain ⟨Q, hqQ⟩ := hq.2.exists_bound_of_continuous hq.1
  have hP := (norm_nonneg (p 0)).trans (hpP 0)
  have hQ := (norm_nonneg (q 0)).trans (hqQ 0)
  let Mp := scalarL2Multiplier p (hp.1.aestronglyMeasurable (μ := PDE.volumeOn Ω)) P hP
    (ae_of_all _ hpP)
  let Mq := scalarL2Multiplier q (hq.1.aestronglyMeasurable (μ := PDE.volumeOn Ω)) Q hQ
    (ae_of_all _ hqQ)
  refine (continuous_inner.comp (((Mp.continuous.comp hF).add (Mq.continuous.comp hG)).prodMk hH)).congr
    fun x => (Analysis.integral_mul_eq_inner_L2 ?_ (hh x)).symm
  have hp' := scalarL2Multiplier_apply_ae p hp.1.aestronglyMeasurable P hP (ae_of_all _ hpP) (F x)
  filter_upwards [Lp.coeFn_add (Mp (F x)) (Mq (G x)), hp', (scalarL2Multiplier_apply_ae q hq.1.aestronglyMeasurable Q hQ (ae_of_all _ hqQ) (G x)), hf x, hg x] with y hsum hp hq hf hg
  change Mp (F x) y = p y * F x y at hp
  change Mq (G x) y = q y * G x y at hq
  simp only [hsum, Pi.add_apply, hp, hq, hf, hg, Function.comp_apply]

/-- The fixed-slice identity extends from the dense smooth core using bounded slice
multipliers. No quantitative coefficient bound is needed for this equality. -/
theorem reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : ℝ → PDE.Vec d → PDE.Vec d) (c F : ℝ → PDE.Vec d → ℝ)
    (ha : IsSmoothOnClosedCylinder r₀ r₁ Ω a)
    (hb : IsSmoothOnClosedCylinder r₀ r₁ Ω b)
    (hc : IsSmoothOnClosedCylinder r₀ r₁ Ω c)
    (hF : IsSmoothOnClosedCylinder r₀ r₁ Ω F)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ) (hτ : τ ∈ Icc 0 (r₁ - r₀))
    (hχshift : χ.ShiftMapsInto k h Ω) (hηshift : η.ShiftMapsInto k h Ω) (u : H10HilbertGraph hΩ) :
    h10CommutatorFixedStepOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η χ k h τ hηshift u := by
  let X := H10HilbertGraph hΩ
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h η.tsupport_subset hηshift
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V := (valueCLM hΩ).comp A
  let J i := (PDE.hilbertVectorLpCoord Ω 2 i).comp (gradientCLM hΩ)
  let G i := (J i).comp A
  let W i := (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h).comp (valueCLM hΩ)
  let M := scalarL2Multiplier (Ω := Ω) η.toFun (cutoff_aestronglyMeasurable η) 1 zero_le_one (cutoff_norm_le_one η)
  let E i := G i - W i
  let H i := G i + W i
  let U i := M.comp (J i)
  let U₀ := M.comp (valueCLM hΩ)
  have hE (i : Fin d) (v : X) : (fun y => G i v y - W i v y) =ᵐ[PDE.volumeOn Ω] E i v :=
    (Lp.coeFn_sub (G i v) (W i v)).symm
  have hH (i : Fin d) (v : X) : (fun y => G i v y + W i v y) =ᵐ[PDE.volumeOn Ω] H i v :=
    (Lp.coeFn_add (G i v) (W i v)).symm
  have hM (v : PDE.ScalarLp Ω 2) := (scalarL2Multiplier_apply_ae η.toFun
    (cutoff_aestronglyMeasurable η) 1 zero_le_one (cutoff_norm_le_one η) v).symm
  let sourceD : PDE.Vec d → ℝ := fun y => ζ τ * η y *
    spatialDifferenceQuotient k h (fun z => F (r₁ - z.1) z.2) (τ, y)
  have hsource : Continuous sourceD ∧ HasCompactSupport sourceD :=
    (cutoffSlice_translate_quotient η k h (ζ τ) (r₀ := r₀) (r₁ := r₁)
      (IsSmoothOnNeighborhood.reverseTimeClosedCylinder hF) hτ hηshift).2
  have hsrc : Continuous (fun v : X => ∫ y in Ω, sourceD y * V v y) :=
    (continuous_inner.comp (continuous_const.prodMk V.continuous)).congr fun v =>
      (Analysis.integral_mul_eq_inner_L2
        (coeFn_compactlySupportedContinuousToScalarLp sourceD hsource.1 hsource.2).symm
        (Filter.EventuallyEq.rfl : _ =ᵐ[PDE.volumeOn Ω] V v)).symm
  have coeff {f : TimeVelocity d → ℝ}
      (hs : IsSmoothOnNeighborhood f (scalarParabolicClosedCylinder r₀ r₁ Ω)) :=
    cutoffSlice_translate_quotient χ k h (ζ τ) (IsSmoothOnNeighborhood.reverseTimeClosedCylinder hs) hτ hχshift
  have hA (i j : Fin d) := coeff (IsSmoothOnNeighborhood.coefficientEntry a ha i j)
  have hD (j : Fin d) := coeff (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)
  have hC := coeff hc
  have hprincipal (i j : Fin d) := continuous_weighted_pairing (hA i j).1 (hA i j).2
    (E j).continuous (U j).continuous (H i).continuous (hE j) (fun v => hM (J j v)) (hH i)
  have hdrift (j : Fin d) := continuous_weighted_pairing (hD j).1 (hD j).2
    (E j).continuous (U j).continuous V.continuous (hE j) (fun v => hM (J j v))
    (fun v => Filter.EventuallyEq.rfl)
  have hscalar := continuous_weighted_pairing hC.1 hC.2 V.continuous U₀.continuous V.continuous
    (fun v => Filter.EventuallyEq.rfl) (fun v => hM (valueCLM hΩ v)) (fun v => Filter.EventuallyEq.rfl)
  have hright : Continuous (h10CommutatorRawRhs r₀ r₁ hΩ a b c F ζ η χ k h τ hηshift) :=
    ((hsrc.neg.sub (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => hprincipal i j)).sub
      (continuous_finset_sum _ fun j _ => hdrift j)).add hscalar
  have hleft : Continuous (h10CommutatorLhs r₀ r₁ h₀₁ hΩ hΩbounded a b c F hF ζ η k h τ hηshift) :=
    continuous_const.mul (((reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hF τ).continuous.comp
      B.continuous).sub (continuous_reverseTimeSpatialForm_apply_energyTest
        r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc τ hτ B))
  exact congrFun ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
    hleft hright (funext (smoothCore_fixedStep_reverseTimeSource_sub_reverseTimeSpatialForm_eq_commutator
      r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc F hF ζ η χ k h τ hηshift hτ))) u

end HypoellipticAleksandrov.Parabolic.Dirichlet
