module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import MathCollab.Density.Stronger.Atkinson.FiniteWeightVariation
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCutoffVariation
public import MathCollab.Density.Stronger.Atkinson.ZetaBandSecondDerivatives
public import MathCollab.Density.Stronger.Atkinson.AtkinsonFirstDerivative
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
public import MathCollab.Density.Stronger.Atkinson.ContinuousKernelPrimitive
public import MathCollab.Density.Stronger.Atkinson.IntervalSecondDerivativeBounds
public import MathCollab.Density.Stronger.Atkinson.SecondDerivativeComposition
public import MathCollab.Density.Stronger.PointMean.HorizontalEdges
public import MathCollab.Density.Stronger.Fourth.SquareTail
public import LaterPairs.Native.RobertSargosGcdProjection
public import LaterPairs.Native.RobertSargosGcdSums
public import LaterPairs.Native.RobertSargosWeightedGcdFibers

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                    

noncomputable section
namespace TaoTrudgianYang2025

theorem RobertSargosReducedSystem.frequency_gcd_le {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) (hQ : 0 < Q) :
    (robertSargosFrequencyGcd p:ℝ) ≤ 2*Q := by
  have hqn : p.q₁ ≠ 0 := by
    have hr : (p.q₁:ℝ) ≠ 0 := abs_pos.mp (lt_of_lt_of_le hQ h.q₁_support.1)
    exact_mod_cast hr
  have hd : (robertSargosFrequencyGcd p:ℤ) ∣ p.q₁ :=
    (integerTripleGcd_dvd p.d p.q₁ p.q₂).2.1
  have hc : robertSargosFrequencyGcd p ≤ p.q₁.natAbs := by
    apply Nat.le_of_dvd (Int.natAbs_pos.mpr hqn)
    simpa using Int.natAbs_dvd_natAbs.mpr hd
  have hcR : (robertSargosFrequencyGcd p:ℝ) ≤ p.q₁.natAbs := by exact_mod_cast hc
  have he : (p.q₁.natAbs:ℝ) = |(p.q₁:ℝ)| := by
    simpa using
      congrArg (fun z : ℤ => (z:ℝ)) (Int.natCast_natAbs p.q₁)
  exact hcR.trans (he.trans_le h.q₁_support.2)



theorem RobertSargosReducedSystem.gcd_key_mem {R H Q δ : ℝ}
    {p : RobertSargosPoint} (h : RobertSargosReducedSystem R H Q δ p) (hQ : 0 < Q) :
    robertSargosGcdKey p ∈ (Finset.Icc 1 ⌊R⌋₊) ×ˢ (Finset.Icc 1 ⌊2*Q⌋₊) := by
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨h.coefficient_gcd_pos,
      (Nat.le_floor_iff ((abs_nonneg (p.r:ℝ)).trans h.r_bound)).mpr h.coefficient_gcd_le⟩
  · exact Finset.mem_Icc.mpr ⟨h.frequency_gcd_pos,
      (Nat.le_floor_iff (by positivity : 0 ≤ 2*Q)).mpr (h.frequency_gcd_le hQ)⟩



theorem exists_robertSargos_reduced_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset RobertSargosPoint) (R H Q δ : ℝ),
      1 ≤ R → 1 ≤ H → 1 ≤ Q → 0 ≤ δ → R ≤ H/2 →
      (∀ p ∈ S, RobertSargosReducedSystem R H Q δ p) →
      (S.card:ℝ) ≤ C*(R*H*Q)^(1+ε)*(1+δ*Q) := by
  classical
  have hη : 0 < ε/2 := by linarith
  obtain ⟨Cf,hCf,hfiber⟩ := exists_robertSargos_weighted_gcd_fiber_count (ε/2) hη
  obtain ⟨Ch,hCh,hharmonic⟩ := exists_robertSargos_gcd_harmonic_bound (ε/2) hη
  refine ⟨Cf*Ch,by positivity,?_⟩
  intro S R H Q δ hR hH hQ hδ hRH hmem
  have hQp : 0 < Q := by linarith
  have hB : 0 < R*H*Q := by positivity
  let F := (Finset.Icc 1 ⌊R⌋₊) ×ˢ (Finset.Icc 1 ⌊2*Q⌋₊)
  let M := Cf*(R*H*Q)^(1+ε/2)*(1+δ*Q)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hmaps : Set.MapsTo robertSargosGcdKey S F := by
    intro p hp
    exact (hmem p hp).gcd_key_mem hQp
  have hcardR : (S.card:ℝ) =
      ∑ z ∈ F, ((S.filter (fun p => robertSargosGcdKey p = z)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hf : ∀ z ∈ F, ((S.filter (fun p => robertSargosGcdKey p = z)).card:ℝ) ≤
      M*(1/((z.1:ℝ)*(z.2:ℝ))) := by
    intro z hz
    have h₁ := Finset.mem_Icc.mp (Finset.mem_product.mp hz).1
    have h₂ := Finset.mem_Icc.mp (Finset.mem_product.mp hz).2
    have hb := hfiber (S.filter (fun p => robertSargosGcdKey p = z))
      R H Q δ z.1 z.2 hR hH hQ hδ hRH h₁.1 h₂.1 ((Nat.le_floor_iff (by positivity : 0 ≤ 2*Q)).mp h₂.2)
      (fun p hp => hmem p (Finset.mem_filter.mp hp).1)
      (fun p hp => (congrArg (fun z : ℕ × ℕ => z.1) (Finset.mem_filter.mp hp).2).symm)
      (fun p hp => (congrArg (fun z : ℕ × ℕ => z.2) (Finset.mem_filter.mp hp).2).symm)
    simpa only [M,div_eq_mul_inv,one_mul] using hb
  have hw : (∑ z ∈ F, 1/((z.1:ℝ)*(z.2:ℝ))) =
      (harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ) := by
    rw [Finset.sum_product]
    exact sum_inverse_gcd_product _ _
  have hpow : (R*H*Q)^(1+ε/2)*(R*H*Q)^(ε/2) = (R*H*Q)^(1+ε) := by
    rw [← Real.rpow_add hB]
    congr 1
    ring
  calc
    _ = _ := hcardR
    _ ≤ ∑ z ∈ F, M*(1/((z.1:ℝ)*(z.2:ℝ))) := Finset.sum_le_sum hf
    _ = M*(∑ z ∈ F, 1/((z.1:ℝ)*(z.2:ℝ))) := by rw [Finset.mul_sum]
    _ = M*((harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ)) := by rw [hw]
    _ ≤ M*(Ch*(R*H*Q)^(ε/2)) :=
      mul_le_mul_of_nonneg_left (hharmonic R H Q hR hH hQ) hM
    _ = (Cf*Ch)*((R*H*Q)^(1+ε/2)*(R*H*Q)^(ε/2))*(1+δ*Q) := by
      ring
    _ = _ := by rw [hpow]

end TaoTrudgianYang2025

