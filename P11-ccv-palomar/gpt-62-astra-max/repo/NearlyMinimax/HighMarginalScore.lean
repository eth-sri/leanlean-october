module

public import NearlyMinimax.HighMarginalLikelihood
public import NearlyMinimax.HighResponseDecoding
public import NearlyMinimax.WeightedScoreContraction


@[expose] public section

/-! The actual observed-data score: the averaged genuine likelihood derivative
 divided by the averaged genuine likelihood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

section
variable {E : Type*} [MeasurableSpace E] {d : ℕ} {dependent : J → J → Prop} [Std.Symm dependent]
    (ν : Measure (HistoryMarked dependent E)) (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)

def highMarginalLikelihoodDerivative
    {n : ℕ} (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (z : IndexedSample d n) : ℝ :=
  ∫ ω, highHistoryLikelihoodDerivative π activation a V η p F ω z ∂ν

def highMarginalIndexScore
    (z : IndexedSample d n) : ℝ :=
  highMarginalLikelihoodDerivative ν π activation a V η p F z /
    highMarginalRawLikelihood ν a V p F z

def highMarginalRealScore
    (z : Fin n → Observation d) : ℝ :=
  highMarginalIndexScore ν π activation n a V η p F (decodeDesignResponse a z)

end

section
variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ} {dependent : J → J → Prop}
    [Std.Symm dependent] (ν : Measure (HistoryMarked dependent E)) [SFinite ν] (π : Measure E)
    [SFinite π] {activation : E → ℝ} (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    {p F : HistoryMarked dependent E → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F))
include hF ham hp

theorem highMarginalRealScore_measurable :
    Measurable (highMarginalRealScore ν π activation n a V η p F) :=
  ((highHistoryLikelihoodDerivative_measurable π ham n a V η hp hF).stronglyMeasurable.integral_prod_left'.measurable.div (highMarginalRawLikelihood_measurable ν n a V hp hF)).comp
    (decodeDesignResponse_measurable a)

end

variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ} {dependent : J → J → Prop}
    [Std.Symm dependent] (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] {activation : E → ℝ} (ham : Measurable activation) {Ba : ℝ}
    (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba) {n : ℕ}
include hBa habound ham

/-- Actual marginal score testing has the genuine averaged derivative
as its density; all Fubini integrability is derived from primitive bounds. -/
theorem highMarginalIndexScore_integral (a V η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    let likelihoodDerivative := highHistoryLikelihoodDerivative π activation a V η p F
    (∫ z, H (encodeDesignResponse a z) *
      highMarginalIndexScore ν π activation n a V η p F z
      ∂(highSampleIndexKernel n a V hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z,
          H (encodeDesignResponse a z.2) *
            likelihoodDerivative z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  intro likelihoodDerivative
  let m := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable hp
  have hb (ω)  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν hm n haRaw hb
  have hpb ω x : |p ω x| ≤ |bRaw| := by
    grind
  have hL (z) := highMarginalRawLikelihood_pos ν (n := n) (abs_nonneg _) ha.ne' hp hF
    (fun ω x => haRaw.trans_le (hraw ω x).1) hpb hq z
  have hdens : Measurable (fun z => ENNReal.ofReal
      (highMarginalRawLikelihood ν a V p F z / massPowerNormalizer ν m n)) :=
    ((highMarginalRawLikelihood_measurable ν n a V hp hF).div_const _).ennreal_ofReal
  rw [highMassTilt_index_marginal_density ν n hp hF haRaw ha.ne' hraw
    (fun ω x y => (hq ω x y).le),
    integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hL _).le hG.le), smul_eq_mul]
  have hi : Integrable (fun z =>
      H (encodeDesignResponse a z.2) *
        likelihoodDerivative z.1 z.2)
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound
      (((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
        (highHistoryLikelihoodDerivative_measurable π ham n a V η hp hF)).aestronglyMeasurable
      (B * ((Fintype.card J) * (Ba * |bRaw|^n) + η^2 * (|bRaw|^n * (n/a^2))))
    exact Eventually.of_forall fun z => by
      change ‖H (encodeDesignResponse a z.2) *
        likelihoodDerivative z.1 z.2‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hHb _) (highHistoryLikelihoodDerivative_abs_le π hBa
        habound a V η (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2)
        (abs_nonneg _) hB
  calc
    _ = (massPowerNormalizer ν m n)⁻¹ *
        ∫ z, H (encodeDesignResponse a z) *
          highMarginalLikelihoodDerivative ν π activation a V η p F z
          ∂highSampleReference d n := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp [highMarginalIndexScore]
        field_simp [(hL z).ne'] <;> ring
    _ = _ := by
      congr 1
      rw [MeasureTheory.integral_prod_symm _ hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp [highMarginalLikelihoodDerivative]
        rw [integral_const_mul]

theorem highMarginalRealScore_integral {a V : ℝ} (η aRaw bRaw B : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hB : 0 ≤ B)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z, H z * highMarginalRealScore ν π activation n a V η p F z
      ∂(highRealSampleKernel n a V hp hF) ∘ₘ
        (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z,
          H (encodeDesignResponse a z.2) *
            highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2
          ∂ν.prod (highSampleReference d n) := by
  have hm : Measurable (fun z => H z *
      highMarginalRealScore ν π activation n a V η p F z) :=
    hH.mul (highMarginalRealScore_measurable ν π ham n a V η hp hF)
  rw [highRealSampleKernel, ← Measure.map_comp _ _ (encodeDesignResponse_measurable a),
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hm.stronglyMeasurable]
  have he := highMarginalIndexScore_integral ν π ham hBa habound a V η aRaw bRaw B ha haRaw hB hp hF hraw hq hH hHb
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp [highMarginalRealScore]
    rw [decodeDesignResponse_encode ha]

end NearlyMinimax
