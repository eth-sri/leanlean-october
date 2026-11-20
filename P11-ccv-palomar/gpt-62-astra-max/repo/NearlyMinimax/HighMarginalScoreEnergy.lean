module

public import NearlyMinimax.HighMarginalScore
public import NearlyMinimax.PosteriorScoreEnergy


@[expose] public section

/-! Actual observed-data Fisher energy is bounded by genuine latent
append/heat likelihood Fisher energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem highMarginalRealScore_memLp_energy {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    {dependent : J → J → Prop} [Std.Symm dependent]
    {ν : Measure (HistoryMarked dependent E)} [IsProbabilityMeasure ν]
    {π : Measure E} [IsProbabilityMeasure π] {activation : E → ℝ} (ham : Measurable activation)
    {Ba : ℝ} (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    {n : ℕ} {a V η aRaw bRaw : ℝ} (ha : 0 < a) (haRaw : 0 < aRaw)
    {p F : HistoryMarked dependent E → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (hE : Integrable (fun z =>
      (highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2)^2 /
        highRawSampleLikelihood a V (p z.1) (F z.1) z.2) (ν.prod (highSampleReference d n))) :
    let P := (highRealSampleKernel n a V hp hF) ∘ₘ
      (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)
    MemLp (highMarginalRealScore ν π activation n a V η p F) 2 P ∧
      (∫ z, (highMarginalRealScore ν π activation n a V η p F z)^2 ∂P) ≤
        (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
          ∫ z,
            (highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2)^2 /
              highRawSampleLikelihood a V (p z.1) (F z.1) z.2 ∂ν.prod (highSampleReference d n) := by
  let μ := highSampleReference d n
  let L : HistoryMarked dependent E × (IndexedSample d n) → ℝ := fun z =>
    highRawSampleLikelihood a V (p z.1) (F z.1) z.2
  let D : HistoryMarked dependent E × (IndexedSample d n) → ℝ := fun z =>
    highHistoryLikelihoodDerivative π activation a V η p F z.1 z.2
  let m := fun ω => highRawDensityMass (p ω)
  let G := massPowerNormalizer ν m n
  have hb (ω)  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Eventually.of_forall (hraw ω))
  have hpb ω x : |p ω x| ≤ |bRaw| := by
    grind
  have hLp (z) : 0 < L z := highRawSampleLikelihood_pos p F (fun ω x => haRaw.trans_le (hraw ω x).1) hq ..
  have hLb (z) : L z ≤ |bRaw|^n := (le_abs_self _).trans
    (highRawSampleLikelihood_abs_le (abs_nonneg _) (hpb z.1) ha.ne' (fun x y => (hq z.1 x y).le) _)
  have hDb (z) : |D z| ≤ (Fintype.card J) * (Ba * |bRaw|^n) +
      η^2 * (|bRaw|^n * (n/a^2)) :=
    highHistoryLikelihoodDerivative_abs_le π hBa habound a V η (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2
  have he := posteriorMeanScore_memLp_energy
    (highRawSampleLikelihood_joint_measurable n a V hp hF)
    (highHistoryLikelihoodDerivative_measurable π ham n a V η hp hF)
    hLp (massPowerNormalizer_pos ν (highRawDensityMass_joint_measurable hp) n haRaw hb) hLb hDb hE
  have hden := highMassTilt_index_marginal_density ν n hp hF haRaw ha.ne'
    hraw (fun ω x y => (hq ω x y).le)
  let Pi := (highSampleIndexKernel n a V hp hF) ∘ₘ massPowerTilt ν m n
  let score := highMarginalIndexScore ν π activation n a V η p F
  have hpost : posteriorMeanScore ν L D = score := rfl
  rw [hpost] at he
  change Pi = μ.withDensity (fun z => ENNReal.ofReal ((∫ ω, L (ω,z) ∂ν) / G)) at hden
  rw [← hden] at he
  have hmap : (highRealSampleKernel n a V hp hF) ∘ₘ massPowerTilt ν m n =
      Pi.map (encodeDesignResponse a) := (Measure.map_comp _ _ (encodeDesignResponse_measurable a)).symm
  have hR := highMarginalRealScore_measurable ν π ham n a V η hp hF
  have hcomp : (fun z => highMarginalRealScore ν π activation n a V η p F
      (encodeDesignResponse a z)) = score := by
    funext z
    exact congrArg (score)
      (decodeDesignResponse_encode ha z)
  rw [hmap]
  constructor
  · apply (memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable).2
    simpa only [Function.comp_def, hcomp] using he.1
  · rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
    grind

end NearlyMinimax
