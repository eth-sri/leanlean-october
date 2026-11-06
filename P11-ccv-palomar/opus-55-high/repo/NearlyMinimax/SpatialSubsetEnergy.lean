module

public import NearlyMinimax.SpatialSubsetIntegral
public import Mathlib.Data.Finset.Powerset
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual square-integrability and finite subset-sum energy bounds on Q^k. -/
𝚫
𝛉
𝚨
𝚩

𝗇 𝔅 𝘫
𝗃 𝔔 fun j => ἀ $ e.symm j
𝗇 𝔍 𝔔 U
theorem finite_pi_reindex_integrable [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ)
    (hf : Integrable f $ Measure.pi 𝔅 ) :
    Integrable (fun U : I → E => f 𝔍) $ Measure.pi 𝔅 := by
  have hp := measurePreserving_piCongrLeft 𝔅 e
  have he U : (Equiv.piCongrLeft 𝚓 e) U =
      𝔍 := by
    funext j
    simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, he] using hp.integrable_comp_of_integrable hf

𝗇 𝔈 fun V => f V ^ 2
𝗇 𝔉 spatialSubsetConfiguration s U
𝗇 𝔎 (Fin s.card → Covariate d) → ℝ
𝗇 𝔏 fullSpatialPatchDesign d s.card
𝗇 𝔐 fullSpatialPatchDesign d k
𝗇 𝔑 𝖪
theorem spatial_subset_square_integrable_enumerated (s : 𝘓₂)
    (f : 𝔎)
    (hf : Integrable 𝔈 𝔏) :
    Integrable (fun U => f 𝔉 ^ 2)
      𝔐 := by
  let e := (Fintype.equivFin s).trans $ finCongr $ Fintype.card_coe s
  have hi := finite_pi_reindex_integrable 𝔑 e
    𝔈 hf
  have h := finite_pi_subset_integrable 𝔑 s
    (fun V => f 𝔔 V ^ 2) hi
  exact h

𝗇 𝔄 (∑ i ∈ s, f i x) ^ 2
𝗇 𝔇 f i x ^ 2
𝗇 𝔒 s.card * ∑ i ∈ s, 𝔇
𝗃 𝔓 Integrable (fun x => ἀ) μ
𝗃 𝔖 ∫ x, ἀ ∂μ
theorem finite_sum_square_integral_le [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ) K
    (hm : ∀ i ∈ s, Measurable $ f i )
    (hi : ∀ i ∈ s, 𝔓 𝔇)
    (hK : ∀ i ∈ s, 𝔖 𝔇 ≤ K) :
    𝔖 𝔄 ≤ s.card ^ 2 * K := by
  classical
  have hb x : 𝔄 ≤ 𝔒 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq s 𝙃 fun i => f i x
  have hu : 𝔓 𝔒 :=
    (integrable_finsetSum s hi).const_mul _
  have hl : 𝔓 𝔄 := by
    apply hu.mono' ((Finset.measurable_fun_sum s hm).pow_const 2).aestronglyMeasurable
    simp_all
  have h := integral_mono hl hu hb
  rw [integral_const_mul, integral_finsetSum _ hi] at h
  apply h.trans
  simpa only [Finset.sum_const, nsmul_eq_mul, sq, ← mul_assoc] using mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK) $ Nat.cast_nonneg s.card

𝗇 𝔊 d * (k - r)
/-- This is the exact binomial and unused-coordinate factor in the paper's
subset lift; each selected kernel is integrated over its genuine Q^r law. -/
theorem spatial_subset_sum_square_integral_le
    (f : (s : 𝘓₂) → 𝔎) K
    (hm : ∀ s ∈ Finset.univ.powersetCard r, Measurable $ f s )
    (hi : ∀ s ∈ Finset.univ.powersetCard r,
      Integrable (fun V => f s V ^ 2) 𝔏)
    (hK : ∀ s ∈ Finset.univ.powersetCard r,
       ∫ V, f s V ^ 2 ∂𝔏 ≤ K) :
     ∫ U, (∑ s ∈ Finset.univ.powersetCard r,
      f s 𝔉) ^ 2 ∂𝔐 ≤
       k.choose r ^ 2 * 2 ^ 𝔊 * K := by
  classical
  have h := finite_sum_square_integral_le 𝔐
    (Finset.univ.powersetCard r)
    (fun s U => f s 𝔉) (2 ^ 𝔊 * K)
    (fun s hs => (hm s hs).comp $ spatialSubsetConfiguration_measurable s )
    (fun s hs => spatial_subset_square_integrable_enumerated s (f s) $ hi s hs )
     fun s hs => by
      rw [spatial_subset_square_integral_enumerated]
      simp_all
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h
