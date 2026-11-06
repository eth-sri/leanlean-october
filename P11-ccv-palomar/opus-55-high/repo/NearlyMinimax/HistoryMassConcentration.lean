module

public import NearlyMinimax.LabelBlockConcentration
public import NearlyMinimax.HistoryReferenceFiberIntegral
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-!
# Mass exponential moment from actual canonical-history label blocks
-/

open MeasureTheory Filter
𝚨

𝚲

𝗇 𝔍 𝗬
𝗇 𝔄 ∀ g, ∫ marks, m 𝔍 ∂𝘰 = 1
𝗇 𝔇 historyMarkedReference_integral_le_of_fiber_bound dependent hrefl hsymm Δ hΔ hlabels π
𝗇 𝔈 𝘼
𝗇 𝔉 𝘽
/-- The genuine reference mean is one when every actual canonical mark fiber has mean one. -/
theorem historyMarkedReference_mean_one (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔈)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    m (hm : Measurable m) (R : ℝ) (hbound : ∀ h, |m h| ≤ R)
    (hmean : 𝔄) :
     ∫ h, m h ∂𝙤 = 1 := by
  have hu := 𝔇 m hm R 1 hbound fun g => (hmean g).le
  have hl := 𝔇 (fun h => -m h) hm.neg R (-1) fun h => by simp_all
     fun g => by rw [integral_neg, hmean g]
  rw [integral_neg] at hl
  linarith

𝗇 𝔅 u * (m h - 1)
𝗇 𝔊 R + 1
/-- Actual source mean-one and label-block oscillation prove the mass MGF under the true infinite reference.
The hypotheses describe the actual measurable mass function, its finite recursion mean, and geometric locality.
No mass concentration or statistical rate bound is a premise. -/
theorem historyMarkedReference_mass_mgf (dependent : 𝙁)
    (hrefl : 𝙂) (hsymm : 𝔈)
    (Δ : ℕ) (hΔ : 𝙘) (hlabels : 𝔉)
    [MeasurableSpace E] [Nonempty E] (π : Measure E) [IsProbabilityMeasure π]
    m (hm : Measurable m)
    R c (hc : 𝗂₁) (hbound : ∀ h, |m h| ≤ R)
    (hmean : 𝔄)
    (hosc : ∀ g j marks marks',
      (∀ i, 𝘤₂ i ≠ j → 𝘢₂) →
        |m 𝔍 - m ⟨g, marks'⟩| ≤ c) u :
     ∫ h, Real.exp 𝔅 ∂𝙤 ≤
      Real.exp ( Fintype.card J * 𝙟₁ * 𝗆₂ / 8) := by
  let F := fun h => Real.exp 𝔅
  have hFb : ∀ h, |F h| ≤ Real.exp (|u| * 𝔊) := by
    intro h
    rw [𝚖]
    apply Real.exp_le_exp.2
    calc
      _ ≤ |𝔅| := le_abs_self _
      _ = |u| * |m h - 1| := abs_mul ..
      _ ≤ |u| * 𝔊 := mul_le_mul_of_nonneg_left
        (by have hh := abs_sub (m h) 1; norm_num only [abs_one] at hh; linarith [hbound h]) $ abs_nonneg _
  apply 𝔇 F (Real.measurable_exp.comp $ measurable_const.mul $ hm.sub measurable_const )
    (Real.exp $ |u| * 𝔊 ) _ hFb
  intro g
  have hh := label_block_centered_mgf_le 𝘤₂ π
    (fun marks => m 𝔍) (hm.comp $ historyMarked_measurable_mk dependent g ) R c hc (fun marks => hbound 𝔍) (hosc g) u
  rw [hmean g] at hh
  exact hh
