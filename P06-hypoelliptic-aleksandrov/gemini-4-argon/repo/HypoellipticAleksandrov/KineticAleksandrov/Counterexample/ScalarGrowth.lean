module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
import Mathlib.Tactic

/-!
# Global scalar growth

Compact middle-interval bounds and the two actual normalized limits control the whole profile.
-/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Set
open scoped Topology

/- Continuous real functions with finite normalized limits have a global power bound. -/
theorem scalar_power_growth (f : ℝ → ℝ) (alpha c ) (hf : Continuous f)
    (ht : Tendsto (fun s => f s / Real.rpow |s| alpha) atTop (𝓝 c))
    (hb : Tendsto (fun s => f s / Real.rpow |s| alpha) atBot (𝓝 c)) :
    ∃ K : ℝ, 0 < K ∧ c ≤ K ∧ ∀ s, |f s| ≤ K * (1 + Real.rpow |s| alpha) := by
  have htc := ht.abs.eventually (Iio_mem_nhds (lt_add_one |c|))
  have hbc := hb.abs.eventually (Iio_mem_nhds (lt_add_one |c|))
  obtain ⟨a, ha⟩ := eventually_atTop.mp htc
  obtain ⟨b, hb⟩ := eventually_atBot.mp hbc
  let R : ℝ := max (max a (-b)) 1
  have hR : 1 ≤ R := le_max_right _ _
  have hRa : a ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRb : -b ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨M, hM⟩ := (isCompact_Icc.image hf.abs).bddAbove
  let K : ℝ := max (max M (|c| + 1)) 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKM : M ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hKc : |c| + 1 ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨K, hK, (le_abs_self c).trans ((le_add_of_nonneg_right zero_le_one).trans hKc), ?_⟩
  intro s
  have hpow : 0 ≤ Real.rpow |s| alpha := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hs : s ∈ Icc (-R) R
  · have hm : |f s| ≤ M := hM (mem_image_of_mem _ hs)
    exact hm.trans (hKM.trans (le_mul_of_one_le_right hK.le (by linarith)))
  · have hs0 : s ≠ 0 := by
      intro hz
      apply hs
      subst s
      constructor <;> linarith
    have hp : 0 < Real.rpow |s| alpha := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_pos_of_pos (abs_pos.mpr hs0) alpha
    have hratio : |f s / Real.rpow |s| alpha| < |c| + 1 := by
      rcases lt_or_ge s (-R) with hleft | hleft
      · exact hb s (by linarith)
      · exact ha s (by
          have hr : R < s := by
            by_contra hn
            exact hs ⟨hleft, le_of_not_gt hn⟩
          linarith)
    rw [abs_div, abs_of_pos hp] at hratio
    have hfs := (div_lt_iff₀ hp).mp hratio
    exact hfs.le.trans ((mul_le_mul_of_nonneg_right hKc hpow).trans
      (mul_le_mul_of_nonneg_left (by linarith) hK.le))

/- The source similarity function has a uniform global power-growth bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
