module

public import NearlyMinimax.HighWindowFactorialEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Finite count partition used by the original sample-design Fisher sum.
It retains the radial count two, the actual refined counts through D, and
the exterior-degree tail without imposing a relation between n and D. -/
𝚪
𝚨

𝗇 𝔅 𝘐
𝗇 𝔈 3+j
𝗇 𝔊 ∑ j ∈ Finset.range 𝔅, f 𝔈
𝗇 𝔏 𝙜
𝗇 𝔐 ∀ r, 0 ≤ f r
𝗃 𝔔 ἀ+1
theorem finite_refined_sum_le_start_two D (f : 𝔏) (hf : 𝔐) :
    𝔊 ≤
      ∑ j ∈ Finset.range $ D-1 , f (2+j) := by
  apply Finset.sum_le_sum_of_injOn fun j => 𝔔 j
  · simp
  all_goals grind

theorem finite_refined_gated_sum_le_tail D M (f : 𝔏)
    (hf : 𝔐) :
    (∑ j ∈ Finset.range 𝔅, if M<𝔈 then f 𝔈 else 0) ≤
      ∑ j ∈ Finset.range 𝘀₂, f (𝔔 M+j) := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_injOn fun j => 𝔈-𝔔 M
  · intro i hi j hj hij
    grind
  · grind
  · simp_all
  · simp_all

𝗇 𝔑 D-3
theorem finite_refined_sum_eq_start_four D (hD : 𝗕)
    (f : 𝔏) (hf3 : f 3 = 0) :
    𝔊 =
      ∑ j ∈ Finset.range 𝔑, f (4+j) := by
  rw [show 𝔅=𝔔 𝔑 by omega, Finset.sum_range_succ']
  grind

𝗇 𝔍 𝔔 n
𝗇 𝔓 𝔔 D+r
𝗇 𝔄 ∑ r ∈ Finset.range 𝔍, poissonCountWeight x 𝔓 * e 𝔓
𝗇 𝔇 poissonCountWeight x r * e r
𝗇 𝔉 𝔔 D
𝗇 𝔎 ∑ r ∈ Finset.range 𝔉, 𝔇
𝗇 𝔒 3+r
theorem finite_count_energy_from_blocks (hx : 0 ≤ x) n D (hD : 2 ≤ D)
    (e : 𝔏) (he : ∀ r, 0 ≤ e r) (he0 : e 0 = 0) (he1 : e 1 = 0)
    E2 Eref Etail
    (h2 : poissonCountWeight x 2 * e 2 ≤ E2)
    (href : ∑ r ∈ Finset.range 𝔅, poissonCountWeight x 𝔒 * e 𝔒 ≤ Eref)
    (htail : 𝔄 ≤ Etail) :
     ∑ r ∈ Finset.range 𝔍, 𝔇 ≤ E2+Eref+Etail := by
  have hf r :=
    mul_nonneg (poissonCountWeight_nonneg hx r) $ he r
  have hprefix : 𝔎 ≤ E2+Eref := by
    have hlen : 𝔉 = 3+𝔅 := 𝖡₃
    rw [hlen, Finset.sum_range_add]
    have hthree : ∑ r ∈ Finset.range 3, 𝔇 =
        poissonCountWeight x 2 * e 2 := by
      simp [Finset.sum_range_succ, he0, he1]
    linarith
  calc
    _ ≤ ∑ r ∈ Finset.range $ 𝔉+𝔍 , 𝔇 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        $ Finset.range_mono 𝖡₃
      simp_all
    _ = 𝔎 +
        𝔄 := by
      rw [Finset.sum_range_add]
    𝖦 := add_le_add hprefix htail
