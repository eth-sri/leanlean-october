module

public import NearlyMinimax.FinePairResponseBounds
public import NearlyMinimax.HighFrameLocalBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Bounds on the actual pair alias and even-field remainder. The response
cap follows from the genuine finite response packet and chart frame. -/
𝚫
𝚨
𝚬

theorem fine_pair_filtered_sum_abs_bound s (P : I → Prop) [DecidablePred P]
    (c H : 𝗦₂) R B K (hB : 𝙐)
    (hc : ∀ i ∈ s, |c i| ≤ B) (hR : |R| ≤ K) :
    |∑ i ∈ s, c i * (if P i then 1 else 0) * H i * R| ≤
      B*K * ∑ i ∈ s, if P i then |H i| else 0 := by
  apply 𝘡
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hP : P i
  · simp only [if_pos hP]
    calc
      _ = |c i| * |R| * |H i| := 𝖤₃
      _ ≤ B*K * |H i| := mul_le_mul_of_nonneg_right
        (mul_le_mul (hc i hi) hR (abs_nonneg _) hB) $ abs_nonneg _
  simp_all

section Actual
variable {d n F : ℕ}

𝗇 𝔄 fun v => 𝖨 𝙬 v y
𝗇 𝔉 𝘀
𝗇 𝔏 𝙸
𝗇 𝔐 𝖲
𝗇 𝔒 𝙔
theorem finePairDistance_response_bound_of_chart (q : ℕ) (hn : 𝗚)
    (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hηρ : η ≤ 𝔏) (U : 𝙇) (hU : ∀ i l, |𝚅| ≤ 2)
    (g w : 𝔒) (c : 𝔐) (y : 𝙈)
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝔏) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → 𝔉) :
    |𝗔 𝖺₂ c
      𝔄| ≤
        𝘁 * 𝙒^2 * 𝙎 :=
  finePairDistance_response_all_count_bound q hn C a V η ρ (lt_of_lt_of_le zero_lt_one hC)
    ha hη hρ hηρ U g w c y hc hg hw
    𝘢 hp

𝗇 𝔅 finePairDistance_response_bound_of_chart q hn C a V η ρ hC ha hη hρ hηρ U hU g w c y hc hg hw hp
𝗇 𝔇 𝗺₁ * (𝘁 * 𝚍 * 𝙎)
𝗇 𝔈 fun W => finePairCountCoefficient ad bd M n W.card * ∏ i ∈ W, p i
𝗇 𝔊 fun W _ => finePairCountCoefficient_product_bound ad bd haD hab M p hpD W
𝗇 𝔍 finePairTimeSubsetMoment T0 N U
𝗇 𝔎 finePairDensityCoefficientBudget_nonneg ad bd (haD.trans hab).le M n
𝗇 𝔑 𝖳
𝗃 𝔓 ἀ ad bd T0 N M q C U p c 𝔄
theorem finePairPairAliasAction_abs_bound_of_chart
    ad bd T0 N (haD : 𝖼) (hab : 𝖽) M q (hn : 𝗚)
    C a V η ρ (hC : 1 ≤ C) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hηρ : η ≤ 𝔏) U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔒) (hpD : 𝔑)
    (c : 𝔐) y
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝔏) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔉) :
    |𝔓 finePairPairAliasAction| ≤
      𝔇 *
          ∑ W ∈ Finset.univ.powerset,
            if W.card = 2 then |𝔍 W| else 0 := fine_pair_filtered_sum_abs_bound Finset.univ.powerset (fun W => W.card = 2)
    𝔈
     𝔍 _ _ _
    𝔎
    𝔊
    𝔅

theorem finePairEvenFieldAction_abs_bound_of_chart
    ad bd T0 N (haD : 𝖼) (hab : 𝖽) M q (hn : 𝗚)
    C a V η ρ (hC : 1 ≤ C) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁)
    (hηρ : η ≤ 𝔏) U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝔒) (hpD : 𝔑)
    (c : 𝔐) y
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝔏) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔉) :
    |𝔓 finePairEvenFieldAction| ≤
      𝔇 *
          ∑ W ∈ Finset.univ.powerset,
            if 4 ≤ W.card ∧ Even W.card then |𝔍 W| else 0 := fine_pair_filtered_sum_abs_bound Finset.univ.powerset (fun W => 4 ≤ W.card ∧ Even W.card)
    𝔈
     𝔍 _ _ _
    𝔎
    𝔊
    𝔅
