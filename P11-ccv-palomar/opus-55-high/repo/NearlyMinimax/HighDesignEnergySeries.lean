module

public import NearlyMinimax.HighDesignScoreTransfer
public import NearlyMinimax.HighNormalizedCounts
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual iid membership partition gives the finite factorial
score-energy series. The selected-observation spatial integrals remain
explicit, so this bridge does not assume a global score budget. -/
𝚫
𝚳
𝚨
𝚩
𝚱
𝚬

𝗇 𝔅 𝙍
𝗇 𝔉 Finset.range 𝗉
theorem finset_sum_cardinality (F : 𝙜) :
     ∑ S : 𝔅, F S.card =
      ∑ r ∈ 𝔉, n.choose r * F r := by
  have h := Finset.sum_powerset (Finset.univ : 𝔅) fun S => F S.card
  simp at h
  rw [h]
  apply Finset.sum_congr rfl
  intro r hr
  simpa only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat] using
       Finset.sum_powersetCard r Finset.univ F

𝗇 𝔄 𝘯₁
𝗇 𝔇 Measure.pi 𝘫
𝗇 𝔈 ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S fun i => x i.val
𝗇 𝔊 ψ ^ S.card * J S.card
𝗇 𝔍 ∫ z, H S z ∂𝔄
𝗇 𝔎 (S : 𝔅) → (S → α) → ℝ
𝗇 𝔏 ∫ x, E x ∂𝔇
section

variable [MeasurableSpace α]
    (μ : Measure α)
    [IsProbabilityMeasure μ]
    (n)
    (A)
    (hA : MeasurableSet A)
    (E)
    (hE : Integrable E 𝔇)
    (H : 𝔎)
    (hH : ∀ S, Integrable (H S) 𝔄)
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : 𝔈)
    (ψ)

include μ hA hE hH hHn hdom

𝗇 𝔐 ∀ S : 𝔅, 𝔍 ≤ 𝔊
𝗃 𝔑 ἀ μ n A hA E hE H hH hHn hdom
theorem iid_local_energy_le_binomial_spatial_series (J : 𝙜)
    (hspatial : 𝔐) :
    𝔏 ≤
      ∑ r ∈ 𝔉, n.choose r * ψ ^ r * J r := by
  calc
    _ ≤ ∑ S : 𝔅, 𝔍 :=
      𝔑 iid_local_energy_le_selected_sum
    _ ≤ ∑ S : 𝔅, 𝔊 :=
      Finset.sum_le_sum fun S _ => hspatial S
    𝘿 := by
      rw [finset_sum_cardinality fun r => ψ ^ r * J r ]
      field_simp

theorem iid_local_energy_le_factorial_spatial_series (hψ : 0 ≤ ψ) (J : 𝙜) (hJ : ∀ r, 0 ≤ J r)
    (hspatial : 𝔐) :
    𝔏 ≤
      ∑ r ∈ 𝔉, (n * ψ) ^ r / r.factorial * J r := by
  refine (𝔑 iid_local_energy_le_binomial_spatial_series ψ J hspatial).trans ?_
  apply Finset.sum_le_sum
  intro r hr
  calc
    _ ≤ n ^ r / r.factorial * ψ ^ r * J r := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r n) $ pow_nonneg hψ r ) $ hJ r
    𝘿 := 𝖢₃
