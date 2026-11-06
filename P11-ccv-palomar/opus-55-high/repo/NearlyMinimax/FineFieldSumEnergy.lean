module

public import NearlyMinimax.FineFieldSubsetL2
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Summation of actual time-integrated higher field moments over all
selected subsets, with a geometric count envelope. -/
𝚫
𝚪
𝚨
𝚩

𝗇 𝔅 𝙉
def fineFieldSubsetEnergyBase (d : ℕ) : ℝ :=
  4 * 𝔅 ^ d * hyperplaneSpatialMomentConstant d ^ 2

theorem hyperplaneSpatialMomentConstant_ge_one d :
    1 ≤ hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have hc := spatialExponentialConstant_nonneg d
  bound

𝗇 𝔄 lo ^ (2 - 𝙊)
𝗇 𝔇 d * k
𝗇 𝔈 finePairTimeSubsetMoment lo hi U S
𝗇 𝔉 hyperplaneSpatialMomentConstant d ^ (2 * k)
𝗇 𝔊 𝘓₂
𝗇 𝔍 fullSpatialPatchDesign d k
𝗇 𝔎 pow_nonneg hC _
theorem finePairTimeSubsetMoment_uniform_square_integral_le [NeZero d]
    (hd : 3 ≤ d) (hlo : 𝙫₁) (S : 𝔊) (hS : 4 ≤ S.card) :
     ∫ U : Fin k → Covariate d, 𝔈 ^ 2
      ∂𝔍 ≤
       2 ^ 𝔇 * 𝔉 *
        k ^ 8 * 𝔄 ^ 2 := by
  have hc : S.card ≤ k := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card $ Finset.subset_univ S
  have hv : 2 ^ (d * (k - S.card)) ≤ 𝔅 ^ 𝔇 :=
    pow_le_pow_right₀  𝖠₄  $ Nat.mul_le_mul_left d $ Nat.sub_le ..
  have hj : S.card ^ 8 ≤ 𝙦 ^ 8 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hc) 8
  have h := finePairTimeSubsetMoment_square_integral_le hd (hi := hi) hlo S hS
  apply h.trans
  have hC := (hyperplaneSpatialMomentConstant_positive d).le
  have h3 := mul_le_mul (mul_le_mul hv (pow_le_pow_right₀ (hyperplaneSpatialMomentConstant_ge_one d) $ Nat.mul_le_mul_left 2 hc ) 𝔎 𝖠₃ ) hj (pow_nonneg (Nat.cast_nonneg S.card) 8)
    $ mul_nonneg  𝖠₃  𝔎
  convert mul_le_mul_of_nonneg_right h3 $ sq_nonneg 𝔄 using 1 <;> simp only [mul_pow] <;> ring

𝗇 𝔏 hs S hS
/-- Any family of higher subsets has the same geometric count envelope;
the concrete even-subset field family is a particular case. -/
theorem finePairTimeSubsetMoment_sum_abs_square_integral_le [NeZero d]
    (hd : 3 ≤ d) (hlo : 𝙫₁) (s : Finset 𝔊)
    (hs : ∀ S ∈ s, 4 ≤ S.card) :
     ∫ U : Fin k → Covariate d, (∑ S ∈ s, |𝔈|) ^ 2
      ∂𝔍 ≤
      fineFieldSubsetEnergyBase d ^ k * k ^ 8 * 𝔄 ^ 2 := by
  classical
  let K := 2 ^ 𝔇 * 𝔉 *
    k ^ 8 * 𝔄 ^ 2
  have hK : 𝖭₂ := by
    have hC := (hyperplaneSpatialMomentConstant_positive d).le
    positivity
  have h := finite_sum_square_integral_le 𝔍 s
    (fun S U => |𝔈|) K
    (fun S _ => (finePairTimeSubsetMoment_measurable lo hi S).abs)
     fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_square_integrable hd hlo S 𝔏
     fun S hS => by simpa only [sq_abs] using finePairTimeSubsetMoment_uniform_square_integral_le hd hlo S 𝔏
  have hcNat : s.card ≤ 2 ^ k := by
    have hsub : s ⊆ Finset.univ.powerset := 𝖢₄
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsub
  have hc : s.card ^ 2 ≤ (𝔅 ^ k) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hcNat) 2
  apply (h.trans $ mul_le_mul_of_nonneg_right hc hK ).trans_eq
  dsimp [fineFieldSubsetEnergyBase]
  simp only [mul_pow]
  have hfour : 4 ^ k = 𝔅 ^ (k * 2) := by
    rw [show 4 = 𝔅 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm]
  rw [hfour]
  ring
