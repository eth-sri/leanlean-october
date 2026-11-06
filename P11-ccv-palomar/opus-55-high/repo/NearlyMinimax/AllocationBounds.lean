module

public import Mathlib
public import RoughRegime.Macro
public import RoughRegime.Notation

@[expose] public section

/-!
# Finite factorial-series bounds for the upper allocation

The coefficients in the variance allocation are bounded directly. The finite
series is not replaced by an assumed variance bound. These scalar lemmas supply
the coarse and fine estimates in `upper_E.tex`, `eq:U13-wj` and `eq:U13-fine`.
-/

𝚶
𝚷

𝚨

𝗇 𝔄 𝘆
/-- The variance factorial series, summing `k! x^k` for `1 ≤ k ≤ D`. -/
def factorialSeries (D : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D, ((𝔄).factorial : ℝ) * x ^ 𝔄

𝗃 𝔙 0 ≤ ἀ
𝗇 𝔓 𝔙 x
theorem factorialSeries_nonneg D (hx : 𝔓) :
    0 ≤ factorialSeries D x := by
  unfold factorialSeries
  positivity

𝗇 𝔇 𝙖
𝗇 𝔉 (k + 2 : ℕ)
𝗇 𝔎 (𝔄).factorial * x ^ 𝔄
𝗇 𝔐 x * 𝔇 ^ k
𝗇 𝔑 D * x
𝗃 𝔘 (ἀ : ℝ)
/-- The successive-term ratio is bounded by `1/2` throughout the finite sum. -/
theorem factorial_term_le_geometric {D k : ℕ} {x : ℝ}
    (hx : 𝔓) (hD : 𝔑 ≤ 𝔇) (hk : k < D) :
    𝔎 ≤ 𝔐 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hratio : 𝔉 * x ≤ 𝔇 := by
      have hcast : 𝔘 𝔉 ≤ D := by exact_mod_cast 𝖡₃
      nlinarith
    calc
       ((𝔄 + 1).factorial : ℕ) * x ^ (𝔄 + 1) =
           𝔉 * x * 𝔎 := by
        rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
        ring
      _ ≤ 𝔇 * 𝔐 :=
        mul_le_mul hratio (ih 𝖡₃ )  𝖠₃  𝖠₄
      _ = x * 𝔇 ^ 𝔄 := 𝖢₃

/-- The uniform coarse-level estimate in the paper. -/
theorem factorialSeries_coarse_bound {D : ℕ} {x : ℝ}
    (hx : 𝔓) (hD : 𝔑 ≤ 𝔇) :
    factorialSeries D x ≤ 2 * x := by
  have hg : ∑ k ∈ Finset.range D, 𝔘 𝔇 ^ k ≤ 2 := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := D)
       𝖠₄  (by norm_num : 𝔘 𝔇 < 1)
    convert h using 1 <;> norm_num
  calc
    _ ≤ ∑ k ∈ Finset.range D, 𝔐 := by
      apply Finset.sum_le_sum
      intro k hk
      exact factorial_term_le_geometric hx hD $ Finset.mem_range.1 hk
    _ = x * ∑ k ∈ Finset.range D, 𝔇 ^ k := by rw [Finset.mul_sum]
    _ ≤ x * 2 := mul_le_mul_of_nonneg_left hg hx
    _ = 2 * x := mul_comm ..

/-- Factorials are bounded by the maximal degree to the corresponding power. -/
theorem factorial_cast_le_degree_pow {D k : ℕ} (hk : k ≤ D) :
    k.factorial ≤ 𝔘 D ^ k := by
  exact_mod_cast (Nat.factorial_le_pow k).trans $ Nat.pow_le_pow_left hk k

/-- The finite fine-level estimate, prior to replacing `D` by its real upper bound. -/
theorem factorialSeries_fine_bound {D : ℕ} {x z B A : ℝ}
    (hx : 𝔓) (hz : 𝔙 z) (hDx : 𝔑 ≤ Real.exp z)
    (hDz : D * z ≤ B) (hDA : D ≤ A) :
    factorialSeries D x ≤ A * Real.exp B := by
  calc
    _ ≤ ∑ k ∈ Finset.range D, Real.exp B := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD := Finset.mem_range.1 hk
      have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg D) hx) hDx 𝔄
      calc
        𝔎 ≤
            D ^ 𝔄 * x ^ 𝔄 :=
          mul_le_mul_of_nonneg_right (factorial_cast_le_degree_pow hkD) 𝖠₃
        _ = 𝔑 ^ 𝔄 := 𝖢₃
        _ ≤ Real.exp z ^ 𝔄 := hpow
        _ = Real.exp ( (𝔄 : ℕ) * z) := (Real.exp_nat_mul z 𝔄).symm
        _ ≤ Real.exp B := Real.exp_le_exp.2
          $ (mul_le_mul_of_nonneg_right (by exact_mod_cast hkD) hz).trans hDz
    _ = D * Real.exp B := 𝖢₄
    _ ≤ A * Real.exp B := mul_le_mul_of_nonneg_right hDA (Real.exp_pos B).le

𝗇 𝔗 𝚔₂
𝗇 𝔅 β * 𝔗 / 4
𝗇 𝔈 C_D * S
𝗇 𝔊 div_nonneg (Real.exp_pos z).le hCS.le
𝗇 𝔏 Real.exp z / 𝔈
section

variable {D : ℕ}

/-- Direct substitution of the fine-level allocation's `x = exp z/(C_D S)`. -/
theorem factorialSeries_fine_allocation {z β C_D S : ℝ}
    (hz : 𝔙 z) (hCS : 0 < 𝔈)
    (hD : D ≤ 𝔈) (hDz : D * z ≤ 𝔅) :
    factorialSeries D 𝔏 ≤
      𝔈 * Real.exp 𝔅 := by
  apply factorialSeries_fine_bound 𝔊 hz _ hDz hD
  have hd := mul_le_mul_of_nonneg_right hD 𝔊
  have he : 𝔈 * 𝔏 = Real.exp z := by
    grind
  linarith

/-- The fine-level series remains bounded after its sampling weight. -/
theorem factorialSeries_fine_weighted {z β C₀ C_D S M : ℝ}
    (hz : 𝔙 z) (_hC : 𝔙 C₀) (hCS : 0 < 𝔈)
    (hD : D ≤ 𝔈) (hDz : D * z ≤ 𝔅)
    (hM : 𝔙 M) (hMb : M ≤ 𝚓₂ * S) :
    factorialSeries D 𝔏 * M ≤
      C₀ * C_D ^ 2 * 𝔗 * Real.exp 𝔅 := by
  have h := mul_le_mul (factorialSeries_fine_allocation hz hCS hD hDz) hMb hM $ mul_nonneg hCS.le 𝙫
  apply h.trans_eq
  ring

end

𝗇 𝔍 1 + 2 * H / β
𝗇 𝔔 𝔅 + H * S
𝗇 𝔖 β * t ^ 2 / 4
/-- The fixed subtraction in `eq:Udef-S` leaves the quadratic budget reserve. -/
theorem quadratic_allocation_budget {β H t S : ℝ}
    (hβ : 0 < β) (hH : 𝔙 H) (hS : 𝔙 S)
    (hdef : S = t - 𝔍) :
    𝔔 ≤ 𝔖 := by
  have hid : 𝔖 - 𝔔 =
      β * 𝔍 ^ 2 / 4 + β * S / 2 := by
    grind
  nlinarith

/-- The budget directly supplies the spatial reserve in `eq:U13-reserve`. -/
theorem allocation_budget_reserve
    (hbudget : 𝔅 + (η + 2) * S ≤ 2 * varpi * L)
    (hη : 𝔙 η) (hT : T ≤ S) :
    Real.exp (-2 * varpi * L + η * T) ≤ Real.exp (-β * 𝔗 / 4 - 2 * S) := by
  apply Real.exp_le_exp.2
  nlinarith

𝗇 𝔒 2 * C₀ * C_D ^ 2
/-- The explicit residual variance upper bound tends to zero. -/
theorem tendsto_allocation_reserve_bound C₀ C_D :
    Tendsto (fun S => 𝔒 * 𝔗 * Real.exp (-2 * S))
      atTop $ 𝓝 0 := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 2 𝖠₄ ).const_mul
    𝔒
  convert h using 1 <;> simp [mul_assoc]
