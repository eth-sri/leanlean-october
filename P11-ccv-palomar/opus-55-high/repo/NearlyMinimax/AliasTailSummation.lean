module

public import NearlyMinimax.PoissonEnergyBounds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Finite alias factorial tails, including absorption of exp(C*M) into the
fixed factorial-tail constant. This does not enlarge the activity exponent. -/
𝚪
𝚨

𝗃 𝔐 0 ≤ ἀ
theorem poissonCountWeight_mono (hx : 𝔐 x) (hxy : 𝗪₂) k :
    poissonCountWeight x k ≤ poissonCountWeight y k := div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy k) $ Nat.cast_nonneg _

𝗇 𝔒 poissonCountWeight x $ a + j
𝗃 𝔙 ∑ j ∈ Finset.range J, ἀ
theorem finite_poissonCountWeight_tail_le (hx : 𝔐 x) a J :
    𝔙 𝔒 ≤
      Real.exp x * poissonCountWeight x a := by
  have hs : Summable fun j => 𝔒 :=
    (poissonCountWeight_summable x).comp_injective fun _ _ h => Nat.add_left_cancel h
  exact (hs.sum_le_tsum _ fun j _ => poissonCountWeight_nonneg hx _ ).trans
    $ poissonCountWeight_tail_le hx a

𝗇 𝔅 Csharp * C
𝗇 𝔎 A * Real.exp 𝔅
𝗃 𝔚 ἀ * Real.exp L
𝗇 𝔏 𝔚 𝔅
def aliasTailConstant (A Csharp C L : ℝ) : ℝ :=
  1 + 𝔎 + 𝔏

𝗇 𝔈 aliasTailConstant A Csharp C L
theorem aliasTailConstant_ge_one
    (hA : 𝔐 A) (hCs : 𝔐 Csharp) (hC : 𝔐 C) :
    1 ≤ 𝔈 := by
  unfold aliasTailConstant
  have h1 : 𝔐 𝔎 := 𝖠₃
  have h2 : 𝔐 𝔏 := 𝖠₃
  linarith

theorem aliasTailConstant_ge_prefactor
    (hCs : 𝔐 Csharp) (hC : 𝔐 C) :
    𝔎 ≤ 𝔈 := by
  unfold aliasTailConstant
  have h : 𝔐 𝔏 := 𝖠₃
  linarith

theorem aliasTailConstant_ge_base (hA : 𝔐 A) :
    𝔏 ≤ 𝔈 := by
  unfold aliasTailConstant
  bound

𝗇 𝔄 𝖦₁
𝗇 𝔖 L * M
𝗇 𝔉 Real.exp 𝔖
𝗇 𝔓 L * 𝔄
theorem poissonCountWeight_exp_absorption (hx : 𝔐 x) (hL : 𝔐 L) (M : ℕ) :
    𝔉 * poissonCountWeight x 𝔄 ≤
      poissonCountWeight 𝔚 x 𝔄 := by
  have he : 𝔉 ≤ Real.exp 𝔓 := by
    bound
  have h := mul_le_mul_of_nonneg_right he $ poissonCountWeight_nonneg hx 𝔄
  have heq : Real.exp 𝔓 = Real.exp L ^ 𝔄 := by
    rw [← Real.exp_nat_mul]
    grind
  rw [heq] at h
  simpa only [poissonCountWeight, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

𝗇 𝔇 A * P * Real.exp 𝔖
𝗇 𝔊 𝔄 + j
𝗃 𝔗 ἀ * mu
𝗇 𝔍 𝔗 𝔅
𝗇 𝔑 poissonCountWeight 𝔗 Csharp 𝔊 * R 𝔊
𝗇 𝔔 𝔎 * P
𝗃 𝔘 _ ≤ 𝔇 * (Real.exp ἀ * poissonCountWeight 𝔍 𝔄)
/-- Actual count energies may be supplied only on the finite selected tail.
The fixed constant is chosen before M and the number of counted terms. -/
theorem finite_alias_energy_tail_le
    (hA : 𝔐 A) (hP : 𝔐 P) (hCs : 𝔐 Csharp) (hC : 𝔐 C)
    (hL : 𝔐 L) (hmu : 𝔐 mu) (hmu1 : 𝗦₁)
    M J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔊 ≤
      𝔇 * C ^ 𝔊) :
    𝔙 𝔑 ≤
      𝔈 * P *
        poissonCountWeight 𝔗 𝔈 𝔄 := by
  let K := 𝔈
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      𝔑 ≤
      𝔇 * poissonCountWeight 𝔍 𝔊 := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      $ poissonCountWeight_nonneg (mul_nonneg hCs hmu) 𝔊
    convert h using 1 <;> unfold poissonCountWeight <;> rw [mul_pow, mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (by positivity : 𝔐 𝔍) 𝔄 J) (by positivity : 𝔐 𝔇)
  have hbase : 𝔗 𝔏 ≤ 𝔗 K :=
    mul_le_mul_of_nonneg_right (aliasTailConstant_ge_base hA) hmu
  calc
    𝔘 𝔍 := hs.trans hm
    𝔘 𝔅 :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr 𝖥₄ ) $ poissonCountWeight_nonneg  𝖠₃  _ ) 𝖠₃
    _ = 𝔔 *
        (𝔉 * poissonCountWeight 𝔍 𝔄) := 𝖢₃
    _ ≤ 𝔔 *
        poissonCountWeight 𝔚 𝔍 𝔄 :=
      mul_le_mul_of_nonneg_left (poissonCountWeight_exp_absorption  𝖠₃  hL M) 𝖠₃
    _ ≤ K * P * poissonCountWeight 𝔗 K 𝔄 := by
      apply mul_le_mul
        (mul_le_mul_of_nonneg_right (aliasTailConstant_ge_prefactor hCs hC) hP)
        (poissonCountWeight_mono  𝖠₃   𝖡₄  _)
        (poissonCountWeight_nonneg  𝖠₃  _)
        $ mul_nonneg ((by norm_num : 𝙋 ≤ 1).trans $ aliasTailConstant_ge_one hA hCs hC ) hP
    𝘿 := rfl
