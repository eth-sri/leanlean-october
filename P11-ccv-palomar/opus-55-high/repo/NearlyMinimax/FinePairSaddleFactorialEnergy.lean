module

public import NearlyMinimax.FinePairFactorialEnergy
public import NearlyMinimax.LowerAliasScale
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual fine-pair alias cutoff loses a fixed exp(L M), which is
absorbed into the factorial-tail constant before the saddle shift is chosen. -/
𝚪
𝚨
𝚩

𝗇 𝔄 N^(4-𝙊)
𝗇 𝔅 𝗗₁
𝗇 𝔈 ell=𝗐
𝗇 𝔐 𝗦
theorem fine_pair_alias_cutoff_inverse {d : ℕ} (hd : 4 ≤ d)
    {N ell c0 D } (hN : 𝘹) (hell : 𝔈) :
    1/ell^𝔅 = 𝔄*Real.exp (c0*D*𝔅) := by
  have hnat : ((𝔅 : ℕ) : ℝ) = 𝔅 := by
    simp_all
  have hpow : 𝔄 = (N^𝔅)⁻¹ := by
    rw [show 𝔐-d = -𝔅 by ring, Real.rpow_neg hN.le,
      ← hnat, Real.rpow_natCast]
  rw [hell, mul_pow, ← Real.exp_nat_mul, hpow, one_div, mul_inv_rev, ← Real.exp_neg,
    mul_comm $ Real.exp _ ]
  grind

def finePairSaddleAliasExponent (d : ℕ) (c0 K : ℝ) : ℝ :=
  2*c0+c0*K*(𝙊-4)

𝗇 𝔒 finePairSaddleAliasExponent d c0 K
𝗇 𝔇 Real.exp $ 𝔒*M
𝗃 𝔗 0 ≤ ἀ
theorem fine_pair_alias_cutoff_scale_le {d M : ℕ} (hd : 4 ≤ d)
    {N ell tau c0 D K } (hN : 𝘹) (hell : 𝔈)
    (hc0 : 𝔗 c0) (hK : 𝔗 K) (htau : tau ≤ c0) (hD : 𝚋₁) :
    Real.exp 𝙹₁/ell^𝔅 ≤
      𝔄*𝔇 := by
  rw [div_eq_mul_inv, ← one_div, fine_pair_alias_cutoff_inverse hd hN hell]
  rw [← mul_assoc, mul_comm (Real.exp _) $ N^_ , mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ $ Real.rpow_nonneg hN.le _
  apply Real.exp_le_exp.mpr
  have hdR : 𝔐 ≤ d := by exact_mod_cast hd
  have hT := mul_le_mul_of_nonneg_right htau (by positivity : 0 ≤ 𝙉*M)
  have hDK := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ c0*𝔅)
  unfold finePairSaddleAliasExponent
  linarith

𝗃 𝔔 ἀ d q aD bD C a rho c0
𝗇 𝔍 𝔔 finePairUniformSpatialPrefactor * 6
𝗇 𝔎 finePairAliasGeometricBase d bD*2^8
def finePairSaddleAliasFactorialConstant (d q : ℕ) (aD bD C a rho c0 K Cs : ℝ) : ℝ :=
  aliasTailConstant
    (𝔍*𝙉^d*spatialInverseFourConstant d)
    Cs 𝔎 𝔒

𝗇 𝔓 A*finePairAliasGeometricBase d bD^n
𝗇 𝔉 𝔓*n^8*𝗸
𝗇 𝔊 𝖦₁+j
𝗇 𝔏 𝔔 finePairSaddleAliasFactorialConstant K Cs
𝗇 𝔑 𝗸*𝔄
𝗃 𝔖 finePairAliasActionSpatialBudget d ἀ M q ad bd C a rho eta ell
theorem finite_fine_pair_saddle_alias_budget_le {d } (hd : 4 ≤ d)
    {aD bD ad bd c0 K : ℝ} (haD : 𝘗₂) (ha : aD ≤ ad) (hb : bd ≤ bD)
    (hab : 𝖽) (htau : exteriorTau 𝙻 ≤ c0)
    (hc0 : 𝔗 c0) (hK : 𝔗 K) (M D q J : ℕ)
    C a rho eta ell N Cs mu (hN : 𝘹)
    (hell : 𝔈) (hD : 𝚋₁)
    (hCs : 𝔗 Cs) (hmu : 𝔗 mu) (hmu1 : 𝗦₁) :
     ∑ j ∈ Finset.range J, poissonCountWeight 𝖫₂ 𝔊 *
      𝔖 𝔊 ≤
      𝔏 *
        𝔑 *
          poissonCountWeight (𝔏*mu) 𝖦₁ := by
  let A := 𝔍*𝗝*spatialInverseFourConstant d
  have hA : 𝔗 A := by
    positivity [𝔔 finePairUniformSpatialPrefactor_nonneg,
      spatialInverseFourConstant_nonneg d]
  have hBase := finePairAliasGeometricBase_nonneg d bD
  have hL : 𝔗 𝔒 := by
    unfold finePairSaddleAliasExponent
    have hdR : 𝔐 ≤ d := by exact_mod_cast hd
    positivity
  apply finite_alias_energy_tail_le hA  𝖠₃  hCs
     𝖠₃  hL
    hmu hmu1 M J fun n => 𝔖 n
  intro j _
  let n := 𝔊
  have h := finePairAliasActionSpatialBudget_uniform_geometric_le haD ha hb hab htau d n M q C a rho eta ell $ by rw [hell]; positivity
  have hm := mul_le_mul_of_nonneg_left (fine_pair_alias_cutoff_scale_le hd hN hell hc0 hK htau hD)
    (by positivity : 𝔗 𝔉)
  have hm' := mul_le_mul_of_nonneg_right (polynomial_count_factor_le n 8)
    (by positivity : 0 ≤ 𝔓*𝗸*𝔄*
      𝔇)
  apply h.trans
  calc
    _ ≤ 𝔉 *
        (𝔄*𝔇) := by
      convert hm using 1 <;> dsimp [A] <;> ring
    _ ≤ A*𝔑*𝔇*
        𝔎^n := by
      convert hm' using 1 <;> (try rw [mul_pow]) <;> ring
