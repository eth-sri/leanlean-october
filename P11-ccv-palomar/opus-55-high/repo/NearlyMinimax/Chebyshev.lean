module

public import NearlyMinimax.MomentRules
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import RoughRegime.Macro

𝗎



open Polynomial Finset

𝗇 𝔎 x ^ 2 - 1
𝗇 𝔢 x + Real.sqrt 𝔎
/-- The nonnegative real inverse hyperbolic cosine on `[1,∞)`. -/
def exteriorTau (x : ℝ) : ℝ := Real.log 𝔢

theorem cosh_exteriorTau x (hx : 1 ≤ x) : Real.cosh (exteriorTau x) = x := by
  have hs : 0 ≤ 𝔎 := by nlinarith
  have hsq := Real.sq_sqrt hs
  have hinv : 𝔢⁻¹ = x - Real.sqrt 𝔎 := by
    field_simp
    nlinarith
  rw [exteriorTau, Real.cosh_log $ by positivity , hinv]
  ring

theorem exteriorTau_nonneg x (hx : 1 ≤ x) : 0 ≤ exteriorTau x := by
  apply Real.log_nonneg
  exact hx.trans $ le_add_of_nonneg_right $ Real.sqrt_nonneg _

𝗇 𝔞 b - a
𝗇 𝔦 a + b
𝗇 𝔄 𝔦 / 𝔞
𝗇 𝔤 Real.sqrt b + Real.sqrt a
𝗇 𝔥 Real.sqrt b - Real.sqrt a
𝗇 𝔏 𝔤 / 𝔥
𝗇 𝔐 a < b
𝗇 𝔔 2 * Real.sqrt a * Real.sqrt b / 𝔞
𝗇 𝔡 0 < a
/-- The two forms of the paper's exterior exponent coincide. -/
theorem exteriorTau_sqrt_ratio a b (ha : 𝔡) (hab : 𝔐) :
    exteriorTau 𝔄 =
      Real.log 𝔏 := by
  have hroot : Real.sqrt (𝔄 ^ 2 - 1) =
      𝔔 := by
    have hr : 0 ≤ 𝔔 := by positivity
    rw [← Real.sqrt_sq hr]
    grind
  rw [exteriorTau, hroot]
  grind

𝗃 𝔠 ἀ a b
/-- Exponential decay parameter corresponding to the paper's exponent. -/
theorem exp_neg_exteriorTau a b (ha : 𝔡) (hab : 𝔐) :
    Real.exp (-exteriorTau 𝔄) =
      𝔥 / 𝔤 := by
  have hslt := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hratio : 0 < 𝔏 := by
    positivity
  rw [𝔠 exteriorTau_sqrt_ratio ha hab, Real.exp_neg, Real.exp_log hratio, inv_div]

/-- A Chebyshev polynomial has degree at most its nonnegative index. -/
theorem chebyshev_natDegree_le (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ n).natDegree ≤ n := by
  simp

𝗃 𝔩 (-1) ^ ἀ
𝗇 𝔙 𝔩 n
/-- Reflection parity of the Chebyshev polynomials. -/
theorem chebyshev_eval_neg (n : ℕ) x :
    (Polynomial.Chebyshev.T ℝ n).eval (-x) =
      𝔙 * (Polynomial.Chebyshev.T ℝ n).eval x := by
  simp

𝗇 𝔅 Fin $ n + 1
𝗇 𝔚 (i.val : ℝ) * Real.pi / n
/-- The standard Chebyshev–Lobatto nodes, in decreasing order. -/
def lobattoNode (n : ℕ) (i : 𝔅) : ℝ :=
  Real.cos 𝔚

𝗇 𝔑 1 ≤ n
private theorem lobatto_angle_mem (n : ℕ) (hn : 𝔑) (i : 𝔅) :
    𝔚 ∈ Set.Icc 0 Real.pi := by
  constructor
  · positivity
  · apply (div_le_iff₀ $ by exact_mod_cast hn ).mpr
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast by omega
    nlinarith [Real.pi_pos]

theorem lobattoNode_strictAnti n (hn : 𝔑) : StrictAnti $ lobattoNode n := by
  intro i j hij
  apply Real.strictAntiOn_cos (lobatto_angle_mem n hn i) $ lobatto_angle_mem n hn j
  apply div_lt_div_of_pos_right _ $ by exact_mod_cast hn
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast hij

𝗇 𝔇 𝔞 / 2
𝗇 𝔈 𝔦 / 2
/-- The exterior nodes appearing in the finite moment rule. -/
def exteriorNode (a b : ℝ) (n : ℕ) (i : 𝔅) : ℝ :=
  𝔈 + 𝔇 * lobattoNode n i

𝗇 𝔟 𝔠 exteriorNode n
theorem exteriorNode_strictAnti a b (hab : 𝔐) n (hn : 𝔑) :
    StrictAnti 𝔟 := by
  intro i j hij
  dsimp [exteriorNode]
  have h := mul_lt_mul_of_pos_left (lobattoNode_strictAnti n hn hij)
    (by linarith : 0 < 𝔇)
  linarith

𝗇 𝔊 𝔠 exteriorNode n i
𝗇 𝔒 i.val * Real.pi / n
theorem exteriorNode_mem a b (hab : a ≤ b) n i :
    𝔊 ∈ 𝔠 Set.Icc := by
  dsimp [exteriorNode, lobattoNode]
  constructor <;> nlinarith [Real.cos_le_one 𝔒,
    Real.neg_one_le_cos 𝔒]

𝗇 𝔛 (Finset.univ : Finset 𝔅).erase i
/-- The explicit cardinal weights from the paper. -/
def exteriorWeight (a b : ℝ) (n : ℕ) (i : 𝔅) : ℝ :=
  ∏ j ∈ 𝔛,
    𝔟 j / (𝔟 j - 𝔊)

𝗇 𝔍 𝔠 exteriorWeight n i
𝗃 𝔪 𝔠 ἀ hab n hn
/-- Chebyshev–Lobatto exterior cardinal weights reproduce evaluation at zero through degree `n`. -/
theorem exterior_rule_exact a b (hab : 𝔐) (n : ℕ) (hn : 𝔑)
    (P : ℝ[X]) (hP : P.degree ≤ n) :
     ∑ i : 𝔅, 𝔍 * P.eval 𝔊 =
      P.eval 0 := by
  apply exterior_product_rule_exact Finset.univ 𝔟
    (𝔪 exteriorNode_strictAnti).injective.injOn
  simpa using hP.trans_lt $ by exact_mod_cast Nat.lt_succ_self n

𝗇 𝔉 z j / (z j - z i)
𝗇 𝔖 if i < j then -1 else 1
𝗇 𝔧 n - i.val
𝗇 𝔗 (-1 : ℝ) ^ 𝔧
𝗇 𝔣 ∏ j ∈ 𝔛, 𝔉
private theorem positive_decreasing_weight_sign (n : ℕ) (z : 𝔅 → ℝ)
    (hz : ∀ i, 0 < z i) (hanti : StrictAnti z) (i : 𝔅) :
    𝔣 =
      𝔗 *
        |𝔣| := by
  let S := Finset.univ.erase i
  have hf j (hj : j ∈ S) :
      𝔉 = 𝔖 * |𝔉| := by
    by_cases hij : i < j
    · rw [if_pos hij, abs_of_neg $ div_neg_of_pos_of_neg (hz j)
        $ sub_neg.mpr $ hanti hij ]
      ring
    · have hji' := lt_of_le_of_ne (le_of_not_gt hij) (Finset.mem_erase.mp hj).1
      rw [if_neg hij, abs_of_pos $ div_pos (hz j) $ sub_pos.mpr $ hanti hji' , one_mul]
  have hs : ∏ j ∈ S, 𝔖 = 𝔗 := by
    rw [Finset.prod_ite]
    have hset : S.filter fun j => i < j = Finset.Ioi i := by
      grind
    simp_all
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  grind

𝗇 𝔨 𝔇⁻¹
𝗇 𝔜 (X - C 𝔈) * C 𝔨
/-- The Chebyshev polynomial rescaled to the interval `[a,b]`. -/
def intervalChebyshev (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
    𝔜

𝗇 𝔓 𝔠 intervalChebyshev n
theorem intervalChebyshev_degree a b n :
    (𝔓).degree ≤ n := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_comp_le.trans
  have hd : (𝔜).natDegree ≤ 1 := by
    apply Polynomial.natDegree_mul_le.trans
    simp
  exact (Nat.mul_le_mul (chebyshev_natDegree_le n) hd).trans $ by simp

theorem intervalChebyshev_at_node a b (hab : 𝔐) n
    (hn : 𝔑) i :
    (𝔓).eval 𝔊 = 𝔩 i.val := by
  have hnorm : (𝔊 - 𝔈) * 𝔨 =
      lobattoNode n i := by
    dsimp [exteriorNode]
    grind
  simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
  rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
  simp
  have hang : n * 𝔒 = i.val * Real.pi := by
    field_simp
  rw [hang]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

/-- The exterior weight signs alternate along the Lobatto nodes. -/
theorem exterior_weight_sign a b (ha : 𝔡) (hab : 𝔐) n
    (hn : 𝔑) i :
    𝔍 = 𝔩 𝔧 * |𝔍| := by
  apply positive_decreasing_weight_sign
  · intro j
    exact ha.trans_le (𝔠 exteriorNode_mem (le_of_lt hab) n j).1
  · exact 𝔪 exteriorNode_strictAnti

𝗇 𝔘 n * exteriorTau 𝔄
/-- The exact atom variation of the exterior finite rule, expressed through inverse cosh. -/
theorem exterior_rule_variation a b (ha : 𝔡) (hab : 𝔐) n
    (hn : 𝔑) :
     ∑ i : 𝔅, |𝔍| =
      Real.cosh 𝔘 := by
  have hratio : 1 ≤ 𝔄 := by
    apply (le_div_iff₀ $ by linarith ).mpr
    linarith
  have hnorm : (0 - 𝔈) * 𝔨 = -𝔄 := by
    field_simp
    ring
  have heval : (𝔓).eval 0 =
      𝔙 * Real.cosh 𝔘 := by
    simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
    rw [chebyshev_eval_neg]
    congr 1
    calc
      _ = (Polynomial.Chebyshev.T ℝ n).eval
        (Real.cosh $ exteriorTau 𝔄 ) := by
          rw [cosh_exteriorTau _ hratio]
      _ = _ := by
        simp
  have hexact := 𝔪 exterior_rule_exact 𝔓
    $ 𝔠 intervalChebyshev_degree n
  have hnode : ∀ i , 𝔍 *
      (𝔓).eval 𝔊 =
        𝔙 * |𝔍| := by
    intro i
    rw [𝔪 intervalChebyshev_at_node i]
    nth_rw 1 [𝔠 exterior_weight_sign ha hab n hn i]
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel $ by omega ]
  simp_rw [hnode] at hexact
  rw [← Finset.mul_sum, heval] at hexact
  simp_all

/-- The exterior rule's variation has the exponential bound used in local packet costs. -/
theorem exterior_rule_variation_le_exp a b (ha : 𝔡) (hab : 𝔐)
    n (hn : 𝔑) :
     ∑ i : 𝔅, |𝔍| ≤
      Real.exp 𝔘 := by
  rw [𝔠 exterior_rule_variation ha hab n hn, Real.cosh_eq]
  have hratio : 1 ≤ 𝔄 := by
    apply (le_div_iff₀ $ by linarith ).mpr
    linarith
  have ht := mul_nonneg (Nat.cast_nonneg n) $ exteriorTau_nonneg _ hratio
  have he := Real.exp_le_exp.mpr $ show
      -𝔘 ≤
      𝔘 by linarith
  linarith
