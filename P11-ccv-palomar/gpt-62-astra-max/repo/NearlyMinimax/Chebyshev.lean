module

public import NearlyMinimax.MomentRules
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

noncomputable section

namespace NearlyMinimax

open Polynomial Finset

variable {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)

/-- The nonnegative real inverse hyperbolic cosine on `[1,∞)`. -/
def exteriorTau : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

/-- The exterior Chebyshev exponent after affine rescaling of `[a,b]`. -/
abbrev intervalExteriorTau (a b : ℝ) := exteriorTau ((a + b) / (b - a))

theorem cosh_exteriorTau {x : ℝ} (hx : 1 ≤ x) : Real.cosh (exteriorTau x) = x := by
  have hs : 0 ≤ x ^ 2 - 1 := by nlinarith
  let root := Real.sqrt (x ^ 2 - 1)
  have hp : 0 < x + root := by positivity
  have hsq := Real.sq_sqrt hs
  have hinv : (x + root)⁻¹ = x - root := by
    field_simp
    nlinarith
  rw [exteriorTau, Real.cosh_log hp, hinv]
  ring

theorem exteriorTau_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ exteriorTau x := by
  apply Real.log_nonneg
  exact hx.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))

include ha hab in
/-- The two forms of the paper's exterior exponent coincide. -/
theorem exteriorTau_sqrt_ratio :
    intervalExteriorTau a b =
      Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) := by
  have hb  := ha.trans hab
  have hsqa  := Real.sq_sqrt (le_of_lt ha)
  have hsqb  := Real.sq_sqrt (le_of_lt hb)
  have hroot : Real.sqrt (((a + b) / (b - a)) ^ 2 - 1) =
      2 * Real.sqrt a * Real.sqrt b / (b - a) := by
    have hr : 0 ≤ 2 * Real.sqrt a * Real.sqrt b / (b - a) := by positivity
    rw [← Real.sqrt_sq hr]
    grind
  rw [intervalExteriorTau, exteriorTau, hroot]
  grind

include ha hab in
/-- Exponential decay parameter corresponding to the paper's exponent. -/
theorem exp_neg_exteriorTau :
    Real.exp (-intervalExteriorTau a b) =
      (Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a) := by
  have hslt  := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hratio : 0 < (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) := by
    positivity
  rw [exteriorTau_sqrt_ratio ha hab, Real.exp_neg, Real.exp_log hratio, inv_div]

/-- A Chebyshev polynomial has degree at most its nonnegative index. -/
theorem chebyshev_natDegree_le :
    (Polynomial.Chebyshev.T ℝ n).natDegree ≤ n := by
  simp

/-- Reflection parity of the Chebyshev polynomials. -/
theorem chebyshev_eval_neg :
    (Polynomial.Chebyshev.T ℝ n).eval (-x) =
      (-1) ^ n * (Polynomial.Chebyshev.T ℝ n).eval x := by
  simp

/-- The standard Chebyshev–Lobatto nodes, in decreasing order. -/
def lobattoNode {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  Real.cos (i.val * Real.pi / n)

private theorem lobatto_angle_mem {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    i.val * Real.pi / n ∈ Set.Icc 0 Real.pi := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_iff₀ hnp).mpr
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast (show i.val ≤ n by omega)
    nlinarith [Real.pi_pos]

include hn in
theorem lobattoNode_strictAnti : StrictAnti (lobattoNode (n := n)) := by
  intro i j hij
  apply Real.strictAntiOn_cos (lobatto_angle_mem hn i) (lobatto_angle_mem hn j)
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hn)
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast hij

/-- The exterior nodes appearing in the finite moment rule. -/
def exteriorNode (a b : ℝ) {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  (a + b) / 2 + ((b - a) / 2) * lobattoNode i

include hab hn in
theorem exteriorNode_strictAnti :
    StrictAnti (exteriorNode a b (n := n)) := by
  intro i j hij
  dsimp [exteriorNode]
  have h := mul_lt_mul_of_pos_left (lobattoNode_strictAnti n hn hij)
    (by linarith : 0 < (b - a) / 2)
  linarith

theorem exteriorNode_mem (hab : a ≤ b) {n : ℕ} (i : Fin (n + 1)) :
    exteriorNode a b i ∈ Set.Icc a b := by
  dsimp [exteriorNode, lobattoNode]
  constructor <;> nlinarith [Real.cos_le_one (i.val * Real.pi / n),
    Real.neg_one_le_cos (i.val * Real.pi / n)]

/-- The explicit cardinal weights from the paper. -/
def exteriorWeight (a b : ℝ) {n : ℕ} (i : Fin (n + 1)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    exteriorNode a b j / (exteriorNode a b j - exteriorNode a b i)

include hab in
/-- Chebyshev–Lobatto exterior cardinal weights reproduce evaluation at zero through degree `n`. -/
theorem exterior_rule_exact {n : ℕ} (hn : 1 ≤ n)
    {P : ℝ[X]} (hP : P.degree ≤ n) :
    (∑ i : Fin (n + 1), exteriorWeight a b i * P.eval (exteriorNode a b i)) =
      P.eval 0 := by
  apply exterior_product_rule_exact
    (exteriorNode_strictAnti hab n hn).injective.injOn
  simpa using hP.trans_lt (show (n : WithBot ℕ) < n + 1 by exact_mod_cast Nat.lt_succ_self n)

private theorem positive_decreasing_weight_sign (z : Fin (n + 1) → ℝ)
    (hz : ∀ i, 0 < z i) (hanti : StrictAnti z) (i : Fin (n + 1)) :
    (∏ j ∈ Finset.univ.erase i, z j / (z j - z i)) =
      (-1) ^ (n - i.val) *
        |∏ j ∈ Finset.univ.erase i, z j / (z j - z i)| := by
  let S := Finset.univ.erase i
  have hf (j : Fin (n + 1)) (hj : j ∈ S) :
      z j / (z j - z i) = (if i < j then (-1) else 1) * |z j / (z j - z i)| := by
    have hji  := (Finset.mem_erase.mp hj).1
    by_cases hij : i < j
    · rw [if_pos hij, abs_of_neg (div_neg_of_pos_of_neg (hz j)
        (sub_neg.mpr (hanti hij)))]
      ring
    · have hji'  := lt_of_le_of_ne (le_of_not_gt hij) hji
      rw [if_neg hij, abs_of_pos (by bound), one_mul]
  have hs : (∏ j ∈ S, if i < j then (-1) else 1) = (-1 : ℝ) ^ (n - i.val) := by
    rw [Finset.prod_ite]
    simp
    have hset : S.filter (fun j => i < j) = Finset.Ioi i := by
      ext j
      simp [S, Finset.mem_Ioi]
      omega
    rw [hset, Fin.card_Ioi]
    congr 1
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf

/-- The Chebyshev polynomial rescaled to the interval `[a,b]`. -/
def intervalChebyshev (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ n).comp
    ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹))

theorem intervalChebyshev_degree (a b : ℝ) (n : ℕ) :
    (intervalChebyshev a b n).degree ≤ n := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_comp_le.trans
  have hd : ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹)).natDegree ≤ 1 := by
    apply Polynomial.natDegree_mul_le.trans
    simp
  exact (Nat.mul_le_mul (chebyshev_natDegree_le n) hd).trans (by simp)

theorem intervalChebyshev_at_node (a b : ℝ) (hab : a < b) {n : ℕ}
    (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (intervalChebyshev a b n).eval (exteriorNode a b i) = (-1) ^ i.val := by
  have hba : b - a ≠ 0 := by linarith
  have hnorm : (exteriorNode a b i - (a + b) / 2) * ((b - a) / 2)⁻¹ =
      lobattoNode i := by
    dsimp [exteriorNode]
    field_simp [hba]
    ring
  simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
  rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
  simp
  have hang : n * (i.val * Real.pi / n) = i.val * Real.pi := by
    field_simp
  rw [hang]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

include ha hab in
/-- The exterior weight signs alternate along the Lobatto nodes. -/
theorem exterior_weight_sign {n : ℕ}
    (hn : 1 ≤ n) (i : Fin (n + 1)) :
    exteriorWeight a b i = (-1) ^ (n - i.val) * |exteriorWeight a b i| := by
  apply positive_decreasing_weight_sign
  · intro j
    exact ha.trans_le (exteriorNode_mem (le_of_lt hab) j).1
  · exact exteriorNode_strictAnti hab n hn

include ha hab hn in
/-- The exact atom variation of the exterior finite rule, expressed through inverse cosh. -/
theorem exterior_rule_variation :
    (∑ i : Fin (n + 1), |exteriorWeight a b i|) =
      Real.cosh (n * intervalExteriorTau a b) := by
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hnorm : (0 - (a + b) / 2) * ((b - a) / 2)⁻¹ = -((a + b) / (b - a)) := by
    field_simp
    ring
  have heval : (intervalChebyshev a b n).eval 0 =
      (-1) ^ n * Real.cosh (n * intervalExteriorTau a b) := by
    simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
    rw [chebyshev_eval_neg]
    congr 1
    calc
      _ = (Polynomial.Chebyshev.T ℝ n).eval
        (Real.cosh (intervalExteriorTau a b)) := by
          rw [cosh_exteriorTau hratio]
      _ = _ := by
        simp
  have hexact := exterior_rule_exact hab hn
    (intervalChebyshev_degree a b n)
  have hnode : ∀ i : Fin (n + 1), exteriorWeight a b i *
      (intervalChebyshev a b n).eval (exteriorNode a b i) =
        (-1) ^ n * |exteriorWeight a b i| := by
    intro i
    rw [intervalChebyshev_at_node a b hab hn i]
    nth_rw 1 [exterior_weight_sign ha hab hn i]
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by omega)]
  simp_rw [hnode] at hexact
  rw [← Finset.mul_sum, heval] at hexact
  exact mul_left_cancel₀ (by positivity) hexact

include ha hab hn in
/-- The exterior rule's variation has the exponential bound used in local packet costs. -/
theorem exterior_rule_variation_le_exp :
    (∑ i : Fin (n + 1), |exteriorWeight a b i|) ≤
      Real.exp (n * intervalExteriorTau a b) := by
  rw [exterior_rule_variation ha hab n hn, Real.cosh_eq]
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have ht  := mul_nonneg (Nat.cast_nonneg n) (exteriorTau_nonneg hratio)
  have he := Real.exp_le_exp.mpr (show
      -(n * intervalExteriorTau a b) ≤
      n * intervalExteriorTau a b by linarith)
  linarith

end NearlyMinimax
