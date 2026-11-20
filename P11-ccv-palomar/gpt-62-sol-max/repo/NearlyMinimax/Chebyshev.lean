module

public import NearlyMinimax.MomentRules
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

noncomputable section

namespace NearlyMinimax

open Polynomial Finset

/-- The nonnegative real inverse hyperbolic cosine on `[1,∞)`. -/
def exteriorTau (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))

section
variable (x : ℝ) (hx : 1 ≤ x)
include hx

theorem cosh_exteriorTau : Real.cosh (exteriorTau x) = x := Real.cosh_arcosh hx

theorem exteriorTau_nonneg : 0 ≤ exteriorTau x := Real.arcosh_nonneg hx

end

theorem exteriorTau_interval_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    0 ≤ exteriorTau ((a+b)/(b-a)) :=
  exteriorTau_nonneg _ ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  linarith only [Real.cosh_add_sinh (x := x), Real.sinh_nonneg_iff.mpr hx]

section
variable (a b : ℝ) (ha : 0 < a) (hab : a < b)
include ha hab

/-- The two forms of the paper's exterior exponent coincide. -/
theorem exteriorTau_sqrt_ratio :
    exteriorTau ((a + b) / (b - a)) =
      Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) := by
  have hb := ha.trans hab
  have hsqa := Real.sq_sqrt (le_of_lt ha)
  have hsqb := Real.sq_sqrt (le_of_lt hb)
  have hslt := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hba : b - a ≠ 0 := by linarith
  have hsminus : Real.sqrt b - Real.sqrt a ≠ 0 := by linarith
  have hroot : Real.sqrt (((a + b) / (b - a)) ^ 2 - 1) =
      2 * Real.sqrt a * Real.sqrt b / (b - a) := by
    have hr : 0 ≤ 2 * Real.sqrt a * Real.sqrt b / (b - a) := by positivity
    rw [← Real.sqrt_sq hr] <;> grind
  rw [exteriorTau, hroot]
  grind

/-- Exponential decay parameter corresponding to the paper's exponent. -/
theorem exp_neg_exteriorTau :
    Real.exp (-exteriorTau ((a + b) / (b - a))) =
      (Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a) := by
  have hslt := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have hratio : 0 < (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) := by
    positivity
  rw [exteriorTau_sqrt_ratio a b ha hab, Real.exp_neg, Real.exp_log hratio, inv_div]

end

section
variable (n : ℕ)

/-- A Chebyshev polynomial has degree at most its nonnegative index. -/
theorem chebyshev_natDegree_le :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).natDegree ≤ n := by
  simp

/-- Reflection parity of the Chebyshev polynomials. -/
theorem chebyshev_eval_neg (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (-x) =
      (-1 : ℝ) ^ n * (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x := by
  simp_all

end

/-- The standard Chebyshev–Lobatto nodes, in decreasing order. -/
def lobattoNode (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Real.cos ((i.val : ℝ) * Real.pi / n)

section
variable (n : ℕ) (hn : 1 ≤ n)
include hn

private theorem lobatto_angle_mem (i : Fin (n + 1)) :
    (i.val : ℝ) * Real.pi / n ∈ Set.Icc 0 Real.pi := by
  have hnp : (0 : ℝ) < n := by positivity
  constructor
  · positivity
  · apply (div_le_iff₀ hnp).mpr
    have hi : (i.val : ℝ) ≤ n := by exact_mod_cast (show i.val ≤ n by omega)
    nlinarith [Real.pi_pos]

theorem lobattoNode_strictAnti : StrictAnti (lobattoNode n) := by
  intro i j hij
  apply Real.strictAntiOn_cos (lobatto_angle_mem n hn i) (lobatto_angle_mem n hn j)
  apply div_lt_div_of_pos_right _ (by positivity : (0 : ℝ) < n)
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  simp_all

end

/-- The exterior nodes appearing in the finite moment rule. -/
def exteriorNode (a b : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  (a + b) / 2 + ((b - a) / 2) * lobattoNode n i

section
variable (a b : ℝ)

theorem exteriorNode_strictAnti (hab : a < b) (n : ℕ) (hn : 1 ≤ n) :
    StrictAnti (exteriorNode a b n) := by
  intro i j hij
  dsimp [exteriorNode]
  have h := mul_lt_mul_of_pos_left (lobattoNode_strictAnti n hn hij)
    (by linarith : (0 : ℝ) < (b - a) / 2)
  linarith

theorem exteriorNode_mem (hab : a ≤ b) (n : ℕ) (i : Fin (n + 1)) :
    exteriorNode a b n i ∈ Set.Icc a b := by
  dsimp [exteriorNode, lobattoNode]
  constructor <;> nlinarith [Real.cos_le_one ((i.val : ℝ) * Real.pi / n),
    Real.neg_one_le_cos ((i.val : ℝ) * Real.pi / n)]

end

/-- The explicit cardinal weights from the paper. -/
def exteriorWeight (a b : ℝ) (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
    exteriorNode a b n j / (exteriorNode a b n j - exteriorNode a b n i)

/-- Chebyshev–Lobatto exterior cardinal weights reproduce evaluation at zero through degree `n`. -/
theorem exterior_rule_exact (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n)
    (P : ℝ[X]) (hP : P.degree ≤ n) :
    (∑ i : Fin (n + 1), exteriorWeight a b n i * P.eval (exteriorNode a b n i)) =
      P.eval 0 := by
  apply exterior_product_rule_exact Finset.univ (exteriorNode a b n)
    (exteriorNode_strictAnti a b hab n hn).injective.injOn
  simpa using hP.trans_lt (show (n : WithBot ℕ) < n + 1 by exact_mod_cast Nat.lt_succ_self n)

/-- The sign of a finite product is determined by the count of negative factors.
Zero factors may be assigned to either sign class. -/
theorem signed_prod_abs {ι : Type*} (s : Finset ι) (f : ι → ℝ) (P : ι → Prop)
    [DecidablePred P] (h : ∀ j ∈ s, if P j then f j ≤ 0 else 0 ≤ f j) :
    (∏ j ∈ s, f j) = (-1 : ℝ) ^ (s.filter P).card * |∏ j ∈ s, f j| := by
  have hs : (∏ j ∈ s, if P j then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (s.filter P).card := by
    rw [Finset.prod_ite]
    simp
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hj' := h j hj
  split_ifs at hj' ⊢ <;> simp [abs_of_nonpos, abs_of_nonneg, *]

private theorem positive_decreasing_weight_sign (n : ℕ) (z : Fin (n + 1) → ℝ)
    (hz : ∀ i, 0 < z i) (hanti : StrictAnti z) (i : Fin (n + 1)) :
    (∏ j ∈ Finset.univ.erase i, z j / (z j - z i)) =
      (-1 : ℝ) ^ (n - i.val) * |∏ j ∈ Finset.univ.erase i, z j / (z j - z i)| := by
  have hs : (Finset.univ.erase i).filter (i < ·) = Finset.Ioi i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Ioi]
    omega
  rw [← show (Finset.Ioi i).card = n - i.val by simp [Fin.card_Ioi], ← hs]
  apply signed_prod_abs
  intro j _
  split_ifs with h
  · exact (div_neg_of_pos_of_neg (hz j) (sub_neg.mpr (hanti h))).le
  · exact div_nonneg (hz j).le (sub_nonneg.mpr (hanti.antitone (le_of_not_gt h)))

/-- The Chebyshev polynomial rescaled to the interval `[a,b]`. -/
def intervalChebyshev (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (n : ℤ)).comp
    ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹))

section
variable (a b : ℝ)

theorem intervalChebyshev_degree (n : ℕ) :
    (intervalChebyshev a b n).degree ≤ n := by
  apply Polynomial.degree_le_of_natDegree_le
  apply Polynomial.natDegree_comp_le.trans
  have hd : ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹) : ℝ[X]).natDegree ≤ 1 := by
    apply Polynomial.natDegree_mul_le.trans
    simp
  exact (Nat.mul_le_mul (chebyshev_natDegree_le n) hd).trans (by simp)

theorem intervalChebyshev_at_node (hab : a < b) (n : ℕ)
    (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (intervalChebyshev a b n).eval (exteriorNode a b n i) = (-1 : ℝ) ^ i.val := by
  have hba : b - a ≠ 0 := by linarith
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnorm : (exteriorNode a b n i - (a + b) / 2) * ((b - a) / 2)⁻¹ =
      lobattoNode n i := by
    dsimp [exteriorNode]
    field_simp [hba]
    ring
  simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
  rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_natCast]
  have hang : (n : ℝ) * ((i.val : ℝ) * Real.pi / n) = (i.val : ℝ) * Real.pi := by
    field_simp
  rw [hang]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val

section
variable (ha : 0 < a) (hab : a < b) (n : ℕ)
    (hn : 1 ≤ n)
include ha hab hn

/-- The exterior weight signs alternate along the Lobatto nodes. -/
theorem exterior_weight_sign (i : Fin (n + 1)) :
    exteriorWeight a b n i = (-1 : ℝ) ^ (n - i.val) * |exteriorWeight a b n i| := by
  apply positive_decreasing_weight_sign
  · intro j
    exact ha.trans_le (exteriorNode_mem a b (le_of_lt hab) n j).1
  · apply exteriorNode_strictAnti <;> assumption

/-- The exact atom variation of the exterior finite rule, expressed through inverse cosh. -/
theorem exterior_rule_variation :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) =
      Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hba : b - a ≠ 0 := by linarith
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith : 0 < b - a)).mpr
    linarith
  have hnorm : (0 - (a + b) / 2) * ((b - a) / 2)⁻¹ = -((a + b) / (b - a)) := by
    field_simp
    ring
  have heval : (intervalChebyshev a b n).eval 0 =
      (-1 : ℝ) ^ n * Real.cosh ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
    simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
    rw [chebyshev_eval_neg]
    congr 1
    calc
      _ = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval
        (Real.cosh (exteriorTau ((a + b) / (b - a)))) := by
          rw [cosh_exteriorTau _ hratio]
      _ = _ := by
        simp
  have hexact := exterior_rule_exact a b hab n hn (intervalChebyshev a b n)
    (intervalChebyshev_degree a b n)
  have hnode : ∀ i : Fin (n + 1), exteriorWeight a b n i *
      (intervalChebyshev a b n).eval (exteriorNode a b n i) =
        (-1 : ℝ) ^ n * |exteriorWeight a b n i| := by
    intro i
    rw [intervalChebyshev_at_node a b hab n hn i]
    nth_rw 1 [exterior_weight_sign a b ha hab n hn i]
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by omega : i.val ≤ n)]
  simp_rw [hnode] at hexact
  rw [← Finset.mul_sum, heval] at hexact
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hexact

/-- The exterior rule's variation has the exponential bound used in local packet costs. -/
theorem exterior_rule_variation_le_exp :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) ≤
      Real.exp ((n : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  rw [exterior_rule_variation a b ha hab n hn]
  exact cosh_le_exp_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (exteriorTau_interval_nonneg ha.le hab))

end

end

end NearlyMinimax
