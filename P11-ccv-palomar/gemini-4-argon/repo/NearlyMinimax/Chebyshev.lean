module
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin
@[expose] public section
noncomputable section
open Polynomial Finset
namespace NearlyMinimax
section Cardinal
variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
theorem cardinal_coefficient_exact (s : Finset ι) (v )
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) (a ) :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * P.eval (v i)) = P.coeff a := by
  have h := congrArg (fun p => p.coeff a) (Lagrange.eq_interpolate hv hP)
  simp only [Lagrange.interpolate_apply, finset_sum_coeff, coeff_C_mul] at h
  simpa only [mul_comm] using h.symm
theorem cardinal_derivative_exact (s : Finset ι) (v )
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) (x ) :
    (∑ i ∈ s, (Lagrange.basis s v i).derivative.eval x * P.eval (v i)) =
      P.derivative.eval x := by
  have h := congrArg (fun p => p.derivative.eval x)
    (Lagrange.eq_interpolate hv hP)
  simp only [Lagrange.interpolate_apply, derivative_sum, derivative_C_mul,
    eval_finset_sum, eval_mul, eval_C] at h
  simpa only [mul_comm] using h.symm
theorem exterior_product_rule_exact (s : Finset ι) (v )
    (hv : Set.InjOn v s) (P : F[X]) (hP : P.degree < s.card) :
    (∑ i ∈ s, (∏ j ∈ s.erase i, v j / (v j - v i)) * P.eval (v i)) = P.eval 0 := by
  have h_cardinal_evaluation_exact : (∑ i ∈ s, (Lagrange.basis s v i).eval 0 * P.eval (v i)) = P.eval 0 := by
    have h := congrArg (fun p => p.eval 0) (Lagrange.eq_interpolate hv hP)
    simpa only [Lagrange.interpolate_apply, eval_finset_sum, eval_mul, eval_C,
      mul_comm] using h.symm
  have h_cardinal_weight_at_zero (i : ι) : (Lagrange.basis s v i).eval 0 = ∏ j ∈ s.erase i, v j / (v j - v i) := by
    simp only [Lagrange.basis, eval_prod, Lagrange.basisDivisor, eval_mul,
      eval_C, eval_sub, eval_X, zero_sub]
    apply Finset.prod_congr rfl
    intro j hj
    rw [show v i - v j = -(v j - v i) by ring, inv_neg]
    simp [div_eq_mul_inv, mul_comm]
  simpa only [h_cardinal_weight_at_zero] using h_cardinal_evaluation_exact
theorem cardinal_coefficient_monomial (s : Finset ι) (v : ι → F)
    (hv : Set.InjOn v s) (a b : ℕ) (hb : b < s.card) :
    (∑ i ∈ s, (Lagrange.basis s v i).coeff a * (v i) ^ b) =
      if b = a then 1 else 0 := by
  simpa [coeff_X_pow, eq_comm] using cardinal_coefficient_exact s v hv (X ^ b) (by simpa only [degree_X_pow, Nat.cast_withBot] using (WithBot.coe_lt_coe.mpr hb)) a
end Cardinal
def responseNode (q ) (j : Fin (2 * q + 2)) : ℝ :=
  j.val / (2 * q + 1)
theorem responseNode_injective (q ) : Function.Injective (responseNode q) := by
  intro i j hij
  have hn : (2 * q + 1 : ℝ) ≠ 0 := by positivity
  have h : (i.val : ℝ) = j.val := by
    apply (div_left_inj' hn).mp
    simpa [responseNode] using hij
  exact Fin.ext (by exact_mod_cast h)
def responseWeight (q ) (j : Fin (2 * q + 2)) : ℝ :=
  (Lagrange.basis Finset.univ (responseNode q) j).coeff 2
theorem response_rule_moments (q a : ℕ) (ha : a ≤ 2 * q + 1) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * (responseNode q j) ^ a) =
      if a = 2 then 1 else 0 := by
  exact cardinal_coefficient_monomial Finset.univ (responseNode q)
    (responseNode_injective q).injOn 2 a (by simpa using (show a < 2 * q + 2 by omega))
theorem response_rule_exact (q : ℕ) (P : ℝ[X]) (hP : P.degree < 2 * q + 2) :
    (∑ j : Fin (2 * q + 2), responseWeight q j * P.eval (responseNode q j)) =
      P.coeff 2 := by
  exact cardinal_coefficient_exact Finset.univ (responseNode q)
    (responseNode_injective q).injOn P (by simpa using hP) 2
theorem response_zero_mass (q ) :
    (∑ j : Fin (2 * q + 2), responseWeight q j) = 0 := by
  simpa using response_rule_moments q 0 (by omega)
def fairSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem fairSign_abs (b ) : |fairSign b| = 1 := by cases b <;> norm_num [fairSign]
theorem finite_sum_abs_bound {κ : Type*} [Fintype κ] (g b : κ → ℝ)
    (h : ∀ k, |g k| ≤ b k) : |∑ k, g k| ≤ ∑ k, b k := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun k hk => h k))
section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def covarianceAtom (C : ℝ) (i j : ι) (s t : Bool) : ι → ℝ :=
  fun k => (fairSign s * (if i = k then 1 else 0) +
    fairSign t * (if j = k then 1 else 0)) / (2 * C)
def covarianceWeight (C : ℝ) (A : ι → ι → ℝ) (i j : ι) (s t : Bool) : ℝ :=
  C ^ 2 / 2 * A i j * fairSign s * fairSign t
def covarianceAction (C : ℝ) (A : ι → ι → ℝ) (f : (ι → ℝ) → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool,
    covarianceWeight C A i j s t * f (covarianceAtom C i j s t)
theorem sign_mean (C a x y ) :
    (∑ s : Bool, ∑ t : Bool,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        ((fairSign s * x + fairSign t * y) / (2 * C))) = 0 := by
  simp [fairSign]
  ring
theorem sign_second (C a x y u v ) (hC : C ≠ 0) :
    (∑ s : Bool, ∑ t : Bool,
      (C ^ 2 / 2 * a * fairSign s * fairSign t) *
        (((fairSign s * x + fairSign t * y) / (2 * C)) *
          ((fairSign s * u + fairSign t * v) / (2 * C)))) =
      a / 2 * (x * v + y * u) := by
  simp only [Fintype.sum_bool, fairSign, Bool.false_eq_true, ↓reduceIte]
  field_simp
  ring
theorem covarianceAction_add (C A)
    (f g : (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => f x + g x) =
      covarianceAction C A f + covarianceAction C A g := by
  simp only [covarianceAction, mul_add, Finset.sum_add_distrib]
theorem covarianceAction_mul (C a A)
    (f : (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => a * f x) = a * covarianceAction C A f := by
  simp only [covarianceAction, mul_left_comm, Finset.mul_sum]
theorem covarianceAction_sum  (S C)
    (A : ι → ι → ℝ) (f : κ → (ι → ℝ) → ℝ) :
    covarianceAction C A (fun x => ∑ i ∈ S, f i x) =
      ∑ i ∈ S, covarianceAction C A (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [covarianceAction]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [covarianceAction_add, ih]
theorem covariance_zero_mass (C : ℝ) (A : ι → ι → ℝ) :
    covarianceAction C A (fun _ => 1) = 0 := by
  have h_sign_mass (a) : (∑ s : Bool, ∑ t : Bool, C ^ 2 / 2 * a * fairSign s * fairSign t) = 0 := by
    simp [fairSign]
  simp only [covarianceAction, covarianceWeight, mul_one]
  simp_rw [h_sign_mass]
  simp
theorem covariance_zero_mean (C : ℝ) (A : ι → ι → ℝ) (k : ι) :
    covarianceAction C A (fun x => x k) = 0 := by
  simp only [covarianceAction, covarianceWeight, covarianceAtom]
  simp_rw [sign_mean]
  simp
theorem covariance_second_moment_symmetric (C A)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (k l : ι) :
    covarianceAction C A (fun x => x k * x l) = A k l := by
  have h_covariance_second_moment (k : ι) (l : ι) : covarianceAction C A (fun x => x k * x l) = (A k l + A l k) / 2 := by
    simp only [covarianceAction, covarianceWeight, covarianceAtom]
    simp_rw [sign_second C _ _ _ _ _ hC]
    simp [mul_add, Finset.sum_add_distrib, mul_ite]
    ring
  rw [h_covariance_second_moment, hA l k]
  ring
theorem covarianceAtom_mem_ball (C : ℝ) (hC : 0 < C) (i j : ι) (s t : Bool) :
    (∑ k, |covarianceAtom C i j s t k|) ≤ C⁻¹ := by
  have hden : 0 < 2 * C := by positivity
  calc
    (∑ k, |covarianceAtom C i j s t k|) ≤
        ∑ k, (|(fairSign s * (if i = k then 1 else 0))| +
          |(fairSign t * (if j = k then 1 else 0))|) / (2 * C) := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp [covarianceAtom]
      rw [abs_div, abs_of_pos hden]
      exact div_le_div_of_nonneg_right (abs_add_le _ _) (le_of_lt hden)
    _ = C⁻¹ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
      simp [apply_ite abs]
      field_simp
      ring
theorem covariance_weight_variation (C : ℝ) (A : ι → ι → ℝ) :
    (∑ i, ∑ j, ∑ s : Bool, ∑ t : Bool, |covarianceWeight C A i j s t|) =
      2 * C ^ 2 * ∑ i, ∑ j, |A i j| := by
  have hw (i j : ι) (s t : Bool) : |covarianceWeight C A i j s t| = C ^ 2 / 2 * |A i j| := by
    dsimp [covarianceWeight]
    rw [abs_mul, abs_mul, abs_mul, abs_div]
    simp [abs_of_nonneg (sq_nonneg C)]
  simp_rw [hw]
  simp only [Fintype.sum_bool]
  calc
    (∑ i, ∑ j, (C ^ 2 / 2 * |A i j| + C ^ 2 / 2 * |A i j| +
      (C ^ 2 / 2 * |A i j| + C ^ 2 / 2 * |A i j|))) =
      ∑ i, ∑ j, 2 * C ^ 2 * |A i j| := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
    _ = _ := by simp only [Finset.mul_sum]
theorem covarianceAction_abs_le (C B A)
    (f : (ι → ℝ) → ℝ)
    (hf : ∀ i j s t, |f (covarianceAtom C i j s t)| ≤ B) :
    |covarianceAction C A f| ≤ (2 * C ^ 2 * ∑ i, ∑ j, |A i j|) * B := by
  have ht (i j : ι) (s t : Bool) :
      |covarianceWeight C A i j s t * f (covarianceAtom C i j s t)| ≤
        |covarianceWeight C A i j s t| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf i j s t) (abs_nonneg _)
  have h := finite_sum_abs_bound
    (fun i => ∑ (j : ι), ∑ s : Bool, ∑ t : Bool,
      covarianceWeight C A i j s t * f (covarianceAtom C i j s t))
    (fun i => ∑ (j : ι), ∑ s : Bool, ∑ t : Bool, |covarianceWeight C A i j s t| * B)
    (fun i => finite_sum_abs_bound _ _ (fun j =>
      finite_sum_abs_bound _ _ (fun s => finite_sum_abs_bound _ _ (ht i j s))))
  simpa only [covarianceAction, ← Finset.sum_mul, covariance_weight_variation] using h
end Covariance
def exteriorTau (x : ℝ) : ℝ := Real.log (x + Real.sqrt (x ^ 2 - 1))
theorem cosh_exteriorTau (x ) (hx : 1 ≤ x) : Real.cosh (exteriorTau x) = x := by
  have hs : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hp : 0 < x + Real.sqrt (x ^ 2 - 1) := by positivity
  have := Real.sq_sqrt hs
  have hinv : (x + Real.sqrt (x ^ 2 - 1))⁻¹ = x - Real.sqrt (x ^ 2 - 1) := by
    field_simp
    nlinarith
  rw [exteriorTau, Real.cosh_log hp, hinv]
  ring
theorem exteriorTau_nonneg (x ) (hx : 1 ≤ x) : 0 ≤ exteriorTau x := by
  apply Real.log_nonneg
  exact hx.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
theorem exteriorTau_sqrt_ratio (a b ) (ha : 0 < a) (hab : a < b) :
    exteriorTau ((a + b) / (b - a)) =
      Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) := by
  have hb  := ha.trans hab
  have hsqa  := Real.sq_sqrt (le_of_lt ha)
  have hsqb  := Real.sq_sqrt (le_of_lt hb)
  have  := Real.sqrt_pos.mpr ha
  have  := Real.sqrt_pos.mpr hb
  have  := Real.sqrt_lt_sqrt (le_of_lt ha) hab
  have  := sub_pos.mpr hab
  have : b - a ≠ 0 := by linarith
  have : Real.sqrt b - Real.sqrt a ≠ 0 := by linarith
  have : Real.sqrt b + Real.sqrt a ≠ 0 := by positivity
  have hroot : Real.sqrt (((a + b) / (b - a)) ^ 2 - 1) =
      2 * Real.sqrt a * Real.sqrt b / (b - a) := by
    have hr : 0 ≤ 2 * Real.sqrt a * Real.sqrt b / (b - a) := by positivity
    rw [← Real.sqrt_sq hr]
    congr 1
    rw [div_pow, div_pow, mul_pow, mul_pow, hsqa, hsqb]
    field_simp
    ring
  rw [exteriorTau, hroot]
  congr 1
  calc
    (a + b) / (b - a) + 2 * Real.sqrt a * Real.sqrt b / (b - a) =
      (Real.sqrt b + Real.sqrt a) ^ 2 /
        ((Real.sqrt b - Real.sqrt a) * (Real.sqrt b + Real.sqrt a)) := by
          rw [← add_div]
          congr 1 <;> nlinarith
    _ = (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) := by
      field_simp
theorem chebyshev_natDegree_le (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ ↑n).natDegree ≤ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      have he : ((n + 2 : ℕ) : ℤ) = ↑n + 2 := by omega
      have he1 : ((n + 1 : ℕ) : ℤ) = ↑n + 1 := by omega
      rw [he, Polynomial.Chebyshev.T_add_two]
      apply (Polynomial.natDegree_sub_le _ _).trans
      apply max_le
      · have h := Polynomial.natDegree_mul_le
          (p := (2 : ℝ[X]) * X) (q := Polynomial.Chebyshev.T ℝ (↑n + 1))
        have : ((2 : ℝ[X]) * X).natDegree ≤ 1 := by simp
        rw [← he1] at h ⊢
        omega
      · omega
theorem chebyshev_eval_neg (n : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ ↑n).eval (-x) =
      (-1 : ℝ) ^ n * (Polynomial.Chebyshev.T ℝ ↑n).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih0 ih1 =>
      have he : ((n + 2 : ℕ) : ℤ) = ↑n + 2 := by omega
      have he1 : ((n + 1 : ℕ) : ℤ) = ↑n + 1 := by omega
      rw [he, Polynomial.Chebyshev.T_add_two]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, ← he1, ih0, ih1]
      rw [pow_succ, pow_succ]
      ring
def lobattoNode (n ) (i : Fin (n + 1)) : ℝ :=
  Real.cos (i.val * Real.pi / n)
theorem lobattoNode_strictAnti (n ) (hn : 1 ≤ n) : StrictAnti (lobattoNode n) := by
  have h_lobatto_angle_mem (i : Fin (n + 1)) : i.val * Real.pi / n ∈ Set.Icc 0 Real.pi := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
      have : (i.val : ℝ) ≤ n := by exact_mod_cast (show i.val ≤ n by omega)
      nlinarith [Real.pi_pos]
  intro i j hij
  apply Real.strictAntiOn_cos (h_lobatto_angle_mem i) (h_lobatto_angle_mem j)
  apply div_lt_div_of_pos_right _ (by exact_mod_cast hn : (0 : ℝ) < n)
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact_mod_cast hij
def exteriorNode (a b : ℝ) (n ) (i : Fin (n + 1)) : ℝ :=
  (a + b) / 2 + ((b - a) / 2) * lobattoNode n i
theorem exteriorNode_strictAnti (a b ) (hab : a < b) (n ) (hn : 1 ≤ n) :
    StrictAnti (exteriorNode a b n) := by
  intro i j hij
  dsimp [exteriorNode]
  have := mul_lt_mul_of_pos_left (lobattoNode_strictAnti n hn hij)
    (by linarith : 0 < (b - a) / 2)
  linarith
theorem exteriorNode_mem (a b ) (hab : a ≤ b) (n ) (i : Fin (n + 1)) :
    exteriorNode a b n i ∈ Set.Icc a b := by
  dsimp [exteriorNode, lobattoNode]
  constructor <;> nlinarith [Real.cos_le_one (i.val * Real.pi / n),
    Real.neg_one_le_cos (i.val * Real.pi / n)]
def exteriorWeight (a b : ℝ) (n ) (i : Fin (n + 1)) : ℝ :=
  ∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i,
    exteriorNode a b n j / (exteriorNode a b n j - exteriorNode a b n i)
theorem exterior_rule_exact (a b ) (hab : a < b) (n : ℕ) (hn : 1 ≤ n)
    (P : ℝ[X]) (hP : P.degree ≤ n) :
    (∑ i : Fin (n + 1), exteriorWeight a b n i * P.eval (exteriorNode a b n i)) =
      P.eval 0 := by
  apply exterior_product_rule_exact Finset.univ (exteriorNode a b n)
    (exteriorNode_strictAnti a b hab n hn).injective.injOn
  simpa using hP.trans_lt (show (n : WithBot ℕ) < n + 1 by exact_mod_cast Nat.lt_succ_self n)
theorem positive_decreasing_weight_sign (n z)
    (hz : ∀ i, 0 < z i) (hanti : StrictAnti z) (i : Fin (n + 1)) :
    (∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, z j / (z j - z i)) =
      (-1 : ℝ) ^ (n - i.val) *
        |∏ j ∈ (Finset.univ : Finset (Fin (n + 1))).erase i, z j / (z j - z i)| := by
  let S := (Finset.univ : Finset (Fin (n + 1))).erase i
  have hf (j : Fin (n + 1)) (hj : j ∈ S) :
      z j / (z j - z i) = (if i < j then (-1 : ℝ) else 1) * |z j / (z j - z i)| := by
    have hji  := (Finset.mem_erase.mp hj).1
    by_cases hij : i < j
    · rw [if_pos hij, abs_of_neg (div_neg_of_pos_of_neg (hz j)
        (sub_neg.mpr (hanti hij)))]
      ring
    · have hji'  := lt_of_le_of_ne (le_of_not_gt hij) hji
      rw [if_neg hij, abs_of_pos (div_pos (hz j) (sub_pos.mpr (hanti hji'))), one_mul]
  have hs : (∏ j ∈ S, if i < j then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (n - i.val) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hset : S.filter (fun j => i < j) = Finset.Ioi i := by
      ext j
      simp [S, Finset.mem_Ioi]
      omega
    rw [hset, Fin.card_Ioi]
    congr 1
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf
def intervalChebyshev (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ n).comp
    ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹))
theorem exterior_rule_variation (a b ) (ha : 0 < a) (hab : a < b) (n )
    (hn : 1 ≤ n) :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) =
      Real.cosh (n * exteriorTau ((a + b) / (b - a))) := by
  have hnorm : (0 - (a + b) / 2) * ((b - a) / 2)⁻¹ = -((a + b) / (b - a)) := by
    field_simp
    ring
  have heval : (intervalChebyshev a b n).eval 0 =
      (-1 ) ^ n * Real.cosh (n * exteriorTau ((a + b) / (b - a))) := by
    simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
    rw [chebyshev_eval_neg]
    congr 1
    calc
      _ = (Polynomial.Chebyshev.T ℝ ↑n).eval
        (Real.cosh (exteriorTau ((a + b) / (b - a)))) := by
          rw [cosh_exteriorTau _ (by apply (le_div_iff₀ (by linarith : 0 < b - a)).mpr; linarith)]
      _ = _ := by
        rw [Polynomial.Chebyshev.T_real_cosh]
        simp
  have h_intervalChebyshev_degree : (intervalChebyshev a b n).degree ≤ n := by
    apply Polynomial.degree_le_of_natDegree_le
    apply Polynomial.natDegree_comp_le.trans
    have hd : ((X - C ((a + b) / 2)) * C (((b - a) / 2)⁻¹) : ℝ[X]).natDegree ≤ 1 := by
      apply Polynomial.natDegree_mul_le.trans
      simp
    exact (Nat.mul_le_mul (chebyshev_natDegree_le n) hd).trans (by simp)
  have hexact := exterior_rule_exact a b hab n hn (intervalChebyshev a b n)
    h_intervalChebyshev_degree
  have hnode : ∀ i, exteriorWeight a b n i *
      (intervalChebyshev a b n).eval (exteriorNode a b n i) =
        (-1 : ℝ) ^ n * |exteriorWeight a b n i| := by
    intro i
    have h_exterior_weight_sign : exteriorWeight a b n i = (-1 : ℝ) ^ (n - i.val) * |exteriorWeight a b n i| := by
      apply positive_decreasing_weight_sign
      · intro j
        exact ha.trans_le (exteriorNode_mem a b (le_of_lt hab) n j).1
      · exact exteriorNode_strictAnti a b hab n hn
    have h_intervalChebyshev_at_node : (intervalChebyshev a b n).eval (exteriorNode a b n i) = (-1 ) ^ i.val := by
      have hba : b - a ≠ 0 := by linarith
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      have hnorm : (exteriorNode a b n i - (a + b) / 2) * ((b - a) / 2)⁻¹ =
          lobattoNode n i := by
        dsimp [exteriorNode]
        field_simp [hba]
        ring
      simp only [intervalChebyshev, eval_comp, eval_mul, eval_sub, eval_X, eval_C, hnorm]
      rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
      simp only [Int.cast_natCast, mul_div_cancel₀ _ hn0]
      simpa using Real.cos_nat_mul_pi_sub 0 i.val
    rw [h_intervalChebyshev_at_node]
    nth_rw 1 [h_exterior_weight_sign]
    rw [mul_right_comm, ← pow_add, Nat.sub_add_cancel (by omega : i.val ≤ n)]
  simp_rw [hnode] at hexact
  rw [← Finset.mul_sum, heval] at hexact
  exact mul_left_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0)) hexact
theorem exterior_rule_variation_le_exp (a b ) (ha : 0 < a) (hab : a < b)
    (n ) (hn : 1 ≤ n) :
    (∑ i : Fin (n + 1), |exteriorWeight a b n i|) ≤
      Real.exp (n * exteriorTau ((a + b) / (b - a))) := by
  rw [exterior_rule_variation a b ha hab n hn, Real.cosh_eq]
  have hratio : 1 ≤ (a + b) / (b - a) := by
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have  := mul_nonneg (Nat.cast_nonneg n) (exteriorTau_nonneg _ hratio)
  have := Real.exp_le_exp.mpr (show
      -(n * exteriorTau ((a + b) / (b - a))) ≤
      n * exteriorTau ((a + b) / (b - a)) by linarith)
  linarith
end NearlyMinimax
