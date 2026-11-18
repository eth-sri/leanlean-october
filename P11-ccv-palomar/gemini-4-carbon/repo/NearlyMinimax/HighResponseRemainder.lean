module

public import Mathlib
public import NearlyMinimax.Chebyshev
public import NearlyMinimax.LowSmoothnessVariance

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal
namespace NearlyMinimax

-- ============================================================================
-- 1. Chebyshev-Lobatto Derivative Rule, Atomic Rules, and High Response Updates
-- ============================================================================

section DerivativeAndResponseRules
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

section LobattoRule
open Polynomial Finset

def lobattoDerivativeWeight (m : ℕ) (i : Fin ((2 * m + 1) + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (lobattoNode (2 * m + 1)) i).derivative.eval 0

theorem lobattoNode_reflection (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    lobattoNode n i.rev = -lobattoNode n i := by
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hi : i.val ≤ n := by omega
  unfold lobattoNode
  rw [show (i.rev.val : ℝ) * Real.pi / n = Real.pi - (i.val : ℝ) * Real.pi / n by
    simp only [Fin.val_rev]
    rw [show n + 1 - (i.val + 1) = n - i.val by omega, Nat.cast_sub hi]; push_cast; field_simp,
    Real.cos_pi_sub]

private lemma odd_lobatto_nodal_derivative_zero (m : ℕ) :
    (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).derivative.eval 0 = 0 := by
  have hev : (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).comp (-X) =
      Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1)) := by
    rw [Lagrange.nodal, Polynomial.prod_comp]
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    simp_rw [show ∀ i : Fin ((2 * m + 1) + 1),
      -X - C (lobattoNode (2 * m + 1) i) = (-1) * (X - C (lobattoNode (2 * m + 1) i.rev)) from
      fun i => by rw [lobattoNode_reflection (2 * m + 1) (by omega), map_neg]; ring]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show (-1 : ℝ[X]) ^ ((2 * m + 1) + 1) = 1 by
      rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega, pow_mul]; norm_num, one_mul]
    exact Fintype.prod_equiv Fin.revPerm _ _ fun _ => rfl
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) hev
  simp only [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_X, neg_zero] at h
  linarith

theorem lobatto_derivative_rule_variation (m : ℕ) :
    (∑ i : Fin ((2 * m + 1) + 1), |lobattoDerivativeWeight m i|) = (2 * m + 1 : ℕ) := by
  let n := 2 * m + 1
  let z := lobattoNode n
  have hanti : StrictAnti z := lobattoNode_strictAnti n (by dsimp [n]; omega)
  have hnz (i : Fin (n + 1)) : z i ≠ 0 := fun hz => by
    have hrev := lobattoNode_reflection n (by dsimp [n]; omega) i
    have hi : i.rev = i := hanti.injective (by dsimp [z] at hz ⊢; rw [hrev, hz]; simp)
    have hval := congrArg Fin.val hi; simp only [Fin.val_rev] at hval; dsimp [n] at hval; omega
  let c := -(Lagrange.nodal Finset.univ z).eval 0
  let r := fun i : Fin (n + 1) => |Lagrange.nodalWeight Finset.univ z i| / (z i) ^ 2
  have hw (i : Fin (n + 1)) : lobattoDerivativeWeight m i = c * (-1 : ℝ) ^ i.val * r i := by
    have hfac : Lagrange.basis Finset.univ z i * (X - C (z i)) =
        C (Lagrange.nodalWeight Finset.univ z i) * Lagrange.nodal Finset.univ z := by
      rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i),
        ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ i),
        Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i)]
      ring
    have hd := congrArg (fun p : ℝ[X] => p.derivative.eval 0) hfac
    have hW : (Lagrange.nodal Finset.univ z).derivative.eval 0 = 0 := odd_lobatto_nodal_derivative_zero m
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, zero_sub, sub_zero, eval_one, mul_one, eval_zero, zero_mul,
      zero_add, hW, mul_zero] at hd
    rw [Lagrange.eval_basis_not_at_node (v := z) (x := 0) (Finset.mem_univ i) (Ne.symm (hnz i))] at hd
    simp only [zero_sub, inv_neg] at hd; field_simp [hnz i] at hd
    have hd0 : lobattoDerivativeWeight m i = c * Lagrange.nodalWeight Finset.univ z i / (z i) ^ 2 :=
      (eq_div_iff (pow_ne_zero 2 (hnz i))).mpr (by dsimp [lobattoDerivativeWeight, c, z, n] at hd ⊢; nlinarith)
    have hsign : Lagrange.nodalWeight Finset.univ z i =
        (-1 : ℝ) ^ i.val * |Lagrange.nodalWeight Finset.univ z i| := by
      let S := (Finset.univ : Finset (Fin (n + 1))).erase i
      have hs : (∏ j ∈ S, if j < i then (-1 : ℝ) else 1) = (-1 : ℝ) ^ i.val := by
        rw [Finset.prod_ite]; simp only [Finset.prod_const, one_pow, mul_one]
        rw [show S.filter (fun j => j < i) = Finset.Iio i by ext; simp [S, Finset.mem_Iio]; omega, Fin.card_Iio]
      unfold Lagrange.nodalWeight
      change (∏ j ∈ S, (z i - z j)⁻¹) = _
      rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      by_cases hlt : j < i
      · rw [if_pos hlt, abs_of_neg (inv_lt_zero.mpr (sub_neg.mpr (hanti hlt)))]; ring
      · rw [if_neg hlt, abs_of_pos (inv_pos.mpr (sub_pos.mpr (hanti (lt_of_le_of_ne (le_of_not_gt hlt) hji.symm)))), one_mul]
    rw [hd0]; nth_rw 1 [hsign]; dsimp [r]; ring
  have hr (i : Fin (n + 1)) : 0 ≤ r i := div_nonneg (abs_nonneg _) (sq_nonneg _)
  have habs (i : Fin (n + 1)) : |lobattoDerivativeWeight m i| = |c| * r i := by
    rw [hw, abs_mul, abs_mul, abs_pow, abs_of_nonneg (hr i)]; norm_num
  have hcheb (i : Fin (n + 1)) :
      (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (z i) = (-1 : ℝ) ^ i.val := by
    have h := intervalChebyshev_at_node (-1) 1 (by norm_num) n (by dsimp [n]; omega) i
    norm_num [intervalChebyshev, exteriorNode] at h; exact h
  have hexact : (∑ i : Fin (n + 1), lobattoDerivativeWeight m i *
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (z i)) =
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).derivative.eval 0 := by
    apply cardinal_derivative_exact Finset.univ z hanti.injective.injOn
    simpa using (Polynomial.degree_le_of_natDegree_le (chebyshev_natDegree_le n)).trans_lt
      (show (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) by exact_mod_cast Nat.lt_succ_self n)
  simp_rw [show ∀ i : Fin (n + 1), lobattoDerivativeWeight m i *
      (Polynomial.Chebyshev.T ℝ ((n : ℕ) : ℤ)).eval (z i) = c * r i from fun i => by
    rw [hcheb i, hw]
    rw [show (c * (-1 : ℝ) ^ i.val * r i) * (-1 : ℝ) ^ i.val = c * r i * ((-1 : ℝ) ^ 2) ^ i.val by
      rw [← pow_mul, mul_comm 2 i.val, pow_mul]; ring]
    norm_num] at hexact
  rw [← Finset.mul_sum] at hexact
  simp_rw [habs]; rw [← Finset.mul_sum, ← abs_of_nonneg (Finset.sum_nonneg fun i _ => hr i), ← abs_mul, hexact]
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [eval_mul, eval_natCast, Int.cast_natCast]
  rw [show ((2 * m + 1 : ℕ) : ℤ) - 1 = 2 * (m : ℤ) by dsimp [n]; omega,
    Polynomial.Chebyshev.U_eval_two_mul_zero, abs_mul,
    show |((m : ℤ).negOnePow : ℝ)| = 1 by exact_mod_cast Int.abs_negOnePow (m : ℤ),
    mul_one, abs_of_nonneg (Nat.cast_nonneg _)]

theorem lobattoDerivativeWeight_abs_reflection (m : ℕ) (i : Fin ((2 * m + 1) + 1)) :
    |lobattoDerivativeWeight m i.rev| = |lobattoDerivativeWeight m i| := by
  let n := 2 * m + 1
  let z := lobattoNode n
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) := (lobattoNode_strictAnti n hn).injective.injOn
  have hpoly : (Lagrange.basis Finset.univ z i.rev).comp (-X) = Lagrange.basis Finset.univ z i := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
    · refine (Polynomial.degree_le_of_natDegree_le (Polynomial.natDegree_comp_le.trans ?_)).trans_lt
        (by simpa using (by exact_mod_cast Nat.lt_succ_self n : (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ)))
      simp [Lagrange.natDegree_basis hv (Finset.mem_univ i.rev)]
    · rw [Lagrange.degree_basis hv (Finset.mem_univ i)]
      simpa using (by exact_mod_cast Nat.lt_succ_self n : (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ))
    · intro j _
      rw [eval_comp, eval_neg, eval_X, ← lobattoNode_reflection n hn j]
      by_cases hij : i = j
      · subst hij; rw [Lagrange.eval_basis_self hv (Finset.mem_univ i.rev), Lagrange.eval_basis_self hv (Finset.mem_univ i)]
      · have hrev : i.rev ≠ j.rev := fun heq => hij (by simpa using congrArg Fin.rev heq)
        change (Lagrange.basis Finset.univ z i.rev).eval (z j.rev) = (Lagrange.basis Finset.univ z i).eval (z j)
        rw [Lagrange.eval_basis_of_ne hrev (Finset.mem_univ j.rev), Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) hpoly
  simp only [derivative_comp, derivative_neg, derivative_X, eval_mul, eval_neg,
    eval_comp, eval_X, neg_zero, neg_one_mul] at h
  change -lobattoDerivativeWeight m i.rev = lobattoDerivativeWeight m i at h
  rw [show lobattoDerivativeWeight m i.rev = -lobattoDerivativeWeight m i by linarith, abs_neg]

def derivativeOrder (D : ℕ) : ℕ := 2 * ((D - 1) / 2) + 1

private lemma derivativeOrder_bounds (D : ℕ) (hD : 1 ≤ D) :
    derivativeOrder D ≤ D ∧ D ≤ derivativeOrder D + 1 := by
  have := Nat.mod_lt (D - 1) (by norm_num : 0 < 2)
  have := Nat.mod_add_div (D - 1) 2
  dsimp [derivativeOrder]; omega

theorem derivative_rule_exact (D : ℕ) (hD : 1 ≤ D) (P : ℝ[X]) (hP : P.degree ≤ D) :
    (∑ i : Fin (derivativeOrder D + 1),
      lobattoDerivativeWeight ((D - 1) / 2) i * P.eval (lobattoNode (derivativeOrder D) i)) =
      P.derivative.eval 0 := by
  let m := (D - 1) / 2
  let n := 2 * m + 1
  let z := lobattoNode n
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) := (lobattoNode_strictAnti n hn).injective.injOn
  have hP' : P.degree ≤ (n + 1 : ℕ) := hP.trans (by exact_mod_cast (derivativeOrder_bounds D hD).2)
  change (∑ i : Fin (n + 1), lobattoDerivativeWeight m i * P.eval (z i)) = P.derivative.eval 0
  by_cases hp : P.degree < (n + 1 : ℕ)
  · exact cardinal_derivative_exact Finset.univ z hv P (by simpa using hp) 0
  have hdeg : P.degree = (n + 1 : ℕ) := le_antisymm hP' (le_of_not_gt hp)
  have hp0 : P ≠ 0 := fun hz => by rw [hz, degree_zero] at hdeg; exact WithBot.bot_ne_coe hdeg
  let W := Lagrange.nodal Finset.univ z
  let Q := P - C P.leadingCoeff * W
  have hCW : (C P.leadingCoeff * W).degree = P.degree := by
    rw [degree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hp0), hdeg]; simp [W, Lagrange.degree_nodal]
  have hQ : Q.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simpa only [Q, hdeg, Finset.card_univ, Fintype.card_fin] using
      Polynomial.degree_sub_lt_left hCW.symm hp0
        (by simp [leadingCoeff_mul, W, (Lagrange.nodal_monic (s := Finset.univ) (v := z)).leadingCoeff])
  have hex := cardinal_derivative_exact Finset.univ z hv Q hQ 0
  simp_rw [show ∀ i : Fin (n + 1), Q.eval (z i) = P.eval (z i) from
      fun i => by simp [Q, W, Lagrange.eval_nodal_at_node (Finset.mem_univ i)],
    show Q.derivative.eval 0 = P.derivative.eval 0 by
      simp only [Q, derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C]
      change P.derivative.eval 0 - P.leadingCoeff *
        (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).derivative.eval 0 = P.derivative.eval 0
      rw [odd_lobatto_nodal_derivative_zero, mul_zero, sub_zero]] at hex
  exact hex

theorem derivative_rule_variation (D : ℕ) (hD : 1 ≤ D) :
    (∑ i : Fin (derivativeOrder D + 1), |lobattoDerivativeWeight ((D - 1) / 2) i|) =
      derivativeOrder D ∧ (derivativeOrder D : ℝ) ≤ D :=
  ⟨lobatto_derivative_rule_variation ((D - 1) / 2), by exact_mod_cast (derivativeOrder_bounds D hD).1⟩

end LobattoRule

-- Finite atomic signed rule

def atomicSignedRule {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (z : ι → X) (w : ι → ℝ) : SignedMeasure X :=
  ∑ i, VectorMeasure.dirac (z i) (w i)

theorem atomicSignedRule_integral {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    [MeasurableSingletonClass X] (z : ι → X) (w : ι → ℝ) (f : X → ℝ) :
    ∫ᵛ x, f x ∂<•(atomicSignedRule z w) = ∑ i, w i * f (z i) := by
  rw [atomicSignedRule, VectorMeasure.integral_finsetSum_vectorMeasure fun i _ => by
    change Integrable f (VectorMeasure.dirac (z i) (w i)).variation
    rw [VectorMeasure.variation_dirac]
    exact (integrable_dirac enorm_lt_top).smul_measure_nnreal]
  simp

-- High response updates and high-order remainder

section ResponseUpdates
open Polynomial

def ternaryLinePolynomial (a f V δ : ℝ) (y : Fin 3) : ℝ[X] :=
  C (ternaryMass a f V y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (δ ^ 2 * ternaryVarianceDerivative a y)

private lemma ternary_line_polynomial_eval (a f V δ z : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative, div_eq_mul_inv] <;> ring

private lemma ternary_line_polynomial_natDegree (a f V δ : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 :=
  (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_monomial_le _).trans (by norm_num)))) (natDegree_monomial_le _))

def responseLinePolynomial (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3) : ℝ[X] :=
  ∏ i, ternaryLinePolynomial a (f i) V (δ i) (y i)

private lemma response_line_polynomial_eval (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) :
    (responseLinePolynomial n a V f δ y).eval z = ∏ i, ternaryMass a (f i + z * δ i) V (y i) := by
  simp only [responseLinePolynomial, eval_prod, ternary_line_polynomial_eval]

private lemma response_line_rule_exact (q n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (hn : n ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) =
      (responseLinePolynomial n a V f δ y).coeff 2 := by
  have hnd : (responseLinePolynomial n a V f δ y).natDegree ≤ 2 * n :=
    (natDegree_prod_le _ _).trans ((Finset.sum_le_sum (g := fun _ => 2)
      fun _ _ => ternary_line_polynomial_natDegree _ _ _ _ _).trans_eq (by simp [mul_comm]))
  simpa only [response_line_polynomial_eval] using response_rule_exact q
    (responseLinePolynomial n a V f δ y)
    (degree_le_natDegree.trans_lt (by exact_mod_cast (show (responseLinePolynomial n a V f δ y).natDegree < 2 * q + 2 from
      hnd.trans_lt (by omega))))

private lemma response_line_quadratic_coefficient (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3) :
    2 * (responseLinePolynomial n a V f δ y).coeff 2 =
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ i) V (y i))
        (fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i))
        (fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 := by
  let Q := responseLinePolynomial n a V f δ y
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (f i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (f i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  have hd : (fun z => Q.derivative.eval z) = finiteProductFirst Finset.univ H D :=
    funext fun z => (Q.hasDerivAt z).unique
      (by simpa only [Q, response_line_polynomial_eval] using finite_product_hasDerivAt Finset.univ H D z fun i _ => hH i z)
  have hsecond := finite_product_first_hasDerivAt Finset.univ H D E 0 (fun i _ => hH i 0) fun i _ => hD i 0
  rw [← hd] at hsecond
  have he := (Q.derivative.hasDerivAt 0).unique hsecond
  change Q.derivative.derivative.eval 0 = finiteProductSecond Finset.univ H D E 0 at he
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
  norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.zero_add] at he
  simpa only [mul_comm, Q, H, D, E] using he

theorem responseNode_mem_unit (q : ℕ) (j : Fin (2 * q + 2)) :
    responseNode q j ∈ Icc (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < (2 * q + 1 : ℕ) := by positivity
  exact ⟨div_nonneg (by positivity) hden.le, (div_le_one hden).mpr (by exact_mod_cast (by omega : j.val ≤ 2 * q + 1))⟩

private lemma response_scalar_product_action_abs_bound (q n : ℕ) (hn : 1 ≤ n)
    (a V η ρ : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
        (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2) := by
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  let A := (2 * ρ + a) / a ^ 2
  let S := 2 / a ^ 2
  let B := 4 * (A ^ 2 + S) * n ^ 2 * η ^ 2
  have hB : 0 ≤ B := by dsimp [B, A, S]; positivity
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (f i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (f i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  let HP := fun z => ∏ i, H i z
  let DP := finiteProductFirst Finset.univ H D
  let EP := finiteProductSecond Finset.univ H D E
  have hHP (z : ℝ) (_ : z ∈ Icc (0 : ℝ) 1) : HasDerivAt HP (DP z) z :=
    finite_product_hasDerivAt Finset.univ H D z fun i _ => hH i z
  have hDP (z : ℝ) (_ : z ∈ Icc (0 : ℝ) 1) : HasDerivAt DP (EP z) z :=
    finite_product_first_hasDerivAt Finset.univ H D E z (fun i _ => hH i z) fun i _ => hD i z
  have hEP (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |EP z| ≤ B := by
    have h := finite_product_second_abs_bound Finset.univ H D E z (2 * η * A) (4 * η ^ 2 * S)
      (by dsimp [A]; positivity) (by dsimp [S]; positivity)
      (fun i _ => by rw [abs_of_nonneg (hp z hz i (y i))]; exact ternary_mass_le_one a _ V ha.ne' (hp z hz i) (y i))
      (fun i _ => by rw [abs_mul]; exact mul_le_mul (hδ i) (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i)) (abs_nonneg _) (by positivity))
      fun i _ => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hs : (δ i) ^ 2 ≤ (2 * η) ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2
        simpa only [S] using (mul_le_mul hs (ternary_mean_second_derivative_abs_bound a ha (y i)) (abs_nonneg _) (by positivity)).trans_eq (by ring)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    refine h.trans ?_
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmore : 0 ≤ ((n : ℝ) ^ 2 - n) * (η ^ 2 * S) := mul_nonneg (by nlinarith) (mul_nonneg (sq_nonneg η) (by dsimp [S]; positivity))
    dsimp [B, A, S] at *; nlinarith
  have hrem (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |HP z - HP 0 - z * DP 0| ≤ B := by
    have hz0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hDdiff (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : |DP u - DP 0| ≤ B := by
      have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun x hx => (hDP x hx).hasDerivWithinAt)
        (fun x hx => by simpa only [Real.norm_eq_abs] using hEP x hx) (convex_Icc 0 1) hz0 hu
      simp only [Real.norm_eq_abs, sub_zero] at h
      exact h.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hu.1], hu.2⟩) hB).trans_eq (mul_one B))
    let G := fun u => HP u - HP 0 - u * DP 0
    have hG (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : HasDerivAt G (DP x - DP 0) x :=
      (((hHP x hx).sub_const (HP 0)).sub ((hasDerivAt_id x).mul_const (DP 0))).congr_deriv (by ring)
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hG x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hDdiff x hx) (convex_Icc (0 : ℝ) 1) hz0 hz
    simp only [G, sub_zero, zero_mul, sub_self, Real.norm_eq_abs] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩) hB).trans_eq (mul_one B))
  change |∑ j : Fin (2 * q + 2), responseWeight q j * HP (responseNode q j)| ≤ _
  rw [show (∑ j : Fin (2 * q + 2), responseWeight q j * HP (responseNode q j)) =
      ∑ j : Fin (2 * q + 2), responseWeight q j * (HP (responseNode q j) - HP 0 - responseNode q j * DP 0) by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    rw [← Finset.sum_mul, ← Finset.sum_mul, response_zero_mass, response_zero_mean]; simp]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum
    (g := fun j => |responseWeight q j| * B) fun j _ => ?_)).trans_eq (Finset.sum_mul _ _ _).symm
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hrem _ (responseNode_mem_unit q j)) (abs_nonneg _)

def polynomialResponseTaylor (q : ℕ) (P : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (2 * q + 2), monomial k (P.coeff k)

private lemma response_scalar_high_order_remainder (q : ℕ) (hq : 1 ≤ q) (n : ℕ)
    (a V η ρ B : ℝ) (f δ : Fin n → ℝ) (y : Fin n → Fin 3)
    (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hB : 1 ≤ B)
    (hMean : (2 * ρ + a) / a ^ 2 ≤ B) (hSecond : 2 / a ^ 2 ≤ B)
    (hf : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |f i + z * δ i| ≤ ρ)
    (hp : ∀ z ∈ Icc (0 : ℝ) 1, ∀ i u, 0 ≤ ternaryMass a (f i + z * δ i) V u)
    (hδ : ∀ i, |δ i| ≤ 2 * η) :
    |(∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) -
      (responseLinePolynomial n a V f δ y).coeff 2| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
        ((n : ℝ) * (2 * η * B)) ^ (2 * q + 2) := by
  have hit_eval (P : ℝ[X]) (r : ℕ) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      iteratedDerivWithin r (fun z => P.eval z) (Icc (0 : ℝ) 1) z = (derivative^[r] P).eval z := by
    have hid (k : ℕ) : iteratedDeriv k (fun z => P.eval z) = fun z => (derivative^[k] P).eval z := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
        exact funext fun u => ((derivative^[k] P).hasDerivAt u).deriv
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
      (by simpa only [coe_aeval_eq_eval] using (P.contDiff_aeval (𝕜 := ℝ) r).contDiffAt) hz]
    exact congrFun (hid r) z
  have hprod_der (s : Finset (Fin n)) (P : Fin n → ℝ[X]) (b₀ z : ℝ) (hb₀ : 0 ≤ b₀)
      (hP : ∀ i ∈ s, ∀ r : ℕ, |(derivative^[r] (P i)).eval z| ≤ b₀ ^ r) :
      ∀ r : ℕ, |(derivative^[r] (∏ i ∈ s, P i)).eval z| ≤ ((s.card : ℝ) * b₀) ^ r := by
    induction s using Finset.induction_on with
    | empty =>
      intro r; by_cases hr : r = 0
      · simp [hr]
      · rw [Finset.prod_empty, iterate_derivative_one (Nat.pos_of_ne_zero hr)]
        simp only [eval_zero, abs_zero, Finset.card_empty, Nat.cast_zero, zero_mul]; positivity
    | @insert i s hi ih =>
      intro r
      rw [Finset.prod_insert hi, iterate_derivative_mul, eval_finsetSum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum (g := fun k => (r.choose k : ℝ) * (b₀ ^ (r - k) * ((s.card : ℝ) * b₀) ^ k)) fun k _ => ?_).trans_eq ?_)
      · simp only [nsmul_eq_mul, eval_mul, eval_natCast, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ r.choose k)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hP i (Finset.mem_insert_self _ _) (r - k))
            (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) k) (abs_nonneg _) (pow_nonneg hb₀ _))
          (Nat.cast_nonneg _)
      · rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one,
          show ((s.card : ℝ) + 1) * b₀ = (s.card : ℝ) * b₀ + b₀ by ring, add_pow]
        exact Finset.sum_congr rfl fun _ _ => by ring
  let P := responseLinePolynomial n a V f δ y
  let M := ((n : ℝ) * (2 * η * B)) ^ (2 * q + 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hPder (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |(derivative^[2 * q + 2] P).eval z| ≤ M := by
    simpa only [P, M, responseLinePolynomial, Finset.card_univ, Fintype.card_fin] using
      hprod_der Finset.univ (fun i => ternaryLinePolynomial a (f i) V (δ i) (y i)) (2 * η * B) z
        (by positivity) (fun i _ r => by
          have hd1 (u : ℝ) : (ternaryLinePolynomial a (f i) V (δ i) (y i)).derivative.eval u =
              δ i * ternaryMeanDerivative a (f i + u * δ i) (y i) := by
            have h := (ternary_hasDerivAt_mean a (f i + u * δ i) V (y i)).comp u (((hasDerivAt_id u).mul_const (δ i)).const_add (f i))
            have he := (ternaryLinePolynomial a (f i) V (δ i) (y i)).hasDerivAt u
            simp only [ternary_line_polynomial_eval] at he
            exact he.unique (h.congr_deriv (by ring))
          have hd2 (u : ℝ) : (ternaryLinePolynomial a (f i) V (δ i) (y i)).derivative.derivative.eval u =
              (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i) := by
            have h := ((ternary_hasDerivAt_mean_derivative a (f i + u * δ i) (y i)).comp u
              (((hasDerivAt_id u).mul_const (δ i)).const_add (f i))).const_mul (δ i)
            have he := (ternaryLinePolynomial a (f i) V (δ i) (y i)).derivative.hasDerivAt u
            simp only [hd1] at he
            exact he.unique (h.congr_deriv (by ring))
          rcases r with _ | _ | _ | r
          · rw [Function.iterate_zero_apply, ternary_line_polynomial_eval, pow_zero, abs_of_nonneg (hp z hz i (y i))]
            exact ternary_mass_le_one a _ V ha.ne' (hp z hz i) (y i)
          · rw [Function.iterate_one, hd1, pow_one, abs_mul]
            exact (mul_le_mul (hδ i) ((ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i)).trans hMean)
              (abs_nonneg _) (by positivity)).trans_eq (by ring)
          · change |(derivative^[2] (ternaryLinePolynomial a (f i) V (δ i) (y i))).eval z| ≤ (2 * η * B) ^ 2
            rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply', Function.iterate_one,
              hd2, abs_mul, abs_of_nonneg (sq_nonneg _)]
            have hδ2 : (δ i) ^ 2 ≤ (2 * η) ^ 2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2
            have hSB : 2 / a ^ 2 ≤ B ^ 2 := hSecond.trans (by nlinarith [hB])
            exact (mul_le_mul hδ2 ((ternary_mean_second_derivative_abs_bound a ha (y i)).trans hSB)
              (abs_nonneg _) (by positivity)).trans_eq (by ring)
          · rw [iterate_derivative_eq_zero ((ternary_line_polynomial_natDegree _ _ _ _ _).trans_lt (by omega)), eval_zero, abs_zero]
            positivity) (2 * q + 2)
  simp only [← response_line_polynomial_eval]
  change |(∑ j : Fin (2 * q + 2), responseWeight q j * P.eval (responseNode q j)) - P.coeff 2| ≤
    (∑ j : Fin (2 * q + 2), |responseWeight q j|) * M
  have htex : (∑ j : Fin (2 * q + 2), responseWeight q j *
      (polynomialResponseTaylor q P).eval (responseNode q j)) = P.coeff 2 := by
    have hdeg : (polynomialResponseTaylor q P).natDegree ≤ 2 * q + 1 :=
      natDegree_sum_le_of_forall_le _ _ fun k hk =>
        (natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hk; omega)
    rw [response_rule_exact q _ (degree_le_natDegree.trans_lt (by exact_mod_cast hdeg.trans_lt (by omega)))]
    simp only [polynomialResponseTaylor, finsetSum_coeff, coeff_monomial]
    simp [Finset.mem_range, show 2 < 2 * q + 2 by omega]
  rw [← htex, ← Finset.sum_sub_distrib]
  refine ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (g := fun j => |responseWeight q j| * M) fun j _ => ?_)).trans_eq (Finset.sum_mul _ _ _).symm
  rw [← mul_sub, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have hteval : (polynomialResponseTaylor q P).eval (responseNode q j) =
      taylorWithinEval (fun z => P.eval z) (2 * q + 1) (Icc (0 : ℝ) 1) 0 (responseNode q j) := by
    rw [taylor_within_apply]
    simp only [polynomialResponseTaylor, eval_finsetSum, eval_monomial]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hit_eval P k 0 (by norm_num), ← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
    simp only [Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul, sub_zero, smul_eq_mul]
    have hk0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp
  rw [hteval]
  have hsmooth : ContDiff ℝ (2 * q + 1 + 1) fun z => P.eval z := by
    simpa only [coe_aeval_eq_eval] using P.contDiff_aeval (𝕜 := ℝ) (2 * q + 1 + 1)
  have h := taylor_mean_remainder_bound (f := fun z => P.eval z) (n := 2 * q + 1)
    zero_le_one hsmooth.contDiffOn (responseNode_mem_unit q j) fun z hz => by
      rw [hit_eval P (2 * q + 1 + 1) z hz]
      simpa only [Real.norm_eq_abs, show 2 * q + 1 + 1 = 2 * q + 2 by omega] using hPder z hz
  rw [Real.norm_eq_abs, sub_zero] at h
  have hz := responseNode_mem_unit q j
  have hfac : (1 : ℝ) ≤ (2 * q + 1).factorial := by exact_mod_cast Nat.factorial_pos (2 * q + 1)
  exact h.trans ((div_le_self (mul_nonneg hM (pow_nonneg hz.1 _)) hfac).trans
    ((mul_le_mul_of_nonneg_left (pow_le_one₀ hz.1 hz.2) hM).trans_eq (mul_one M)))

section CovarianceAndRemainder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coefficientReset (c v : ι → ℝ) (z : ℝ) : ι → ℝ := fun i => (1 - z) * c i + z * v i

def responseMatrixAction (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  covarianceAction C A fun v => ∑ j : Fin (2 * q + 2),
    responseWeight q j * Φ (coefficientReset c v (responseNode q j))

theorem responseMatrixAction_zero_mass (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    responseMatrixAction q C A c (fun _ => 1) = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]

omit [DecidableEq ι] in
theorem coefficientReset_mem_ball (C : ℝ) (c v : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc (0 : ℝ) 1) (hc : ∑ i, |c i| ≤ C⁻¹) (hv : ∑ i, |v i| ≤ C⁻¹) :
    (∑ i, |coefficientReset c v z i|) ≤ C⁻¹ := by
  calc
    _ ≤ ∑ i, ((1 - z) * |c i| + z * |v i|) := Finset.sum_le_sum fun i _ =>
      (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2]), abs_of_nonneg hz.1])
    _ = (1 - z) * (∑ i, |c i|) + z * (∑ i, |v i|) := by rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 - z) * C⁻¹ + z * C⁻¹ := add_le_add (mul_le_mul_of_nonneg_left hc (by linarith [hz.2]))
      (mul_le_mul_of_nonneg_left hv hz.1)
    _ = _ := by ring

def spatialFrameCovariance (A : ι → ι → ℝ) {n : ℕ} (φ : Fin n → ι → ℝ) (i l : Fin n) : ℝ :=
  ∑ k, ∑ m, φ i k * φ l m * A k m

def coefficientRegression {n : ℕ} (η : ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) : Fin n → ℝ :=
  fun i => g i + η * w i * ∑ k, φ i k * c k

def coefficientDirection {n : ℕ} (η : ℝ) (w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ) : Fin n → ℝ :=
  fun i => η * w i * ∑ k, φ i k * (v k - c k)

omit [DecidableEq ι] in
private lemma coefficientRegression_reset {n : ℕ} (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) (z : ℝ) :
    coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i :=
  funext fun i => by
    have hs : (∑ k, φ i k * coefficientReset c v z k) =
        (∑ k, φ i k * c k) + z * ((∑ k, φ i k * v k) - ∑ k, φ i k * c k) := by
      calc
        (∑ k, φ i k * coefficientReset c v z k) =
            ∑ k, (φ i k * c k + z * (φ i k * v k - φ i k * c k)) :=
          Finset.sum_congr rfl fun _ _ => by dsimp [coefficientReset]; ring
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [coefficientRegression, coefficientDirection, hs, mul_sub, Finset.sum_sub_distrib]; ring

omit [DecidableEq ι] in
private lemma coefficient_direction_and_reset_bounds {n : ℕ} (C η ρ : ℝ)
    (hη : 0 ≤ η) (hηρ : η ≤ ρ / 2) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c v : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hv : ∑ k, |v k| ≤ C⁻¹)
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1) :
    (∀ i, |coefficientDirection η w φ c v i| ≤ 2 * η) ∧
    ∀ z ∈ Icc (0 : ℝ) 1, ∀ i, |coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i| ≤ ρ := by
  have hm (i : Fin n) : |η * w i| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)
  refine ⟨fun i => ?_, fun z hz i => ?_⟩
  · have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact (abs_sub _ _).trans (by linarith [hφ v hv i, hφ c hc i])
    change |η * w i * ∑ k, φ i k * (v k - c k)| ≤ 2 * η
    rw [abs_mul]; exact (mul_le_mul (hm i) hprof (abs_nonneg _) hη).trans_eq (by ring)
  · rw [← congrFun (coefficientRegression_reset η g w φ c v z) i]
    have hprof := hφ _ (coefficientReset_mem_ball C c v z hz hc hv) i
    change |g i + η * w i * ∑ k, φ i k * coefficientReset c v z k| ≤ ρ
    have hpt : |η * w i * ∑ k, φ i k * coefficientReset c v z k| ≤ η := by
      rw [abs_mul]; exact (mul_le_mul (hm i) hprof (abs_nonneg _) hη).trans_eq (mul_one η)
    exact (abs_add_le _ _).trans (by linarith [hg i, hpt])

theorem covariance_direction_product {n : ℕ} (C η : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i l : Fin n) :
    covarianceAction C A (fun v => coefficientDirection η w φ c v i *
      coefficientDirection η w φ c v l) = η ^ 2 * w i * w l * spatialFrameCovariance A φ i l := by
  have hdisp (k m : ι) : covarianceAction C A (fun v => (v k - c k) * (v m - c m)) = A k m := by
    rw [show (fun v : ι → ℝ => (v k - c k) * (v m - c m)) =
      fun v => v k * v m + (-c m) * v k + (-c k) * v m + c k * c m * 1 from funext fun _ => by ring,
      covarianceAction_add, covarianceAction_add, covarianceAction_add,
      covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
      covariance_second_moment_symmetric C A hC hA, covariance_zero_mean,
      covariance_zero_mean, covariance_zero_mass]
    ring
  rw [show (fun v : ι → ℝ => coefficientDirection η w φ c v i * coefficientDirection η w φ c v l) =
      fun v => η ^ 2 * w i * w l * ∑ k, ∑ m, (φ i k * φ l m) * ((v k - c k) * (v m - c m)) from
    funext fun _ => by
      simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring,
    covarianceAction_mul, covarianceAction_sum]
  congr 1; refine Finset.sum_congr rfl fun k _ => ?_
  rw [covarianceAction_sum]; refine Finset.sum_congr rfl fun m _ => ?_
  rw [covarianceAction_mul, hdisp]

def highResponseProduct {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (coefficientRegression η g w φ c i) V (y i)

theorem high_response_matrix_second {n : ℕ} (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      (1 / 2 : ℝ) * covarianceAction C A fun v =>
        finiteProductSecond Finset.univ
          (fun i z => ternaryMass a (coefficientRegression η g w φ c i +
            z * coefficientDirection η w φ c v i) V (y i))
          (fun i z => coefficientDirection η w φ c v i * ternaryMeanDerivative a
            (coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i) (y i))
          (fun i _ => (coefficientDirection η w φ c v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0 := by
  rw [← covarianceAction_mul]; apply congrArg (covarianceAction C A); funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  rw [response_line_rule_exact q n a V _ _ y hn]
  linarith [response_line_quadratic_coefficient n a V
    (coefficientRegression η g w φ c) (coefficientDirection η w φ c v) y]

def highResponseVarianceTerm {n : ℕ} (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) * ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (coefficientRegression η g w φ c l) V (y l)

theorem high_response_matrix_heat {n : ℕ} (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c
  let p := fun i => ternaryMass a (f i) V (y i)
  let m := fun i => ternaryMeanDerivative a (f i) (y i)
  let e := fun i => ternaryMeanSecondDerivative a (y i)
  let S : (ι → ℝ) → ℝ := fun v => ∑ i : Fin n,
    ((∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) * m l * m i * (δ v l * δ v i)) +
      (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i))
  rw [high_response_matrix_second q hn C a V η A g w φ c y]
  change (1 / 2 : ℝ) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * e i) 0) = _
  simp_rw [show ∀ v : ι → ℝ, finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * e i) 0 = S v from fun _ => by
    simp only [finiteProductSecond, zero_mul, add_zero, S]
    refine Finset.sum_congr rfl fun _ _ => ?_
    congr 1
    · rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by dsimp [p, m]; ring
    · dsimp [p]; ring]
  unfold S; rw [covarianceAction_sum]
  simp_rw [show ∀ i : Fin n, covarianceAction C A
      (fun v => (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) * m l * m i * (δ v l * δ v i)) +
        (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i)) =
      2 * η ^ 2 * (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i from fun i => by
    rw [covarianceAction_add, covarianceAction_sum,
      Finset.sum_eq_zero fun l hl => by
        rw [covarianceAction_mul, covariance_direction_product C η A hC hA w φ c l i,
          hdiag l i, ite_eq_right (Finset.ne_of_mem_erase hl), mul_zero, mul_zero],
      zero_add, covarianceAction_mul, covariance_direction_product C η A hC hA w φ c i i,
      hdiag i i, ite_eq_left rfl]
    dsimp [e, highResponseVarianceTerm]; rw [ternary_heat_identity]; dsimp [p, f]; ring]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem high_response_matrix_all_count_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ / 2) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y)| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin (2 * q + 2), |responseWeight q j|) *
          (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2)) := by
  unfold responseMatrixAction
  refine covarianceAction_abs_le _ _ _ _ fun k l s t => ?_
  let v := covarianceAtom C k l s t
  obtain ⟨hδ, hf⟩ := coefficient_direction_and_reset_bounds C η ρ hη hηρ g w φ c v
    hc (covarianceAtom_mem_ball C hC k l s t) hg hw hφ
  simp only [highResponseProduct, coefficientRegression_reset]
  exact response_scalar_product_action_abs_bound q n hn a V η ρ _ _ y ha hη hρ hf
    (fun z hz i u => hp _ (hf z hz i) u) hδ

def highResponseQuadraticAction {n : ℕ} (C a V η : ℝ) (A : ι → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  covarianceAction C A fun v =>
    (responseLinePolynomial n a V (coefficientRegression η g w φ c)
      (coefficientDirection η w φ c v) y).coeff 2

def highResponseDerivativeBudget (a ρ : ℝ) : ℝ :=
  max 1 (max ((2 * ρ + a) / a ^ 2) (2 / a ^ 2))

theorem highResponseDerivativeBudget_guards (a ρ : ℝ) :
    1 ≤ highResponseDerivativeBudget a ρ ∧
    (2 * ρ + a) / a ^ 2 ≤ highResponseDerivativeBudget a ρ ∧
    2 / a ^ 2 ≤ highResponseDerivativeBudget a ρ :=
  ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

def highResponseDefect {n : ℕ} (q : ℕ) (C a V η : ℝ) (A : ι → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) -
    highResponseQuadraticAction C a V η A g w φ c y

theorem high_response_matrix_heat_with_defect {n : ℕ} (q : ℕ)
    (C a V η : ℝ) (A : ι → ι → ℝ) (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (y : Fin n → Fin 3) (d : Fin n → ℝ)
    (hdiag : ∀ i l, spatialFrameCovariance A φ i l = if i = l then d i else 0) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      η ^ 2 * ∑ i, (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i +
        highResponseDefect q C a V η A g w φ c y := by
  have hqe : highResponseQuadraticAction C a V η A g w φ c y =
      responseMatrixAction n C A c (fun c => highResponseProduct a V η g w φ c y) := by
    unfold highResponseQuadraticAction responseMatrixAction
    apply congrArg (covarianceAction C A); funext v
    simp only [highResponseProduct, coefficientRegression_reset]
    exact (response_line_rule_exact n n a V _ _ y le_rfl).symm
  unfold highResponseDefect
  rw [hqe, high_response_matrix_heat n le_rfl C a V η A hC hA g w φ c y d hdiag]; ring

def highResponseRemainderConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  2 * C ^ 2 * (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    (2 * highResponseDerivativeBudget a ρ) ^ (2 * q + 2)

theorem high_response_defect_abs_bound {n : ℕ} (q : ℕ) (hq : 1 ≤ q)
    (C a V η ρ : ℝ) (hC : 0 < C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2)
    (A : ι → ι → ℝ) (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ)
    (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |highResponseDefect q C a V η A g w φ c y| ≤
      highResponseRemainderConstant q C a ρ * (∑ k, ∑ l, |A k l|) *
        (n : ℝ) ^ (2 * q + 2) * η ^ (2 * q + 2) := by
  obtain ⟨hB, hMean, hSecond⟩ := highResponseDerivativeBudget_guards a ρ
  let B := highResponseDerivativeBudget a ρ
  have hmain : |highResponseDefect q C a V η A g w φ c y| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin (2 * q + 2), |responseWeight q j|) * ((n : ℝ) * (2 * η * B)) ^ (2 * q + 2)) := by
    unfold highResponseDefect responseMatrixAction highResponseQuadraticAction
    rw [show covarianceAction C A
        (fun v => ∑ j : Fin (2 * q + 2), responseWeight q j *
          highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) -
        covarianceAction C A
          (fun v => (responseLinePolynomial n a V (coefficientRegression η g w φ c)
            (coefficientDirection η w φ c v) y).coeff 2) =
        covarianceAction C A fun v =>
          (∑ j : Fin (2 * q + 2), responseWeight q j *
            highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) -
          (responseLinePolynomial n a V (coefficientRegression η g w φ c)
            (coefficientDirection η w φ c v) y).coeff 2 by
      simp only [covarianceAction, mul_sub, Finset.sum_sub_distrib]]
    apply covarianceAction_abs_le
    intro k l s t
    let v := covarianceAtom C k l s t
    obtain ⟨hδ, hf⟩ := coefficient_direction_and_reset_bounds C η ρ hη hηρ g w φ c v
      hc (covarianceAtom_mem_ball C hC k l s t) hg hw hφ
    simp only [highResponseProduct, coefficientRegression_reset]
    exact response_scalar_high_order_remainder q hq n a V η ρ B _ _ y ha hη hρ hB hMean hSecond hf
      (fun z hz i u => hp _ (hf z hz i) u) hδ
  refine hmain.trans_eq ?_
  unfold highResponseRemainderConstant; dsimp [B]
  rw [show (n : ℝ) * (2 * η * highResponseDerivativeBudget a ρ) =
    (2 * highResponseDerivativeBudget a ρ) * (n : ℝ) * η by ring, mul_pow, mul_pow]
  ring

end CovarianceAndRemainder
end ResponseUpdates
end DerivativeAndResponseRules


-- ============================================================================
-- 2. Finite History Polynomials, Order Volumes, Upper Sets, and Transport
-- ============================================================================

section HistoryCombinatorics

section PolynomialOrderAndUpperSets
variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyMaximalPieces (S : Finset α) : Finset α := by
  classical exact S.filter fun x => ∀ y ∈ S, x ≤ y → y = x

theorem mem_historyMaximalPieces {S : Finset α} {x : α} :
    x ∈ historyMaximalPieces S ↔ x ∈ S ∧ ∀ y ∈ S, x ≤ y → y = x := by
  classical simp [historyMaximalPieces]

private lemma historyMaximalPieces_subset (S : Finset α) : historyMaximalPieces S ⊆ S :=
  fun _ hx => (mem_historyMaximalPieces.1 hx).1

@[simp] def historyDeletionCoefficient (weight : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, S => ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x)

@[simp] theorem historyDeletionCoefficient_succ (weight : α → ℝ) (k : ℕ) (S : Finset α) :
    historyDeletionCoefficient weight (k + 1) S =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionCoefficient weight k (S.erase x) := rfl

def historyDeletionPolynomial (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (S.card + 1), t ^ k / (k.factorial : ℝ) * historyDeletionCoefficient weight k S

private lemma historyDeletionPolynomial_at_zero (weight : α → ℝ) (S : Finset α) :
    historyDeletionPolynomial weight S 0 = 1 := by
  rw [historyDeletionPolynomial, Finset.sum_eq_single 0] <;> simp +contextual [zero_pow]

private lemma historyDeletionPolynomial_hasDerivAt (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyDeletionPolynomial weight S)
      (∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) t) t := by
  refine (HasDerivAt.fun_sum (u := Finset.range (S.card + 1)) fun k _ =>
    (((hasDerivAt_id' t).pow k).div_const (k.factorial : ℝ)).mul_const
      (historyDeletionCoefficient weight k S)).congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [id_eq, mul_one, Nat.cast_zero, zero_mul, zero_div, add_zero, Nat.add_sub_cancel]
  refine (Finset.sum_congr rfl fun k _ => by
    change _ = t ^ k / (k.factorial : ℝ) * historyDeletionCoefficient weight (k + 1) S
    rw [Nat.factorial_succ]; push_cast; field_simp).trans ?_
  simp_rw [historyDeletionCoefficient_succ, Finset.mul_sum]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxS := historyMaximalPieces_subset S hx
  have hc : (S.erase x).card + 1 = S.card := by
    have := Finset.card_erase_of_mem hxS; have := Finset.card_pos.2 ⟨x, hxS⟩; omega
  simp [historyDeletionPolynomial, hc, Finset.mul_sum, mul_left_comm, mul_assoc]

def IncomparableHistoryParts (P Q : Finset α) : Prop :=
  ∀ p ∈ P, ∀ q ∈ Q, ¬ p ≤ q ∧ ¬ q ≤ p

omit [DecidableEq α] in
private lemma IncomparableHistoryParts.symm {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    IncomparableHistoryParts Q P := fun q hq p hp => (h p hp q hq).symm

omit [DecidableEq α] in
private lemma IncomparableHistoryParts.disjoint {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    Disjoint P Q := Finset.disjoint_left.2 fun x hxP hxQ => (h x hxP x hxQ).1 le_rfl

private lemma historyMaximalPieces_union {P Q : Finset α} (h : IncomparableHistoryParts P Q) :
    historyMaximalPieces (P ∪ Q) = historyMaximalPieces P ∪ historyMaximalPieces Q := by
  classical
  ext x; rw [mem_historyMaximalPieces, Finset.mem_union, Finset.mem_union,
    mem_historyMaximalPieces, mem_historyMaximalPieces]
  refine ⟨fun ⟨hx, hm⟩ => hx.elim
    (fun hxP => Or.inl ⟨hxP, fun y hy => hm y (Finset.mem_union_left _ hy)⟩)
    (fun hxQ => Or.inr ⟨hxQ, fun y hy => hm y (Finset.mem_union_right _ hy)⟩), ?_⟩
  rintro (⟨hxP, hm⟩ | ⟨hxQ, hm⟩)
  · exact ⟨Or.inl hxP, fun y hy hxy => (Finset.mem_union.1 hy).elim (fun hyP => hm y hyP hxy)
      fun hyQ => ((h x hxP y hyQ).1 hxy).elim⟩
  · exact ⟨Or.inr hxQ, fun y hy hxy => (Finset.mem_union.1 hy).elim
      (fun hyP => ((h y hyP x hxQ).2 hxy).elim) fun hyQ => hm y hyQ hxy⟩

def historyOrderCount (S : Finset α) : ℝ := historyDeletionCoefficient (fun _ : α => (1 : ℝ)) S.card S

def historyOrderVolume (S : Finset α) : ℝ := historyOrderCount S / (S.card.factorial : ℝ)

@[simp] private lemma historyOrderVolume_empty : historyOrderVolume (∅ : Finset α) = 1 := by
  simp [historyOrderVolume, historyOrderCount]

private lemma historyOrderCount_recursion (S : Finset α) (hS : S.Nonempty) :
    historyOrderCount S = ∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x) := by
  have hpos := Finset.card_pos.2 hS
  unfold historyOrderCount
  conv_lhs => rw [show S.card = (S.card - 1) + 1 by omega, historyDeletionCoefficient_succ]
  exact Finset.sum_congr rfl fun x hx => by
    rw [Finset.card_erase_of_mem (historyMaximalPieces_subset S hx), one_mul]

private lemma historyOrderVolume_nonneg (S : Finset α) : 0 ≤ historyOrderVolume S := by
  refine div_nonneg ?_ (by positivity)
  have hh (k : ℕ) : ∀ T : Finset α, 0 ≤ historyDeletionCoefficient (fun _ : α => (1 : ℝ)) k T := by
    induction k with
    | zero => simp
    | succ k ih => intro T; exact Finset.sum_nonneg fun x _ => by simpa only [one_mul] using ih (T.erase x)
  exact hh S.card S

private lemma historyOrderVolume_le_one (S : Finset α) : historyOrderVolume S ≤ 1 := by
  refine (div_le_one (by positivity : 0 < (S.card.factorial : ℝ))).2 ?_
  induction S using Finset.strongInductionOn with | _ S ih =>
  by_cases he : S = ∅
  · subst S; simp [historyOrderCount]
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    rw [historyOrderCount_recursion S hS]
    calc
      _ ≤ ∑ _x ∈ historyMaximalPieces S, ((S.card - 1).factorial : ℝ) := Finset.sum_le_sum fun x hx => by
        have hxS := historyMaximalPieces_subset S hx
        simpa only [Finset.card_erase_of_mem hxS] using ih (S.erase x) (Finset.erase_ssubset hxS)
      _ = (historyMaximalPieces S).card * ((S.card - 1).factorial : ℝ) := by simp
      _ ≤ (S.card : ℝ) * ((S.card - 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (historyMaximalPieces_subset S)) (by positivity)
      _ = (S.card.factorial : ℝ) := by
        have hc : S.card = (S.card - 1) + 1 := by omega
        conv_rhs => rw [hc, Nat.factorial_succ]
        push_cast; congr 1; exact_mod_cast hc

private lemma historyOrderVolume_recursion (S : Finset α) :
    (S.card : ℝ) * historyOrderVolume S = ∑ x ∈ historyMaximalPieces S, historyOrderVolume (S.erase x) := by
  classical
  by_cases he : S = ∅
  · subst S; simp [historyMaximalPieces]
  · have hS := Finset.nonempty_iff_ne_empty.2 he
    have hn := Finset.card_pos.2 hS
    have hc : S.card = (S.card - 1) + 1 := by omega
    unfold historyOrderVolume
    rw [historyOrderCount_recursion S hS]
    conv_lhs => arg 2; arg 2; rw [hc, Nat.factorial_succ]
    push_cast
    rw [show (S.card : ℝ) = ((S.card - 1 : ℕ) : ℝ) + 1 by exact_mod_cast hc]
    calc
      _ = (∑ x ∈ historyMaximalPieces S, historyOrderCount (S.erase x)) / ((S.card - 1).factorial : ℝ) := by
        field_simp [show (((S.card - 1 : ℕ) : ℝ) + 1) ≠ 0 by positivity]
      _ = _ := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun x hx => by rw [Finset.card_erase_of_mem (historyMaximalPieces_subset S hx)]

private lemma historyOrderVolume_union {P Q : Finset α} (hinc : IncomparableHistoryParts P Q) :
    historyOrderVolume (P ∪ Q) = historyOrderVolume P * historyOrderVolume Q := by
  classical
  suffices hmain : ∀ n : ℕ, ∀ P Q : Finset α, (P ∪ Q).card = n → IncomparableHistoryParts P Q →
      historyOrderVolume (P ∪ Q) = historyOrderVolume P * historyOrderVolume Q from
    hmain (P ∪ Q).card P Q rfl hinc
  intro n; induction n using Nat.strong_induction_on with | _ n ih =>
  intro P Q hn hinc
  by_cases he : P ∪ Q = ∅
  · obtain ⟨rfl, rfl⟩ := Finset.union_eq_empty.1 he; simp
  · have hdis := hinc.disjoint
    have hside : ∀ A B : Finset α, (A ∪ B).card = n → IncomparableHistoryParts A B →
        (∑ x ∈ historyMaximalPieces A, historyOrderVolume ((A ∪ B).erase x)) =
          (A.card : ℝ) * historyOrderVolume A * historyOrderVolume B := by
      intro A B hAB hiAB
      have hdAB := hiAB.disjoint
      rw [show (∑ x ∈ historyMaximalPieces A, historyOrderVolume ((A ∪ B).erase x)) =
          ∑ x ∈ historyMaximalPieces A, historyOrderVolume (A.erase x) * historyOrderVolume B from
        Finset.sum_congr rfl fun x hx => by
          have hxA := historyMaximalPieces_subset A hx
          have hU : (A ∪ B).erase x = A.erase x ∪ B := by
            rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem fun hxB => Finset.disjoint_left.1 hdAB hxA hxB]
          rw [hU]
          exact ih _ (by rw [← hU, ← hAB]; exact Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_union_left _ hxA)))
            (A.erase x) B rfl (fun a ha b hb => hiAB a (Finset.mem_of_mem_erase ha) b hb),
        ← Finset.sum_mul, ← historyOrderVolume_recursion]
    have hrec := historyOrderVolume_recursion (P ∪ Q)
    rw [historyMaximalPieces_union hinc,
      Finset.sum_union (hdis.mono (historyMaximalPieces_subset P) (historyMaximalPieces_subset Q)),
      hside P Q hn hinc] at hrec
    simp_rw [Finset.union_comm P Q] at hrec
    rw [hside Q P (by rwa [Finset.union_comm]) hinc.symm, Finset.union_comm Q P] at hrec
    have hpos : (0 : ℝ) < (P ∪ Q).card := by exact_mod_cast Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 he)
    apply mul_left_cancel₀ hpos.ne'
    rw [hrec, Finset.card_union_of_disjoint hdis]; push_cast; ring

def historyComponentWeight (weight : α → ℝ) (ρ t : ℝ) (P : Finset α) : ℝ :=
  (t / ρ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, weight x

private lemma historyComponentWeight_union (weight : α → ℝ) (ρ t : ℝ) {P Q : Finset α}
    (hinc : IncomparableHistoryParts P Q) :
    historyComponentWeight weight ρ t (P ∪ Q) =
      historyComponentWeight weight ρ t P * historyComponentWeight weight ρ t Q := by
  have hdis := hinc.disjoint
  unfold historyComponentWeight
  rw [Finset.card_union_of_disjoint hdis, pow_add, historyOrderVolume_union hinc, Finset.prod_union hdis]; ring

private lemma historyComponentWeight_abs_le {weight : α → ℝ} {ρ t B : ℝ} (P : Finset α)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (_hB : 0 ≤ B) (hw : ∀ x ∈ P, |weight x| ≤ B) :
    |historyComponentWeight weight ρ t P| ≤ (t * B / ρ) ^ P.card := by
  have hp : 0 ≤ t / ρ := div_nonneg ht hρ.le
  unfold historyComponentWeight
  rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hp _), abs_of_nonneg (historyOrderVolume_nonneg P), Finset.abs_prod]
  refine (mul_le_mul (mul_le_mul_of_nonneg_left (historyOrderVolume_le_one P) (pow_nonneg hp _))
    ((Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hw).trans_eq (Finset.prod_const B))
    (by positivity) (by positivity)).trans_eq ?_
  rw [mul_one, ← mul_pow]; congr 1; ring

def IsHistoryUpper (S U : Finset α) : Prop :=
  U ⊆ S ∧ ∀ x ∈ U, ∀ y ∈ S, x ≤ y → y ∈ U

def historyUpperSets (S : Finset α) : Finset (Finset α) := by
  classical exact S.powerset.filter (IsHistoryUpper S)

omit [DecidableEq α] in
private lemma mem_historyUpperSets {S U : Finset α} :
    U ∈ historyUpperSets S ↔ IsHistoryUpper S U := by
  classical
  simp only [historyUpperSets, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

private lemma historyUpper_maximal_subset {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyMaximalPieces U ⊆ historyMaximalPieces S := fun x hx => by
  obtain ⟨hxU, hmax⟩ := mem_historyMaximalPieces.1 hx
  exact mem_historyMaximalPieces.2 ⟨hU.1 hxU, fun y hy hxy => hmax y (hU.2 x hxU y hy hxy) hxy⟩

private lemma historyUpper_maximal_eq_inter {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyMaximalPieces U = U ∩ historyMaximalPieces S := by
  ext x; refine ⟨fun hx => Finset.mem_inter.2 ⟨historyMaximalPieces_subset U hx, historyUpper_maximal_subset hU hx⟩,
    fun hx => ?_⟩
  obtain ⟨hxU, hxS⟩ := Finset.mem_inter.1 hx
  exact mem_historyMaximalPieces.2 ⟨hxU, fun y hy => (mem_historyMaximalPieces.1 hxS).2 y (hU.1 hy)⟩

private lemma historyUpper_erase {S U : Finset α} (hU : IsHistoryUpper S U) {x : α}
    (_hx : x ∈ historyMaximalPieces U) : IsHistoryUpper (S.erase x) (U.erase x) :=
  ⟨Finset.erase_subset_erase _ hU.1, fun a ha b hb hab =>
    Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hb).1, hU.2 a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab⟩⟩

private lemma historyUpper_insert {S U : Finset α} {x : α}
    (hx : x ∈ historyMaximalPieces S) (hU : IsHistoryUpper (S.erase x) U) :
    IsHistoryUpper S (insert x U) := by
  obtain ⟨hxS, hmax⟩ := mem_historyMaximalPieces.1 hx
  refine ⟨Finset.insert_subset hxS (hU.1.trans (Finset.erase_subset _ _)), fun a ha b hb hab => ?_⟩
  rcases Finset.mem_insert.1 ha with rfl | haU
  · rw [hmax b hb hab]; exact Finset.mem_insert_self _ _
  · by_cases hbx : b = x
    · subst b; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hU.2 a haU b (Finset.mem_erase.2 ⟨hbx, hb⟩) hab)

private lemma historyUpper_not_mem_deleted {S U : Finset α} {x : α}
    (hU : IsHistoryUpper (S.erase x) U) : x ∉ U := fun hxU => Finset.notMem_erase x S (hU.1 hxU)

omit [DecidableEq α] in
private lemma historyUpper_disjoint_incomparable {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) (hdis : Disjoint P Q) :
    IncomparableHistoryParts P Q := fun p hp q hq =>
  ⟨fun hpq => Finset.disjoint_left.1 hdis (hP.2 p hp q (hQ.1 hq) hpq) hq,
   fun hqp => Finset.disjoint_left.1 hdis hp (hQ.2 q hq p (hP.1 hp) hqp)⟩

private lemma historyUpper_nonempty_maximal {S U : Finset α} (_hU : IsHistoryUpper S U)
    (hne : U.Nonempty) : (historyMaximalPieces U).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := U.exists_maximal hne
  exact ⟨x, mem_historyMaximalPieces.2 ⟨hx, fun y hy hxy => le_antisymm (hmax hy hxy) hxy⟩⟩

private lemma historyUpper_disjoint_iff {S P Q : Finset α}
    (hP : IsHistoryUpper S P) (hQ : IsHistoryUpper S Q) :
    Disjoint P Q ↔ Disjoint (historyMaximalPieces P) (historyMaximalPieces Q) := by
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty,
    ← Finset.not_nonempty_iff_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  refine not_congr ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ => ?_⟩
  · obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
    obtain ⟨y, hxy, hyS, hmax⟩ := S.exists_le_maximal (hP.1 hxP)
    have hymax : y ∈ historyMaximalPieces S :=
      mem_historyMaximalPieces.2 ⟨hyS, fun z hz hyz => le_antisymm (hmax hz hyz) hyz⟩
    refine ⟨y, Finset.mem_inter.2 ⟨?_, ?_⟩⟩
    · rw [historyUpper_maximal_eq_inter hP]; exact Finset.mem_inter.2 ⟨hP.2 x hxP y hyS hxy, hymax⟩
    · rw [historyUpper_maximal_eq_inter hQ]; exact Finset.mem_inter.2 ⟨hQ.2 x hxQ y hyS hxy, hymax⟩
  · obtain ⟨hxP, hxQ⟩ := Finset.mem_inter.1 hx
    exact ⟨x, Finset.mem_inter.2 ⟨historyMaximalPieces_subset P hxP, historyMaximalPieces_subset Q hxQ⟩⟩

private lemma historyUpper_maximal_sum (S : Finset α) (F : Finset α → α → ℝ) :
    (∑ U ∈ historyUpperSets S, ∑ x ∈ historyMaximalPieces U, F U x) =
      ∑ x ∈ historyMaximalPieces S, ∑ U ∈ historyUpperSets (S.erase x), F (insert x U) x := by
  classical
  suffices hh : (∑ i ∈ (historyUpperSets S).sigma historyMaximalPieces, F i.1 i.2) =
      ∑ i ∈ (historyMaximalPieces S).sigma (fun x => historyUpperSets (S.erase x)), F (insert i.1 i.2) i.1 by
    simpa only [Finset.sum_sigma] using hh
  refine Finset.sum_bij (fun i _ => ⟨i.2, i.1.erase i.2⟩) ?_ ?_ ?_ ?_
  · intro i hi
    obtain ⟨hiU, hix⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    exact Finset.mem_sigma.2 ⟨historyUpper_maximal_subset hU hix, mem_historyUpperSets.2 (historyUpper_erase hU hix)⟩
  · intro ⟨U, x⟩ hi ⟨V, y⟩ hj heq
    obtain ⟨_, hix⟩ := Finset.mem_sigma.1 hi
    obtain ⟨_, hjy⟩ := Finset.mem_sigma.1 hj
    have hxy : x = y := congrArg Sigma.fst heq
    subst hxy
    have hrest : U.erase x = V.erase x := congrArg Sigma.snd heq
    have hUV : U = V := by
      rw [← Finset.insert_erase (historyMaximalPieces_subset U hix),
        ← Finset.insert_erase (historyMaximalPieces_subset V hjy), hrest]
    subst hUV; rfl
  · intro ⟨x, U⟩ hi
    obtain ⟨hix, hiU⟩ := Finset.mem_sigma.1 hi
    have hU := mem_historyUpperSets.1 hiU
    refine ⟨⟨insert x U, x⟩, Finset.mem_sigma.2 ⟨mem_historyUpperSets.2 (historyUpper_insert hix hU),
      mem_historyMaximalPieces.2 ⟨Finset.mem_insert_self _ _,
        fun y hy => (mem_historyMaximalPieces.1 hix).2 y ((historyUpper_insert hix hU).1 hy)⟩⟩, ?_⟩
    simp only [Finset.erase_insert (historyUpper_not_mem_deleted hU)]
  · intro i hi
    rw [Finset.insert_erase (historyMaximalPieces_subset i.1 (Finset.mem_sigma.1 hi).2)]

def historyUpperDensity (weight : α → ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  ∑ U ∈ historyUpperSets S, t ^ U.card * historyOrderVolume U * ∏ x ∈ U, weight x

@[simp] private lemma historyUpperDensity_at_zero (weight : α → ℝ) (S : Finset α) :
    historyUpperDensity weight S 0 = 1 := by
  rw [historyUpperDensity, Finset.sum_eq_single ∅]
  · simp
  · intro U _ hne; simp [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne))]
  · intro h; exact (h (mem_historyUpperSets.2 ⟨Finset.empty_subset _, by simp⟩)).elim

private lemma historyUpperDensity_hasDerivAt (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyUpperDensity weight S)
      (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) t) t := by
  have hh : HasDerivAt (historyUpperDensity weight S)
      (∑ U ∈ historyUpperSets S,
        ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * ∏ x ∈ U, weight x) t :=
    HasDerivAt.fun_sum fun U _ => by
      simpa only [id_eq, mul_one] using! (((hasDerivAt_id t).pow U.card).mul_const
        (historyOrderVolume U)).mul_const (∏ x ∈ U, weight x)
  refine hh.congr_deriv ?_
  simp_rw [show ∀ U : Finset α, ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * (∏ x ∈ U, weight x) =
      ∑ x ∈ historyMaximalPieces U, weight x * (t ^ (U.erase x).card * historyOrderVolume (U.erase x) *
        ∏ y ∈ U.erase x, weight y) from fun U => by
    rw [show ((U.card : ℝ) * t ^ (U.card - 1)) * historyOrderVolume U * (∏ x ∈ U, weight x) =
      t ^ (U.card - 1) * ((U.card : ℝ) * historyOrderVolume U) * (∏ x ∈ U, weight x) by ring,
      historyOrderVolume_recursion, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x hx => by
      have hxU := historyMaximalPieces_subset U hx
      rw [Finset.card_erase_of_mem hxU, ← Finset.mul_prod_erase U weight hxU]; ring]
  rw [historyUpper_maximal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold historyUpperDensity; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun U hU => by
    rw [Finset.erase_insert (historyUpper_not_mem_deleted (mem_historyUpperSets.1 hU))]

theorem historyUpperDensity_eq_deletionPolynomial (weight : α → ℝ) (S : Finset α) (t : ℝ) :
    historyUpperDensity weight S t = historyDeletionPolynomial weight S t := by
  induction S using Finset.strongInductionOn generalizing t with | _ S ih =>
  have hd (u : ℝ) : HasDerivAt (fun v => historyUpperDensity weight S v -
      historyDeletionPolynomial weight S v) 0 u := by
    have hh := (historyUpperDensity_hasDerivAt weight S u).sub (historyDeletionPolynomial_hasDerivAt weight S u)
    rwa [show (∑ x ∈ historyMaximalPieces S, weight x * historyUpperDensity weight (S.erase x) u) =
      ∑ x ∈ historyMaximalPieces S, weight x * historyDeletionPolynomial weight (S.erase x) u from
      Finset.sum_congr rfl fun x hx => by
        rw [ih (S.erase x) (Finset.erase_ssubset (historyMaximalPieces_subset S hx)) u], sub_self] at hh
  have hh := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simp only [historyUpperDensity_at_zero, historyDeletionPolynomial_at_zero, sub_self] at hh
  exact sub_eq_zero.1 hh

def historyScaledUpperDensity (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) : ℝ :=
  historyUpperDensity (fun x => weight x / ρ) S t

theorem historyScaledUpperDensity_eq_components (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) :
    historyScaledUpperDensity weight ρ S t =
      ∑ U ∈ historyUpperSets S, historyComponentWeight weight ρ t U :=
  Finset.sum_congr rfl fun _ _ => by
    dsimp [historyComponentWeight]; rw [Finset.prod_div_distrib, Finset.prod_const, div_pow]; ring

theorem historyScaledUpperDensity_hasDerivAt (weight : α → ℝ) (ρ : ℝ) (S : Finset α) (t : ℝ) :
    HasDerivAt (historyScaledUpperDensity weight ρ S)
      (ρ⁻¹ * ∑ x ∈ historyMaximalPieces S, weight x * historyScaledUpperDensity weight ρ (S.erase x) t) t :=
  (historyUpperDensity_hasDerivAt (fun x => weight x / ρ) S t).congr_deriv
    (by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by dsimp [historyScaledUpperDensity]; ring)

end PolynomialOrderAndUpperSets

section OrderIsoTransport
variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]

theorem historyMaximalPieces_orderIso_map (e : A ≃o B) (S : Finset A) :
    historyMaximalPieces (S.map e.toEquiv.toEmbedding) =
      (historyMaximalPieces S).map e.toEquiv.toEmbedding := by
  classical
  have hmem (T : Finset A) (b : B) : b ∈ T.map e.toEquiv.toEmbedding ↔ e.symm b ∈ T :=
    ⟨fun hb => by obtain ⟨a, ha, hab⟩ := Finset.mem_map.1 hb; rwa [show e.symm b = a from e.injective (by simpa using hab.symm)],
     fun hb => Finset.mem_map.2 ⟨e.symm b, hb, e.apply_symm_apply b⟩⟩
  ext b; rw [mem_historyMaximalPieces, hmem, hmem, mem_historyMaximalPieces]
  refine ⟨fun ⟨hb, hm⟩ => ⟨hb, fun a ha hba => e.injective ?_⟩, fun ⟨hb, hm⟩ => ⟨hb, fun c hc hbc => ?_⟩⟩
  · simpa only [e.apply_symm_apply] using hm (e a) (Finset.mem_map.2 ⟨a, ha, rfl⟩)
      (by simpa only [e.apply_symm_apply] using e.monotone hba)
  · simpa only [e.apply_symm_apply] using congrArg e (hm (e.symm c) ((hmem S c).1 hc) (e.symm.monotone hbc))

private lemma historyDeletionCoefficient_orderIso_map (e : A ≃o B) (weight : B → ℝ)
    (k : ℕ) (S : Finset A) :
    historyDeletionCoefficient weight k (S.map e.toEquiv.toEmbedding) =
      historyDeletionCoefficient (weight ∘ e) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ, historyMaximalPieces_orderIso_map, Finset.sum_map]
    exact Finset.sum_congr rfl fun x _ => by rw [← Finset.map_erase, ih]; rfl

theorem historyScaledUpperDensity_orderIso_map (e : A ≃o B) (weight : B → ℝ)
    (ρ : ℝ) (S : Finset A) (t : ℝ) :
    historyScaledUpperDensity weight ρ (S.map e.toEquiv.toEmbedding) t =
      historyScaledUpperDensity (weight ∘ e) ρ S t := by
  unfold historyScaledUpperDensity
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial; rw [Finset.card_map]
  exact Finset.sum_congr rfl fun k _ => by rw [historyDeletionCoefficient_orderIso_map]; rfl

end OrderIsoTransport

-- ============================================================================
-- 3. Polymer Gas Positivity, Connected Components, Word Heap, and Activity
-- ============================================================================

section GasAndComponents

private lemma deletion_comparison {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (T U : Finset α) (hUT : U ⊆ T)
    (hstep : ∀ V ⊆ T, ∀ x ∈ V, F (V.erase x) ≤ 2 * F V) :
    F U ≤ (2 : ℝ) ^ (T.card - U.card) * F T := by
  induction T using Finset.strongInductionOn generalizing U with | _ T ih =>
  by_cases heq : U = T
  · subst U; simp
  · obtain ⟨x, hxT, hxU⟩ := Finset.not_subset.mp fun hTU => heq (Finset.Subset.antisymm hUT hTU)
    have hue : U ⊆ T.erase x := fun y hy => Finset.mem_erase.mpr ⟨fun h => hxU (h ▸ hy), hUT hy⟩
    have hcard : T.card - U.card = ((T.erase x).card - U.card) + 1 := by
      have := Finset.card_le_card hue; have := Finset.card_erase_of_mem hxT
      have := Finset.card_pos.mpr ⟨x, hxT⟩; omega
    calc
      F U ≤ (2 : ℝ) ^ ((T.erase x).card - U.card) * F (T.erase x) :=
        ih (T.erase x) (Finset.erase_ssubset hxT) U hue fun V hV => hstep V (hV.trans (Finset.erase_subset _ _))
      _ ≤ (2 : ℝ) ^ ((T.erase x).card - U.card) * (2 * F T) :=
        mul_le_mul_of_nonneg_left (hstep T Finset.Subset.rfl x hxT) (by positivity)
      _ = (2 : ℝ) ^ (T.card - U.card) * F T := by rw [hcard, pow_succ]; ring

private lemma positive_deletion_recurrence {α β : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (rows : Finset α → α → Finset β)
    (removed : β → Finset α) (weight : β → ℝ)
    (hempty : F ∅ = 1)
    (hremove : ∀ S x, x ∈ S → ∀ P ∈ rows S x, x ∈ removed P ∧ removed P ⊆ S)
    (hrec : ∀ S x, x ∈ S → F S = F (S.erase x) + ∑ P ∈ rows S x, weight P * F (S \ removed P))
    (hactivity : ∀ S x, x ∈ S → (∑ P ∈ rows S x, |weight P| * (2 : ℝ) ^ ((removed P).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < F S ∧ ∀ x ∈ S, F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
  intro S; induction S using Finset.strongInductionOn with | _ S ih =>
  by_cases he : S = ∅
  · subst S; simp [hempty]
  · have hratio (x : α) (hx : x ∈ S) :
        0 < F (S.erase x) ∧ F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x) := by
      have hprev := ih (S.erase x) (Finset.erase_ssubset hx)
      have hterms (P : β) (hP : P ∈ rows S x) :
          0 ≤ F (S \ removed P) ∧ F (S \ removed P) ≤ (2 : ℝ) ^ ((removed P).card - 1) * F (S.erase x) := by
        obtain ⟨hxP, hPS⟩ := hremove S x hx P hP
        have hsub : S \ removed P ⊆ S.erase x := fun y hy => by
          obtain ⟨hyS, hyn⟩ := Finset.mem_sdiff.mp hy
          exact Finset.mem_erase.mpr ⟨fun h => hyn (h ▸ hxP), hyS⟩
        have hc : (S.erase x).card - (S \ removed P).card = (removed P).card - 1 := by
          have := Finset.card_le_card hPS; have := Finset.card_pos.mpr ⟨x, hxP⟩
          rw [Finset.card_erase_of_mem hx, Finset.card_sdiff_of_subset hPS]; omega
        refine ⟨(ih _ (hsub.trans_ssubset (Finset.erase_ssubset hx))).1.le, ?_⟩
        rw [← hc]
        exact deletion_comparison F (S.erase x) (S \ removed P) hsub fun V hV y hy => by
          linarith [((ih V (hV.trans_ssubset (Finset.erase_ssubset hx))).2 y hy).1]
      have herr : |F S - F (S.erase x)| ≤ F (S.erase x) / 2 := by
        rw [hrec S x hx, add_sub_cancel_left]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine ((Finset.sum_le_sum (g := fun P => |weight P| * ((2 : ℝ) ^ ((removed P).card - 1) * F (S.erase x)))
            fun P hP => ?_).trans_eq ?_).trans
          ((mul_le_mul_of_nonneg_right (hactivity S x hx) hprev.1.le).trans_eq (by ring))
        · rw [abs_mul, abs_of_nonneg (hterms P hP).1]
          exact mul_le_mul_of_nonneg_left (hterms P hP).2 (abs_nonneg _)
        · simp_rw [← mul_assoc]; rw [Finset.sum_mul]
      exact ⟨hprev.1, by linarith [neg_le_abs (F S - F (S.erase x))],
        by linarith [le_abs_self (F S - F (S.erase x))]⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
    exact ⟨by linarith [(hratio x hx).1, (hratio x hx).2.1], fun y hy => (hratio y hy).2⟩

private lemma deletion_ratios_global_bounds {α : Type*} [DecidableEq α]
    (F : Finset α → ℝ) (hempty : F ∅ = 1)
    (hstep : ∀ S x, x ∈ S → F (S.erase x) / 2 ≤ F S ∧ F S ≤ 3 / 2 * F (S.erase x)) :
    ∀ S, (1 / 2 : ℝ) ^ S.card ≤ F S ∧ F S ≤ (3 / 2 : ℝ) ^ S.card := by
  intro S; induction S using Finset.induction_on with
  | empty => simp [hempty]
  | @insert x S hx ih =>
    have h := hstep (insert x S) x (by simp)
    simp only [Finset.erase_insert hx] at h
    rw [Finset.card_insert_of_notMem hx, pow_succ, pow_succ]
    constructor <;> nlinarith [ih.1, ih.2]

section GasDefinitions
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def CompatibleHistoryFamily (support : β → Finset α) (F : Finset β) : Prop :=
  ∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q)

def historyGasFamilies (P : Finset β) (support : β → Finset α) (S : Finset α) : Finset (Finset β) := by
  classical exact P.powerset.filter fun F => CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S

def historyGasPartition (P : Finset β) (support : β → Finset α) (weight : β → ℝ) (S : Finset α) : ℝ :=
  ∑ F ∈ historyGasFamilies P support S, ∏ p ∈ F, weight p

def historyGasRows (P : Finset β) (support : β → Finset α) (S : Finset α) (x : α) : Finset β :=
  P.filter fun p => x ∈ support p ∧ support p ⊆ S

omit [DecidableEq β] in
private lemma mem_historyGasFamilies {P : Finset β} {support : β → Finset α} {S : Finset α} {F : Finset β} :
    F ∈ historyGasFamilies P support S ↔
      F ⊆ P ∧ CompatibleHistoryFamily support F ∧ ∀ p ∈ F, support p ⊆ S := by
  classical simp only [historyGasFamilies, Finset.mem_filter, Finset.mem_powerset]

omit [DecidableEq β] in
private lemma historyGasPartition_empty (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (hne : ∀ p ∈ P, (support p).Nonempty) : historyGasPartition P support weight ∅ = 1 := by
  classical
  unfold historyGasPartition
  rw [show historyGasFamilies P support ∅ = {∅} by
    ext F; rw [Finset.mem_singleton, mem_historyGasFamilies]
    refine ⟨fun ⟨hFP, _, hs⟩ => Finset.eq_empty_iff_forall_notMem.2 fun p hp => ?_,
      fun hF => by subst F; simp [CompatibleHistoryFamily]⟩
    obtain ⟨x, hx⟩ := hne p (hFP hp); simpa using hs p hp hx]
  simp

private lemma historyGasFamily_insert_component {P : Finset β} {support : β → Finset α} {S : Finset α}
    {F : Finset β} {p : β} (hF : F ∈ historyGasFamilies P support (S \ support p))
    (hp : p ∈ P) (hps : support p ⊆ S) : insert p F ∈ historyGasFamilies P support S := by
  obtain ⟨hFP, hcompat, hsupport⟩ := mem_historyGasFamilies.1 hF
  refine mem_historyGasFamilies.2 ⟨Finset.insert_subset hp hFP, fun q hq r hr hqr => ?_, fun q hq => ?_⟩
  · by_cases hqp : q = p
    · subst q; have hrF := Finset.mem_of_mem_insert_of_ne hr (Ne.symm hqr)
      exact Finset.disjoint_left.2 fun x hx hx' => (Finset.mem_sdiff.1 (hsupport r hrF hx')).2 hx
    · have hqF := Finset.mem_of_mem_insert_of_ne hq hqp
      by_cases hrp : r = p
      · subst r; exact Finset.disjoint_left.2 fun x hx hx' => (Finset.mem_sdiff.1 (hsupport q hqF hx)).2 hx'
      · exact hcompat q hqF r (Finset.mem_of_mem_insert_of_ne hr hrp) hqr
  · rcases Finset.mem_insert.1 hq with rfl | hq
    · exact hps
    · exact (hsupport q hq).trans Finset.sdiff_subset

private lemma historyGasPartition_deletion (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (S : Finset α) (x : α) :
    historyGasPartition P support weight S = historyGasPartition P support weight (S.erase x) +
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
  classical
  have herase : historyGasFamilies P support (S.erase x) =
      (historyGasFamilies P support S).filter (fun F => ¬ ∃ p ∈ F, x ∈ support p) := by
    ext F; rw [mem_historyGasFamilies, Finset.mem_filter, mem_historyGasFamilies]
    exact ⟨fun ⟨hFP, hc, hs⟩ => ⟨⟨hFP, hc, fun p hp => (hs p hp).trans (Finset.erase_subset _ _)⟩,
        fun ⟨p, hp, hxp⟩ => (Finset.mem_erase.1 (hs p hp hxp)).1 rfl⟩,
      fun ⟨⟨hFP, hc, hs⟩, hnone⟩ => ⟨hFP, hc, fun p hp y hy =>
        Finset.mem_erase.2 ⟨fun hyx => hnone ⟨p, hp, hyx ▸ hy⟩, hs p hp hy⟩⟩⟩
  have hact : (∑ F ∈ (historyGasFamilies P support S).filter (fun F => ∃ p ∈ F, x ∈ support p), ∏ p ∈ F, weight p) =
      ∑ p ∈ historyGasRows P support S x, weight p * historyGasPartition P support weight (S \ support p) := by
    let rows := historyGasRows P support S x
    let fams := fun p => historyGasFamilies P support (S \ support p)
    suffices hh : (∑ i ∈ rows.sigma fams, weight i.1 * ∏ p ∈ i.2, weight p) =
        ∑ F ∈ (historyGasFamilies P support S).filter (fun F => ∃ p ∈ F, x ∈ support p), ∏ p ∈ F, weight p by
      rw [← hh, Finset.sum_sigma]
      exact Finset.sum_congr rfl fun _ _ => by dsimp [historyGasPartition, fams]; rw [Finset.mul_sum]
    refine Finset.sum_bij (fun i _ => insert i.1 i.2) ?_ ?_ ?_ ?_
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      exact Finset.mem_filter.2 ⟨historyGasFamily_insert_component hiF hiP hiS, i.1, Finset.mem_insert_self _ _, hix⟩
    · intro ⟨p, F⟩ hi ⟨q, G⟩ hj heq
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨hjp, hjG⟩ := Finset.mem_sigma.1 hj
      obtain ⟨hiP, hix, hiS⟩ := Finset.mem_filter.1 hip
      obtain ⟨_, hjx, _⟩ := Finset.mem_filter.1 hjp
      have hfam := historyGasFamily_insert_component hiF hiP hiS
      have hji : q ∈ insert p F := heq ▸ Finset.mem_insert_self _ _
      have hpq : p = q := by
        by_contra hne
        exact Finset.disjoint_left.1 ((mem_historyGasFamilies.1 hfam).2.1 p (Finset.mem_insert_self _ _) q hji hne) hix hjx
      subst hpq
      have hnF : p ∉ F := fun hp => (Finset.mem_sdiff.1 ((mem_historyGasFamilies.1 hiF).2.2 p hp hix)).2 hix
      have hnG : p ∉ G := fun hp => (Finset.mem_sdiff.1 ((mem_historyGasFamilies.1 hjG).2.2 p hp hix)).2 hix
      have hFG := congrArg (fun T : Finset β => T.erase p) heq
      simp only [Finset.erase_insert hnF, Finset.erase_insert hnG] at hFG
      subst hFG; rfl
    · intro F hF
      obtain ⟨hfam, p, hp, hxp⟩ := Finset.mem_filter.1 hF
      obtain ⟨hFP, hc, hs⟩ := mem_historyGasFamilies.1 hfam
      refine ⟨⟨p, F.erase p⟩, Finset.mem_sigma.2 ⟨Finset.mem_filter.2 ⟨hFP hp, hxp, hs p hp⟩,
        mem_historyGasFamilies.2 ⟨(Finset.erase_subset _ _).trans hFP,
          fun q hq r hr => hc q (Finset.mem_of_mem_erase hq) r (Finset.mem_of_mem_erase hr),
          fun q hq y hy => Finset.mem_sdiff.2 ⟨hs q (Finset.mem_of_mem_erase hq) hy,
            fun hyp => Finset.disjoint_left.1 (hc q (Finset.mem_of_mem_erase hq) p hp (Finset.mem_erase.1 hq).1) hy hyp⟩⟩⟩,
        Finset.insert_erase hp⟩
    · intro i hi
      obtain ⟨hip, hiF⟩ := Finset.mem_sigma.1 hi
      obtain ⟨_, hix, _⟩ := Finset.mem_filter.1 hip
      rw [Finset.prod_insert fun hp => (Finset.mem_sdiff.1 ((mem_historyGasFamilies.1 hiF).2.2 i.1 hp hix)).2 hix]
  rw [← hact, historyGasPartition, historyGasPartition, herase, add_comm]
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

private lemma historyGasPartition_positive (P : Finset β) (support : β → Finset α) (weight : β → ℝ)
    (hne : ∀ p ∈ P, (support p).Nonempty)
    (hactivity : ∀ S x, x ∈ S →
      (∑ p ∈ historyGasRows P support S x, |weight p| * (2 : ℝ) ^ ((support p).card - 1)) ≤ 1 / 2) :
    ∀ S, 0 < historyGasPartition P support weight S ∧ ∀ x ∈ S,
      historyGasPartition P support weight (S.erase x) / 2 ≤ historyGasPartition P support weight S ∧
      historyGasPartition P support weight S ≤ 3 / 2 * historyGasPartition P support weight (S.erase x) :=
  positive_deletion_recurrence (historyGasPartition P support weight) (historyGasRows P support) support weight
    (historyGasPartition_empty P support weight hne) (fun _ _ _ _ hp => (Finset.mem_filter.1 hp).2)
    (fun S x _ => historyGasPartition_deletion P support weight S x) hactivity

end GasDefinitions

section ConnectedUpperComponents
variable {α : Type*} [PartialOrder α] [DecidableEq α]

def historyComparableEdge (U : Finset α) (a b : α) : Prop := a ∈ U ∧ b ∈ U ∧ (a ≤ b ∨ b ≤ a)

def HistoryConnected (U : Finset α) (a b : α) : Prop := Relation.EqvGen (historyComparableEdge U) a b

def historyComponent (U : Finset α) (a : α) : Finset α := by
  classical exact U.filter (HistoryConnected U a)

omit [DecidableEq α] in
private lemma mem_historyComponent {U : Finset α} {a b : α} :
    b ∈ historyComponent U a ↔ b ∈ U ∧ HistoryConnected U a b := by
  classical exact Finset.mem_filter

omit [DecidableEq α] in
private lemma historyComponent_connected_lift {U : Finset α} {r a b : α}
    (h : HistoryConnected U a b) : HistoryConnected U r a → HistoryConnected (historyComponent U r) a b := by
  induction h with
  | rel a b hab =>
    exact fun hra => .rel _ _ ⟨mem_historyComponent.2 ⟨hab.1, hra⟩,
      mem_historyComponent.2 ⟨hab.2.1, .trans _ _ _ hra (.rel _ _ hab)⟩, hab.2.2⟩
  | refl => exact fun _ => .refl _
  | symm _ _ hab ih => exact fun hrb => .symm _ _ (ih (.trans _ _ _ hrb (.symm _ _ hab)))
  | trans _ _ _ hab _ ihab ihbc => exact fun hra => .trans _ _ _ (ihab hra) (ihbc (.trans _ _ _ hra hab))

def IsConnectedHistorySubset (U : Finset α) : Prop :=
  U.Nonempty ∧ ∀ a ∈ U, ∀ b ∈ U, HistoryConnected U a b

omit [DecidableEq α] in
private lemma historyComponent_upper {S U : Finset α} (hU : IsHistoryUpper S U) (r : α) :
    IsHistoryUpper S (historyComponent U r) :=
  ⟨fun _ h => hU.1 (mem_historyComponent.1 h).1, fun a ha b hb hab => by
    obtain ⟨haU, hra⟩ := mem_historyComponent.1 ha
    have hbU := hU.2 a haU b hb hab
    exact mem_historyComponent.2 ⟨hbU, .trans _ _ _ hra (.rel _ _ ⟨haU, hbU, Or.inl hab⟩)⟩⟩

def historyComponents (U : Finset α) : Finset (Finset α) := U.image (historyComponent U)

private lemma historyComponents_pairwise_disjoint (U : Finset α) :
    ∀ P ∈ historyComponents U, ∀ Q ∈ historyComponents U, P ≠ Q → Disjoint P Q := by
  intro P hP Q hQ hpq
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hP
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hQ
  rw [Finset.disjoint_iff_inter_eq_empty, ← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  obtain ⟨hxp, hxq⟩ := Finset.mem_inter.1 hx
  have hpq_conn : HistoryConnected U p q := .trans _ _ _ (mem_historyComponent.1 hxp).2 (.symm _ _ (mem_historyComponent.1 hxq).2)
  refine hpq (Finset.ext fun y => ?_)
  rw [mem_historyComponent, mem_historyComponent]
  exact ⟨fun ⟨hy, hpy⟩ => ⟨hy, .trans _ _ _ (.symm _ _ hpq_conn) hpy⟩,
    fun ⟨hy, hqy⟩ => ⟨hy, .trans _ _ _ hpq_conn hqy⟩⟩

private lemma historyComponents_biUnion (U : Finset α) : (historyComponents U).biUnion id = U := by
  ext x; rw [Finset.mem_biUnion]
  exact ⟨fun ⟨P, hP, hx⟩ => by obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hP; exact (mem_historyComponent.1 hx).1,
    fun hx => ⟨historyComponent U x, Finset.mem_image_of_mem _ hx, mem_historyComponent.2 ⟨hx, .refl _⟩⟩⟩

private lemma historyUpper_biUnion {S : Finset α} {F : Finset (Finset α)}
    (hF : ∀ P ∈ F, IsHistoryUpper S P) : IsHistoryUpper S (F.biUnion id) :=
  ⟨fun x hx => by obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx; exact (hF P hP).1 hxP,
   fun x hx y hy hxy => by obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.1 hx; exact Finset.mem_biUnion.2 ⟨P, hP, (hF P hP).2 x hxP y hy hxy⟩⟩

private lemma historyComponentWeight_eq_component_prod (weight : α → ℝ) (ρ t : ℝ)
    {S U : Finset α} (hU : IsHistoryUpper S U) :
    historyComponentWeight weight ρ t U =
      ∏ P ∈ historyComponents U, historyComponentWeight weight ρ t P := by
  have hbi : ∀ F : Finset (Finset α), (∀ P ∈ F, IsHistoryUpper S P) →
      (∀ P ∈ F, ∀ Q ∈ F, P ≠ Q → Disjoint P Q) →
      historyComponentWeight weight ρ t (F.biUnion id) = ∏ P ∈ F, historyComponentWeight weight ρ t P := by
    intro F; induction F using Finset.induction_on with
    | empty => simp [historyComponentWeight]
    | @insert P F hPF ih =>
      intro hF hdis
      have hFin : ∀ Q ∈ F, IsHistoryUpper S Q := fun Q hQ => hF Q (Finset.mem_insert_of_mem hQ)
      have hPdis : Disjoint P (F.biUnion id) := Finset.disjoint_left.2 fun x hxP hxF => by
        obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
        exact Finset.disjoint_left.1 (hdis P (Finset.mem_insert_self _ _) Q
          (Finset.mem_insert_of_mem hQ) fun heq => hPF (heq ▸ hQ)) hxP hxQ
      rw [Finset.biUnion_insert, id_eq, historyComponentWeight_union weight ρ t
          (historyUpper_disjoint_incomparable (hF P (Finset.mem_insert_self _ _)) (historyUpper_biUnion hFin) hPdis),
        Finset.prod_insert hPF, ih hFin fun Q hQ R hR => hdis Q (Finset.mem_insert_of_mem hQ) R (Finset.mem_insert_of_mem hR)]
  conv_lhs => rw [← historyComponents_biUnion U]
  exact hbi (historyComponents U) (fun P hP => by obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hP; exact historyComponent_upper hU r)
    (historyComponents_pairwise_disjoint U)

def historyUpperPolymers (S : Finset α) : Finset (Finset α) := by
  classical exact (historyUpperSets S).filter IsConnectedHistorySubset

omit [DecidableEq α] in
private lemma mem_historyUpperPolymers {S P : Finset α} :
    P ∈ historyUpperPolymers S ↔ IsHistoryUpper S P ∧ IsConnectedHistorySubset P := by
  classical simp only [historyUpperPolymers, Finset.mem_filter, mem_historyUpperSets]

private lemma historyUpperPolymer_support_nonempty {S P : Finset α} (hP : P ∈ historyUpperPolymers S) :
    (historyMaximalPieces P).Nonempty :=
  historyUpper_nonempty_maximal (mem_historyUpperPolymers.1 hP).1 (mem_historyUpperPolymers.1 hP).2.1

private lemma historyComponent_incomparable_union {P Q : Finset α}
    (hinc : IncomparableHistoryParts P Q) (hP : IsConnectedHistorySubset P) {p : α} (hp : p ∈ P) :
    historyComponent (P ∪ Q) p = P := by
  have hpres {a b : α} (h : HistoryConnected (P ∪ Q) a b) : a ∈ P ↔ b ∈ P := by
    induction h with
    | rel a b hab =>
      refine ⟨fun haP => (Finset.mem_union.1 hab.2.1).elim id fun hbQ =>
          hab.2.2.elim (fun h1 => ((hinc a haP b hbQ).1 h1).elim) (fun h2 => ((hinc a haP b hbQ).2 h2).elim),
        fun hbP => (Finset.mem_union.1 hab.1).elim id fun haQ =>
          hab.2.2.elim (fun h1 => ((hinc b hbP a haQ).2 h1).elim) (fun h2 => ((hinc b hbP a haQ).1 h2).elim)⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  ext x; refine ⟨fun hx => (hpres (mem_historyComponent.1 hx).2).1 hp, fun hx => mem_historyComponent.2
    ⟨Finset.mem_union_left _ hx, Relation.EqvGen.mono (r := historyComparableEdge P)
      (fun _ _ hab => ⟨Finset.mem_union_left _ hab.1, Finset.mem_union_left _ hab.2.1, hab.2.2⟩) _ _ (hP.2 p hp x hx)⟩⟩

private lemma historyGasFamily_components_biUnion {S R : Finset α} {F : Finset (Finset α)}
    (hF : F ∈ historyGasFamilies (historyUpperPolymers S) historyMaximalPieces R) :
    historyComponents (F.biUnion id) = F := by
  obtain ⟨hFP, hc, _⟩ := mem_historyGasFamilies.1 hF
  have hcomp {P : Finset α} (hP : P ∈ F) {p : α} (hp : p ∈ P) : historyComponent (F.biUnion id) p = P := by
    have hupper (Q : Finset α) (hQ : Q ∈ F) : IsHistoryUpper S Q := (mem_historyUpperPolymers.1 (hFP hQ)).1
    have hdis : Disjoint P ((F.erase P).biUnion id) := Finset.disjoint_left.2 fun x hxP hxF => by
      obtain ⟨Q, hQ, hxQ⟩ := Finset.mem_biUnion.1 hxF
      obtain ⟨hQP, hQF⟩ := Finset.mem_erase.1 hQ
      exact Finset.disjoint_left.1 ((historyUpper_disjoint_iff (hupper P hP) (hupper Q hQF)).2
        (hc P hP Q hQF hQP.symm)) hxP hxQ
    have hinc := historyUpper_disjoint_incomparable (hupper P hP)
      (historyUpper_biUnion fun Q hQ => hupper Q (Finset.mem_of_mem_erase hQ)) hdis
    conv_lhs => rw [show F.biUnion id = P ∪ (F.erase P).biUnion id by
      conv_lhs => rw [← Finset.insert_erase hP]
      rw [Finset.biUnion_insert, id_eq]]
    exact historyComponent_incomparable_union hinc (mem_historyUpperPolymers.1 (hFP hP)).2 hp
  ext P; refine ⟨fun hP => ?_, fun hP => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨Q, hQ, hpQ⟩ := Finset.mem_biUnion.1 hp
    rwa [hcomp hQ hpQ]
  · obtain ⟨p, hp⟩ := (mem_historyUpperPolymers.1 (hFP hP)).2.1
    exact Finset.mem_image.2 ⟨p, Finset.mem_biUnion.2 ⟨P, hP, hp⟩, hcomp hP hp⟩

private lemma historyScaledUpperDensity_eq_gas (weight : α → ℝ) (ρ t : ℝ) (S : Finset α) :
    historyScaledUpperDensity weight ρ S t =
      historyGasPartition (historyUpperPolymers S) historyMaximalPieces
        (historyComponentWeight weight ρ t) (historyMaximalPieces S) := by
  rw [historyScaledUpperDensity_eq_components, historyGasPartition]
  refine Finset.sum_bij (fun U _ => historyComponents U) ?_ ?_ ?_ ?_
  · intro U hU
    have hu := mem_historyUpperSets.1 hU
    have hup {P : Finset α} (hP : P ∈ historyComponents U) : IsHistoryUpper S P := by
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hP; exact historyComponent_upper hu r
    refine mem_historyGasFamilies.2 ⟨fun P hP => mem_historyUpperPolymers.2 ⟨hup hP, ?_⟩,
      fun P hP Q hQ hpq => (historyUpper_disjoint_iff (hup hP) (hup hQ)).1
        (historyComponents_pairwise_disjoint U P hP Q hQ hpq),
      fun P hP => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hP
      exact ⟨⟨r, mem_historyComponent.2 ⟨hr, .refl _⟩⟩, fun a ha b hb =>
        historyComponent_connected_lift (.trans _ _ _ (.symm _ _ (mem_historyComponent.1 ha).2)
          (mem_historyComponent.1 hb).2) (mem_historyComponent.1 ha).2⟩
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.1 hP
      exact (historyUpper_maximal_subset (historyComponent_upper ⟨Finset.Subset.refl _, fun _ _ _ hy _ => hy⟩ r)).trans
        (historyUpper_maximal_subset hu)
  · intro U _ V _ hUV
    simpa only [historyComponents_biUnion] using congrArg (fun F : Finset (Finset α) => F.biUnion id) hUV
  · intro F hF
    exact ⟨F.biUnion id, mem_historyUpperSets.2 (historyUpper_biUnion fun _ hP =>
        (mem_historyUpperPolymers.1 ((mem_historyGasFamilies.1 hF).1 hP)).1),
      historyGasFamily_components_biUnion hF⟩
  · intro U hU
    exact historyComponentWeight_eq_component_prod weight ρ t (mem_historyUpperSets.1 hU)

end ConnectedUpperComponents
end GasAndComponents

section WordHeapAndCoverGraph

def historyCoverGraph (α : Type*) [PartialOrder α] : SimpleGraph α where
  Adj a b := a ⋖ b ∨ b ⋖ a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h.ne rfl)⟩

instance historyCoverGraph_locallyFinite {α : Type*} [PartialOrder α] [Fintype α] :
    (historyCoverGraph α).LocallyFinite := fun _ => Fintype.ofFinite _

structure WordHeapPiece {J : Type*} (word : List J) (dependent : J → J → Prop) where
  position : Fin word.length

@[ext] theorem WordHeapPiece.ext {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : x.position = y.position) : x = y := by
  cases x; cases y; cases h; rfl

instance wordHeapPiece_decidableEq {J : Type*} (word : List J) (dependent : J → J → Prop) :
    DecidableEq (WordHeapPiece word dependent) := Classical.decEq _

instance wordHeapPiece_fintype {J : Type*} (word : List J) (dependent : J → J → Prop) :
    Fintype (WordHeapPiece word dependent) :=
  Fintype.ofEquiv (Fin word.length)
    { toFun := fun i => ⟨i⟩, invFun := WordHeapPiece.position, left_inv := fun _ => rfl, right_inv := fun _ => rfl }

def wordHeapLabel {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x : WordHeapPiece word dependent) : J := word.get x.position

def wordHeapStep {J : Type*} {word : List J} {dependent : J → J → Prop}
    (x y : WordHeapPiece word dependent) : Prop :=
  x.position < y.position ∧ dependent (wordHeapLabel x) (wordHeapLabel y)

theorem wordHeap_reachable_position_le {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : Relation.ReflTransGen wordHeapStep x y) :
    x.position ≤ y.position := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans hstep.1.le

instance wordHeap_partialOrder {J : Type*} (word : List J) (dependent : J → J → Prop) :
    PartialOrder (WordHeapPiece word dependent) where
  le := Relation.ReflTransGen wordHeapStep
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans
  le_antisymm _ _ hxy hyx := WordHeapPiece.ext (le_antisymm (wordHeap_reachable_position_le hxy) (wordHeap_reachable_position_le hyx))

theorem wordHeapStep_le {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (h : wordHeapStep x y) : x ≤ y :=
  Relation.ReflTransGen.single h

theorem wordHeap_dependent_comparable {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) {x y : WordHeapPiece word dependent}
    (hdep : dependent (wordHeapLabel x) (wordHeapLabel y)) : x ≤ y ∨ y ≤ x := by
  rcases lt_trichotomy x.position y.position with hxy | heq | hyx
  · exact Or.inl (wordHeapStep_le ⟨hxy, hdep⟩)
  · exact Or.inl (WordHeapPiece.ext heq).le
  · exact Or.inr (wordHeapStep_le ⟨hyx, hsymm hdep⟩)

private lemma wordHeap_cover_dependent {J : Type*} {word : List J} {dependent : J → J → Prop}
    {x y : WordHeapPiece word dependent} (hcov : x ⋖ y) :
    dependent (wordHeapLabel x) (wordHeapLabel y) := by
  have hxy : Relation.ReflTransGen wordHeapStep x y := hcov.le
  cases hxy with
  | refl => exact (hcov.ne rfl).elim
  | @tail z y hxz hzy =>
    rcases hcov.eq_or_eq hxz (wordHeapStep_le hzy) with rfl | hzyEq
    · exact hzy.2
    · exact (lt_irrefl z.position (by simpa only [hzyEq] using hzy.1)).elim

theorem wordHeap_maximal_label_injective {J : Type*} {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (S : Finset (WordHeapPiece word dependent)) :
    Set.InjOn wordHeapLabel (historyMaximalPieces S : Set (WordHeapPiece word dependent)) := by
  intro x hx y hy hlab
  obtain ⟨hxS, hxmax⟩ := mem_historyMaximalPieces.1 hx
  obtain ⟨hyS, hymax⟩ := mem_historyMaximalPieces.1 hy
  rcases wordHeap_dependent_comparable (x := x) (y := y) hsymm (by rw [hlab]; exact hrefl _) with hxy | hyx
  · exact (hxmax y hyS hxy).symm
  · exact hymax x hxS hyx

theorem wordHeap_maximal_card_le_labels {J : Type*} [Fintype J] [DecidableEq J]
    {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (S : Finset (WordHeapPiece word dependent)) :
    (historyMaximalPieces S).card ≤ Fintype.card J := by
  rw [← Finset.card_image_iff.2 (wordHeap_maximal_label_injective hrefl hsymm S)]
  exact Finset.card_le_card (Finset.subset_univ _)

def dependentLabelFinset {J : Type*} [Fintype J] (dependent : J → J → Prop) (j : J) : Finset J := by
  classical exact Finset.univ.filter fun i => dependent j i

private lemma wordHeapCoverGraph_degree_le {J : Type*} [Fintype J] {word : List J} {dependent : J → J → Prop}
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (x : WordHeapPiece word dependent) :
    (historyCoverGraph (WordHeapPiece word dependent)).degree x ≤
      2 * (dependentLabelFinset dependent (wordHeapLabel x)).card := by
  classical
  let upper : Finset (WordHeapPiece word dependent) := Finset.univ.filter fun y => x ⋖ y
  let lower : Finset (WordHeapPiece word dependent) := Finset.univ.filter fun y => y ⋖ x
  have hup : upper.card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
    refine Finset.card_le_card_of_injOn wordHeapLabel
      (fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, wordHeap_cover_dependent (Finset.mem_filter.1 hy).2⟩)
      fun y hy z hz hlab => ?_
    have hxy := (Finset.mem_filter.1 hy).2; have hxz := (Finset.mem_filter.1 hz).2
    rcases wordHeap_dependent_comparable (x := y) (y := z) hsymm (by rw [hlab]; exact hrefl _) with hyz | hzy
    · exact (hxz.eq_or_eq hxy.le hyz).resolve_left fun hyx => hxy.ne hyx.symm
    · exact ((hxy.eq_or_eq hxz.le hzy).resolve_left fun hzx => hxz.ne hzx.symm).symm
  have hlow : lower.card ≤ (dependentLabelFinset dependent (wordHeapLabel x)).card := by
    refine Finset.card_le_card_of_injOn wordHeapLabel
      (fun y hy => Finset.mem_filter.2 ⟨Finset.mem_univ _, hsymm (wordHeap_cover_dependent (Finset.mem_filter.1 hy).2)⟩)
      fun y hy z hz hlab => ?_
    have hyx := (Finset.mem_filter.1 hy).2; have hzx := (Finset.mem_filter.1 hz).2
    rcases wordHeap_dependent_comparable (x := y) (y := z) hsymm (by rw [hlab]; exact hrefl _) with hyz | hzy
    · exact ((hyx.eq_or_eq hyz hzx.le).resolve_right hzx.ne).symm
    · exact (hzx.eq_or_eq hzy hyx.le).resolve_right hyx.ne
  change ((historyCoverGraph (WordHeapPiece word dependent)).neighborFinset x).card ≤ _
  rw [show (historyCoverGraph (WordHeapPiece word dependent)).neighborFinset x = upper ∪ lower by
    ext y; rw [SimpleGraph.mem_neighborFinset]
    simp only [upper, lower, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; rfl]
  have := Finset.card_union_le upper lower
  omega

private lemma historyUpperPolymer_coverGraph_connected {α : Type*} [PartialOrder α] [DecidableEq α] [Fintype α]
    {P : Finset α} (hP : P ∈ historyUpperPolymers Finset.univ) :
    ((historyCoverGraph α).induce (P : Set α)).Connected := by
  classical
  let : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  obtain ⟨hupper, hconn⟩ := mem_historyUpperPolymers.1 hP
  obtain ⟨x, hx⟩ := hconn.1
  let : Nonempty (P : Set α) := ⟨⟨x, hx⟩⟩
  refine ⟨fun a b => ?_⟩
  let edge (x y : α) : Prop := x ∈ P ∧ y ∈ P ∧ (x ⋖ y ∨ y ⋖ x)
  have hle_cov {u v : α} (hu : u ∈ P) (huv : u ≤ v) : Relation.EqvGen edge u v := by
    have hh := le_iff_reflTransGen_covBy.1 huv
    induction hh with
    | refl => exact .refl _
    | @tail c v huc hcv ih =>
      have huc' : u ≤ c := le_iff_reflTransGen_covBy.2 huc
      exact .trans _ _ _ (ih huc') (.rel _ _ ⟨hupper.2 u hu c (Finset.mem_univ _) huc',
        hupper.2 u hu v (Finset.mem_univ _) (huc'.trans hcv.le), Or.inl hcv⟩)
  have hcov {u v : α} (hc : HistoryConnected P u v) : Relation.EqvGen edge u v := by
    induction hc with
    | rel u v huv =>
      exact huv.2.2.elim (hle_cov huv.1) fun hvu => .symm _ _ (hle_cov huv.2.1 hvu)
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
  have hreach {u v : α} (hc : Relation.EqvGen edge u v) (hu : u ∈ P) (hv : v ∈ P) :
      ((historyCoverGraph α).induce (P : Set α)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    induction hc with
    | rel u v huv => exact (show ((historyCoverGraph α).induce (P : Set α)).Adj ⟨u, huv.1⟩ ⟨v, huv.2.1⟩ from huv.2.2).reachable
    | refl => exact SimpleGraph.Reachable.refl _
    | symm _ _ _ ih => exact (ih hv hu).symm
    | trans u w v huw _ ih1 ih2 =>
      by_cases hw : w ∈ P
      · exact (ih1 hu hw).trans (ih2 hw hv)
      · have hs {p q : α} (h : Relation.EqvGen edge p q) : p = q ∨ p ∈ P ∧ q ∈ P := by
          induction h with
          | rel _ _ h => exact Or.inr ⟨h.1, h.2.1⟩
          | refl => exact Or.inl rfl
          | symm _ _ _ ih => exact ih.elim (Or.inl ∘ Eq.symm) (Or.inr ∘ And.symm)
          | trans _ _ _ _ _ ihp ihq =>
            rcases ihp with rfl | ⟨hp, hq⟩
            · exact ihq
            · rcases ihq with rfl | ⟨_, hr⟩
              · exact Or.inr ⟨hp, hq⟩
              · exact Or.inr ⟨hp, hr⟩
        exact (hs huw).elim (fun heq => (hw (heq ▸ hu)).elim) fun h => (hw h.2).elim
  exact hreach (hcov (hconn.2 a.val a.prop b.val b.prop)) a.prop b.prop

end WordHeapAndCoverGraph

section SpanningWalkAndActivity
universe u

private lemma finite_tree_closed_spanning_walk {V : Type u} [Fintype V]
    (T : SimpleGraph V) (hT : T.IsTree) (r : V) :
    ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support := by
  classical
  suffices hmain : ∀ n : ℕ, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ (T : SimpleGraph V), T.IsTree → ∀ r : V,
        ∃ p : T.Walk r r, p.length = 2 * (Fintype.card V - 1) ∧ ∀ v, v ∈ p.support from
    hmain (Fintype.card V) V rfl T hT r
  intro n; induction n using Nat.strong_induction_on with | _ n ih =>
  intro V instV hcard T hT r
  by_cases hs : Subsingleton V
  · let : Subsingleton V := hs
    let : Unique V := { default := r, uniq := fun v => Subsingleton.elim v r }
    exact ⟨.nil, by simp, fun v => by simp [Subsingleton.elim v r]⟩
  · let : Nontrivial V := not_subsingleton_iff_nontrivial.1 hs
    obtain ⟨a, b, hab, ha, hb⟩ := hT.exists_ne_and_degree_eq_one
    obtain ⟨v, hvr, hdeg⟩ : ∃ v : V, v ≠ r ∧ T.degree v = 1 :=
      if har : a = r then ⟨b, fun hbr => hab (har.trans hbr.symm), hb⟩ else ⟨a, har, ha⟩
    let S : Set V := {v}ᶜ
    let T' := T.induce S
    let r' : S := ⟨r, by simpa [S] using hvr.symm⟩
    have hT' : T'.IsTree := ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hdeg, hT.isAcyclic.induce S⟩
    have hcard' : Fintype.card S = Fintype.card V - 1 := by simp only [S, Fintype.card_compl_set, Fintype.card_unique]
    obtain ⟨p', hp'len, hp'all⟩ := ih (Fintype.card S) (by rw [← hcard]; exact Fintype.card_subtype_lt (x := v) (by simp [S])) S rfl T' hT' r'
    let f : T' →g T := { toFun := Subtype.val, map_rel' := fun h => h }
    let p : T.Walk r r := p'.map f
    have hplen : p.length = 2 * (Fintype.card S - 1) := by simpa only [p, SimpleGraph.Walk.length_map] using hp'len
    have hpall (x : V) (hxv : x ≠ v) : x ∈ p.support := by
      rw [show p = p'.map f from rfl, SimpleGraph.Walk.support_map]
      exact List.mem_map.2 ⟨⟨x, by simpa [S] using hxv⟩, hp'all _, rfl⟩
    obtain ⟨w, hvw, _⟩ := T.degree_eq_one_iff_existsUnique_adj.1 hdeg
    have hwp := hpall w hvw.ne.symm
    let excursion : T.Walk w w := .cons hvw.symm (.cons hvw .nil)
    let q := ((p.takeUntil w hwp).append excursion).append (p.dropUntil w hwp)
    have hsplit : (p.takeUntil w hwp).length + (p.dropUntil w hwp).length = p.length := by
      simpa only [SimpleGraph.Walk.length_append] using congrArg SimpleGraph.Walk.length (p.take_spec hwp)
    refine ⟨q, ?_, fun x => ?_⟩
    · simp only [q, excursion, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
      have hn : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff_nontrivial.2 inferInstance
      omega
    · by_cases hxv : x = v
      · subst x
        simp only [q, SimpleGraph.Walk.mem_support_append_iff, excursion,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons]
        exact Or.inl (Or.inr (Or.inr (Or.inl trivial)))
      · have hx := hpall x hxv
        rw [← p.take_spec hwp, SimpleGraph.Walk.mem_support_append_iff] at hx
        simp only [q, SimpleGraph.Walk.mem_support_append_iff]
        exact hx.elim (Or.inl ∘ Or.inl) Or.inr

private lemma graph_walk_count_le {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    simp only [SimpleGraph.finsetWalkLength]; split_ifs with h
    · subst u; simp
    · simp
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc
      _ ≤ ∑ w : G.neighborSet u,
          ((G.finsetWalkLength n w v).map ⟨fun p => SimpleGraph.Walk.cons w.prop p, fun a b hab => by cases hab; rfl⟩).card :=
        Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card := by simp
      _ ≤ ∑ _w : G.neighborSet u, D ^ n := Finset.sum_le_sum fun _ _ => ih _
      _ = G.degree u * D ^ n := by simp
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

def graphConnectedSubsets {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (x : V) (k : ℕ) : Finset (Finset V) := by
  classical exact Finset.univ.powerset.filter fun P => x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected

private lemma graph_connected_subsets_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [G.LocallyFinite] (D : ℕ) (hD : ∀ v, G.degree v ≤ D) (x : V) (k : ℕ) :
    (graphConnectedSubsets G x k).card ≤ D ^ (2 * (k - 1)) := by
  classical
  have hwalk {P : Finset V} (hP : P ∈ graphConnectedSubsets G x k) :
      ∃ p : G.Walk x x, p.length = 2 * (k - 1) ∧ p.support.toFinset = P := by
    obtain ⟨hx, hcard, hconn⟩ := (Finset.mem_filter.1 hP).2
    obtain ⟨T, hTG, hT⟩ := hconn.exists_isTree_le
    obtain ⟨p0, hplen, hpall⟩ := finite_tree_closed_spanning_walk T hT ⟨x, hx⟩
    let p := p0.mapLe hTG
    let f : G.induce (P : Set V) →g G := { toFun := Subtype.val, map_rel' := fun h => h }
    refine ⟨p.map f, ?_, ?_⟩
    · have hc : Fintype.card (P : Set V) = P.card := Fintype.card_ofFinset P fun _ => Iff.rfl
      simpa only [p, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_mapLe, hc, hcard] using hplen
    · ext y; rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
      exact ⟨fun ⟨z, _, hzy⟩ => hzy ▸ z.prop,
        fun hy => ⟨⟨y, hy⟩, by simpa only [p, SimpleGraph.Walk.support_mapLe_eq_support] using hpall ⟨y, hy⟩, rfl⟩⟩
  let f : Finset V → G.Walk x x := fun P =>
    if hP : P ∈ graphConnectedSubsets G x k then (hwalk hP).choose else .nil
  have hf (P : Finset V) (hP : P ∈ graphConnectedSubsets G x k) :
      (f P).length = 2 * (k - 1) ∧ (f P).support.toFinset = P := by
    dsimp only [f]; rw [dif_pos hP]; exact (hwalk hP).choose_spec
  refine (Finset.card_le_card_of_injOn f
    (fun P hP => SimpleGraph.mem_finsetWalkLength_iff.2 (hf P hP).1)
    fun P hP Q hQ hPQ => ?_).trans (graph_walk_count_le G D hD _ _ _)
  rw [← (hf P hP).2, hPQ, (hf Q hQ).2]

private lemma history_finite_geom_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) ≤ 1 / (1 - r) := by
  rw [le_div_iff₀ (sub_pos.2 hr1), geom_sum_mul_neg]
  exact sub_le_self _ (pow_nonneg hr N)

private lemma historyUpperRows_activity_le {α : Type*} [PartialOrder α] [DecidableEq α] [Fintype α]
    (weight : α → ℝ) (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    (D : ℕ) (hD : ∀ x : α, (historyCoverGraph α).degree x ≤ D)
    (hsmall : t * B / ρ ≤ 1 / (2 + 2 * (D : ℝ) ^ 2)) (R : Finset α) (x : α) :
    (∑ P ∈ historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x,
      |historyComponentWeight weight ρ t P| * (2 : ℝ) ^ ((historyMaximalPieces P).card - 1)) ≤ 1 / 2 := by
  classical
  let A := historyGasRows (historyUpperPolymers Finset.univ) historyMaximalPieces R x
  let ε := t * B / ρ
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg ht hB) hρ.le
  have hden : 0 < 2 + 2 * (D : ℝ) ^ 2 := by positivity
  have hs := (le_div_iff₀ hden).1 hsmall
  have hp : 0 < 1 - 2 * (D : ℝ) ^ 2 * ε := by
    by_cases he : ε = 0
    · simp [he]
    · have : 0 < ε := lt_of_le_of_ne hε (Ne.symm he); nlinarith
  have hmap (P : Finset α) (hP : P ∈ A) : P.card - 1 ∈ Finset.range (Fintype.card α) := by
    have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hP).2.1
    have := Finset.card_pos.2 ⟨x, hxP⟩; have := Finset.card_le_univ P
    exact Finset.mem_range.2 (by omega)
  change (∑ P ∈ A, _) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine ((Finset.sum_le_sum (g := fun j => (D : ℝ) ^ (2 * j) * (ε ^ (j + 1) * (2 : ℝ) ^ j))
      fun j _ => ?_).trans_eq ?_).trans
    (((mul_le_mul_of_nonneg_left (history_finite_geom_sum_le (r := 2 * (D : ℝ) ^ 2 * ε) (by positivity) (by linarith [hp]) (Fintype.card α)) hε).trans_eq (by ring)).trans
      ((div_le_iff₀ hp).2 (by nlinarith)))
  · calc
      _ ≤ ∑ _P ∈ A.filter (fun P => P.card - 1 = j), ε ^ (j + 1) * (2 : ℝ) ^ j := Finset.sum_le_sum fun P hP => by
        obtain ⟨hPA, hsize⟩ := Finset.mem_filter.1 hP
        have hxP := historyMaximalPieces_subset P (Finset.mem_filter.1 hPA).2.1
        have hcard : P.card = j + 1 := by have := Finset.card_pos.2 ⟨x, hxP⟩; omega
        have hc := historyComponentWeight_abs_le P hρ ht hB fun y _ => hw y
        have hm : (historyMaximalPieces P).card - 1 ≤ P.card - 1 :=
          Nat.sub_le_sub_right (Finset.card_le_card (historyMaximalPieces_subset P)) 1
        simpa only [hcard, Nat.add_sub_cancel] using mul_le_mul hc
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm) (by positivity) (pow_nonneg hε _)
      _ = ((A.filter (fun P => P.card - 1 = j)).card : ℝ) * (ε ^ (j + 1) * (2 : ℝ) ^ j) := by simp
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hcard_le : (A.filter fun P => P.card - 1 = j).card ≤ D ^ (2 * j) := by
          refine (Finset.card_le_card fun P hP => ?_).trans
            (by simpa only [Nat.add_sub_cancel] using graph_connected_subsets_card_le (historyCoverGraph α) D hD x (j + 1))
          obtain ⟨hProw, hsize⟩ := Finset.mem_filter.1 hP
          obtain ⟨hPpoly, hxmax, _⟩ := Finset.mem_filter.1 hProw
          have hxP := historyMaximalPieces_subset P hxmax
          have hcard : P.card = j + 1 := by have := Finset.card_pos.2 ⟨x, hxP⟩; omega
          rw [graphConnectedSubsets]
          exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
            hxP, hcard, historyUpperPolymer_coverGraph_connected hPpoly⟩
        exact_mod_cast hcard_le
  · rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by rw [pow_mul, pow_succ, mul_pow, mul_pow]; ring

private lemma wordHeap_density_bounds {J : Type*} [Fintype J] [DecidableEq J]
    (word : List J) (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (weight : WordHeapPiece word dependent → ℝ) (ρ t B : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B) (hw : ∀ x, |weight x| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyScaledUpperDensity weight ρ Finset.univ t ∧
      historyScaledUpperDensity weight ρ Finset.univ t ≤ (3 / 2 : ℝ) ^ Fintype.card J := by
  have hD (x : WordHeapPiece word dependent) :
      (historyCoverGraph (WordHeapPiece word dependent)).degree x ≤ 2 * Δ :=
    (wordHeapCoverGraph_degree_le hrefl hsymm x).trans (Nat.mul_le_mul_left 2 (hlabels _))
  have hs : t * B / ρ ≤ 1 / (2 + 2 * ((2 * Δ : ℕ) : ℝ) ^ 2) := by convert hsmall using 1; push_cast; ring
  have hpos := historyGasPartition_positive
    (historyUpperPolymers (Finset.univ : Finset (WordHeapPiece word dependent)))
    historyMaximalPieces (historyComponentWeight weight ρ t)
    (fun _ hP => historyUpperPolymer_support_nonempty hP)
    (fun R x _ => historyUpperRows_activity_le weight ρ t B hρ ht hB hw (2 * Δ) hD hs R x)
  have hb := deletion_ratios_global_bounds _
    (historyGasPartition_empty _ _ _ fun _ hP => historyUpperPolymer_support_nonempty hP)
    (fun R x hx => (hpos R).2 x hx)
    (historyMaximalPieces (Finset.univ : Finset (WordHeapPiece word dependent)))
  rw [← historyScaledUpperDensity_eq_gas] at hb
  have hc := wordHeap_maximal_card_le_labels hrefl hsymm (Finset.univ : Finset (WordHeapPiece word dependent))
  exact ⟨(pow_le_pow_of_le_one (by norm_num) (by norm_num) hc).trans hb.1,
    hb.2.trans (pow_le_pow_right₀ (by norm_num) hc)⟩

end SpanningWalkAndActivity

-- ============================================================================
-- 4. History Shapes, Projections, Reference Law, Prior Density, and Word Transport
-- ============================================================================

section HistoryShapesAndMeasures
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

inductive IndependentHistoryExchange {α : Type*} (independent : α → α → Prop) : List α → List α → Prop
  | swap (before after : List α) (x y : α) (hxy : independent x y) :
      IndependentHistoryExchange independent (before ++ x :: y :: after) (before ++ y :: x :: after)

def historyShapeSetoid {α : Type*} (independent : α → α → Prop) : Setoid (List α) where
  r := Relation.EqvGen (IndependentHistoryExchange independent)
  iseqv := ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
    fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

def HistoryShape {α : Type*} (independent : α → α → Prop) := Quotient (historyShapeSetoid independent)

def historyWordState {α X : Type*} (update : α → X → X) (initial : X) (word : List α) : X :=
  word.foldl (fun state piece => update piece state) initial

instance historyShape_countable {α : Type*} [Countable α] (independent : α → α → Prop) :
    Countable (HistoryShape independent) := by
  unfold HistoryShape; infer_instance

def affinePatchUpdate {X : Type*} (patch : Set X) (A B : X → ℝ) (state : X → ℝ) : X → ℝ := by
  classical exact fun x => if x ∈ patch then A x * state x + B x else state x

def responseCoordinateUpdate {α E : Type*} [DecidableEq α]
    (j : α) (response : E → E) (state : α → E) : α → E := Function.update state j (response (state j))

def rawPatchUpdate {α X E : Type*} [DecidableEq α] (j : α) (patch : Set X)
    (A B : X → ℝ) (response : E → E) (state : (X → ℝ) × (α → E)) : (X → ℝ) × (α → E) :=
  (affinePatchUpdate patch A B state.1, responseCoordinateUpdate j response state.2)

theorem rawPatchUpdate_commute {α X E : Type*} [DecidableEq α] {i j : α}
    (P Q : Set X) (A B C D : X → ℝ) (f g : E → E)
    (hij : i ≠ j) (hPQ : Disjoint P Q) (state : (X → ℝ) × (α → E)) :
    rawPatchUpdate j Q C D g (rawPatchUpdate i P A B f state) =
      rawPatchUpdate i P A B f (rawPatchUpdate j Q C D g state) := by
  classical
  unfold rawPatchUpdate
  refine Prod.ext (funext fun x => ?_) ?_
  · by_cases hxP : x ∈ P
    · simp [affinePatchUpdate, hxP, show x ∉ Q from fun hxQ => Set.disjoint_left.1 hPQ hxP hxQ]
    · by_cases hxQ : x ∈ Q <;> simp [affinePatchUpdate, hxP, hxQ]
  · dsimp only [responseCoordinateUpdate]
    simp only [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm hij _ _ state.2

section PairProjections
variable {J : Type*} [DecidableEq J]

def historyPairProjection (i j : J) (word : List J) : List J :=
  word.filter fun x => decide (x = i ∨ x = j)

lemma historyPairProjection_shape_invariant {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {i j : J} (hij : dependent i j) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    historyPairProjection i j u = historyPairProjection i j v := by
  induction h with
  | rel _ _ h =>
    cases h with
    | swap before after x y hxy =>
      by_cases hx : x = i ∨ x = j
      · have hy : ¬ (y = i ∨ y = j) := fun hy => hxy (by
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact hrefl _
          · exact hij
          · exact hsymm hij
          · exact hrefl _)
        simp [historyPairProjection, List.filter_append, hx, hy]
      · by_cases hy : y = i ∨ y = j <;> simp [historyPairProjection, List.filter_append, hx, hy]
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [DecidableEq J] in
theorem historyShapeRelation_cons {independent : J → J → Prop} (a : J) {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) :
    Relation.EqvGen (IndependentHistoryExchange independent) (a :: u) (a :: v) := by
  induction h with
  | rel _ _ h =>
    cases h with | swap before after x y hxy =>
      exact .rel _ _ (IndependentHistoryExchange.swap (a :: before) after x y hxy)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private lemma historyShapeRelation_of_pair_projections {dependent : J → J → Prop}
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    {u v : List J} (hproj : ∀ i j, dependent i j → historyPairProjection i j u = historyPairProjection i j v) :
    Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v := by
  have hfirst {a : J} {w : List J} (ha : a ∈ w) : ∃ before after, w = before ++ a :: after ∧ a ∉ before := by
    induction w with
    | nil => simp at ha
    | cons b w ih =>
      by_cases hba : b = a
      · subst b; exact ⟨[], w, rfl, by simp⟩
      · obtain ⟨before, after, hw, hb⟩ := ih ((List.mem_cons.1 ha).resolve_left (Ne.symm hba))
        exact ⟨b :: before, after, by simp [hw], by simp [hb, Ne.symm hba]⟩
  have hphead {a b : J} {before after : List J} (ha : a ∉ before) (hb : b ∈ before) :
      (historyPairProjection a b (before ++ a :: after)).head? = some b := by
    induction before with
    | nil => simp at hb
    | cons c before ih =>
      have hca : c ≠ a := fun h => ha (List.mem_cons.2 (Or.inl h.symm))
      have hab : a ∉ before := fun h => ha (List.mem_cons.2 (Or.inr h))
      by_cases hcb : c = b
      · subst c; simp [historyPairProjection]
      · simpa [historyPairProjection, hca, hcb] using ih hab ((List.mem_cons.1 hb).resolve_left (Ne.symm hcb))
  have hmove {ind : J → J → Prop} (a : J) (before after : List J) (hb : ∀ b ∈ before, ind b a) :
      Relation.EqvGen (IndependentHistoryExchange ind) (before ++ a :: after) (a :: (before ++ after)) := by
    induction before with
    | nil => exact .refl _
    | cons b before ih =>
      exact .trans _ _ _ (historyShapeRelation_cons b (ih fun c hc => hb c (List.mem_cons_of_mem _ hc)))
        (.rel _ _ (IndependentHistoryExchange.swap [] (before ++ after) b a (hb b List.mem_cons_self)))
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact .refl _
    | cons b v =>
      have hh := congrArg List.head? (hproj b b (hrefl b)); simp [historyPairProjection] at hh
  | cons a u ih =>
    have hamem : a ∈ v := by
      have hm : a ∈ historyPairProjection a a (a :: u) := by simp [historyPairProjection]
      rw [hproj a a (hrefl a)] at hm; exact (List.mem_filter.1 hm).1
    obtain ⟨before, after, hv, ha⟩ := hfirst hamem
    have hind (b : J) (hb : b ∈ before) (hba : dependent b a) : False := by
      have hh := congrArg List.head? (hproj a b (hsymm hba))
      rw [hv, hphead ha hb] at hh
      exact ha ((by simpa [historyPairProjection] using hh : a = b) ▸ hb)
    have hm := hmove (ind := fun b c => ¬ dependent b c) a before after hind
    have hrest (i j : J) (hij : dependent i j) :
        historyPairProjection i j u = historyPairProjection i j (before ++ after) := by
      have hh := (hproj i j hij).trans (hv ▸ historyPairProjection_shape_invariant hrefl hsymm hij hm)
      by_cases hai : a = i ∨ a = j <;> simpa [historyPairProjection, hai] using hh
    rw [hv]; exact .trans _ _ _ (historyShapeRelation_cons a (ih hrest)) (.symm _ _ hm)

def historyShapePairCode (dependent : J → J → Prop)
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) :
    HistoryShape (fun a b => ¬ dependent a b) → ({p : J × J // dependent p.1 p.2} → List J) :=
  Quotient.lift (fun word p => historyPairProjection p.val.1 p.val.2 word)
    fun _ _ h => funext fun p => historyPairProjection_shape_invariant hrefl hsymm p.prop h

def historyShapeMultiplicity (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → ℕ :=
  Quotient.lift (List.count j) fun _ _ h => by
    induction h with
    | rel _ _ h => cases h with | swap => simp [List.count_append, List.count_cons, Nat.add_comm, Nat.add_left_comm]
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

abbrev HistoryMultiplicityShape (dependent : J → J → Prop) (n : J → ℕ) :=
  {g : HistoryShape (fun a b => ¬ dependent a b) // ∀ j, historyShapeMultiplicity dependent j g = n j}

abbrev HistoryOrderedDependentPair (dependent : J → J → Prop) [LinearOrder J] :=
  {p : J × J // p.1 < p.2 ∧ dependent p.1 p.2}

instance historyOrderedDependentPair_fintype [Fintype J] [LinearOrder J] (dependent : J → J → Prop) :
    Fintype (HistoryOrderedDependentPair dependent) := Fintype.ofFinite _

def historyPairBits (i j : J) (word : List J) : List Bool :=
  (historyPairProjection i j word).map fun x => decide (x = j)

lemma historyPairBits_length {i j : J} (hij : i ≠ j) (word : List J) :
    (historyPairBits i j word).length = word.count i + word.count j := by
  rw [historyPairBits, List.length_map]
  induction word with
  | nil => simp [historyPairProjection]
  | cons a word ih =>
    by_cases hai : a = i
    · subst a; simp [historyPairProjection] at ih; simp [historyPairProjection, hij]; omega
    · by_cases haj : a = j
      · subst a; simp [historyPairProjection] at ih; simp [historyPairProjection, Ne.symm hij]; omega
      · simpa [historyPairProjection, List.count_cons, hai, haj] using ih

def historyMultiplicityPairCode (dependent : J → J → Prop) [LinearOrder J] (n : J → ℕ)
    (g : HistoryMultiplicityShape dependent n) :
    ∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2) := fun p =>
  ⟨historyPairBits p.val.1 p.val.2 (Quotient.out g.val), by
    have hout (j : J) : (Quotient.out g.val).count j = n j :=
      (congrArg (historyShapeMultiplicity dependent j) (Quotient.out_eq g.val)).trans (g.prop j)
    rw [historyPairBits_length p.prop.1.ne, hout, hout]⟩

private lemma historyMultiplicityPairCode_injective (dependent : J → J → Prop) [LinearOrder J]
    (hrefl : ∀ i, dependent i i) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (n : J → ℕ) :
    Function.Injective (historyMultiplicityPairCode dependent n) := by
  have hrec {i j : J} (hij : i ≠ j) (w : List J) :
      (historyPairBits i j w).map (fun b => if b then j else i) = historyPairProjection i j w := by
    rw [historyPairBits, List.map_map]
    conv_rhs => rw [← List.map_id (historyPairProjection i j w)]
    refine List.map_congr_left fun x hx => ?_
    rcases of_decide_eq_true (List.mem_filter.1 hx).2 with rfl | rfl <;> simp [hij]
  have hself (j : J) (w : List J) : historyPairProjection j j w = List.replicate (w.count j) j := by
    induction w with
    | nil => simp [historyPairProjection]
    | cons a w ih =>
      by_cases haj : a = j
      · subst a; simpa [historyPairProjection, List.replicate_succ] using congrArg (List.cons j) ih
      · simpa [historyPairProjection, haj] using ih
  intro g h hcode
  have hproj (i j : J) (hij : dependent i j) :
      historyPairProjection i j (Quotient.out g.val) = historyPairProjection i j (Quotient.out h.val) := by
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have he : historyPairBits i j (Quotient.out g.val) = historyPairBits i j (Quotient.out h.val) :=
        congrArg Subtype.val (congrFun hcode ⟨⟨i, j⟩, hlt, hij⟩)
      rw [← hrec hlt.ne, ← hrec hlt.ne, he]
    · have hout (x : HistoryMultiplicityShape dependent n) : (Quotient.out x.val).count i = n i :=
        (congrArg (historyShapeMultiplicity dependent i) (Quotient.out_eq x.val)).trans (x.prop i)
      rw [hself, hself, hout g, hout h]
    · have hsym (w : List J) : historyPairProjection i j w = historyPairProjection j i w := by
        simp [historyPairProjection, or_comm]
      have he : historyPairBits j i (Quotient.out g.val) = historyPairBits j i (Quotient.out h.val) :=
        congrArg Subtype.val (congrFun hcode ⟨⟨j, i⟩, hgt, hsymm hij⟩)
      rw [hsym, hsym, ← hrec hgt.ne, ← hrec hgt.ne, he]
  apply Subtype.ext
  exact (Quotient.out_eq g.val).symm.trans
    ((Quotient.sound (historyShapeRelation_of_pair_projections hrefl hsymm hproj)).trans (Quotient.out_eq h.val))

end PairProjections

section ShapeDegreeAndReference
variable {J : Type*} [Fintype J] [LinearOrder J]

private lemma historyMultiplicityShape_card_le_degree (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) (n : J → ℕ) :
    Nat.card (HistoryMultiplicityShape dependent n) ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) := by
  classical
  let : Finite (HistoryMultiplicityShape dependent n) :=
    Finite.of_injective _ (historyMultiplicityPairCode_injective dependent hrefl hsymm n)
  have hh := Nat.card_le_card_of_injective (historyMultiplicityPairCode dependent n)
    (historyMultiplicityPairCode_injective dependent hrefl hsymm n)
  have hc : Nat.card (∀ p : HistoryOrderedDependentPair dependent, List.Vector Bool (n p.val.1 + n p.val.2)) =
      2 ^ (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_pi, card_vector, Fintype.card_bool, Finset.prod_pow_eq_pow_sum]
  rw [hc] at hh
  refine hh.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) ?_)
  let inc (j : J) : Finset (HistoryOrderedDependentPair dependent) :=
    Finset.univ.filter fun p => p.val.1 = j ∨ p.val.2 = j
  have hexp : (∑ p : HistoryOrderedDependentPair dependent, (n p.val.1 + n p.val.2)) =
      ∑ j : J, (inc j).card * n j := by
    simp_rw [show ∀ p : HistoryOrderedDependentPair dependent,
        n p.val.1 + n p.val.2 = ∑ j : J, if p.val.1 = j ∨ p.val.2 = j then n j else 0 from fun p => by
      simp_rw [show ∀ j : J, (if p.val.1 = j ∨ p.val.2 = j then n j else 0) =
          (if p.val.1 = j then n j else 0) + (if p.val.2 = j then n j else 0) from fun j => by
        by_cases h1 : p.val.1 = j
        · simp [h1, show p.val.2 ≠ j from fun h => p.prop.1.ne (h1.trans h.symm)]
        · by_cases h2 : p.val.2 = j <;> simp [h1, h2]]
      rw [Finset.sum_add_distrib]; simp [eq_comm]]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_filter]; simp [inc]
  rw [hexp, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right (n j) ?_
  have hj : j ∈ dependentLabelFinset dependent j := Finset.mem_filter.2 ⟨Finset.mem_univ _, hrefl _⟩
  refine (le_of_le_of_eq ?_ (Finset.card_erase_of_mem hj)).trans (Nat.sub_le_sub_right (hlabels j) 1)
  let other (p : HistoryOrderedDependentPair dependent) : J := if p.val.1 = j then p.val.2 else p.val.1
  refine Finset.card_le_card_of_injOn other (fun p hp => ?_) fun p hp q hq hpq => Subtype.ext ?_
  · rcases (Finset.mem_filter.1 hp).2 with h1 | h2
    · simp only [other, if_pos h1]
      exact Finset.mem_erase.2 ⟨h1 ▸ p.prop.1.ne.symm, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1 ▸ p.prop.2⟩⟩
    · have hne : p.val.1 ≠ j := h2 ▸ p.prop.1.ne
      simp only [other, if_neg hne]
      exact Finset.mem_erase.2 ⟨hne, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2 ▸ hsymm p.prop.2⟩⟩
  · have hrec (r : HistoryOrderedDependentPair dependent) (hr : r ∈ inc j) :
        r.val = if j < other r then (j, other r) else (other r, j) := by
      rcases r with ⟨⟨a, b⟩, hab, hdep⟩
      rcases (Finset.mem_filter.1 hr).2 with rfl | rfl
      · simp [other, hab]
      · simp [other, hab.ne, not_lt_of_gt hab]
    rw [hrec p hp, hrec q hq, hpq]

def historyShapeLength (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℕ := ∑ j : J, historyShapeMultiplicity dependent j g

private lemma historyShapeLength_mk (dependent : J → J → Prop) (word : List J) :
    historyShapeLength dependent (Quotient.mk _ word) = word.length := by
  change (∑ j : J, word.count j) = word.length
  induction word with
  | nil => simp
  | cons a word ih =>
    simp_rw [show ∀ j : J, (a :: word).count j = word.count j + if j = a then 1 else 0 from fun j => by
      by_cases hja : j = a
      · subst j; simp
      · simp [hja, Ne.symm hja]]
    rw [Finset.sum_add_distrib, ih]; simp

def historyReferenceRho (Δ : ℕ) : ℝ := (1 / 2 : ℝ) ^ (Δ + 1)

theorem historyReferenceRho_pos (Δ : ℕ) : 0 < historyReferenceRho Δ := by
  unfold historyReferenceRho; positivity

def historyShapeReferenceWeight (dependent : J → J → Prop) (Δ : ℕ)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : ℝ :=
  historyReferenceRho Δ ^ historyShapeLength dependent g

private lemma historyShapeReferenceWeight_summable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ) :
    Summable (historyShapeReferenceWeight dependent Δ) := by
  classical
  refine summable_of_sum_le (c := (4 / 3 : ℝ) ^ Fintype.card J)
    (fun _ => pow_nonneg (historyReferenceRho_pos Δ).le _) fun A => ?_
  let code := fun g => fun j => historyShapeMultiplicity dependent j g
  let C := A.image code
  let N := (∑ n ∈ C, ∑ j : J, n j) + 1
  have hbox : C ⊆ Fintype.piFinset fun _ : J => Finset.range N := fun n hn =>
    Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (by
      have := Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have := Finset.single_le_sum (f := fun m : J → ℕ => ∑ i : J, m i) (fun _ _ => Nat.zero_le _) hn
      dsimp [N]; omega)
  rw [← Finset.sum_fiberwise_of_maps_to (fun g hg => Finset.mem_image_of_mem code hg)]
  refine ((Finset.sum_le_sum (g := fun n : J → ℕ => (1 / 4 : ℝ) ^ (∑ j : J, n j)) fun n _ => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hbox fun _ _ _ => by positivity)).trans ?_
  · have heq : (∑ g ∈ A.filter (fun g => code g = n), historyShapeReferenceWeight dependent Δ g) =
        ((A.filter (fun g => code g = n)).card : ℝ) * historyReferenceRho Δ ^ (∑ j : J, n j) := by
      rw [Finset.sum_congr rfl (g := fun _ => historyReferenceRho Δ ^ (∑ j : J, n j)) fun g hg => by
        unfold historyShapeReferenceWeight historyShapeLength
        rw [show (fun j => historyShapeMultiplicity dependent j g) = n from (Finset.mem_filter.1 hg).2]]
      simp
    rw [heq]
    have hcard : (A.filter (fun g => code g = n)).card ≤ 2 ^ ((Δ - 1) * ∑ j : J, n j) := by
      let F := A.filter fun g => code g = n
      let f : F → HistoryMultiplicityShape dependent n := fun g => ⟨g.val, fun j => congrFun (Finset.mem_filter.1 g.prop).2 j⟩
      let : Finite (HistoryMultiplicityShape dependent n) :=
        Finite.of_injective _ (historyMultiplicityPairCode_injective dependent hrefl hsymm n)
      have hh := Nat.card_le_card_of_injective f fun g h heq =>
        Subtype.ext (congrArg (fun z : HistoryMultiplicityShape dependent n => z.val) heq)
      rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hh
      exact hh.trans (historyMultiplicityShape_card_le_degree dependent hrefl hsymm Δ hlabels n)
    refine (mul_le_mul_of_nonneg_right
      (show ((A.filter (fun g => code g = n)).card : ℝ) ≤ (2 : ℝ) ^ ((Δ - 1) * ∑ j : J, n j) by exact_mod_cast hcard)
      (pow_nonneg (historyReferenceRho_pos Δ).le _)).trans_eq ?_
    rw [pow_mul, ← mul_pow, show (2 : ℝ) ^ (Δ - 1) * historyReferenceRho Δ = 1 / 4 by
      unfold historyReferenceRho; rw [show Δ + 1 = (Δ - 1) + 2 by omega, pow_add, ← mul_assoc, ← mul_pow]; norm_num]
  · simp_rw [← Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_prod_piFinset (Finset.range N) fun _ r => (1 / 4 : ℝ) ^ r]
    refine (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun _ _ => ?_).trans_eq (by rw [Finset.prod_const, Finset.card_univ])
    have hh := history_finite_geom_sum_le (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) N
    norm_num at hh ⊢; exact hh

abbrev HistoryMarked (dependent : J → J → Prop) (E : Type*) :=
  Σ g : HistoryShape (fun a b => ¬ dependent a b), Fin (historyShapeLength dependent g) → E

theorem historyMarked_measurable_mk (dependent : J → J → Prop) {E : Type*}
    [MeasurableSpace E] (g : HistoryShape (fun a b => ¬ dependent a b)) :
    Measurable (fun marks : Fin (historyShapeLength dependent g) → E => (⟨g, marks⟩ : HistoryMarked dependent E)) :=
  Measurable.of_le_map (iInf_le _ g)

theorem historyMarked_measurable_iff (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (f : HistoryMarked dependent E → X) :
    Measurable f ↔ ∀ g, Measurable (fun marks => f ⟨g, marks⟩) :=
  ⟨fun hf g => hf.comp (historyMarked_measurable_mk dependent g),
   fun hf s hs => by
     change MeasurableSet[⨅ g, MeasurableSpace.map (Sigma.mk g)
       (inferInstance : MeasurableSpace (Fin (historyShapeLength dependent g) → E))] (f ⁻¹' s)
     exact MeasurableSpace.measurableSet_iInf.2 fun g => hf g hs⟩

theorem historySigma_borelSpace {I : Type*} [Countable I] {X : I → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, BorelSpace (X i)] :
    BorelSpace (Sigma X) := by
  refine ⟨le_antisymm (fun s hs => ?_) (MeasurableSpace.generateFrom_le fun s hs =>
    MeasurableSpace.measurableSet_iInf.2 fun i => (hs.preimage continuous_sigmaMk).measurableSet)⟩
  have hsec (i : I) : MeasurableSet (Sigma.mk i ⁻¹' s) := MeasurableSpace.measurableSet_iInf.1 hs i
  let : MeasurableSpace (Sigma X) := borel (Sigma X)
  let : BorelSpace (Sigma X) := ⟨rfl⟩
  rw [show s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) by
    ext x; exact ⟨fun hx => Set.mem_iUnion.2 ⟨x.1, x.2, hx, rfl⟩,
      fun hx => by rcases Set.mem_iUnion.1 hx with ⟨_, _, hy, rfl⟩; exact hy⟩]
  exact MeasurableSet.iUnion fun i =>
    (Topology.IsClosedEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image' (hsec i)

theorem historyShapeLength_out (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeLength dependent g = g.out.length := by
  have hh := congrArg (historyShapeLength dependent) (Quotient.out_eq g)
  rwa [historyShapeLength_mk, eq_comm] at hh

def historyShapeCanonicalLabels (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) : Fin (historyShapeLength dependent g) → J :=
  fun i => g.out.get (Fin.cast (historyShapeLength_out dependent g) i)

def historyMarkedRawState (dependent : J → J → Prop) {E X : Type*}
    (update : J → E → X → X) (initial : X) (h : HistoryMarked dependent E) : X :=
  (List.ofFn fun i : Fin (historyShapeLength dependent h.1) => i).foldl
    (fun state i => update (historyShapeCanonicalLabels dependent h.1 i) (h.2 i) state) initial

theorem historyMarkedRawState_measurable (dependent : J → J → Prop) {E X : Type*}
    [MeasurableSpace E] [MeasurableSpace X] (update : J → E → X → X)
    (hu : ∀ j, Measurable (fun ex : E × X => update j ex.1 ex.2)) (initial : X) :
    Measurable (historyMarkedRawState dependent update initial) := by
  rw [historyMarked_measurable_iff]; intro g; dsimp only [historyMarkedRawState]
  have hfold (n : ℕ) (labels : Fin n → J) (indices : List (Fin n)) :
      ∀ (f : (Fin n → E) → X), Measurable f →
        Measurable (fun marks => indices.foldl (fun state i => update (labels i) (marks i) state) (f marks)) := by
    induction indices with
    | nil => exact fun _ hf => hf
    | cons i indices ih =>
      exact fun f hf => ih _ ((hu (labels i)).comp ((measurable_pi_apply i).prodMk hf))
  exact hfold _ _ _ (fun _ => initial) measurable_const

def historyMarkedReferenceRaw (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π)

private lemma historyMarkedReferenceRaw_univ (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    historyMarkedReferenceRaw dependent Δ π Set.univ =
      ∑' g, ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) := by
  unfold historyMarkedReferenceRaw
  rw [Measure.sum_apply _ MeasurableSet.univ]
  congr 1; funext g
  rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]; simp

private lemma historyMarkedReferenceRaw_univ_one_le (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    1 ≤ historyMarkedReferenceRaw dependent Δ π Set.univ := by
  rw [historyMarkedReferenceRaw_univ]
  let empty : HistoryShape (fun a b => ¬ dependent a b) := Quotient.mk _ []
  simpa [empty, historyShapeReferenceWeight, historyShapeLength_mk] using
    ENNReal.le_tsum (f := fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g)) empty

theorem historyMarkedReferenceRaw_finite (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
  ⟨by rw [historyMarkedReferenceRaw_univ]
      exact (historyShapeReferenceWeight_summable dependent hrefl hsymm Δ hΔ hlabels).tsum_ofReal_lt_top⟩

def historyMarkedReference (dependent : J → J → Prop) (Δ : ℕ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedReferenceRaw dependent Δ π

theorem historyMarkedReference_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] :
    IsProbabilityMeasure (historyMarkedReference dependent Δ π) := by
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  refine ⟨?_⟩
  rw [historyMarkedReference, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π)))
    (measure_ne_top _ _)

-- Shape append

omit [Fintype J] [LinearOrder J] in
lemma historyShapeRelation_append {independent : J → J → Prop} {u v : List J}
    (h : Relation.EqvGen (IndependentHistoryExchange independent) u v) (suffix : List J) :
    Relation.EqvGen (IndependentHistoryExchange independent) (u ++ suffix) (v ++ suffix) := by
  induction h with
  | rel _ _ h =>
    cases h with | swap before after x y hxy =>
      simpa only [List.append_assoc, List.cons_append] using
        Relation.EqvGen.rel _ _ (IndependentHistoryExchange.swap before (after ++ suffix) x y hxy)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

def historyShapeAppend (dependent : J → J → Prop) (j : J) :
    HistoryShape (fun a b => ¬ dependent a b) → HistoryShape (fun a b => ¬ dependent a b) :=
  Quotient.lift (fun word => Quotient.mk _ (word ++ [j]))
    fun _ _ h => Quotient.sound (historyShapeRelation_append h [j])

omit [Fintype J] [LinearOrder J] in
@[simp] theorem historyShapeAppend_mk (dependent : J → J → Prop) (j : J) (word : List J) :
    historyShapeAppend dependent j (Quotient.mk _ word) = Quotient.mk _ (word ++ [j]) := rfl

omit [Fintype J] in
theorem historyShapeAppend_injective (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (j : J) :
    Function.Injective (historyShapeAppend dependent j) := by
  intro g h heq
  induction g using Quotient.inductionOn with | _ u =>
  induction h using Quotient.inductionOn with | _ v =>
  refine Quotient.sound (historyShapeRelation_of_pair_projections hrefl hsymm fun i k hik => ?_)
  have hc := congrArg (fun shape => historyShapePairCode dependent hrefl hsymm shape ⟨(i, k), hik⟩) heq
  change (u ++ [j]).filter _ = (v ++ [j]).filter _ at hc
  rw [List.filter_append, List.filter_append] at hc
  exact List.append_cancel_right hc

theorem historyShapeReferenceWeight_append (dependent : J → J → Prop) (Δ : ℕ) (j : J)
    (g : HistoryShape (fun a b => ¬ dependent a b)) :
    historyShapeReferenceWeight dependent Δ (historyShapeAppend dependent j g) =
      historyReferenceRho Δ * historyShapeReferenceWeight dependent Δ g := by
  have hlen : historyShapeLength dependent (historyShapeAppend dependent j g) =
      historyShapeLength dependent g + 1 := by
    induction g using Quotient.inductionOn
    rw [historyShapeAppend_mk, historyShapeLength_mk, historyShapeLength_mk]; simp
  unfold historyShapeReferenceWeight; rw [hlen, pow_succ, mul_comm]

-- Marked prior density and measure identity

def historyMarkedPieceWeight (dependent : J → J → Prop) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) (x : WordHeapPiece h.1.out dependent) : ℝ :=
  a (h.2 (Fin.cast (historyShapeLength_out dependent h.1).symm x.position))

def historyMarkedDensity (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : ℝ :=
  historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ Finset.univ t

theorem historyMarkedDensity_measurable (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) :
    Measurable (historyMarkedDensity dependent ρ t a) := by
  classical
  refine (historyMarked_measurable_iff dependent _).2 fun g => ?_
  unfold historyMarkedDensity
  simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
  change Measurable fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      (t / ρ) ^ P.card * historyOrderVolume P *
        ∏ x ∈ P, a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position))
  exact Finset.measurable_fun_sum _ fun P _ =>
    (Finset.measurable_fun_prod _ fun x _ => ha.comp (measurable_pi_apply _)).const_mul _

theorem historyMarkedDensity_bounds (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ t B : ℝ) (hρ : 0 < ρ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    {E : Type*} (a : E → ℝ) (ha : ∀ e, |a e| ≤ B)
    (hsmall : t * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) (h : HistoryMarked dependent E) :
    (1 / 2 : ℝ) ^ Fintype.card J ≤ historyMarkedDensity dependent ρ t a h ∧
      historyMarkedDensity dependent ρ t a h ≤ (3 / 2 : ℝ) ^ Fintype.card J :=
  wordHeap_density_bounds h.1.out dependent hrefl hsymm Δ hlabels
    (historyMarkedPieceWeight dependent a h) ρ t B hρ ht hB (fun _ => ha _) hsmall

@[simp] theorem historyMarkedDensity_zero (dependent : J → J → Prop) (ρ : ℝ) {E : Type*}
    (a : E → ℝ) (h : HistoryMarked dependent E) : historyMarkedDensity dependent ρ 0 a h = 1 := by
  unfold historyMarkedDensity historyScaledUpperDensity
  exact historyUpperDensity_at_zero _ _

def historyMarkedFiberPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (g : HistoryShape (fun i j => ¬ dependent i j)) :
    Measure (Fin (historyShapeLength dependent g) → E) :=
  (Measure.pi fun _ => π).withDensity
    fun marks => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩)

def historyMarkedPriorRaw (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  Measure.sum fun g => ENNReal.ofReal (historyShapeReferenceWeight dependent Δ g) •
    Measure.map (Sigma.mk g) (historyMarkedFiberPrior dependent Δ t π a g)

def historyMarkedPrior (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ) {E : Type*}
    [MeasurableSpace E] (π : Measure E) (a : E → ℝ) : Measure (HistoryMarked dependent E) :=
  (historyMarkedReferenceRaw dependent Δ π Set.univ)⁻¹ • historyMarkedPriorRaw dependent Δ t π a

theorem historyMarkedPrior_probability (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Integrable a π)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2)) :
    IsProbabilityMeasure (historyMarkedPrior dependent Δ t π a) := by
  have hfib (g : HistoryShape (fun i j => ¬ dependent i j)) :
      IsProbabilityMeasure (historyMarkedFiberPrior dependent Δ t π a g) := by
    let idx : WordHeapPiece g.out dependent → Fin (historyShapeLength dependent g) :=
      fun x => Fin.cast (historyShapeLength_out dependent g).symm x.position
    have hidx : Function.Injective idx := fun x y hxy => WordHeapPiece.ext (Fin.cast_injective _ hxy)
    have hpint (S : Finset (Fin (historyShapeLength dependent g))) :
        Integrable (fun marks : Fin (historyShapeLength dependent g) → E => ∏ i ∈ S, a (marks i))
          (Measure.pi fun _ => π) ∧
        (∫ marks : Fin (historyShapeLength dependent g) → E, ∏ i ∈ S, a (marks i)
          ∂Measure.pi fun _ => π) = ∏ _i ∈ S, ∫ e, a e ∂π := by
      have hp (marks : Fin (historyShapeLength dependent g) → E) :
          (∏ i, if i ∈ S then a (marks i) else 1) = ∏ i ∈ S, a (marks i) := Finset.prod_ite_mem_eq S _
      simp_rw [← hp]
      refine ⟨Integrable.fintype_prod (μ := fun _ : Fin (historyShapeLength dependent g) => π)
        (f := fun i e => if i ∈ S then a e else 1) fun i => by by_cases hi : i ∈ S <;> simp [hi, ha], ?_⟩
      rw [integral_fintype_prod_eq_prod fun i (e : E) => if i ∈ S then a e else 1]
      exact (Finset.prod_congr rfl fun i _ => by by_cases hi : i ∈ S <;> simp [hi]).trans
        (Finset.prod_ite_mem_eq S _)
    have hterm (P : Finset (WordHeapPiece g.out dependent)) :
        Integrable (fun marks => (t / historyReferenceRho Δ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (idx x)))
          (Measure.pi fun _ : Fin (historyShapeLength dependent g) => π) := by
      have hiP : Integrable (fun marks : Fin (historyShapeLength dependent g) → E => ∏ x ∈ P, a (marks (idx x)))
          (Measure.pi fun _ => π) := by
        simpa only [Finset.prod_image hidx.injOn] using (hpint (P.image idx)).1
      exact hiP.const_mul _
    have hprod_eq (P : Finset (WordHeapPiece g.out dependent)) :
        (∫ marks : Fin (historyShapeLength dependent g) → E, ∏ x ∈ P, a (marks (idx x))
          ∂Measure.pi fun _ => π) = ∏ _x ∈ P, ∫ e, a e ∂π := by
      calc
        _ = ∫ marks : Fin (historyShapeLength dependent g) → E, ∏ i ∈ P.image idx, a (marks i)
              ∂Measure.pi fun _ => π :=
          integral_congr_ae (Filter.Eventually.of_forall fun _ => (Finset.prod_image hidx.injOn).symm)
        _ = ∏ _i ∈ P.image idx, ∫ e, a e ∂π := (hpint (P.image idx)).2
        _ = _ := Finset.prod_image hidx.injOn
    have he : (∫ marks, historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩
        ∂Measure.pi fun _ : Fin (historyShapeLength dependent g) => π) = 1 := by
      unfold historyMarkedDensity
      simp_rw [historyScaledUpperDensity_eq_components, historyComponentWeight]
      change (∫ marks, ∑ P ∈ historyUpperSets (Finset.univ : Finset (WordHeapPiece g.out dependent)),
        (t / historyReferenceRho Δ) ^ P.card * historyOrderVolume P * ∏ x ∈ P, a (marks (idx x))
        ∂Measure.pi fun _ => π) = 1
      rw [integral_finsetSum _ fun P _ => hterm P]
      simp_rw [integral_const_mul, hprod_eq, hcenter]
      rw [Finset.sum_eq_single ∅]
      · simp
      · intro P _ hne; rw [Finset.prod_const]; simp [zero_pow (Finset.card_ne_zero.2 (Finset.nonempty_iff_ne_empty.2 hne))]
      · intro hnot; exact (hnot (mem_historyUpperSets.2 ⟨Finset.empty_subset _, by simp⟩)).elim
    have hnn (marks : Fin (historyShapeLength dependent g) → E) :
        0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a ⟨g, marks⟩ :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans
        (historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels _ t B
          (historyReferenceRho_pos Δ) ht hB a habound hsmall ⟨g, marks⟩).1
    refine ⟨?_⟩
    unfold historyMarkedFiberPrior
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_of_integral_eq_one he) (Filter.Eventually.of_forall hnn), he]
    simp
  let : IsFiniteMeasure (historyMarkedReferenceRaw dependent Δ π) :=
    historyMarkedReferenceRaw_finite dependent hrefl hsymm Δ hΔ hlabels π
  refine ⟨?_⟩
  rw [historyMarkedPrior, Measure.smul_apply, smul_eq_mul, show historyMarkedPriorRaw dependent Δ t π a Set.univ =
      historyMarkedReferenceRaw dependent Δ π Set.univ by
    rw [historyMarkedReferenceRaw_univ, historyMarkedPriorRaw, Measure.sum_apply _ MeasurableSet.univ]
    congr 1; funext g
    let := hfib g
    rw [Measure.smul_apply, Measure.map_apply (historyMarked_measurable_mk dependent g) MeasurableSet.univ]; simp]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (historyMarkedReferenceRaw_univ_one_le dependent Δ π)))
    (measure_ne_top _ _)

theorem historyMarkedPrior_eq_withDensity (dependent : J → J → Prop) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ) (ha : Measurable a) :
    historyMarkedPrior dependent Δ t π a =
      (historyMarkedReference dependent Δ π).withDensity
        fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h) := by
  let p : HistoryMarked dependent E → ℝ≥0∞ :=
    fun h => ENNReal.ofReal (historyMarkedDensity dependent (historyReferenceRho Δ) t a h)
  have hp : Measurable p := (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
  unfold historyMarkedPrior historyMarkedReference
  rw [withDensity_smul_measure]
  congr 1
  unfold historyMarkedPriorRaw historyMarkedReferenceRaw
  rw [withDensity_sum]
  congr 1; funext g
  rw [withDensity_smul_measure]
  congr 1
  ext s hs
  have hf := historyMarked_measurable_mk dependent g (E := E)
  rw [Measure.map_apply hf hs, historyMarkedFiberPrior, withDensity_apply _ (hs.preimage hf),
    withDensity_apply _ hs, Measure.restrict_map hf hs, lintegral_map hp hf]

end ShapeDegreeAndReference

-- Adjacent exchange and word heap transport

section WordHeapTransport
variable {J : Type*}

def historyPositionStep {n : ℕ} (dependent : J → J → Prop) (labels : Fin n → J)
    (x y : Fin n) : Prop := x < y ∧ dependent (labels x) (labels y)

theorem wordHeap_le_iff_position_reachable (word : List J) (dependent : J → J → Prop)
    (x y : WordHeapPiece word dependent) :
    x ≤ y ↔ Relation.ReflTransGen (historyPositionStep dependent word.get) x.position y.position := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail hstep
  · have hlift {p q : Fin word.length}
        (hpq : Relation.ReflTransGen (historyPositionStep dependent word.get) p q) :
        Relation.ReflTransGen wordHeapStep (⟨p⟩ : WordHeapPiece word dependent) ⟨q⟩ := by
      induction hpq with
      | refl => exact .refl
      | tail _ hstep ih => exact ih.tail hstep
    cases x; cases y; exact hlift h

private lemma historyAdjacent_swap_lt {n : ℕ} (labels : Fin n → J) (dependent : J → J → Prop)
    (i j x y : Fin n) (hij : i.val + 1 = j.val) (hind : ¬ dependent (labels i) (labels j))
    (hxy : historyPositionStep dependent labels x y) :
    Equiv.swap i j x < Equiv.swap i j y := by
  have hlt : x.val < y.val := hxy.1
  by_cases hxi : x = i
  · subst x; by_cases hyj : y = j
    · subst y; exact (hind hxy.2).elim
    · have hyi : y ≠ i := fun he => by subst y; simp at hlt
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      change j.val < y.val; have := Fin.val_ne_iff.2 hyj; omega
  · by_cases hxj : x = j
    · subst x
      have hyi : y ≠ i := fun he => by subst y; omega
      have hyj : y ≠ j := fun he => by subst y; simp at hlt
      simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hyi hyj]
      change i.val < y.val; omega
    · by_cases hyi : y = i
      · subst y; simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxi hxj]
        change x.val < j.val; omega
      · by_cases hyj : y = j
        · subst y; simp only [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hxi hxj]
          change x.val < i.val; have := Fin.val_ne_iff.2 hxi; omega
        · simpa only [Equiv.swap_apply_of_ne_of_ne hxi hxj, Equiv.swap_apply_of_ne_of_ne hyi hyj] using hxy.1

theorem historyShapeRelation_heapIso (dependent : J → J → Prop)
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    {u v : List J} (h : Relation.EqvGen (IndependentHistoryExchange (fun a b => ¬ dependent a b)) u v) :
    ∃ e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent,
      ∀ x, wordHeapLabel (e x) = wordHeapLabel x := by
  induction h with
  | rel u v h =>
    cases h with
    | swap before after a b hind =>
      let u0 := before ++ a :: b :: after
      let v0 := before ++ b :: a :: after
      have hlen : u0.length = v0.length := by simp [u0, v0]
      let i : Fin u0.length := ⟨before.length, by simp [u0]⟩
      let j : Fin u0.length := ⟨before.length + 1, by simp [u0]⟩
      have hne : i ≠ j := fun he => by have := congrArg Fin.val he; dsimp [i, j] at this; omega
      let e : Fin u0.length ≃ Fin v0.length := (Equiv.swap i j).trans (finCongr hlen)
      have hget (x : Fin u0.length) : v0.get (e x) = u0.get x := by
        simp only [List.get_eq_getElem, e, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
        by_cases hxi : x = i
        · subst x; simp only [Equiv.swap_apply_left, i, j, u0, v0]
          rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]; simp
        · by_cases hxj : x = j
          · subst x; simp only [Equiv.swap_apply_right, i, j, u0, v0]
            rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]; simp
          · simp only [Equiv.swap_apply_of_ne_of_ne hxi hxj, u0, v0]
            have hni : x.val ≠ before.length := fun hv => hxi (Fin.ext hv)
            have hnj : x.val ≠ before.length + 1 := fun hv => hxj (Fin.ext hv)
            by_cases hlt : x.val < before.length
            · rw [List.getElem_append_left hlt, List.getElem_append_left hlt]
            · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
              obtain ⟨k, hk⟩ : ∃ k, x.val - before.length = k + 2 := ⟨x.val - before.length - 2, by omega⟩
              simp [hk]
      have hui : u0.get i = a := by simp only [List.get_eq_getElem, u0, i]; rw [List.getElem_append_right (by omega)]; simp
      have huj : u0.get j = b := by simp only [List.get_eq_getElem, u0, j]; rw [List.getElem_append_right (by omega)]; simp
      have hstep (x y : Fin u0.length) :
          historyPositionStep dependent u0.get x y ↔ historyPositionStep dependent v0.get (e x) (e y) := by
        unfold historyPositionStep
        rw [hget x, hget y]
        simp only [e, Equiv.trans_apply, finCongr_apply, Fin.cast_lt_cast]
        refine ⟨fun h => ⟨historyAdjacent_swap_lt u0.get dependent i j x y rfl (by rw [hui, huj]; exact hind) h, h.2⟩,
          fun h => ⟨?_, h.2⟩⟩
        have he := historyAdjacent_swap_lt (u0.get ∘ Equiv.swap i j) dependent i j
          (Equiv.swap i j x) (Equiv.swap i j y) rfl
          (by simp only [Function.comp_def, Equiv.swap_apply_left, Equiv.swap_apply_right, hui, huj]
              exact fun hba => hind (hsymm hba))
          ⟨h.1, by simpa only [Function.comp_def, Equiv.swap_apply_self] using h.2⟩
        simpa only [Equiv.swap_apply_self] using he
      refine ⟨{
        toFun := fun x => ⟨e x.position⟩
        invFun := fun x => ⟨e.symm x.position⟩
        left_inv := fun x => WordHeapPiece.ext (e.symm_apply_apply x.position)
        right_inv := fun x => WordHeapPiece.ext (e.apply_symm_apply x.position)
        map_rel_iff' := fun {x y} => by
          rw [wordHeap_le_iff_position_reachable, wordHeap_le_iff_position_reachable]
          refine ⟨fun h => ?_, Relation.ReflTransGen.lift e (fun a b h => (hstep a b).1 h) x.position y.position⟩
          have hl := Relation.ReflTransGen.lift e.symm (r := historyPositionStep dependent v0.get)
            (p := historyPositionStep dependent u0.get)
            (fun a b hab => (hstep (e.symm a) (e.symm b)).2 (by simpa only [e.apply_symm_apply] using hab))
            (e x.position) (e y.position) h
          dsimp only [Function.onFun] at hl
          simpa only [e.symm_apply_apply] using hl }, fun x => hget x.position⟩
  | refl => exact ⟨OrderIso.refl _, fun _ => rfl⟩
  | symm _ _ _ ih =>
    obtain ⟨e, he⟩ := ih
    exact ⟨e.symm, fun x => by simpa only [e.apply_symm_apply] using (he (e.symm x)).symm⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨e₁, he₁⟩ := ih₁; obtain ⟨e₂, he₂⟩ := ih₂
    exact ⟨e₁.trans e₂, fun x => (he₂ (e₁ x)).trans (he₁ x)⟩

end WordHeapTransport
end HistoryShapesAndMeasures
end HistoryCombinatorics
end NearlyMinimax
