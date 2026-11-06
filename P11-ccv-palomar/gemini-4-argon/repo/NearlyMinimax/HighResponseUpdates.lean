module
public import NearlyMinimax.Chebyshev
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import NearlyMinimax.LowSmoothnessVariance
@[expose] public section
noncomputable section
open Polynomial Finset MeasureTheory VectorMeasure Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}
def lobattoDerivativeWeight (m : ℕ) (i : Fin ((2 * m + 1) + 1)) : ℝ :=
  (Lagrange.basis Finset.univ (lobattoNode (2 * m + 1)) i).derivative.eval 0
theorem lobattoNode_reflection (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    lobattoNode n i.rev = -lobattoNode n i := by
  have hangle : (↑i.rev.val * Real.pi / n) =
      Real.pi - ↑i.val * Real.pi / n := by
    simp only [Fin.val_rev]
    rw [show n + 1 - (i.val + 1) = n - i.val by omega, Nat.cast_sub (by omega)]
    push_cast
    field_simp
  unfold lobattoNode
  rw [hangle, Real.cos_pi_sub]
theorem odd_lobatto_nodal_even (m : ℕ) :
    (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).comp (-X) =
      Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1)) := by
  rw [Lagrange.nodal, Polynomial.prod_comp]
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have hf (i : Fin ((2 * m + 1) + 1)) :
      -X - C (lobattoNode (2 * m + 1) i) =
        (-1) * (X - C (lobattoNode (2 * m + 1) i.rev)) := by
    rw [lobattoNode_reflection (2 * m + 1) (by omega), map_neg]
    ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have heven : (-1 : ℝ[X]) ^ ((2 * m + 1) + 1) = 1 := by
    rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega, pow_mul]
    norm_num
  rw [heven, one_mul]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)
theorem odd_lobatto_nodal_derivative_zero (m : ℕ) :
    (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).derivative.eval 0 = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) (odd_lobatto_nodal_even m)
  simp only [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_X, neg_zero] at h
  linarith
theorem cardinal_mul_node_factor {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℝ) (i : ι) (hi : i ∈ S) :
    Lagrange.basis S z i * (X - C (z i)) =
      C (Lagrange.nodalWeight S z i) * Lagrange.nodal S z := by
  have hb : Lagrange.basis S z i = C (Lagrange.nodalWeight S z i) *
      Lagrange.nodal (S.erase i) z := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
      ← Lagrange.nodal_erase_eq_nodal_div hi]
  rw [hb, Lagrange.nodal_eq_mul_nodal_erase hi]
  ring
theorem cardinal_derivative_zero_formula {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → ℝ) (i : ι) (hi : i ∈ S) (hzi : z i ≠ 0)
    (hW : (Lagrange.nodal S z).derivative.eval 0 = 0) :
    (Lagrange.basis S z i).derivative.eval 0 =
      -(Lagrange.nodal S z).eval 0 * Lagrange.nodalWeight S z i / (z i) ^ 2 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0)
    (cardinal_mul_node_factor S z i hi)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul, eval_sub, eval_X, eval_C, zero_sub, sub_zero, mul_one, zero_mul, zero_add, hW, mul_zero] at h
  rw [Lagrange.eval_basis_not_at_node (v := z) (x := 0) hi (Ne.symm hzi)] at h
  simp only [zero_sub, inv_neg] at h
  field_simp at h
  apply (eq_div_iff (pow_ne_zero 2 hzi)).mpr
  nlinarith
theorem decreasing_nodalWeight_sign (n : ℕ) (z : Fin (n + 1) → ℝ)
    (hz : StrictAnti z) (i : Fin (n + 1)) :
    Lagrange.nodalWeight Finset.univ z i =
      (-1 : ℝ) ^ i.val * |Lagrange.nodalWeight Finset.univ z i| := by
  let S := (Finset.univ : Finset (Fin (n + 1))).erase i
  have hf (j : Fin (n + 1)) (hj : j ∈ S) :
      (z i - z j)⁻¹ = (if j < i then (-1 : ℝ) else 1) * |(z i - z j)⁻¹| := by
    have hji  := (Finset.mem_erase.mp hj).1
    by_cases hlt : j < i
    · rw [if_pos hlt, abs_of_neg (inv_lt_zero.mpr (sub_neg.mpr (hz hlt)))]
      ring
    · have hij  := lt_of_le_of_ne (le_of_not_gt hlt) hji.symm
      rw [if_neg hlt, abs_of_pos (inv_pos.mpr (sub_pos.mpr (hz hij))), one_mul]
  have hs : (∏ j ∈ S, if j < i then (-1 : ℝ) else 1) = (-1 : ℝ) ^ i.val := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    have hset : S.filter (fun j => j < i) = Finset.Iio i := by
      ext j
      simp [S, Finset.mem_Iio]
      omega
    rw [hset, Fin.card_Iio]
  unfold Lagrange.nodalWeight
  change (∏ j ∈ S, (z i - z j)⁻¹) = _
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf
theorem lobattoDerivativeWeight_factorization (m : ℕ) (i : Fin ((2 * m + 1) + 1)) :
    lobattoDerivativeWeight m i =
      -(Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).eval 0 * (-1 : ℝ) ^ i.val *
        (|Lagrange.nodalWeight Finset.univ (lobattoNode (2 * m + 1)) i| /
          lobattoNode (2 * m + 1) i ^ 2) := by
  have h_odd_lobattoNode_ne_zero : lobattoNode (2 * m + 1) i ≠ 0 := by
    intro hz
    have hrev := lobattoNode_reflection (2 * m + 1) (by omega) i
    have hi : i.rev = i := (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective (by rw [hrev, hz]; simp)
    have hval := congrArg Fin.val hi
    simp only [Fin.val_rev] at hval
    omega
  rw [lobattoDerivativeWeight, cardinal_derivative_zero_formula Finset.univ
    (lobattoNode (2 * m + 1)) i (Finset.mem_univ i) h_odd_lobattoNode_ne_zero
    (odd_lobatto_nodal_derivative_zero m)]
  nth_rw 1 [decreasing_nodalWeight_sign (2 * m + 1) (lobattoNode (2 * m + 1))
    (lobattoNode_strictAnti (2 * m + 1) (by omega)) i]
  ring
theorem chebyshev_at_lobatto (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (Polynomial.Chebyshev.T ℝ ↑n).eval (lobattoNode n i) = (-1 : ℝ) ^ i.val := by
  have : (n : ℝ) ≠ 0 := by positivity
  rw [lobattoNode, Polynomial.Chebyshev.T_real_cos]
  simp only [Int.cast_natCast, mul_div_cancel₀ _ this]
  simpa using Real.cos_nat_mul_pi_sub 0 i.val
theorem chebyshev_odd_derivative_abs (m : ℕ) :
    |(Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ) : ℤ)).derivative.eval 0| = (2 * m + 1 : ℕ) := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [eval_mul, eval_natCast, Int.cast_natCast]
  have he : ((2 * m + 1 : ℕ) : ℤ) - 1 = 2 * ↑m := by omega
  rw [he, Polynomial.Chebyshev.U_eval_two_mul_zero, abs_mul]
  have hs : |((m : ℤ).negOnePow : ℝ)| = 1 := by
    exact_mod_cast Int.abs_negOnePow (m : ℤ)
  rw [hs, mul_one, abs_of_nonneg (Nat.cast_nonneg (2 * m + 1))]
theorem lobatto_derivative_rule_variation (m : ℕ) :
    (∑ i : Fin ((2 * m + 1) + 1), |lobattoDerivativeWeight m i|) = (2 * m + 1 : ℕ) := by
  let c := -(Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).eval 0
  let r := fun i : Fin ((2 * m + 1) + 1) =>
    |Lagrange.nodalWeight Finset.univ (lobattoNode (2 * m + 1)) i| /
      lobattoNode (2 * m + 1) i ^ 2
  have hr (i : Fin ((2 * m + 1) + 1)) : 0 ≤ r i :=
    div_nonneg (abs_nonneg _) (sq_nonneg _)
  have hw (i : Fin ((2 * m + 1) + 1)) :
      lobattoDerivativeWeight m i = c * (-1 : ℝ) ^ i.val * r i :=
    lobattoDerivativeWeight_factorization m i
  have habs (i : Fin ((2 * m + 1) + 1)) :
      |lobattoDerivativeWeight m i| = |c| * r i := by
    rw [hw, abs_mul, abs_mul, abs_pow, abs_of_nonneg (hr i)]
    norm_num
  have heval (i : Fin ((2 * m + 1) + 1)) :
      lobattoDerivativeWeight m i *
        (Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ) : ℤ)).eval (lobattoNode (2 * m + 1) i) = c * r i := by
    rw [chebyshev_at_lobatto (2 * m + 1) (by omega) i, hw]
    have hs : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm i.val 2, pow_mul]
      norm_num
    calc
      (c * (-1 : ℝ) ^ i.val * r i) * (-1 : ℝ) ^ i.val =
        c * r i * ((-1 : ℝ) ^ i.val) ^ 2 := by ring
      _ = _ := by rw [hs, mul_one]
  have h_lobatto_derivative_rule_exact (P : ℝ[X]) (hP : P.degree ≤ 2 * m + 1) : (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight m i * P.eval (lobattoNode (2 * m + 1) i)) =
      P.derivative.eval 0 := by
    apply cardinal_derivative_exact Finset.univ (lobattoNode (2 * m + 1))
      (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective.injOn
    simpa using hP.trans_lt (show (2 * m + 1 : WithBot ℕ) < ((2 * m + 1) + 1 : ℕ) by
      exact_mod_cast Nat.lt_succ_self (2 * m + 1))
  have hexact := h_lobatto_derivative_rule_exact (Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ) : ℤ)) (Polynomial.degree_le_of_natDegree_le (chebyshev_natDegree_le (2 * m + 1)))
  simp_rw [heval] at hexact
  rw [← Finset.mul_sum] at hexact
  calc
    (∑ i : Fin ((2 * m + 1) + 1), |lobattoDerivativeWeight m i|) =
        |c| * ∑ i, r i := by simp_rw [habs]; rw [Finset.mul_sum]
    _ = |c * ∑ i, r i| := by
      rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg (fun i hi => hr i))]
    _ = _ := by rw [hexact, chebyshev_odd_derivative_abs]
theorem lobattoDerivativeWeight_abs_reflection (m : ℕ) (i : Fin ((2 * m + 1) + 1)) :
    |lobattoDerivativeWeight m i.rev| = |lobattoDerivativeWeight m i| := by
  have h_lobattoDerivativeWeight_reflection : lobattoDerivativeWeight m i.rev = -lobattoDerivativeWeight m i := by
    let n := 2 * m + 1
    let z := lobattoNode n
    have hn : 1 ≤ n := by dsimp [n]; omega
    have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
      (lobattoNode_strictAnti n hn).injective.injOn
    have hpoly : (Lagrange.basis Finset.univ z i.rev).comp (-X) =
        Lagrange.basis Finset.univ z i := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
      · have hnat : ((Lagrange.basis Finset.univ z i.rev).comp (-X)).natDegree ≤ n := by
          apply Polynomial.natDegree_comp_le.trans
          simp [Lagrange.natDegree_basis hv (Finset.mem_univ i.rev)]
        apply (Polynomial.degree_le_of_natDegree_le hnat).trans_lt
        simpa using (show (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) by
          exact_mod_cast Nat.lt_succ_self n)
      · rw [Lagrange.degree_basis hv (Finset.mem_univ i)]
        simpa using (show (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) by
          exact_mod_cast Nat.lt_succ_self n)
      · intro j hj
        rw [eval_comp, eval_neg, eval_X, ← lobattoNode_reflection n hn j]
        by_cases hij : i = j
        · subst j
          rw [Lagrange.eval_basis_self hv (Finset.mem_univ i.rev),
            Lagrange.eval_basis_self hv (Finset.mem_univ i)]
        · have hrev : i.rev ≠ j.rev := by
            intro heq
            have he := congrArg Fin.rev heq
            apply hij
            simpa using he
          change (Lagrange.basis Finset.univ z i.rev).eval (z j.rev) =
            (Lagrange.basis Finset.univ z i).eval (z j)
          rw [Lagrange.eval_basis_of_ne hrev (Finset.mem_univ j.rev),
            Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)]
    have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) hpoly
    simp only [derivative_comp, derivative_neg, derivative_X, eval_neg, eval_comp, eval_X, neg_zero, neg_one_mul] at h
    change -lobattoDerivativeWeight m i.rev = lobattoDerivativeWeight m i at h
    linarith
  rw [h_lobattoDerivativeWeight_reflection, abs_neg]
theorem lobatto_derivative_rule_exact_extra (m : ℕ) (P : ℝ[X])
    (hP : P.degree ≤ (2 * m + 1) + 1) :
    (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight m i * P.eval (lobattoNode (2 * m + 1) i)) =
      P.derivative.eval 0 := by
  let n := 2 * m + 1
  let z := lobattoNode n
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
    (lobattoNode_strictAnti n (by dsimp [n]; omega)).injective.injOn
  by_cases hp : P.degree < (n + 1 : ℕ)
  · exact cardinal_derivative_exact Finset.univ z hv P (by simpa using hp) 0
  have hdeg : P.degree = (n + 1 : ℕ) := le_antisymm hP (le_of_not_gt hp)
  have hp0 : P ≠ 0 := by
    intro hzero
    rw [hzero, degree_zero] at hdeg
    change (⊥ : WithBot ℕ) = ((n + 1 : ℕ) : WithBot ℕ) at hdeg
    exact WithBot.bot_ne_coe hdeg
  let W := Lagrange.nodal Finset.univ z
  let Q := P - C P.leadingCoeff * W
  have hCW : (C P.leadingCoeff * W).degree = P.degree := by
    rw [degree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hp0), hdeg]
    simp [W, Lagrange.degree_nodal]
  have hQ : Q.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    have h := Polynomial.degree_sub_lt hCW.symm hp0 (by simp [leadingCoeff_mul, W, (Lagrange.nodal_monic (s := Finset.univ) (v := z)).leadingCoeff])
    simpa only [Q, hdeg, Finset.card_univ, Fintype.card_fin] using h
  have he (i : Fin (n + 1)) : Q.eval (z i) = P.eval (z i) := by
    simp [Q, W, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
  have hder : Q.derivative.eval 0 = P.derivative.eval 0 := by
    simp only [Q, derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C]
    change P.derivative.eval 0 - P.leadingCoeff *
      (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).derivative.eval 0 = P.derivative.eval 0
    rw [odd_lobatto_nodal_derivative_zero, mul_zero, sub_zero]
  have hexact := cardinal_derivative_exact Finset.univ z hv Q hQ 0
  simp_rw [he, hder] at hexact
  exact hexact
def derivativeOrder (D : ℕ) : ℕ := 2 * ((D - 1) / 2) + 1
theorem derivativeOrder_bounds (D : ℕ) (hD : 1 ≤ D) :
    derivativeOrder D ≤ D ∧ D ≤ derivativeOrder D + 1 := by
  dsimp [derivativeOrder]
  omega
section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]
def atomicSignedRule (z : ι → X) (w : ι → ℝ) : SignedMeasure X :=
  ∑ i, VectorMeasure.dirac (z i) (w i)
def atomicVariationBound (z : ι → X) (w : ι → ℝ) : Measure X :=
  ∑ i, ‖w i‖₊ • Measure.dirac (z i)
theorem atomicSignedRule_integral (z : ι → X) (w : ι → ℝ) (f : X → ℝ) :
    ∫ᵛ x, f x ∂<•(atomicSignedRule z w) = ∑ i, w i * f (z i) := by
  have h_atomic_dirac_integrable (x : X) (w : ℝ) : (VectorMeasure.dirac x w).Integrable f := by
    change Integrable f (VectorMeasure.dirac x w).variation
    rw [VectorMeasure.variation_dirac]
    exact (integrable_dirac (by exact enorm_lt_top)).smul_measure_nnreal
  rw [atomicSignedRule, integral_finsetSum_vectorMeasure
    (fun i hi => (h_atomic_dirac_integrable (z i) (w i)))]
  simp [mul_comm]
theorem atomicSignedRule_variation_le (z : ι → X) (w : ι → ℝ) :
    (atomicSignedRule z w).variation ≤ atomicVariationBound z w := by
  apply (VectorMeasure.variation_finsetSum_le Finset.univ _).trans_eq
  simp only [VectorMeasure.variation_dirac]
  rfl
end Atomic
section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]
theorem atomicVariationBound_total (z : ι → X) (w : ι → ℝ) :
    atomicVariationBound z w Set.univ = ∑ i, ‖w i‖ₑ := by
  simp [atomicVariationBound, Measure.finsetSum_apply, enorm_eq_nnnorm]
theorem atomicSignedRule_totalVariation_le (z : ι → X) (w : ι → ℝ) :
    ((atomicSignedRule z w).variation Set.univ).toReal ≤ ∑ i, |w i| := by
  have h := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at h
  apply (ENNReal.toReal_mono (by simp) h).trans_eq
  rw [ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp
theorem atomicSignedRule_totalVariation_eq (z : ι → X) (w : ι → ℝ)
    (hz : Function.Injective z) :
    ((atomicSignedRule z w).variation Set.univ).toReal = ∑ i, |w i| := by
  have hsingleton (i : ι) : (atomicSignedRule z w).variation {z i} = ‖w i‖ₑ := by
    have h_atomicSignedRule_singleton : atomicSignedRule z w {z i} = w i := by
      rw [atomicSignedRule, VectorMeasure.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        exact VectorMeasure.dirac_apply_of_notMem (by simpa using hz.ne hji)
      · simp
    rw [VectorMeasure.variation_apply_singleton, h_atomicSignedRule_singleton]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i => ({z i} : Set X)) := by
    intro i hi j hj hij
    exact Set.disjoint_singleton.mpr (hz.ne hij)
  have hsum := measure_biUnion_finset (μ := (atomicSignedRule z w).variation)
    hdisj (fun i hi => measurableSet_singleton (z i))
  have hlower : (∑ i, ‖w i‖ₑ) ≤ (atomicSignedRule z w).variation Set.univ := by
    simp_rw [hsingleton] at hsum
    rw [← hsum]
    exact measure_mono (Set.subset_univ _)
  have hupper := Measure.le_iff.1 (atomicSignedRule_variation_le z w) Set.univ MeasurableSet.univ
  rw [atomicVariationBound_total] at hupper
  have he := le_antisymm hupper hlower
  rw [he, ENNReal.toReal_sum (fun i hi => enorm_ne_top)]
  simp
end Atomic
section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Covariance
def ternaryLinePolynomial (a f V δ : ℝ) (y : Fin 3) : ℝ[X] :=
  C (ternaryMass a f V y) + monomial 1 (δ * ternaryMeanDerivative a f y) +
    monomial 2 (δ ^ 2 * ternaryVarianceDerivative a y)
theorem ternary_line_polynomial_eval (a f V δ z : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).eval z = ternaryMass a (f + z * δ) V y := by
  fin_cases y <;> simp [ternaryLinePolynomial, ternaryMass, ternaryMeanDerivative,
    ternaryVarianceDerivative, div_eq_mul_inv] <;> ring
theorem ternary_line_polynomial_natDegree (a f V δ : ℝ) (y : Fin 3) :
    (ternaryLinePolynomial a f V δ y).natDegree ≤ 2 := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (by simp) ((natDegree_monomial_le _).trans (by norm_num))
  · exact natDegree_monomial_le _
def responseLinePolynomial (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) : ℝ[X] := ∏ i, ternaryLinePolynomial a (f i) V (δ i) (y i)
theorem response_line_polynomial_eval (n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (z : ℝ) :
    (responseLinePolynomial n a V f δ y).eval z =
      ∏ i, ternaryMass a (f i + z * δ i) V (y i) := by
  simp only [responseLinePolynomial, eval_prod]
  simp only [ternary_line_polynomial_eval]
theorem response_line_rule_exact (q n : ℕ) (a V : ℝ) (f δ : Fin n → ℝ)
    (y : Fin n → Fin 3) (hn : n ≤ q) :
    (∑ j : Fin (2 * q + 2), responseWeight q j *
      ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i)) =
      (responseLinePolynomial n a V f δ y).coeff 2 := by
  have h_response_line_polynomial_natDegree : (responseLinePolynomial n a V f δ y).natDegree ≤ 2 * n := by
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum (fun i _ => ternary_line_polynomial_natDegree _ _ _ _ _)
      _ = _ := by simp [mul_comm]
  simpa only [response_line_polynomial_eval] using response_rule_exact q
    (responseLinePolynomial n a V f δ y)
    (degree_le_natDegree.trans_lt (by
      exact_mod_cast (show (responseLinePolynomial n a V f δ y).natDegree < 2 * q + 2 from
        h_response_line_polynomial_natDegree.trans_lt (by omega))))
theorem response_scalar_action_abs_bound (q : ℕ) (H D E : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hH : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt H (D z) z)
    (hD : ∀ z ∈ Icc (0 : ℝ) 1, HasDerivAt D (E z) z)
    (hE : ∀ z ∈ Icc (0 : ℝ) 1, |E z| ≤ B)
    (hnodes : ∀ j : Fin (2 * q + 2), responseNode q j ∈ Icc (0 : ℝ) 1) :
    |∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)| ≤
      (∑ j : Fin (2 * q + 2), |responseWeight q j|) * B := by
  have he : (∑ j : Fin (2 * q + 2), responseWeight q j * H (responseNode q j)) =
      ∑ j : Fin (2 * q + 2), responseWeight q j *
        (H (responseNode q j) - H 0 - responseNode q j * D 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← mul_assoc]
    have h_response_zero_mean : (∑ j : Fin (2 * q + 2), responseWeight q j * responseNode q j) = 0 := by
      simpa using response_rule_moments q 1 (by omega)
    rw [← Finset.sum_mul, ← Finset.sum_mul, response_zero_mass, h_response_zero_mean]
    simp
  rw [he]
  calc
    _ ≤ ∑ j : Fin (2 * q + 2), |responseWeight q j *
      (H (responseNode q j) - H 0 - responseNode q j * D 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2 * q + 2), |responseWeight q j| * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have h_affine_line_remainder_abs_bound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |H z - H 0 - z * D 0| ≤ B := by
        have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
        have hDdiff (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : |D u - D 0| ≤ B := by
          have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
            (fun x hx => (hD x hx).hasDerivWithinAt)
            (fun x hx => by simpa only [Real.norm_eq_abs] using hE x hx)
            (convex_Icc (0 : ℝ) 1) hzero hu
          simp only [Real.norm_eq_abs, sub_zero] at h
          have huabs  := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
          exact h.trans (mul_le_mul_of_nonneg_left huabs hB |>.trans_eq (mul_one B))
        let G := fun u => H u - H 0 - u * D 0
        have hG (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : HasDerivAt G (D u - D 0) u :=
          (((hH u hu).sub_const (H 0)).sub ((hasDerivAt_id u).mul_const (D 0))).congr_deriv (by ring)
        have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
          (fun x hx => (hG x hx).hasDerivWithinAt)
          (fun x hx => by simpa only [Real.norm_eq_abs] using hDdiff x hx)
          (convex_Icc (0 : ℝ) 1) hzero hz
        have hzabs  := abs_le.mpr ⟨by linarith [hz.1], hz.2⟩
        simp only [G, sub_zero, zero_mul, sub_self, Real.norm_eq_abs] at h
        exact h.trans (mul_le_mul_of_nonneg_left hzabs hB |>.trans_eq (mul_one B))
      exact mul_le_mul_of_nonneg_left (h_affine_line_remainder_abs_bound _ (hnodes j)) (abs_nonneg _)
    _ = _ := by rw [Finset.sum_mul]
section Covariance
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def coefficientReset (c v : ι → ℝ) (z : ℝ) : ι → ℝ :=
  fun i => (1 - z) * c i + z * v i
def responseMatrixAction (q : ℕ) (C : ℝ) (A : ι → ι → ℝ)
    (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  covarianceAction C A (fun v => ∑ j : Fin (2 * q + 2),
    responseWeight q j * Φ (coefficientReset c v (responseNode q j)))
theorem responseMatrixAction_zero_mass (q : ℕ) (C : ℝ) (A : ι → ι → ℝ) (c : ι → ℝ) :
    responseMatrixAction q C A c (fun _ => 1) = 0 := by
  simp [responseMatrixAction, response_zero_mass, covarianceAction]
theorem responseNode_mem_unit (q : ℕ) (j : Fin (2 * q + 2)) :
    responseNode q j ∈ Icc (0 : ℝ) 1 := by
  have hden : (0 : ℝ) < 2 * q + 1 := by positivity
  constructor
  · exact div_nonneg (by positivity) hden.le
  · apply (div_le_one hden).mpr
    exact_mod_cast (show j.val ≤ 2 * q + 1 by omega)
theorem coefficientReset_mem_ball (C : ℝ) (c v : ι → ℝ) (z : ℝ)
    (hz : z ∈ Icc (0 : ℝ) 1)
    (hc : ∑ i, |c i| ≤ C⁻¹) (hv : ∑ i, |v i| ≤ C⁻¹) :
    (∑ i, |coefficientReset c v z i|) ≤ C⁻¹ := by
  calc
    _ ≤ ∑ i, ((1 - z) * |c i| + z * |v i|) := by
      apply Finset.sum_le_sum
      intro i _
      apply (abs_add_le _ _).trans_eq
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith [hz.2] : 0 ≤ 1 - z), abs_of_nonneg hz.1]
    _ = (1 - z) * (∑ i, |c i|) + z * (∑ i, |v i|) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (1 - z) * C⁻¹ + z * C⁻¹ := add_le_add
      (mul_le_mul_of_nonneg_left hc (by linarith [hz.2])) (mul_le_mul_of_nonneg_left hv hz.1)
    _ = _ := by ring
def spatialFrameCovariance (A : ι → ι → ℝ)  (φ : Fin n → ι → ℝ)
    (i l : Fin n) : ℝ := ∑ k, ∑ m, φ i k * φ l m * A k m
def coefficientRegression  (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) : Fin n → ℝ :=
  fun i => g i + η * w i * ∑ k, φ i k * c k
def coefficientDirection  (η : ℝ) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) : Fin n → ℝ :=
  fun i => η * w i * ∑ k, φ i k * (v k - c k)
theorem coefficientRegression_reset  (η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c v : ι → ℝ) (z : ℝ) :
    coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i := by
  funext i
  have hs : (∑ k, φ i k * coefficientReset c v z k) =
      (∑ k, φ i k * c k) + z * ((∑ k, φ i k * v k) - ∑ k, φ i k * c k) := by
    calc
      _ = ∑ k, (φ i k * c k + z * (φ i k * v k - φ i k * c k)) := by
        apply Finset.sum_congr rfl
        intro k _
        dsimp [coefficientReset]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [coefficientRegression, coefficientDirection, hs, mul_sub, Finset.sum_sub_distrib]
  ring
theorem covariance_direction_product  (C η : ℝ) (A : ι → ι → ℝ)
    (hC : C ≠ 0) (hA : ∀ i j, A i j = A j i) (w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i l : Fin n) :
    covarianceAction C A (fun v => coefficientDirection η w φ c v i *
      coefficientDirection η w φ c v l) = η ^ 2 * w i * w l * spatialFrameCovariance A φ i l := by
  have he : (fun v : ι → ℝ => coefficientDirection η w φ c v i * coefficientDirection η w φ c v l) =
      (fun v => η ^ 2 * w i * w l *
        ∑ k, ∑ m, (φ i k * φ l m) * ((v k - c k) * (v m - c m))) := by
    funext v
    simp only [coefficientDirection, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [he, covarianceAction_mul, covarianceAction_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [covarianceAction_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h_covariance_displacement_second (c : ι → ℝ) (k : ι) (l : ι) : covarianceAction C A (fun v => (v k - c k) * (v l - c l)) = A k l := by
    have hf : (fun v : ι → ℝ => (v k - c k) * (v l - c l)) =
        (fun v => v k * v l + (-c l) * v k + (-c k) * v l + c k * c l * 1) := by
      funext v
      ring
    rw [hf, covarianceAction_add, covarianceAction_add, covarianceAction_add,
      covarianceAction_mul, covarianceAction_mul, covarianceAction_mul,
      covariance_second_moment_symmetric C A hC hA, covariance_zero_mean,
      covariance_zero_mean, covariance_zero_mass]
    ring
  rw [covarianceAction_mul, h_covariance_displacement_second]
def highResponseProduct  (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∏ i, ternaryMass a (coefficientRegression η g w φ c i) V (y i)
theorem high_response_matrix_second  (q : ℕ) (hn : n ≤ q)
    (C a V η : ℝ) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) :
    responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y) =
      (1 / 2 : ℝ) * covarianceAction C A (fun v =>
        finiteProductSecond Finset.univ
          (fun i z => ternaryMass a (coefficientRegression η g w φ c i +
            z * coefficientDirection η w φ c v i) V (y i))
          (fun i z => coefficientDirection η w φ c v i * ternaryMeanDerivative a
            (coefficientRegression η g w φ c i + z * coefficientDirection η w φ c v i) (y i))
          (fun i _ => (coefficientDirection η w φ c v i) ^ 2 * ternaryMeanSecondDerivative a (y i)) 0) := by
  rw [← covarianceAction_mul]
  apply congrArg (covarianceAction C A)
  funext v
  simp only [highResponseProduct, coefficientRegression_reset]
  rw [response_line_rule_exact q n a V _ _ y hn]
  have h_response_line_quadratic_coefficient (f : Fin n → ℝ) (δ : Fin n → ℝ) : 2 * (responseLinePolynomial n a V f δ y).coeff 2 =
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
    have hQ (z : ℝ) : HasDerivAt (fun z => Q.eval z) (finiteProductFirst Finset.univ H D z) z := by
      simpa only [Q, response_line_polynomial_eval] using
        finite_product_hasDerivAt Finset.univ H D z (fun i _ => hH i z)
    have hd : (fun z => Q.derivative.eval z) = finiteProductFirst Finset.univ H D := by
      funext z
      exact (Q.hasDerivAt z).unique (hQ z)
    have hsecond := finite_product_first_hasDerivAt Finset.univ H D E 0
      (fun i _ => hH i 0) (fun i _ => hD i 0)
    rw [← hd] at hsecond
    have he := (Q.derivative.hasDerivAt 0).unique hsecond
    rw [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_derivative] at he
    norm_num only [Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.zero_add] at he
    simpa only [mul_comm, Q, H, D, E] using he
  have := h_response_line_quadratic_coefficient (coefficientRegression η g w φ c) (coefficientDirection η w φ c v)
  linarith
def highResponseVarianceTerm  (a V η : ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) (i : Fin n) : ℝ :=
  ternaryVarianceDerivative a (y i) * ∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
    ternaryMass a (coefficientRegression η g w φ c l) V (y l)
theorem high_response_matrix_heat  (q : ℕ) (hn : n ≤ q)
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
      (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) *
        m l * m i * (δ v l * δ v i)) +
      (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i))
  have hS (v : ι → ℝ) :
      finiteProductSecond Finset.univ
        (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
        (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
        (fun i _ => (δ v i) ^ 2 * e i) 0 = S v := by
    simp only [finiteProductSecond, zero_mul, add_zero, S]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      dsimp [p, m]
      ring
    · dsimp [p]
      ring
  rw [high_response_matrix_second q hn C a V η A g w φ c y]
  change (1 / 2 : ℝ) * covarianceAction C A
    (fun v => finiteProductSecond Finset.univ
      (fun i z => ternaryMass a (f i + z * δ v i) V (y i))
      (fun i z => δ v i * ternaryMeanDerivative a (f i + z * δ v i) (y i))
      (fun i _ => (δ v i) ^ 2 * e i) 0) = _
  simp_rw [hS]
  unfold S
  rw [covarianceAction_sum]
  have he (i : Fin n) : covarianceAction C A
      (fun v => (∑ l ∈ (Finset.univ : Finset (Fin n)).erase i,
        (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) *
          m l * m i * (δ v l * δ v i)) +
        (∏ l ∈ (Finset.univ : Finset (Fin n)).erase i, p l) * e i * (δ v i * δ v i)) =
      2 * η ^ 2 * (w i) ^ 2 * d i * highResponseVarianceTerm a V η g w φ c y i := by
    rw [covarianceAction_add, covarianceAction_sum]
    have hcross (l : Fin n) (hl : l ∈ (Finset.univ : Finset (Fin n)).erase i) :
        covarianceAction C A (fun v =>
          (∏ k ∈ ((Finset.univ : Finset (Fin n)).erase i).erase l, p k) * m l * m i *
            (δ v l * δ v i)) = 0 := by
      rw [covarianceAction_mul, covariance_direction_product C η A hC hA w φ c l i,
        hdiag l i, ite_eq_right (Finset.ne_of_mem_erase hl), mul_zero, mul_zero]
    rw [Finset.sum_eq_zero (fun l hl => hcross l hl), zero_add, covarianceAction_mul,
      covariance_direction_product C η A hC hA w φ c i i, hdiag i i, ite_eq_left rfl]
    dsimp [e, highResponseVarianceTerm]
    rw [ternary_heat_identity]
    dsimp [p, f]
    ring
  simp_rw [he]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem high_response_matrix_all_count_bound  (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ / 2) (A : ι → ι → ℝ) (g w : Fin n → ℝ)
    (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2)
    (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    |responseMatrixAction q C A c (fun c => highResponseProduct a V η g w φ c y)| ≤
      (2 * C ^ 2 * ∑ k, ∑ l, |A k l|) *
        ((∑ j : Fin (2 * q + 2), |responseWeight q j|) *
          (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2) * n ^ 2 * η ^ 2)) := by
  apply covarianceAction_abs_le
  intro k l s t
  let v := covarianceAtom C k l s t
  have hv  := covarianceAtom_mem_ball C hC k l s t
  let f := coefficientRegression η g w φ c
  let δ := coefficientDirection η w φ c v
  have hr (z : ℝ) : coefficientRegression η g w φ (coefficientReset c v z) =
      fun i => f i + z * δ i := coefficientRegression_reset η g w φ c v z
  have hδ (i : Fin n) : |δ i| ≤ 2 * η := by
    have hprof : |∑ k, φ i k * (v k - c k)| ≤ 2 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact (abs_sub _ _).trans (by linarith [hφ v hv i, hφ c hc i])
    change |η * w i * (∑ k, φ i k * (v k - c k))| ≤ 2 * η
    rw [abs_mul]
    exact (mul_le_mul (by rw [abs_mul, abs_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)) hprof (abs_nonneg _) hη).trans_eq (by ring)
  have hf (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |f i + z * δ i| ≤ ρ := by
    have hi := congrFun (hr z) i
    rw [← hi]
    have hball := coefficientReset_mem_ball C c v z hz hc hv
    have hprof := hφ _ hball i
    have hpterm : |η * w i * (∑ k, φ i k * coefficientReset c v z k)| ≤ η := by
      rw [abs_mul]
      exact (mul_le_mul (by rw [abs_mul, abs_of_nonneg hη]; exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one η)) hprof (abs_nonneg _) hη).trans_eq (mul_one η)
    exact (abs_add_le _ _).trans (by linarith [hg i, hpterm])
  have he : (∑ j : Fin (2 * q + 2), responseWeight q j *
      highResponseProduct a V η g w φ (coefficientReset c v (responseNode q j)) y) =
      ∑ j : Fin (2 * q + 2), responseWeight q j *
        ∏ i, ternaryMass a (f i + responseNode q j * δ i) V (y i) := by
    simp only [highResponseProduct, hr]
  rw [he]
  have hp  := fun z hz i u => hp _ (hf z hz i) u
  let H : Fin n → ℝ → ℝ := fun i z => ternaryMass a (f i + z * δ i) V (y i)
  let D : Fin n → ℝ → ℝ := fun i z => δ i * ternaryMeanDerivative a (f i + z * δ i) (y i)
  let E : Fin n → ℝ → ℝ := fun i _ => (δ i) ^ 2 * ternaryMeanSecondDerivative a (y i)
  let A := (2 * ρ + a) / a ^ 2
  let S := 2 / a ^ 2
  have : 0 ≤ A := by dsimp [A]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hH (i : Fin n) (z : ℝ) : HasDerivAt (H i) (D i z) z := by
    have h := (ternary_hasDerivAt_mean a (f i + z * δ i) V (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))
    exact h.congr_deriv (by dsimp [D]; ring)
  have hD (i : Fin n) (z : ℝ) : HasDerivAt (D i) (E i z) z := by
    have h := ((ternary_hasDerivAt_mean_derivative a (f i + z * δ i) (y i)).comp z
      (((hasDerivAt_id z).mul_const (δ i)).const_add (f i))).const_mul (δ i)
    exact h.congr_deriv (by dsimp [E]; ring)
  have hHbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |H i z| ≤ 1 := by
    rw [abs_of_nonneg (hp z hz i (y i))]
    exact ternary_mass_le_one a _ V ha.ne' (hp z hz i) (y i)
  have hDbound (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : Fin n) : |D i z| ≤ 2 * η * A := by
    rw [abs_mul]
    exact mul_le_mul (hδ i) (ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf z hz i) (y i))
      (abs_nonneg _) (by positivity)
  have hEbound (z : ℝ) (i : Fin n) : |E i z| ≤ 4 * η ^ 2 * S := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have h := mul_le_mul (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hδ i) 2) (ternary_mean_second_derivative_abs_bound a ha (y i))
      (abs_nonneg _) (by positivity : 0 ≤ (2 * η) ^ 2)
    simpa only [S] using h.trans_eq (by ring)
  apply response_scalar_action_abs_bound q _ (finiteProductFirst Finset.univ H D)
    (finiteProductSecond Finset.univ H D E) _ (by positivity)
    (fun z hz => finite_product_hasDerivAt Finset.univ H D z (fun i _ => hH i z))
    (fun z hz => finite_product_first_hasDerivAt Finset.univ H D E z
      (fun i _ => hH i z) (fun i _ => hD i z)) _ (responseNode_mem_unit q)
  intro z hz
  have h := finite_product_second_abs_bound Finset.univ H D E z (2 * η * A) (4 * η ^ 2 * S)
    (by positivity) (by positivity) (fun i _ => hHbound z hz i)
    (fun i _ => hDbound z hz i) (fun i _ => hEbound z i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  apply h.trans
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnn : 0 ≤ (n : ℝ) ^ 2 - n := by nlinarith
  have := mul_nonneg hnn (mul_nonneg (sq_nonneg η) hS)
  nlinarith
end Covariance
end NearlyMinimax
