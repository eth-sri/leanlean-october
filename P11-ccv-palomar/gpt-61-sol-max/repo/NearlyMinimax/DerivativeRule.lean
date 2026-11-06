module

public import NearlyMinimax.Chebyshev

@[expose] public section

/-! The odd Chebyshev–Lobatto derivative rule from the finite moment lemma. -/
noncomputable section
namespace NearlyMinimax
open Polynomial Finset

/-- The odd-order Chebyshev derivative-rule weights. -/
def lobattoDerivativeWeight m i  :=
  (Lagrange.basis Finset.univ (lobattoNode (2 * m + 1)) i).derivative.eval 0

theorem lobattoNode_reflection n (hn : 1 ≤ n) i :
    lobattoNode n i.rev = -lobattoNode n i := by
  
  have hi : i.val ≤ n := by omega
  have hangle : ((i.rev.val : ℝ) * Real.pi / n) =
      Real.pi - (i.val : ℝ) * Real.pi / n := by
    simp only [Fin.val_rev]
    rw [show n + 1 - (i.val + 1) = n - i.val by omega, Nat.cast_sub hi]
    
    field_simp
  unfold lobattoNode
  rw [hangle, Real.cos_pi_sub]

theorem odd_lobattoNode_ne_zero m i :
    lobattoNode (2 * m + 1) i ≠ 0 := by
  intro hz
  have hrev := lobattoNode_reflection (2 * m + 1) (by omega) i
  have hi : i.rev = i := (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective (by rw [hrev, hz]; simp)
  grind

private theorem odd_lobatto_nodal_even m :
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

private theorem odd_lobatto_nodal_derivative_zero m :
    (Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).derivative.eval 0 = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) (odd_lobatto_nodal_even m)
  simp only [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_X, neg_zero] at h
  linarith

/-- Interpolation proves derivative exactness through odd order `2m+1`. -/
theorem lobatto_derivative_rule_exact (m : ℕ) (P : ℝ[X]) (hP : P.degree ≤ 2 * m + 1) :
    (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight m i * P.eval (lobattoNode (2 * m + 1) i)) =
      P.derivative.eval 0 := by
  apply cardinal_derivative_exact Finset.univ (lobattoNode (2 * m + 1))
    (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective.injOn
  simpa using hP.trans_lt (show (2 * m + 1 : WithBot ℕ) < ((2 * m + 1) + 1 : ℕ) by
    exact_mod_cast Nat.lt_succ_self (2 * m + 1))

section
variable {ι : Type*} [DecidableEq ι] (S : Finset ι) (z : ι → ℝ) (i : ι) (hi : i ∈ S)
include hi

private theorem cardinal_mul_node_factor  :
    Lagrange.basis S z i * (X - C (z i)) =
      C (Lagrange.nodalWeight S z i) * Lagrange.nodal S z := by
  have hb : Lagrange.basis S z i = C (Lagrange.nodalWeight S z i) *
      Lagrange.nodal (S.erase i) z := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
      ← Lagrange.nodal_erase_eq_nodal_div hi]
  rw [hb, Lagrange.nodal_eq_mul_nodal_erase hi]
  ring

private theorem cardinal_derivative_zero_formula  (hzi : z i ≠ 0)
    (hW : (Lagrange.nodal S z).derivative.eval 0 = 0) :
    (Lagrange.basis S z i).derivative.eval 0 =
      -(Lagrange.nodal S z).eval 0 * Lagrange.nodalWeight S z i / (z i) ^ 2 := by
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0)
    (cardinal_mul_node_factor S z i hi)
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, zero_sub, sub_zero,
    eval_one, mul_one, eval_zero, zero_mul, zero_add, hW, mul_zero] at h
  have he := Lagrange.eval_basis_not_at_node (v := z) (x := 0) hi (Ne.symm hzi)
  grind
end


private theorem decreasing_nodalWeight_sign n z
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
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hlt) hji.symm
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
  
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf

private theorem lobattoDerivativeWeight_factorization m i :
    lobattoDerivativeWeight m i =
      -(Lagrange.nodal Finset.univ (lobattoNode (2 * m + 1))).eval 0 * (-1) ^ i.val *
        (|Lagrange.nodalWeight Finset.univ (lobattoNode (2 * m + 1)) i| /
          lobattoNode (2 * m + 1) i ^ 2) := by
  rw [lobattoDerivativeWeight, cardinal_derivative_zero_formula Finset.univ
    (lobattoNode (2 * m + 1)) i (Finset.mem_univ i) (odd_lobattoNode_ne_zero m i)
    (odd_lobatto_nodal_derivative_zero m)]
  nth_rw 1 [decreasing_nodalWeight_sign (2 * m + 1) (lobattoNode (2 * m + 1))
    (lobattoNode_strictAnti (2 * m + 1) (by omega)) i]
  ring

private theorem chebyshev_at_lobatto (n : ℕ) (hn : 1 ≤ n) i :
    (Polynomial.Chebyshev.T ℝ n).eval (lobattoNode n i) = (-1) ^ i.val := by
  have h := intervalChebyshev_at_node (-1) 1 (by norm_num) n hn i
  norm_num [intervalChebyshev, exteriorNode] at h
  exact h

section
variable (m : ℕ)

private theorem chebyshev_odd_derivative_abs  :
    |(Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ))).derivative.eval 0| = (2 * m + 1 : ℕ) := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [eval_mul, eval_intCast, eval_natCast, Int.cast_natCast]
  have he : ((2 * m + 1 : ℕ) : ℤ) - 1 = 2 * (m : ℤ) := by omega
  rw [he, Polynomial.Chebyshev.U_eval_two_mul_zero, abs_mul]
  have hs : |((m : ℤ).negOnePow : ℝ)| = 1 := by
    exact_mod_cast Int.abs_negOnePow (m : ℤ)
  grind

/-- Exact total atom variation of the odd Chebyshev derivative rule. -/
theorem lobatto_derivative_rule_variation  :
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
    simp_all
  have heval (i : Fin ((2 * m + 1) + 1)) :
      lobattoDerivativeWeight m i *
        (Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ) : ℤ)).eval (lobattoNode (2 * m + 1) i) = c * r i := by
    rw [chebyshev_at_lobatto (2 * m + 1) (by omega) i, hw]
    have hs : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm i.val 2, pow_mul]
      norm_num
    grind
  have hexact := lobatto_derivative_rule_exact m
    (Polynomial.Chebyshev.T ℝ ((2 * m + 1 : ℕ) : ℤ))
    (Polynomial.degree_le_of_natDegree_le (chebyshev_natDegree_le (2 * m + 1)))
  simp_rw [heval] at hexact
  rw [← Finset.mul_sum] at hexact
  calc
    (∑ i : Fin ((2 * m + 1) + 1), |lobattoDerivativeWeight m i|) =
        |c| * ∑ i, r i := by simp_rw [habs]; rw [Finset.mul_sum]
    _ = |c * ∑ i, r i| := by
      rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg (fun i hi => hr i))]
    _ = _ := by rw [hexact, chebyshev_odd_derivative_abs]

/-- Reflection pairs opposite derivative weights; consequently their absolute weights are symmetric. -/
theorem lobattoDerivativeWeight_reflection  i :
    lobattoDerivativeWeight m i.rev = -lobattoDerivativeWeight m i := by
  let n := 2 * m + 1
  let z := lobattoNode n
  have hn : 1 ≤ n := by skip; omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
    (lobattoNode_strictAnti n hn).injective.injOn
  have hpoly : (Lagrange.basis Finset.univ z i.rev).comp (-X) =
      Lagrange.basis Finset.univ z i := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
    · have hnat : ((Lagrange.basis Finset.univ z i.rev).comp (-X)).natDegree ≤ n := by
        apply Polynomial.natDegree_comp_le.trans
        simp_all
      apply (Polynomial.degree_le_of_natDegree_le hnat).trans_lt
      simpa using (show (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) by
        exact_mod_cast Nat.lt_succ_self n)
    · rw [Lagrange.degree_basis hv (Finset.mem_univ i)]
      simpa using (show (n : WithBot ℕ) < ((n + 1 : ℕ) : WithBot ℕ) by
        exact_mod_cast Nat.lt_succ_self n)
    · intro j hj
      rw [eval_comp, eval_neg, eval_X]
      rw [← lobattoNode_reflection n hn j]
      by_cases hij : i = j
      · measurability
      measurability
  have h := congrArg (fun p : ℝ[X] => p.derivative.eval 0) hpoly
  simp only [derivative_comp, derivative_neg, derivative_X, eval_mul, eval_neg,
    eval_one, eval_comp, eval_X, neg_zero, neg_one_mul] at h
  change -lobattoDerivativeWeight m i.rev = lobattoDerivativeWeight m i at h
  linarith

/-- Symmetric total variation of the finite derivative rule. -/
theorem lobattoDerivativeWeight_abs_reflection  i :
    |lobattoDerivativeWeight m i.rev| = |lobattoDerivativeWeight m i| := by
  rw [lobattoDerivativeWeight_reflection, abs_neg]

/-- Even nodal parity extends derivative exactness by one degree beyond ordinary interpolation. -/
theorem lobatto_derivative_rule_exact_extra  (P : ℝ[X])
    (hP : P.degree ≤ (2 * m + 1) + 1) :
    (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight m i * P.eval (lobattoNode (2 * m + 1) i)) =
      P.derivative.eval 0 := by
  let n := 2 * m + 1
  let z := lobattoNode n
  have hn : 1 ≤ n := by skip; omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
    (lobattoNode_strictAnti n hn).injective.injOn
  by_cases hp : P.degree < (n + 1 : ℕ)
  · exact cardinal_derivative_exact Finset.univ z hv P (by simpa using hp) 0
  have hdeg : P.degree = (n + 1 : ℕ) := le_antisymm hP (le_of_not_gt hp)
  have hp0 : P ≠ 0 := by
    bound
  
  let W := Lagrange.nodal Finset.univ z
  let Q := P - C P.leadingCoeff * W
  have hCW : (C P.leadingCoeff * W).degree = P.degree := by
    measurability
  have hCL : P.leadingCoeff = (C P.leadingCoeff * W).leadingCoeff := by
    simp [leadingCoeff_mul, W, (Lagrange.nodal_monic (s := Finset.univ) (v := z)).leadingCoeff]
  have hQ : Q.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    have h := Polynomial.degree_sub_lt hCW.symm hp0 hCL
    simpa only [Q, hdeg, Finset.card_univ, Fintype.card_fin] using h
  have he (i : Fin (n + 1)) : Q.eval (z i) = P.eval (z i) := by
    simp [Q, W, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
  have hder : Q.derivative.eval 0 = P.derivative.eval 0 := by
    simp only [Q, derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C]
    
    rw [odd_lobatto_nodal_derivative_zero, mul_zero, sub_zero]
  have hexact := cardinal_derivative_exact Finset.univ z hv Q hQ 0
  simp_rw [he, hder] at hexact
  exact hexact
end


/-- The largest odd order at most `D`, used in the paper's derivative rule. -/
def derivativeOrder D  := 2 * ((D - 1) / 2) + 1

section
variable (D : ℕ) (hD : 1 ≤ D)
include hD

theorem derivativeOrder_bounds  :
    derivativeOrder D ≤ D ∧ D ≤ derivativeOrder D + 1 := by
  
  
  dsimp [derivativeOrder]
  omega

/-- The rule differentiates every polynomial through the requested order `D` exactly. -/
theorem derivative_rule_exact  (P : ℝ[X]) (hP : P.degree ≤ D) :
    (∑ i : Fin (derivativeOrder D + 1),
      lobattoDerivativeWeight ((D - 1) / 2) i * P.eval (lobattoNode (derivativeOrder D) i)) =
      P.derivative.eval 0 := by
  apply lobatto_derivative_rule_exact_extra
  exact hP.trans (by exact_mod_cast (derivativeOrder_bounds D hD).2)

/-- Its variation is the largest odd integer below `D`, hence at most `D`. -/
theorem derivative_rule_variation  :
    (∑ i : Fin (derivativeOrder D + 1), |lobattoDerivativeWeight ((D - 1) / 2) i|) =
      derivativeOrder D ∧ (derivativeOrder D : ℝ) ≤ D := by
  constructor
  · exact lobatto_derivative_rule_variation ((D - 1) / 2)
  · exact_mod_cast (derivativeOrder_bounds D hD).1
end


end NearlyMinimax
