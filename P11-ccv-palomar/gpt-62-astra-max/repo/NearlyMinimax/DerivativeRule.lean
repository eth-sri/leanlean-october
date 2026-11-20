module

public import NearlyMinimax.Chebyshev

@[expose] public section

/-! The odd Chebyshev–Lobatto derivative rule from the finite moment lemma. -/
noncomputable section
namespace NearlyMinimax
open Polynomial Finset

section
variable {m : ℕ} (i : Fin ((2 * m + 1) + 1))

/-- The odd-order Chebyshev derivative-rule weights. -/
def lobattoDerivativeWeight : ℝ :=
  (Lagrange.basis Finset.univ lobattoNode i).derivative.eval 0

theorem lobattoNode_reflection {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    lobattoNode i.rev = -lobattoNode i := by
  have hangle : (i.rev.val * Real.pi / n) =
      Real.pi - i.val * Real.pi / n := by
    simp only [Fin.val_rev]
    rw [show n + 1 - (i.val + 1) = n - i.val by omega, Nat.cast_sub (by omega)]
    push_cast
    field_simp
  simp_all [lobattoNode]

theorem odd_lobattoNode_ne_zero :
    lobattoNode i ≠ 0 := by
  intro hz
  have hrev := lobattoNode_reflection (by omega) i
  have hi : i.rev = i := (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective (by simp_all)
  grind [congrArg Fin.val hi]

end

section
variable (m : ℕ) {ι : Type*}

private theorem odd_lobatto_nodal_even :
    (Lagrange.nodal Finset.univ (lobattoNode (n := (2 * m + 1)))).comp (-X) =
      Lagrange.nodal Finset.univ (lobattoNode (n := (2 * m + 1))) := by
  rw [Lagrange.nodal, Polynomial.prod_comp]
  simp
  have hf (i : Fin ((2 * m + 1) + 1)) :
      -X - C (lobattoNode i) =
        (-1) * (X - C (lobattoNode i.rev)) := by
    simp [lobattoNode_reflection] <;> ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp
  have heven : (-1 : ℝ[X]) ^ ((2 * m + 1) + 1) = 1 := by
    apply Even.neg_one_pow <;> grind
  rw [heven, one_mul]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => rfl)

private theorem odd_lobatto_nodal_derivative_zero :
    (Lagrange.nodal Finset.univ (lobattoNode (n := (2 * m + 1)))).derivative.eval 0 = 0 := by
  have h := congrArg (fun p => p.derivative.eval 0) (odd_lobatto_nodal_even m)
  simp [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_X, neg_zero] at h
  linarith

/-- Interpolation proves derivative exactness through odd order `2m+1`. -/
theorem lobatto_derivative_rule_exact {m : ℕ} {P : ℝ[X]} (hP : P.degree ≤ 2 * m + 1) :
    (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight i * P.eval (lobattoNode i)) =
      P.derivative.eval 0 := by
  apply cardinal_derivative_exact
    (lobattoNode_strictAnti (2 * m + 1) (by omega)).injective.injOn
  simpa using hP.trans_lt (show (2 * m + 1 : WithBot ℕ) < ((2 * m + 1) + 1) by
    norm_cast <;> omega)

private theorem cardinal_mul_node_factor [DecidableEq ι]
    {S : Finset ι} (z : ι → ℝ) {i : ι} (hi : i ∈ S) :
    Lagrange.basis S z i * (X - C (z i)) =
      C (Lagrange.nodalWeight S z i) * Lagrange.nodal S z := by
  have hb : Lagrange.basis S z i = C (Lagrange.nodalWeight S z i) *
      Lagrange.nodal (S.erase i) z := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
      ← Lagrange.nodal_erase_eq_nodal_div hi]
  rw [hb, Lagrange.nodal_eq_mul_nodal_erase hi]
  ring

private theorem cardinal_derivative_zero_formula [DecidableEq ι]
    {S : Finset ι} {z : ι → ℝ} {i : ι} (hi : i ∈ S) (hzi : z i ≠ 0)
    (hW : (Lagrange.nodal S z).derivative.eval 0 = 0) :
    (Lagrange.basis S z i).derivative.eval 0 =
      -(Lagrange.nodal S z).eval 0 * Lagrange.nodalWeight S z i / (z i) ^ 2 := by
  have h := congrArg (fun p => p.derivative.eval 0)
    (cardinal_mul_node_factor z hi)
  simp at h
  grind [Lagrange.eval_basis_not_at_node hi (Ne.symm hzi)]

private theorem decreasing_nodalWeight_sign {n : ℕ} {z : Fin (n + 1) → ℝ}
    (hz : StrictAnti z) (i : Fin (n + 1)) :
    Lagrange.nodalWeight Finset.univ z i =
      (-1) ^ i.val * |Lagrange.nodalWeight Finset.univ z i| := by
  let S := Finset.univ.erase i
  have hf j (hj : j ∈ S) :
      (z i - z j)⁻¹ = (if j < i then (-1) else 1) * |(z i - z j)⁻¹| := by
    by_cases hlt : j < i
    · rw [if_pos hlt, abs_of_neg (inv_lt_zero.mpr (sub_neg.mpr (hz hlt)))]
      ring
    · have hij  := lt_of_le_of_ne (le_of_not_gt hlt) ((Finset.mem_erase.mp hj).1).symm
      rw [if_neg hlt, abs_of_pos (by bound), one_mul]
  have hs : (∏ j ∈ S, if j < i then (-1) else 1) = (-1 : ℝ) ^ i.val := by
    rw [Finset.prod_ite]
    have hset : S.filter (fun j => j < i) = Finset.Iio i := by
      ext j
      aesop
    simp_all
  unfold Lagrange.nodalWeight
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl hf

private theorem lobattoDerivativeWeight_factorization {m : ℕ} (i : Fin ((2 * m + 1) + 1)) :
    lobattoDerivativeWeight i =
      -(Lagrange.nodal Finset.univ (lobattoNode (n := (2 * m + 1)))).eval 0 * (-1) ^ i.val *
        (|Lagrange.nodalWeight Finset.univ lobattoNode i| /
          lobattoNode i ^ 2) := by
  rw [lobattoDerivativeWeight, cardinal_derivative_zero_formula (Finset.mem_univ i) (odd_lobattoNode_ne_zero i)
    (odd_lobatto_nodal_derivative_zero m)]
  nth_rw 1 [decreasing_nodalWeight_sign
    (lobattoNode_strictAnti _ (by omega)) i]
  ring

private theorem chebyshev_at_lobatto {n : ℕ} (hn : 1 ≤ n) (i : Fin (n + 1)) :
    (Polynomial.Chebyshev.T ℝ n).eval (lobattoNode i) = (-1) ^ i.val := by
  have h := intervalChebyshev_at_node (-1) 1 (by norm_num) hn i
  norm_num [intervalChebyshev, exteriorNode] at h
  exact h

private theorem chebyshev_odd_derivative_abs :
    |(Polynomial.Chebyshev.T ℝ (2 * m + 1 : ℕ)).derivative.eval 0| = (2 * m + 1 : ℕ) := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  norm_num <;> linarith

/-- Exact total atom variation of the odd Chebyshev derivative rule. -/
theorem lobatto_derivative_rule_variation :
    (∑ i : Fin ((2 * m + 1) + 1), |lobattoDerivativeWeight i|) = (2 * m + 1 : ℕ) := by
  let c := -(Lagrange.nodal Finset.univ (lobattoNode (n := (2 * m + 1)))).eval 0
  let r := fun i : Fin ((2 * m + 1) + 1) =>
    |Lagrange.nodalWeight Finset.univ lobattoNode i| /
      lobattoNode i ^ 2
  have hr i : 0 ≤ r i :=
    by positivity
  have hw i :
      lobattoDerivativeWeight i = c * (-1) ^ i.val * r i :=
    lobattoDerivativeWeight_factorization i
  have habs i :
      |lobattoDerivativeWeight i| = |c| * r i := by
    simp_all
  have heval i :
      lobattoDerivativeWeight i *
        (Polynomial.Chebyshev.T ℝ (2 * m + 1 : ℕ)).eval (lobattoNode i) = c * r i := by
    rw [chebyshev_at_lobatto (by omega) i, hw]
    have hs : ((-1 : ℝ) ^ i.val) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm i.val 2, pow_mul]
      norm_num
    grind
  have hexact := lobatto_derivative_rule_exact
    (Polynomial.degree_le_of_natDegree_le (chebyshev_natDegree_le (2 * m + 1)))
  simp_rw [heval] at hexact
  rw [← Finset.mul_sum] at hexact
  calc
    _ =
        |c| * ∑ i, r i := by simp_rw [habs]; rw [Finset.mul_sum]
    _ = |c * ∑ i, r i| := by
      rw [abs_mul, abs_of_nonneg (Finset.sum_nonneg (fun i hi => hr i))]
    _ = _ := by rw [hexact, chebyshev_odd_derivative_abs]

/-- Reflection pairs opposite derivative weights; consequently their absolute weights are symmetric. -/
theorem lobattoDerivativeWeight_reflection (i : Fin ((2 * m + 1) + 1)) :
    lobattoDerivativeWeight i.rev = -lobattoDerivativeWeight i := by
  let n := 2 * m + 1
  let z := lobattoNode (n := n)
  have hn : 1 ≤ n := by omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
    (lobattoNode_strictAnti n hn).injective.injOn
  have hpoly : (Lagrange.basis Finset.univ z i.rev).comp (-X) =
      Lagrange.basis Finset.univ z i := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
    · have hnat : ((Lagrange.basis Finset.univ z i.rev).comp (-X)).natDegree ≤ n := by
        apply Polynomial.natDegree_comp_le.trans
        simp_all
      apply (Polynomial.degree_le_of_natDegree_le hnat).trans_lt
      simpa using (show n < ((n + 1) : WithBot ℕ) by
        exact_mod_cast Nat.lt_succ_self n)
    · rw [Lagrange.degree_basis hv (Finset.mem_univ i)]
      simpa using (show n < ((n + 1) : WithBot ℕ) by
        exact_mod_cast Nat.lt_succ_self n)
    · intro j hj
      rw [eval_comp, eval_neg, eval_X, ← lobattoNode_reflection hn j]
      by_cases hij : i = j <;> aesop
  have h := congrArg (fun p => p.derivative.eval 0) hpoly
  simp [derivative_comp, derivative_neg, derivative_X, eval_mul, eval_neg,
    eval_one, eval_comp, eval_X, neg_zero, neg_one_mul] at h
  apply neg_eq_iff_eq_neg.mp <;> assumption

/-- Symmetric total variation of the finite derivative rule. -/
theorem lobattoDerivativeWeight_abs_reflection (i : Fin ((2 * m + 1) + 1)) :
    |lobattoDerivativeWeight i.rev| = |lobattoDerivativeWeight i| := by
  rw [lobattoDerivativeWeight_reflection, abs_neg]

/-- Even nodal parity extends derivative exactness by one degree beyond ordinary interpolation. -/
theorem lobatto_derivative_rule_exact_extra (P : ℝ[X])
    (hP : P.degree ≤ (2 * m + 1) + 1) :
    (∑ i : Fin ((2 * m + 1) + 1), lobattoDerivativeWeight i * P.eval (lobattoNode i)) =
      P.derivative.eval 0 := by
  let n := 2 * m + 1
  let z := lobattoNode (n := n)
  have hn : 1 ≤ n := by omega
  have hv : Set.InjOn z (Finset.univ : Finset (Fin (n + 1))) :=
    (lobattoNode_strictAnti n hn).injective.injOn
  by_cases hp : P.degree < (n + 1)
  · exact cardinal_derivative_exact hv P (by simpa using hp) 0
  have hdeg : P.degree = (n + 1 : ℕ) := le_antisymm hP (le_of_not_gt hp)
  have hp0 : P ≠ 0 := by
    bound
  let W := Lagrange.nodal Finset.univ z
  let Q := P - C P.leadingCoeff * W
  have hCW : (C P.leadingCoeff * W).degree = P.degree := by
    rw [degree_C_mul (Polynomial.leadingCoeff_ne_zero.mpr hp0), hdeg]
    simp [W, Lagrange.degree_nodal]
  have hCL : P.leadingCoeff = (C P.leadingCoeff * W).leadingCoeff := by
    simp [leadingCoeff_mul, W, (Lagrange.nodal_monic).leadingCoeff]
  have hQ : Q.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simpa only [ hdeg, Finset.card_univ, Fintype.card_fin] using Polynomial.degree_sub_lt hCW.symm hp0 hCL
  have he i : Q.eval (z i) = P.eval (z i) := by
    simp [Q, W, Lagrange.eval_nodal_at_node (Finset.mem_univ i)]
  have hder : Q.derivative.eval 0 = P.derivative.eval 0 := by
    simp only [Q, derivative_sub, derivative_C_mul, eval_sub, eval_mul, eval_C]
    rw [odd_lobatto_nodal_derivative_zero, mul_zero, sub_zero]
  have hexact := cardinal_derivative_exact hv Q hQ 0
  simp_rw [he, hder] at hexact
  exact hexact

end

/-- The largest odd order at most `D`, used in the paper's derivative rule. -/
def derivativeOrder (D : ℕ) : ℕ := 2 * ((D - 1) / 2) + 1

variable {D : ℕ} (hD : 1 ≤ D)
include hD

theorem derivativeOrder_bounds :
    derivativeOrder D ≤ D ∧ D ≤ derivativeOrder D + 1 := by
  dsimp [derivativeOrder]
  omega

/-- The rule differentiates every polynomial through the requested order `D` exactly. -/
theorem derivative_rule_exact {P : ℝ[X]} (hP : P.degree ≤ D) :
    (∑ i : Fin (derivativeOrder D + 1),
      lobattoDerivativeWeight i * P.eval (lobattoNode i)) =
      P.derivative.eval 0 := by
  apply lobatto_derivative_rule_exact_extra
  exact hP.trans (by exact_mod_cast (derivativeOrder_bounds hD).2)

/-- Its variation is the largest odd integer below `D`, hence at most `D`. -/
theorem derivative_rule_variation :
    (∑ i : Fin (derivativeOrder D + 1), |lobattoDerivativeWeight i|) =
      derivativeOrder D ∧ (derivativeOrder D : ℝ) ≤ D := by
  constructor
  · apply lobatto_derivative_rule_variation
  · exact_mod_cast (derivativeOrder_bounds hD).1

end NearlyMinimax
