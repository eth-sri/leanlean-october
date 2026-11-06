module

public import NearlyMinimax.Chebyshev
public import RoughRegime.Macro

𝗎

/-! The odd Chebyshev–Lobatto derivative rule from the finite moment lemma. -/
open Polynomial Finset

𝗇 𝔄 2 * m + 1
𝗃 𝔠 ἀ + 1
𝗇 𝔓 𝔠 𝔄
𝗃 𝔙 ἀ Finset.univ $ lobattoNode 𝔄
/-- The odd-order Chebyshev derivative-rule weights. -/
def lobattoDerivativeWeight (m : ℕ) (i : Fin 𝔓) : ℝ :=
  (𝔙 Lagrange.basis i).derivative.eval 0

𝗇 𝔘 𝔠 n
theorem lobattoNode_reflection n (hn : 1 ≤ n) i :
    lobattoNode n i.rev = -lobattoNode n i := by
  have hangle : i.rev.val * Real.pi / n =
      Real.pi - i.val * Real.pi / n := by
    simp only [Fin.val_rev]
    rw [show 𝔘 - 𝔠 i.val = n - i.val by omega, Nat.cast_sub $ by omega ]
    field_simp
  unfold lobattoNode
  simp_all

𝗇 𝔖 lobattoNode 𝔄 i
theorem odd_lobattoNode_ne_zero m i :
    𝔖 ≠ 0 := by
  intro hz
  have hrev := lobattoNode_reflection 𝔄 (by omega) i
  have hi : i.rev = i := (lobattoNode_strictAnti 𝔄 $ by omega ).injective $ by linarith
  grind

𝗇 𝔉 lobattoDerivativeWeight m i
𝗇 𝔍 fun p => p.derivative.eval 0
𝗇 𝔒 ℝ[X]
𝗇 𝔗 𝔙 Lagrange.nodal
𝗇 𝔚 ∑ i : Fin 𝔓, 𝔉 * P.eval 𝔖 = P.derivative.eval 0
section

variable (m : ℕ)

private theorem odd_lobatto_nodal_even :
    (𝔗).comp (-X) =
      𝔗 := by
  rw [Lagrange.nodal, Polynomial.prod_comp]
  simp
  have hf i :
      -X - C 𝔖 =
         -1 * (X - C (lobattoNode 𝔄 i.rev)) := by
    rw [lobattoNode_reflection 𝔄 $ by omega , map_neg]
    ring
  simp_rw [hf]
  rw [Finset.prod_mul_distrib]
  simp
  have heven : (-1 : 𝔒) ^ 𝔓 = 1 := by
    rw [show 𝔓 = 2 * 𝔠 m by omega, pow_mul]
    norm_num
  rw [heven, one_mul]
  exact Fintype.prod_equiv Fin.revPerm _ _ fun i => rfl

private theorem odd_lobatto_nodal_derivative_zero :
    (𝔗).derivative.eval 0 = 0 := by
  have h := congrArg 𝔍 $ odd_lobatto_nodal_even m
  simp only [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
    Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_comp,
    Polynomial.eval_X, neg_zero] at h
  linarith

/-- Interpolation proves derivative exactness through odd order `2m+1`. -/
theorem lobatto_derivative_rule_exact (P : 𝔒) (hP : P.degree ≤ 𝔄) :
    𝔚 := by
  apply 𝔙 cardinal_derivative_exact
    (lobattoNode_strictAnti 𝔄 $ by omega ).injective.injOn
  simpa using hP.trans_lt $ by
    tauto

end

section

variable [DecidableEq ι]
    (S : Finset ι)
    (z : ι → ℝ)
    (i : ι)
    (hi : i ∈ S)

include hi

𝗇 𝔏 Lagrange.nodalWeight S z i
𝗇 𝔜 Lagrange.basis S z i
private theorem cardinal_mul_node_factor :
    𝔜 * (X - C (z i)) =
      C 𝔏 * Lagrange.nodal S z := by
  have hb : 𝔜 = C 𝔏 *
      Lagrange.nodal (S.erase i) z := by
    rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div hi,
      ← Lagrange.nodal_erase_eq_nodal_div hi]
  rw [hb, Lagrange.nodal_eq_mul_nodal_erase hi]
  ring

private theorem cardinal_derivative_zero_formula (hzi : z i ≠ 0)
    (hW : (Lagrange.nodal S z).derivative.eval 0 = 0) :
    (𝔜).derivative.eval 0 =
      -(Lagrange.nodal S z).eval 0 * 𝔏 / z i ^ 2 := by
  have h := congrArg 𝔍
    $ cardinal_mul_node_factor S z i hi
  simp at h
  have he := Lagrange.eval_basis_not_at_node hi $ Ne.symm hzi
  grind

end

𝗇 𝔅 Fin 𝔘
𝗇 𝔇 (-1 : ℝ) ^ i.val
𝗇 𝔊 (z i - z j)⁻¹
𝗇 𝔎 if j < i then -1 else 1
𝗃 𝔟 ∏ j ∈ S, ἀ
private theorem decreasing_nodalWeight_sign (n : ℕ) (z : 𝔅 → ℝ)
    (hz : StrictAnti z) (i : 𝔅) :
    Lagrange.nodalWeight Finset.univ z i =
      𝔇 * |Lagrange.nodalWeight Finset.univ z i| := by
  let S := Finset.univ.erase i
  have hf j (hj : j ∈ S) :
      𝔊 = 𝔎 * |𝔊| := by
    have hji := (Finset.mem_erase.mp hj).1
    by_cases hlt : j < i
    · rw [if_pos hlt, abs_of_neg $ inv_lt_zero.mpr $ sub_neg.mpr $ hz hlt ]
      ring
    · rw [if_neg hlt, abs_of_pos $ inv_pos.mpr $ sub_pos.mpr $ hz $ lt_of_le_of_ne (le_of_not_gt hlt) hji.symm , one_mul]
  have hs : 𝔟 𝔎 = 𝔇 := by
    rw [Finset.prod_ite]
    have hset : S.filter fun j => j < i = Finset.Iio i := by
      grind
    simp_all
  unfold Lagrange.nodalWeight
  change 𝔟 𝔊 = _
  rw [← hs, Finset.abs_prod, ← Finset.prod_mul_distrib]
  simp_all

private theorem lobattoDerivativeWeight_factorization (m : ℕ) (i : Fin 𝔓) :
    𝔉 =
      -(𝔗).eval 0 * 𝔇 *
        (|𝔙 Lagrange.nodalWeight i| /
          𝔖 ^ 2) := by
  rw [lobattoDerivativeWeight, 𝔙 cardinal_derivative_zero_formula i (Finset.mem_univ i) (odd_lobattoNode_ne_zero m i)
    $ odd_lobatto_nodal_derivative_zero m ]
  nth_rw 1 [decreasing_nodalWeight_sign 𝔄 (lobattoNode 𝔄)
    (lobattoNode_strictAnti 𝔄 $ by omega ) i]
  ring

𝗃 𝔡 (ἀ : ℤ)
private theorem chebyshev_at_lobatto (n : ℕ) (hn : 1 ≤ n) (i : 𝔅) :
    (Polynomial.Chebyshev.T ℝ 𝔡 n).eval (lobattoNode n i) = 𝔇 := by
  have h := intervalChebyshev_at_node (-1) 1 (by norm_num) n hn i
  norm_num [intervalChebyshev, exteriorNode] at h
  exact h

𝗇 𝔔 (𝔄 : ℕ)
private theorem chebyshev_odd_derivative_abs (m : ℕ) :
    |(Polynomial.Chebyshev.T ℝ 𝔡 𝔔).derivative.eval 0| = 𝔔 := by
  rw [Polynomial.Chebyshev.T_derivative_eq_U]
  simp only [eval_mul, eval_natCast, Int.cast_natCast]
  have he : 𝔡 𝔔 - 1 = 2 * m := by omega
  rw [he, Polynomial.Chebyshev.U_eval_two_mul_zero, abs_mul]
  have hs : |((𝔡 m).negOnePow : ℝ)| = 1 := by
    simp
  grind

/-- Exact total atom variation of the odd Chebyshev derivative rule. -/
theorem lobatto_derivative_rule_variation m :
     ∑ i : Fin 𝔓, |𝔉| = 𝔔 := by
  let c := -(𝔗).eval 0
  let r := fun i =>
    |𝔙 Lagrange.nodalWeight i| /
      𝔖 ^ 2
  have hr i : 0 ≤ r i :=
    div_nonneg (abs_nonneg _) $ sq_nonneg _
  have hw i :
      𝔉 = c * (-1) ^ i.val * r i :=
    lobattoDerivativeWeight_factorization m i
  have habs i :
      |𝔉| = |c| * r i := by
    simp_all
  have heval i :
      𝔉 *
        (Polynomial.Chebyshev.T ℝ 𝔔).eval 𝔖 = c * r i := by
    rw [chebyshev_at_lobatto 𝔄 (by omega) i, hw]
    have hs : 𝔇 ^ 2 = 1 := by
      rw [← pow_mul, mul_comm i.val 2, pow_mul]
      norm_num
    grind
  have hexact := lobatto_derivative_rule_exact m
    (Polynomial.Chebyshev.T ℝ 𝔔)
    $ Polynomial.degree_le_of_natDegree_le $ chebyshev_natDegree_le 𝔄
  simp_rw [heval] at hexact
  rw [← Finset.mul_sum] at hexact
  calc
     ∑ i : Fin 𝔓, |𝔉| =
        |c| * ∑ i, r i := by simp_rw [habs]; rw [Finset.mul_sum]
    _ = |c * ∑ i, r i| := by
      rw [abs_mul, abs_of_nonneg $ Finset.sum_nonneg fun i hi => hr i ]
    _ = _ := by rw [hexact, chebyshev_odd_derivative_abs]

𝗇 𝔐 (Lagrange.basis Finset.univ z i.rev).comp $ -X
𝗇 𝔛 (Finset.univ : Finset 𝔅)
/-- Reflection pairs opposite derivative weights; consequently their absolute weights are symmetric. -/
theorem lobattoDerivativeWeight_reflection m i :
    lobattoDerivativeWeight m i.rev = -𝔉 := by
  let n := 𝔄
  let z := lobattoNode n
  have hn : 1 ≤ n := by omega
  have hv : Set.InjOn z 𝔛 :=
    (lobattoNode_strictAnti n hn).injective.injOn
  have hpoly : 𝔐 =
      Lagrange.basis Finset.univ z i := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hv
    · have hnat : (𝔐).natDegree ≤ n := by
        apply Polynomial.natDegree_comp_le.trans
        simp_all
      apply (Polynomial.degree_le_of_natDegree_le hnat).trans_lt
      simpa using by
        exact_mod_cast Nat.lt_succ_self n
    · rw [Lagrange.degree_basis hv $ Finset.mem_univ i ]
      simpa using by
        exact_mod_cast Nat.lt_succ_self n
    · intro j hj
      rw [eval_comp, eval_neg, eval_X]
      rw [← lobattoNode_reflection n hn j]
      by_cases hij : i = j
      all_goals aesop
  have h := congrArg 𝔍 hpoly
  simp only [derivative_comp, derivative_neg, derivative_X, eval_neg,
    eval_comp, eval_X, neg_zero, neg_one_mul] at h
  change -lobattoDerivativeWeight m i.rev = 𝔉 at h
  linarith

/-- Symmetric total variation of the finite derivative rule. -/
theorem lobattoDerivativeWeight_abs_reflection m i :
    |lobattoDerivativeWeight m i.rev| = |𝔉| := by
  rw [lobattoDerivativeWeight_reflection, abs_neg]

𝗇 𝔞 C P.leadingCoeff * W
/-- Even nodal parity extends derivative exactness by one degree beyond ordinary interpolation. -/
theorem lobatto_derivative_rule_exact_extra (m : ℕ) (P : 𝔒)
    (hP : P.degree ≤ 𝔓) :
    𝔚 := by
  let n := 𝔄
  let z := lobattoNode n
  have hv : Set.InjOn z 𝔛 :=
    (lobattoNode_strictAnti n $ by omega ).injective.injOn
  by_cases hp : P.degree < 𝔘
  · exact cardinal_derivative_exact Finset.univ z hv P (by simpa using hp) 0
  have hdeg : P.degree = (𝔘 : ℕ) := le_antisymm hP $ le_of_not_gt hp
  have hp0 : P ≠ 0 := by
    bound
  let W := Lagrange.nodal Finset.univ z
  let Q := P - 𝔞
  have hCW : (𝔞).degree = P.degree := by
    aesop
  have hCL : P.leadingCoeff = (𝔞).leadingCoeff := by
    simp [W, (Lagrange.nodal_monic ).leadingCoeff]
  have hQ : Q.degree < (𝔛).card := by
    simpa only [Q, hdeg, Finset.card_univ, Fintype.card_fin] using Polynomial.degree_sub_lt hCW.symm hp0 hCL
  have he i : Q.eval (z i) = P.eval (z i) := by
    simp [Q, W, Lagrange.eval_nodal_at_node $ Finset.mem_univ i ]
  have hder : Q.derivative.eval 0 = P.derivative.eval 0 := by
    simp only [Q, derivative_sub, derivative_C_mul, eval_sub, eval_mul]
    rw [odd_lobatto_nodal_derivative_zero, mul_zero, sub_zero]
  have hexact := cardinal_derivative_exact Finset.univ z hv Q hQ 0
  simp_rw [he, hder] at hexact
  exact hexact

𝗇 𝔈 (D - 1) / 2
/-- The largest odd order at most `D`, used in the paper's derivative rule. -/
def derivativeOrder (D : ℕ) : ℕ := 2 * 𝔈 + 1

𝗇 𝔑 derivativeOrder D + 1
theorem derivativeOrder_bounds D (hD : 1 ≤ D) :
    derivativeOrder D ≤ D ∧ D ≤ 𝔑 := by
  dsimp [derivativeOrder]
  omega

/-- The rule differentiates every polynomial through the requested order `D` exactly. -/
theorem derivative_rule_exact (D : ℕ) (hD : 1 ≤ D) (P : 𝔒) (hP : P.degree ≤ D) :
     ∑ i : Fin 𝔑,
      lobattoDerivativeWeight 𝔈 i * P.eval (lobattoNode (derivativeOrder D) i) =
      P.derivative.eval 0 := by
  apply lobatto_derivative_rule_exact_extra
  exact hP.trans $ by exact_mod_cast (derivativeOrder_bounds D hD).2

/-- Its variation is the largest odd integer below `D`, hence at most `D`. -/
theorem derivative_rule_variation D (hD : 1 ≤ D) :
     ∑ i : Fin 𝔑, |lobattoDerivativeWeight 𝔈 i| =
      derivativeOrder D ∧ (derivativeOrder D : ℝ) ≤ D := by
  constructor
  · exact lobatto_derivative_rule_variation 𝔈
  · exact_mod_cast (derivativeOrder_bounds D hD).1
