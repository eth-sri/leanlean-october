/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Algebra.Equations
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Algebra.Polynomial.BigOperators

/-! A homogeneous grid curve irreducible over every field by Eisenstein at infinity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Homogeneous line arrangements used in the grid construction. -/
def gridRows (K : Type*) [Field K] (k : ℕ) (j : Fin 3) : MvPolynomial (Fin 3) K :=
  ∏ i ∈ range k, (X j - C (i:K)*X 2)

def gridEquation (K : Type*) [Field K] (k : ℕ) := gridRows K (k+1) 0 + X 2 * gridRows K k 1

variable (K : Type*) [Field K] (k : ℕ)

lemma gridEquation_hom : (gridEquation K k).IsHomogeneous (k+1) := by
  have rows (k j) : (gridRows K k j).IsHomogeneous k := by
    simpa [gridRows] using IsHomogeneous.prod (range k) (fun i : ℕ => X j-C (i:K)*X 2) (fun _ => 1) (fun _ _ => (isHomogeneous_X K j).sub (isHomogeneous_C_mul_X _ _))
  exact (rows _ _).add (by simpa [add_comm] using (isHomogeneous_X K 2).mul (rows k 1))

/-- In the first variable the equation is monic, reduces to a pure power
modulo `Z`, and has constant term divisible by `Z` only once. -/
lemma gridEquation_irred : Irreducible (gridEquation K k) := by
  let A := MvPolynomial (Fin 2) K
  let Z : A := X 1
  let Y : A := X 0
  let Q := ∏ j ∈ range k, (Y-C (j:K)*Z)
  let s := range (k+1)
  let V : Polynomial A := ∏ i ∈ s, (Polynomial.X-Polynomial.C (C (i:K)*Z))
  let G := V+Polynomial.C (Z*Q)
  apply (MulEquiv.irreducible_iff (f:=finSuccEquiv K 2)).mp
  have he : finSuccEquiv K 2 (gridEquation K k) = G := by
    simp only [gridEquation,gridRows,map_add,map_mul,map_prod,map_sub,finSuccEquiv_X_zero,
      show (2:Fin 3)=(1:Fin 2).succ from rfl,show (1:Fin 3)=(0:Fin 2).succ from rfl, finSuccEquiv_X_succ]
    simp [G,V,s,Z,Q,Y,Polynomial.C_mul]
  rw [he]
  have hm : V.Monic := Polynomial.monic_prod_X_sub_C _ _
  have hd : V.natDegree = k+1 := (Polynomial.natDegree_finsetProd_X_sub_C_eq_card s _).trans (card_range _)
  have hlt : (Polynomial.C (Z*Q)).natDegree < V.natDegree := by rw [Polynomial.natDegree_C,hd]; omega
  have hG : G.Monic := hm.add_of_left (Polynomial.degree_lt_degree hlt)
  have hdeg : G.natDegree = k+1 := (Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt).trans hd
  let I := Ideal.span {Z}
  have hI : I.IsPrime := Ideal.isPrime_span_singleton_of_prime (X_prime ..)
  let ψ := Ideal.Quotient.mk I
  have hz : ψ Z = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hmap : G.map ψ = Polynomial.X^(k+1) := by simp [G,V,s,Polynomial.map_prod,hz]
  apply Polynomial.IsEisensteinAt.irreducible (𝓟:=I) _ hI hG.isPrimitive (by omega)
  refine ⟨hG.leadingCoeff_notMem hI.ne_top,?_,?_⟩
  · intro i hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [Polynomial.coeff_X_pow,ne_of_lt (hi.trans_eq hdeg)] using congrArg (Polynomial.coeff · i) hmap
  · have hc : G.coeff 0 = Z*Q := by
      rw [Polynomial.coeff_zero_eq_eval_zero]; simp only [G,V,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,zero_sub]
      rw [prod_eq_zero (mem_range.mpr (Nat.zero_lt_succ k)) (by simp),zero_add]
    intro h
    rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,hc,pow_two] at h
    obtain ⟨u,hu⟩ := (mul_dvd_mul_iff_left (X_ne_zero (1:Fin 2))).mp h
    have := congrArg (eval ![1,0]) hu
    simp [Q,Y,Z] at this

lemma gridEquation_map {L : Type*} [Field L] (φ : K →+* L) : map φ (gridEquation K k) = gridEquation L k := by simp [gridEquation,gridRows]

end
end CCDN
