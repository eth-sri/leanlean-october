/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

import Mathlib.Tactic

public import ArithmeticHeights.RowSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis

-- Used only inside proofs: the complement of a subspace and the basis it produces, the dual
-- basis, the dimension of an annihilator, and the two-sided inverse of a square matrix.
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection

/-!
# The duality theorem for the height of a subspace

A subspace and its annihilator have the same height. This is W. M. Schmidt's theorem: the Plücker
coordinates of the annihilator are those of the subspace read at the complementary index, up to a
sign at each index and one common nonzero factor, and every height in this development is
insensitive to exactly that much — a signed reindexing and a scalar.

## Main results

* `Submodule.mulHeight_comap_piEquiv_dualAnnihilator`, with its Arakelov and absolute companions
  `Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator` and
  `Submodule.absMulHeight_comap_piEquiv_dualAnnihilator` and every logarithmic form: **the duality
  theorem**, the height of `V` against the height of its annihilator, transported back to `ι → K`
  along the standard basis.
* `Matrix.mulHeight_ker_mulVecLin` and its five companions: **the height of a subspace is the
  height of any matrix cutting it out** (Bombieri–Gubler, Corollary 2.8.12) — the solution space of
  `A x = 0` and the row space of `A` have the same height. This is the form Layer 5 consumes.
* `Submodule.exists_plucker_eq_plucker_compl`: the coordinate statement behind both. A subspace and
  its annihilator have bases whose Plücker coordinates agree at complementary indices up to a sign
  and one common nonzero factor — Schmidt's involution `τ`.
* `Submodule.mem_comap_piEquiv_dualAnnihilator`: the transported annihilator is the orthogonal
  complement for the standard bilinear form, and
  `Submodule.eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero` is that reading as a
  way into the theorems above. `Submodule.comap_piEquiv_dualAnnihilator_eq_map` is the same
  subspace in the other spelling, the `map` along the inverse identification.
* `Height.mulHeight_eq_of_forall_eq_or_eq_neg` and its Arakelov and absolute companions: no height
  in this development sees a change of sign in a coordinate. These are statements about Mathlib's
  heights and belong upstream.

## Implementation notes

The annihilator lives in the dual space, so it is transported back to `ι → K` along
`Module.piEquiv ι K K`, whose value at `x` is the functional `v ↦ v ⬝ᵥ x`; the transported
annihilator is therefore the orthogonal complement of `V` for the standard bilinear form.
`Submodule.comap_piEquiv_dualAnnihilator_eq_map` turns the `comap` used here into the `map` along
the inverse equivalence, which is the other spelling in use.

⚠ The annihilator and not the orthogonal complement is what the *proof* must use, even though the
two are identified here. Over a field that is not formally real the two summands `V` and `V^⊥` can
meet — over `ℚ(i)`, the line spanned by `(1, i)` is its own orthogonal complement — so the matrix
whose rows are a basis of `V` stacked on a basis of `V^⊥` is singular, and every argument through
its determinant fails. The proof below is stated for a *complement* `W` of `V`, which always
exists, and reaches the annihilator through the dual basis.

The proof is elementary, and in particular uses neither a Laplace expansion along a block of rows
nor Jacobi's identity for the complementary minors of an inverse, neither of which Mathlib has.
Instead: let the rows of `C` be a basis of `ι → K` whose first block is a basis of `V`, and let the
rows of `D` be the dual basis read back in `ι → K`, so that `C * Dᵀ = 1`. For a set `s` of `k`
columns, multiply `C` by the matrix whose first `k` columns are the standard basis vectors at `s`
and whose remaining columns are the second block of `Dᵀ`. The product is block triangular with the
`s`-minor of the first block of `C` in one corner and an identity in the other, while the second
factor, read through the enumeration of `ι` that lists `s` and then its complement, is block
triangular with the complementary minor of the second block of `D` in one corner. Two applications
of `Matrix.det_fromBlocks_zero₁₂` and `Matrix.det_fromBlocks_zero₂₁` give the identity, and the
factor that appears is the determinant of `C` read through that enumeration, which depends on `s`
only through a permutation sign (`Matrix.det_permute'`).

## References

W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Annals of
Mathematics 85 (1967), §1, equations (2) and (4), where the involution on Grassmann coordinates
that reverses the index order and attaches a sign is what makes the theorem hold in every
normalization at once. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge
University Press (2006), Proposition 2.8.10 and Corollary 2.8.12. The underlying linear algebra is
Hindry–Silverman, *Diophantine Geometry: An Introduction*, Exercise A.1.11(c).

This is Layer 3.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Module Set.powersetCard exteriorPower

namespace Height


end Height

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*}

section Arakelov

variable [NumberField K] [Fintype ι]

/-- **A change of sign in a coordinate does not change the Arakelov height** either: the
archimedean factor is a sum of squares of absolute values and the finite factor a supremum of
absolute values, and neither sees a sign. -/
theorem arakelovMulHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : arakelovMulHeight y = arakelovMulHeight x := by
  have hinf (v : InfinitePlace K) (i : ι) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; exact v.1.map_neg _
  have hfin (v : FinitePlace K) (i : ι) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; simp
  have hzero : y = 0 ↔ x = 0 := by
    simp only [funext_iff, Pi.zero_apply]
    refine ⟨fun h0 i ↦ ?_, fun h0 i ↦ ?_⟩ <;> rcases h i with hi | hi
    · rw [← hi]; exact h0 i
    · have := h0 i; rw [hi, neg_eq_zero] at this; exact this
    · rw [hi, h0 i]
    · rw [hi, h0 i, neg_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hzero.2 rfl]
  · grind [arakelovMulHeight_eq, finprod_congr, iSup_congr]

end Arakelov




end NumberField

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k l : ℕ}

/-- Mathlib's `Matrix.submatrix_mul_equiv`, read as a re-indexing of the inner index of a
product: with both factors square it turns a product of rectangular matrices into a product of
square ones, where `Matrix.det_mul` applies. -/
private lemma mul_eq_submatrix_mul_submatrix {m p r : Type*} [Fintype r]
    (X : Matrix m ι R) (Y : Matrix ι p R) (e : r ≃ ι) :
    X * Y = X.submatrix id e * Y.submatrix e id := by
  rw [Matrix.submatrix_mul_equiv X Y id e id, Matrix.submatrix_id_id]

variable [LinearOrder ι]

variable {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l)

/-- The enumeration of `ι` that lists the elements of `s` in increasing order and then those of
its complement. This is the index identification the complementary-minor identity runs on; the
determinant of a matrix read through it depends on `s` only up to a sign. -/
private noncomputable def enumEquiv  :
    Fin k ⊕ Fin l ≃ ι :=
  (Equiv.sumCongr (s.orderIsoOfFin hs).toEquiv
    ((sᶜ.orderIsoOfFin hsc).toEquiv.trans
      (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_compl))).trans (Equiv.sumCompl (Membership.mem s))

private lemma enumEquiv_inl  (a : Fin k) :
    enumEquiv hs hsc (Sum.inl a) = s.orderEmbOfFin hs a :=
  Finset.coe_orderIsoOfFin_apply s hs a

private lemma enumEquiv_inr  (b : Fin l) :
    enumEquiv hs hsc (Sum.inr b) = sᶜ.orderEmbOfFin hsc b :=
  Finset.coe_orderIsoOfFin_apply sᶜ hsc b

/-- **The complementary-minor identity.** If the rows of `C` and the rows of `D` are dual to one
another for the standard bilinear form, then the maximal minor of the first block of `C` on the
columns `s` is the complementary minor of the second block of `D` times the determinant of `C`
read through the enumeration attached to `s`. This is the whole content of duality: the
`s`-dependence of the factor is a sign, by `Matrix.det_permute'`. -/
private theorem det_submatrix_inl_eq_mul (C D : Matrix (Fin k ⊕ Fin l) ι R) (hCD : C * Dᵀ = 1)
    {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) :
    ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det
      = (C.submatrix id (enumEquiv hs hsc)).det *
          ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc)).det := by
  classical
  have hdual (r c : Fin k ⊕ Fin l) :
      ∑ i, C r i * D c i = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) R) r c := by
    rw [← hCD, Matrix.mul_apply]
    rfl
  set E : Matrix ι (Fin k ⊕ Fin l) R :=
    Matrix.of fun i r ↦ Sum.elim (fun a ↦ if i = s.orderEmbOfFin hs a then 1 else 0)
      (fun b ↦ D (Sum.inr b) i) r with hE
  have hCE : C * E = Matrix.fromBlocks
      ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)) 0
      ((C.submatrix Sum.inr id).submatrix id (s.orderEmbOfFin hs)) 1 := by
    ext r c
    rcases c with a | b
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, mul_ite, Finset.sum_ite_eq' Finset.univ]
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, hdual _ (Sum.inr b), Matrix.one_apply]
  have hEσ : E.submatrix (enumEquiv hs hsc) id = Matrix.fromBlocks 1
      (Matrix.of fun a' b ↦ D (Sum.inr b) (s.orderEmbOfFin hs a')) 0
      ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc))ᵀ := by
    ext r c
    rcases r with a' | b' <;> rcases c with a | b
    · simp only [Matrix.submatrix_apply, id_eq, enumEquiv_inl, hE, Matrix.of_apply, Sum.elim_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      exact if_congr ⟨fun h ↦ (s.orderEmbOfFin hs).injective h, fun h ↦ by rw [h]⟩ rfl rfl
    · simp [hE, enumEquiv_inl]
    · have hne : sᶜ.orderEmbOfFin hsc b' ≠ s.orderEmbOfFin hs a := by
        grind [orderEmbOfFin_mem, Finset.mem_compl]
      simp [hE, enumEquiv_inr, hne]
    · simp [hE, enumEquiv_inr, Matrix.transpose_apply]
  have hdet : (C * E).det = ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det := by
    rw [hCE, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  rw [← hdet, mul_eq_submatrix_mul_submatrix C E (enumEquiv hs hsc), Matrix.det_mul, hEσ,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_transpose]

end Matrix

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {r : Type*} [Fintype r] [DecidableEq r]

omit [Fintype ι] in
/-- Two enumerations of the column index differ by a permutation, so the determinants they
produce differ by a sign. -/
theorem det_submatrix_equiv_eq_or_eq_neg (X : Matrix r ι K) (e₁ e₂ : r ≃ ι) :
    (X.submatrix id e₁).det = (X.submatrix id e₂).det ∨
      (X.submatrix id e₁).det = -(X.submatrix id e₂).det := by
  have h : X.submatrix id e₁ = (X.submatrix id e₂).submatrix id (e₁.trans e₂.symm) := by
    ext i j
    simp
  rw [h, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₁.trans e₂.symm)) with hs | hs <;> rw [hs] <;> simp


omit [Fintype r] in
/-- Rows dual to a family of rows are linearly independent. -/
theorem linearIndependent_row_of_mul_transpose_eq_one {C D : Matrix r ι K}
    (hCD : C * Dᵀ = 1) : LinearIndependent K C.row := by
  refine linearIndependent_iff'.2 fun t g hg i hi ↦ ?_
  have h := congrArg (· ⬝ᵥ D.row i) hg
  simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun j _ ↦ by
    rw [show C.row j ⬝ᵥ D.row i = (C * Dᵀ) j i from rfl, hCD]] at h
  simpa [Matrix.one_apply, Finset.sum_ite_eq' t, hi] using h

/-- The two-sided form of duality of rows: the dual rows expand every vector, with the pairings
against the original rows as coefficients. -/
private lemma eq_sum_dotProduct_smul_row {C D : Matrix r ι K} (hCD : C * Dᵀ = 1)
    (hcard : Fintype.card r = Fintype.card ι) (x : ι → K) :
    x = ∑ j, (C.row j ⬝ᵥ x) • D.row j := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard
  have hsq : (Dᵀ.submatrix e id) * (C.submatrix id e) = 1 := by
    refine mul_eq_one_comm.1 ?_
    rw [← mul_eq_submatrix_mul_submatrix, hCD]
  have hDC : Dᵀ * C = 1 := by
    have hsub : (Dᵀ * C).submatrix e e = (Dᵀ.submatrix e id) * (C.submatrix id e) := by
      ext a b
      simp [Matrix.mul_apply]
    have h : (Dᵀ * C).submatrix e e = (1 : Matrix ι ι K).submatrix e e := by
      rw [hsub, hsq, Matrix.submatrix_one_equiv]
    have h2 := congrArg (fun M ↦ M.submatrix e.symm e.symm) h
    simpa [Matrix.submatrix_submatrix] using h2
  funext i
  have hx : x i = ∑ a, (Dᵀ * C) i a * x a := by
    rw [hDC]
    simp [Matrix.one_apply, Finset.sum_ite_eq]
  rw [hx, Finset.sum_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Matrix.row, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring

end Matrix

namespace Submodule

open Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k l : ℕ}

/-- **The transported annihilator is the orthogonal complement.** `Module.piEquiv ι K K` sends
`x` to the functional `v ↦ v ⬝ᵥ x`, so a vector lies in the annihilator of `V` read back in
`ι → K` exactly when it is orthogonal to `V` for the standard bilinear form. -/
theorem mem_comap_piEquiv_dualAnnihilator {V : Submodule K (ι → K)} {x : ι → K} :
    x ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ↔ ∀ v ∈ V, v ⬝ᵥ x = 0 := by
  simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  refine forall₂_congr fun v _ ↦ ?_
  rw [show ((Module.piEquiv ι K K).toLinearMap x) v = Module.piEquiv ι K K x v from rfl,
    Module.piEquiv_apply_apply]
  simp [dotProduct]

/-- The span of a family is orthogonal to `x` as soon as every member is. -/
private lemma span_le_ker_piEquiv {s : Set (ι → K)} {x : ι → K} (h : ∀ v ∈ s, v ⬝ᵥ x = 0) :
    span K s ≤ LinearMap.ker (Module.piEquiv ι K K x) := by
  rw [Submodule.span_le]
  intro v hv
  simpa only [SetLike.mem_coe, LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul,
    dotProduct] using h v hv

/-- **Every subspace sits in a dual pair of matrices.** The rows of `C` are a basis of `ι → K`
whose first block is a basis of `V`; the rows of `D` are the dual basis, read back in `ι → K`
through the standard bilinear form. -/
theorem exists_dual_matrices (V : Submodule K (ι → K)) (hk : finrank K V = k)
    (hlk : l + k = Fintype.card ι) :
    ∃ C D : Matrix (Fin k ⊕ Fin l) ι K, C * Dᵀ = 1 ∧
      span K (Set.range (C.submatrix Sum.inl id).row) = V := by
  classical
  obtain ⟨W, hW⟩ := V.exists_isCompl
  have hWrank : finrank K W = l := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, hk, Module.finrank_pi] at h
    omega
  let bV := Module.finBasisOfFinrankEq K V hk
  let bW := Module.finBasisOfFinrankEq K W hWrank
  let c : Module.Basis (Fin k ⊕ Fin l) K (ι → K) :=
    (bV.prod bW).map (V.prodEquivOfIsCompl W hW)
  have hcl (a : Fin k) : c (Sum.inl a) = (bV a : ι → K) := by
    aesop
  refine ⟨Matrix.of (⇑c), Matrix.of fun s i ↦ c.coord s (Pi.basisFun K ι i), ?_, ?_⟩
  · ext r s
    rw [Matrix.mul_apply, Matrix.one_apply]
    have : ∑ i, c r i * c.coord s (Pi.basisFun K ι i) = c.coord s (c r) := by
      conv_rhs => rw [← (Pi.basisFun K ι).sum_repr (c r)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [map_smul, smul_eq_mul, Pi.basisFun_repr]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  · have hrange : Set.range ((Matrix.of fun r ↦ (c r)).submatrix
        Sum.inl id).row = V.subtype '' (Set.range bV) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun a ↦ hcl a)
    rw [hrange, Submodule.span_image, bV.span_eq, Submodule.map_top,
      Submodule.range_subtype]

variable [LinearOrder ι]

omit [LinearOrder ι] in
/-- **The second block of the dual basis spans the orthogonal complement.** -/
theorem span_range_inr_row_eq {V : Submodule K (ι → K)} {C D : Matrix (Fin k ⊕ Fin l) ι K}
    (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι)
    (hV : span K (Set.range (C.submatrix Sum.inl id).row) = V) :
    span K (Set.range (D.submatrix Sum.inr id).row)
      = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap := by
  have hdual (r t : Fin k ⊕ Fin l) :
      C.row r ⬝ᵥ D.row t = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K) r t := by
    rw [← hCD]
    rfl
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, mem_comap_piEquiv_dualAnnihilator]
    intro v hv
    rw [← hV] at hv
    have hker := span_le_ker_piEquiv (s := Set.range (C.submatrix Sum.inl id).row)
      (x := (D.submatrix Sum.inr id).row b) (fun y hy ↦ ?_) hv
    · simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct]
        using hker
    · obtain ⟨a, rfl⟩ := hy
      solve_by_elim []
  · rw [mem_comap_piEquiv_dualAnnihilator] at hx
    have hzero (a : Fin k) : C.row (Sum.inl a) ⬝ᵥ x = 0 :=
      hx _ (hV ▸ Submodule.subset_span ⟨a, rfl⟩)
    have hmem : (∑ j, (C.row j ⬝ᵥ x) • D.row j)
        ∈ span K (Set.range (D.submatrix Sum.inr id).row) := by
      aesop (add safe apply [Fintype.sum_sum_type, zero_smul, Finset.sum_const_zero, zero_add, Submodule.sum_mem, Submodule.smul_mem, Submodule.subset_span, rfl])
    rwa [← Matrix.eq_sum_dotProduct_smul_row hCD hcard x] at hmem

/-- **Plücker duality in coordinates** (W. M. Schmidt 1967, §1, equations (2) and (4)). A
subspace and its annihilator have bases whose Plücker coordinates agree at complementary indices,
up to a sign at each index and one common nonzero factor — the involution Schmidt calls `τ`.
Every height in this development is invariant under exactly that much. -/
theorem exists_plucker_eq_plucker_compl (V : Submodule K (ι → K)) (hk : finrank K V = k)
    (hlk : l + k = Fintype.card ι) :
    ∃ (v : Fin k → (ι → K)) (w : Fin l → (ι → K)) (c : K), c ≠ 0 ∧
      LinearIndependent K v ∧ LinearIndependent K w ∧
      span K (Set.range v) = V ∧
      span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
      ∀ s : Set.powersetCard ι k,
        exteriorPower.plucker k v s
            = c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s) ∨
          exteriorPower.plucker k v s
            = -(c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s)) := by
  classical
  obtain ⟨C, D, hCD, hV⟩ := exists_dual_matrices V hk hlk
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨e₀⟩ := Fintype.truncEquivOfCardEq hcard
  have hDC := by
    have h := congrArg Matrix.transpose hCD
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  refine ⟨(C.submatrix Sum.inl id).row, (D.submatrix Sum.inr id).row, (C.submatrix id e₀).det,
    ((let inline_e := e₀;
       IsUnit.of_mul_eq_one ((Dᵀ).submatrix inline_e id).det <| by
         rw [← Matrix.det_mul, ← mul_eq_submatrix_mul_submatrix, hCD, Matrix.det_one])).ne_zero,
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hCD).comp _ Sum.inl_injective,
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hDC).comp _ Sum.inr_injective,
    hV, span_range_inr_row_eq hCD hlk hV, fun s ↦ ?_⟩
  have hs := Set.powersetCard.card_eq s
  have hsc : ((s : Finset ι))ᶜ.card = l := by
    rw [Finset.card_compl, hs]
    omega
  rw [Matrix.plucker_row_eq_det_submatrix, Matrix.plucker_row_eq_det_submatrix,
    Matrix.det_submatrix_inl_eq_mul C D hCD hs hsc]
  rcases Matrix.det_submatrix_equiv_eq_or_eq_neg C (Matrix.enumEquiv hs hsc) e₀ with hsign | hsign
  · refine Or.inl ?_
    rw [hsign]
    rfl
  · refine Or.inr ?_
    rw [hsign, neg_mul]
    rfl

end Submodule

namespace Submodule

open Matrix exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The two tuples of Plücker coordinates attached to `V` and to its annihilator, with the
relation between them. This is `Submodule.exists_plucker_eq_plucker_compl` with the two ranks
existentially bound, the form the height statements consume. -/
private lemma exists_plucker_pair (V : Submodule K (ι → K)) :
    ∃ (k l : ℕ) (hlk : l + k = Fintype.card ι) (v : Fin k → (ι → K)) (w : Fin l → (ι → K))
      (c : K), c ≠ 0 ∧ LinearIndependent K v ∧ LinearIndependent K w ∧
      span K (Set.range v) = V ∧
      span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
      ∀ s : Set.powersetCard ι k,
        plucker k v s = c * plucker l w (Set.powersetCard.compl hlk s) ∨
          plucker k v s = -(c * plucker l w (Set.powersetCard.compl hlk s)) := by
  have hle := by
    have h := V.finrank_le 
    rwa [Module.finrank_pi] at h
  obtain ⟨v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ :=
    exists_plucker_eq_plucker_compl V (l := Fintype.card ι - Module.finrank K V) rfl (by omega)
  exact ⟨_, _, _, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩




section Arakelov

variable [NumberField K]

/-- **The duality theorem in the Arakelov normalization** (Bombieri–Gubler, Proposition 2.8.10).
Schmidt's mechanism gives both normalizations at once: the two coordinate tuples differ by a
signed reindexing and a scalar, and no height in Layer 0 sees either. -/
theorem arakelovMulHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).arakelovMulHeight =
      V.arakelovMulHeight := by
  obtain ⟨k, l, hlk, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ := exists_plucker_pair V
  rw [← hWw, ← hVv, arakelovMulHeight_span_range hv, arakelovMulHeight_span_range hw,
    NumberField.arakelovMulHeight_eq_of_forall_eq_or_eq_neg hpl,
    show (fun s ↦ c * plucker l w (Set.powersetCard.compl hlk s))
      = c • (plucker l w ∘ (Set.powersetCard.compl hlk)) from rfl,
    NumberField.arakelovMulHeight_smul_eq _ hc, NumberField.arakelovMulHeight_comp_equiv]

end Arakelov




end Submodule

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **The orthogonal-complement form of the hypothesis.** A subspace cut out by orthogonality to
`V` for the standard bilinear form *is* the transported annihilator, so each duality theorem above
applies to it. `Submodule.comap_piEquiv_dualAnnihilator_eq_map` turns the `comap` into a `map`
along the inverse, which is the other spelling in use. -/
theorem eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero
    {V W : Submodule K (ι → K)} (h : ∀ x, x ∈ W ↔ ∀ v ∈ V, v ⬝ᵥ x = 0) :
    W = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap :=
  SetLike.ext fun x ↦ (h x).trans mem_comap_piEquiv_dualAnnihilator.symm

end Submodule

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : Type*}

omit [LinearOrder ι] in
/-- **The solution space of `A x = 0` is the orthogonal complement of the row space of `A`.** -/
theorem ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator (A : Matrix m ι K) :
    LinearMap.ker A.mulVecLin =
      (Submodule.span K (Set.range A.row)).dualAnnihilator.comap
        (Module.piEquiv ι K K).toLinearMap := by
  refine Submodule.eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero fun x ↦ ?_
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  refine ⟨fun h v hv ↦ ?_, fun h ↦ funext fun i ↦ h _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hker := Submodule.span_le_ker_piEquiv  
    (fun y hy ↦ by obtain ⟨i, rfl⟩ := hy; exact congrFun h i) hv
  simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct] using hker




section Arakelov

variable [NumberField K]

/-- **The Arakelov height of a subspace is the Arakelov height of any matrix cutting it out**
(Bombieri–Gubler, Corollary 2.8.12), `H_Ar^row(A)` of Bombieri–Vaaler. -/
theorem arakelovMulHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).arakelovMulHeight =
      (Submodule.span K (Set.range A.row)).arakelovMulHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator]

end Arakelov




end Matrix

/-!
### Worked examples
-/

section Examples

open Matrix Submodule

end Examples
