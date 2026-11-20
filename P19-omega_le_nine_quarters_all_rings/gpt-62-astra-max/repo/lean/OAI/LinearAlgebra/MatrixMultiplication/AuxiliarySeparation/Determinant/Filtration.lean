module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.Convolution

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration
open Foundation
variable {K : Type*} [CommRing K]
abbrev Index (e : ℕ) := Fin (e+2) ⊕ Fin e
def delta {I : Type} [DecidableEq I] (j x : I) : K := if x = j then 1 else 0

/-- Adapted columns: monomials in the quotient, or a pair `(-X*w,w)` in the kernel. -/
def column (e : ℕ) : Index e → Fin (e+1) × Fin 2 → K
  | .inl j => Fin.lastCases (delta (Fin.last e,1)) (fun l => delta (l,0)) j
  | .inr j => fun u => delta (j.castSucc,1) u - delta (j.succ,0) u

/-- Quotient rows read `p + X*q`; kernel rows retain `q` below top degree. -/
def row (e : ℕ) {m : ℕ} : Index e → Fin m × Fin 2 → K
  | .inl k, (r,l) => if r.val+l.val = k.val then 1 else 0
  | .inr k, (r,l) => if r.val = k.val ∧ l=1 then 1 else 0

def adaptedTensor (d e : ℕ) : Tensor K (Fin (d+1)) (Index e) (Index (d+e)) :=
  fun i j k => ∑ u, column e j u * row (d+e) k (shift i u.1,u.2)

/-- Restrict convolution times a dot product by the two adapted maps. -/
theorem value_adapted (χ : Price K) (d e : ℕ) : χ.value (adaptedTensor d e) ≤
    2 * χ.value (convolution d e) := by
  let S := Tensor.product (convolution (K := K) d e) (Tensor.dotPairing 2)
  have h := χ.value_restrict S (fun i u => delta i u.1) (column e) (row (d+e))
  apply le_trans
  · convert h using 2
    funext
    simp [adaptedTensor, Tensor.restrict, Fintype.sum_prod_type, delta, S, Tensor.product, Tensor.dotPairing,
      convolution, mul_ite]
  · rw [χ.map_product, χ.value_dot (by decide), mul_comm]; norm_num

/-- The two diagonal blocks are ordinary convolutions, and the lower-left
block is zero. No formula is required for the fourth block. -/
theorem blocks (d e : ℕ) :
    Tensor.pullback id Sum.inl Sum.inl (adaptedTensor (K := K) d (e+1)) = convolution d (e+2) ∧
    Tensor.pullback id Sum.inr Sum.inr (adaptedTensor (K := K) d (e+1)) = convolution d e ∧
    ∀ i j k, adaptedTensor (K := K) d (e+1) i (.inr j) (.inl k) = 0 := by
  refine ⟨?large, ?small, ?mixed⟩
  case' large => funext i j k; cases j using Fin.lastCases
  case' small => funext
  case' mixed => intro i j k
  all_goals
    simp [Tensor.pullback, adaptedTensor, column, delta, ite_mul, sub_mul, Finset.sum_sub_distrib]
    simp [row, shift, convolution, Fin.ext_iff] <;> grind

end OAI.MatrixMultiplication.AuxiliarySeparation.DeterminantFiltration
