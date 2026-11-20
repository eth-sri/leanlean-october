module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Determinant.Filtration
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.TagInequality
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Profile

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation.Price
open Foundation TensorResource DeterminantFiltration
open scoped Classical NNReal
variable {K : Type*} [CommRing K] (χ : Price K)

abbrev convolutionProfile (a b : ℕ) := χ.value (convolution a b)

theorem convolutionProfile_comm (a b : ℕ) : χ.convolutionProfile a b = χ.convolutionProfile b a := by
  let e : Fin (a+b+1) ≃ Fin (b+a+1) := finCongr (by omega)
  rw [convolutionProfile, ← χ.value_swap12]
  apply congrArg χ.eval
  apply classOf_eq_of_reindex (Equiv.refl _) (Equiv.refl _) e
  funext; simp [Tensor.pullback, convolution, shift, Fin.ext_iff, e, Nat.add_comm]

theorem convolutionProfile_concave (d e : ℕ) :
    χ.convolutionProfile d e + χ.convolutionProfile d (e+2) ≤ 2*χ.convolutionProfile d (e+1) := by
  let T := adaptedTensor (K := K) d (e+1)
  let B : Fin 2 → Block (Fin (d+1)) (Index (e+1)) (Index (d+(e+1))) := ![
    ⟨id, Sum.inl, Sum.inl⟩, ⟨id, Sum.inr, Sum.inr⟩]
  obtain ⟨h0,h1,hx⟩ := blocks (K := K) d e
  have hs := χ.value_blocks T B ![1,0] (by
    intro b c x j k; fin_cases b <;> fin_cases c <;> simp [T, B]; exact hx x j k)
  rw [Fin.sum_univ_two, show (B 0).view T = _ from h0, show (B 1).view T = _ from h1, add_comm] at hs
  exact hs.trans (value_adapted χ ..)

/-- Two translated convolutions flank a reversed copy with exchanged legs. -/
theorem convolutionProfile_tripling (a h : ℕ) :
    3 * χ.convolutionProfile a h ≤ χ.convolutionProfile a (3*h+a+2) := by
  let T := convolution (K := K) a (3*h+a+2)
  let B : Fin 3 → Block (Fin (a+1)) (Fin (3*h+a+2+1)) (Fin (a+(3*h+a+2)+1)) := ![
    ⟨id, fun j : Fin (h+1) => ⟨j,by omega⟩, fun k : Fin (a+h+1) => ⟨k,by omega⟩⟩,
    ⟨Fin.rev, fun k : Fin (a+h+1) => ⟨h+1+k.val,by omega⟩, fun j : Fin (h+1) => ⟨a+h+1+j.val,by omega⟩⟩,
    ⟨id, fun j : Fin (h+1) => ⟨2*h+a+2+j.val,by omega⟩, fun k : Fin (a+h+1) => ⟨2*h+a+2+k.val,by omega⟩⟩]
  have hs := χ.value_blocks T B ![0,1,0] (by
    intro b c x j k; fin_cases b <;> fin_cases c <;> simp [B, T, convolution, shift, Fin.ext_iff] <;> grind)
  have hc (b : Fin 3) : χ.value ((B b).view T) = χ.convolutionProfile a h := by
    fin_cases b
    case' «1» => rw [convolutionProfile, ← χ.value_swap23]
    all_goals congr 1; funext; simp [Block.view, Tensor.pullback, B, T, convolution, shift, Fin.ext_iff]; grind [Fin.ext_iff]
  simpa [hc, nsmul_eq_mul] using hs

private def toScalarProfile : ScalarProfile where
  value := χ.convolutionProfile
  unit := by
    have he : convolution (K := K) 0 0 = scalarTensor (Fin 1) := by
      funext i j k; fin_cases i; fin_cases j; fin_cases k; rfl
    simp [convolutionProfile,he]
  symmetric := χ.convolutionProfile_comm
  concave := χ.convolutionProfile_concave
  tripling := χ.convolutionProfile_tripling

/-- On a scalar of dimension `k` the diagonal growth bound forces a
three-to-four power comparison. Pass to powers to remove the constant. -/
theorem scalar_fourth {k : ℕ} (hk : 0 < k) : (k:ℝ)^4 ≤ χ.eval (scalars k)^3 := by
  have hn : 0 ≤ χ.eval (scalars k) := χ.nonnegative _
  apply polynomial_overhead (by positivity) (Polynomial.C (χ.eval (scalars 2) ^ 3))
  intro j
  obtain ⟨n,he⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero j hk.ne')
  have hd := χ.toScalarProfile.diagonal n
  have h : χ.value (convolution n n) ≤ χ.eval (scalars (2*k^j)) := (χ.value_convolution_le n n).trans
    (χ.eval.monotone' ((scalars (K := K)).monotone' (by omega)))
  have hf := hd.trans ((Odd.pow_le_pow (by decide : Odd 3)).mpr h)
  change (n+1:ℝ)^4 ≤ _ at hf
  rw [← Nat.cast_succ, ← he] at hf
  simpa [pow_right_comm, mul_pow] using hf

end OAI.MatrixMultiplication.AuxiliarySeparation.Price
