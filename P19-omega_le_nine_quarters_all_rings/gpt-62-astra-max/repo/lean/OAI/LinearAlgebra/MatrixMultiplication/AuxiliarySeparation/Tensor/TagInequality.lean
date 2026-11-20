module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.Separation

@[expose] public noncomputable section

/-! Grouping words by histogram upgrades finite separation to a bound on triangular arrays of tensor blocks. -/

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation TensorResource
open scoped Classical

variable {K : Type*} [CommRing K]
variable {s n : ℕ} {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
open scoped NNReal

/-- Count words only by their histograms; no estimate of a multinomial
coefficient, rational approximation, or entropy limit is needed. -/
private def histogram {n s : ℕ} (w : Fin n → Fin s) (a : Fin s) : Fin (n+1) :=
  ⟨Fintype.card {i // w i = a}, by simpa using Fintype.card_subtype_le fun i => w i = a⟩

/-- Keep an arbitrary family of distinct words on the split legs of the power. -/
private theorem words_le {I : Type} [Fintype I] [DecidableEq I]
    (B : Fin s → Tensor K X Y Z) (w : I → Fin n → Fin s) (hw : Function.Injective w)
    (ψ : Price K) : ψ.value (sharedFirstTensor fun i => Tensor.word (B ∘ w i)) ≤
      ψ.value (sharedFirstTensor B) ^ n := by
  let side {U : Type} (p : I × (Fin n → U)) (i : Fin n) := (w p.1 i, p.2 i)
  rw [← ψ.value_power]
  convert ψ.value_pullback_le (Tensor.power (sharedFirstTensor B) n) id side side using 2
  funext x y z
  simp [sharedFirstTensor, side, Tensor.pullback, Tensor.power, Tensor.word,
    Fintype.prod_ite_zero, ← funext_iff, hw.eq_iff]

namespace Price
variable (χ : Price K)

/-- Expand the power of a sum over words, grouping by histogram. In each
fiber every character sees a constant value. Finite separation bounds its
entire contribution; the number of fibers grows only polynomially. -/
theorem value_shared (B : Fin s → Tensor K X Y Z) :
    (∑ j, χ.value (B j)) ≤ χ.value (sharedFirstTensor B) := by
  let S := sharedFirstTensor B
  let C := χ.eval (scalars 2)
  apply polynomial_overhead (χ.nonneg S) ((Polynomial.X+1)^s*Polynomial.C C)
  intro n
  let A (c : Fin s → Fin (n+1)) := ∏ b, classOf (B b) ^ (c b).val
  let V c := χ.eval (A c)
  have hc (w : Fin n → Fin s) : classOf (Tensor.word (B ∘ w)) = A (histogram w) := by
    rw [classOf_wordTensor]; simpa [A, histogram] using (Fintype.prod_fiberwise' w (classOf ∘ B)).symm
  have hf (c) : (∑ _ : {w : Fin n → Fin s // histogram w = c}, V c) ≤ C*χ.value S^n := by
    let F := {w : Fin n → Fin s // histogram w = c}
    change (∑ _ : F, V c) ≤ _
    have hn : 0 ≤ C := χ.nonnegative _
    have hs := χ.nonneg S
    rcases isEmpty_or_nonempty F with he | he
    · simpa using (show 0 ≤ C*χ.value S^n by positivity)
    let e := (Fintype.equivFin F).symm
    have h := Integral.separate χ (v := A c) Fintype.card_pos (fun i => Tensor.word (B ∘ (e i).val)) (fun i => by simp only [hc, (e i).property])
    simpa [V,C,S, nsmul_eq_mul] using h.trans (mul_le_mul_of_nonneg_left (words_le B _ (Subtype.val_injective.comp e.injective) χ) hn)
  calc
    _ = ∑ w, V (histogram w) := by simp [Finset.sum_pow', V, ← hc, value, classOf_wordTensor]
    _ = _ := (Fintype.sum_fiberwise' histogram V).symm
    _ ≤ ∑ _ : Fin s → Fin (n+1), C*χ.value S^n := Finset.sum_le_sum fun i _ => hf i
    _ = _ := by simp [mul_assoc]

/-- Coordinate maps for a single block. Its two split legs may have their
own dimensions, and its common leg may be relabeled independently. -/
structure Block (X Y Z : Type) where
  {m n : ℕ}
  x : X → X
  y : Fin (m+1) → Y
  z : Fin (n+1) → Z

def Block.view (B : Block X Y Z) (T : Tensor K X Y Z) := Tensor.pullback B.x B.y B.z T

/-- Project ambient coordinates back onto each block image. On the resulting
common space, one monomial weighting retains all diagonal blocks. -/
theorem value_blocks (T : Tensor K X Y Z)
    (B : Fin s → Block X Y Z) (w : Fin s → ℕ)
    (h : ∀ b c x j k, b ≠ c → T x ((B b).y j) ((B c).z k) ≠ 0 → w c < w b) :
    (∑ i, χ.value ((B i).view T)) ≤ χ.value T := by
  let project {I J : Type} [Nonempty I] (f : I → J) := f ∘ Function.invFun f
  let y b := project (B b).y
  let z b := project (B b).z
  let H b := Tensor.pullback id (y b) (z b) T
  apply le_trans (b := ∑ b, χ.value (H b))
  · apply Finset.sum_le_sum; intro b _
    convert χ.value_pullback_le (H b) (B b).x (B b).y (B b).z using 2
    funext; simp [Block.view, H, Tensor.pullback, y, z, project, Function.apply_invFun_apply]
  apply (χ.value_shared H).trans
  apply χ.value_weighted T _ id (Function.uncurry y) (Function.uncurry z) (fun _ => 0) (fun p => w p.1) fun p => w p.1
  rintro x ⟨b,j⟩ ⟨c,k⟩
  simp [sharedFirstTensor, H, y, z, project, Tensor.pullback, Function.uncurry]
  specialize h b c x (Function.invFun (B b).y j) (Function.invFun (B c).z k)
  split_ifs <;> grind

end Price
end OAI.MatrixMultiplication.AuxiliarySeparation
