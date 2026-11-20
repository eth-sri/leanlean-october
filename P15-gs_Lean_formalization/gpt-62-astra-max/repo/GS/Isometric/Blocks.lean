module

public import GS.Isometric.Layers
public import GS.Isometric.Pack

@[expose] public section

/-! Complete blocks with ties form a real star subalgebra over either field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

namespace Support
variable {κ : Type*} {label : Fin n → κ} {A B : Square 𝕜 n}

@[simp] theorem one : Support label (1 : Square 𝕜 n) := by
  intro i j hij
  have hne : i ≠ j := fun h => hij (congrArg label h)
  simp [hne]

theorem conjTranspose (h : Support label A) : Support label Aᴴ := by
  intro i j hij
  simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]

theorem mul (hA : Support label A) (hB : Support label B) :
    Support label (A*B) := by
  intro i j hij
  change (∑ k, A i k * B k j) = 0
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hik : label i = label k
  · have hkj : label k ≠ label j := fun h => hij (hik.trans h)
    rw [hB k j hkj, mul_zero]
  · rw [hA i k hik, zero_mul]
end Support

variable {b : ℕ} {τ : ℕ → ℕ} {A B : Square 𝕜 n}

/-- Physical coordinates: local index and block number. -/
def layout (hd : b ∣ n) : Fin b × Fin (n/b) ≃ Fin n :=
  (Equiv.prodComm ..).trans (finProdFinEquiv.trans (finCongr (Nat.div_mul_cancel hd)))

def repeatBlocks {k : ℕ} {ι : Type*} (t : Fin k → ι) : (ι → Square 𝕜 b) →⋆ₐ[ℝ] (Fin k → Square 𝕜 b) where
  toFun B := B ∘ t
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

private lemma ties_iff (hd : b ∣ n) : Tied b τ A ↔
    (fun i => readBlock (layout hd) A i i).FactorsThrough (fun i => τ i.val) := by
  let e := layout hd
  have quo (p) : (e p).val / b = p.2.val := by change (e.symm (e p)).2.val = _; rw [e.symm_apply_apply]
  have rem (p) : (e p).val % b = p.1.val := by change (e.symm (e p)).1.val = _; rw [e.symm_apply_apply]
  simp only [Tied,e.surjective.forall,Prod.forall,quo,rem,Fin.val_eq_val,Function.FactorsThrough,← Matrix.ext_iff,readBlock,submatrix_apply]
  grind

/-- Repeat just one block per sharing label, then pack. Taking the range as a
star algebra handles all algebra and adjoint closure at once. -/
def blocks (𝕜 : Type*) [RCLike 𝕜] (b : ℕ) (τ : ℕ → ℕ) (_hb : 0 < b) (hd : b ∣ n) : Layer 𝕜 n :=
  let e := layout hd
  let q (i : Fin (n/b)) := τ i.val
  let t := (pack (𝕜 := 𝕜) e).comp (repeatBlocks q)
  t.range.copy {A | DiagonalBlocks b A ∧ Tied b τ A} (by
    ext X; change DiagonalBlocks b X ∧ Tied b τ X ↔ ∃ B, pack e (B ∘ q) = X
    rw [ties_iff hd,Function.factorsThrough_iff]
    constructor
    · rintro ⟨h,B,hB⟩; exact ⟨B,hB ▸ (pack_read e (fun _ => rfl) h).symm⟩
    · rintro ⟨B,rfl⟩; exact ⟨pack_supported e (fun _ => rfl) _,B,funext fun i => by simp [e,q]⟩)
end GS.Isometric
