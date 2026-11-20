module
public import GS.Isometric.Families
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Reindex
@[expose] public section

/-! Packing complete blocks is a real star-algebra homomorphism, in *any*
coordinate labelling. A supported matrix is recovered by reading its diagonal
blocks, and is unitary exactly when all the blocks are. -/
noncomputable section
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {b k n : ℕ}
variable (e : Fin b × Fin k ≃ Fin n)
def pack : (Fin k → Square 𝕜 b) →⋆ₐ[ℝ] Square 𝕜 n where
  __ := (reindexRingEquiv 𝕜 e).toRingHom.comp (blockDiagonalRingHom (Fin b) (Fin k) 𝕜)
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one,blockDiagonal_smul,submatrix_smul]
  map_star' B := by
    change (blockDiagonal (fun i => (B i)ᴴ)).submatrix e.symm e.symm = ((blockDiagonal B).submatrix e.symm e.symm)ᴴ
    simp

def readBlock (X : Square 𝕜 n) (i j : Fin k) := X.submatrix (fun a => e (a,i)) (fun a => e (a,j))
@[simp] lemma pack_entry (B : Fin k → Square 𝕜 b) (x y : Fin b × Fin k) :
    pack e B (e x) (e y) = if x.2 = y.2 then B x.2 x.1 y.1 else 0 := by
  change blockDiagonal B (e.symm (e x)) (e.symm (e y)) = _; simp [blockDiagonal_apply]
lemma pack_injective : Function.Injective (pack (𝕜 := 𝕜) e) := (reindexRingEquiv 𝕜 e).injective.comp blockDiagonal_injective
lemma pack_unitary (B : Fin k → Square 𝕜 b) : IsU (pack e B) ↔ ∀ i, IsU (B i) := by
  change star (pack e B) * _ = 1 ∧ _ * star (pack e B) = 1 ↔ _
  rw [← map_star,← map_mul,← map_mul,← map_one (pack e),(pack_injective e).eq_iff,(pack_injective e).eq_iff]
  exact ⟨fun ⟨a,c⟩ i => ⟨congrFun a i,congrFun c i⟩, fun h => ⟨funext fun i => (h i).1,funext fun i => (h i).2⟩⟩

variable (he : ∀ i, (e.symm i).2.val = i.val / b)
include he in
lemma pack_supported (B : Fin k → Square 𝕜 b) : DiagonalBlocks b (pack e B) := by
  rintro i j hij; exact if_neg (fun h => hij ((he i).symm.trans ((congrArg Fin.val h).trans (he j))))
include he in
lemma pack_read {X : Square 𝕜 n} (h : DiagonalBlocks b X) : X = pack e (fun i => readBlock e X i i) := by
  ext i j; obtain ⟨⟨a,i⟩,rfl⟩ := e.surjective i; obtain ⟨⟨b,j⟩,rfl⟩ := e.surjective j
  simp only [pack_entry]; split
  · rename_i eq; subst j; rfl
  · apply h; simp only [← he,Equiv.symm_apply_apply,ne_eq,Fin.val_eq_val]; assumption
include he in
lemma packed (X : Square 𝕜 n) : DiagonalBlocks b X ∧ IsU X ↔ ∃ B, (∀ i, IsU (B i)) ∧ X = pack e B := by
  constructor
  · rintro ⟨h,u⟩; have eq := pack_read e he h; exact ⟨_,(pack_unitary e _).1 (eq ▸ u),eq⟩
  · rintro ⟨B,u,rfl⟩; exact ⟨pack_supported e he B,(pack_unitary e B).2 u⟩

lemma read_mul (A B : Square 𝕜 n) (i j : Fin k) : readBlock e (A*B) i j = ∑ l, readBlock e A i l * readBlock e B l j := by
  ext a b
  simp only [readBlock,submatrix_apply,Matrix.mul_apply,Matrix.sum_apply]
  rw [← e.sum_comp, Fintype.sum_prod_type,Finset.sum_comm]
@[simp] lemma read_pack (B : Fin k → Square 𝕜 b) (i j) : readBlock e (pack e B) i j = if i=j then B i else 0 := by
  ext; by_cases h : i=j <;> simp [readBlock,h]

@[simp] lemma read_star (A : Square 𝕜 n) (i j : Fin k) : readBlock e Aᴴ i j = (readBlock e A j i)ᴴ := rfl
@[simp] lemma read_one (i j : Fin k) : readBlock e (1 : Square 𝕜 n) i j = if i=j then 1 else 0 := by simpa only [map_one,Pi.one_apply] using read_pack (𝕜 := 𝕜) e 1 i j
lemma read_cross (B : Fin k → Square 𝕜 b) (i j : Fin b) :
    readBlock ((Equiv.prodComm ..).trans e) (pack e B) i j = diagonal (fun a => B a i j) := by
  ext a b; exact pack_entry e B (i,a) (j,b)
lemma unwire (σ : Equiv.Perm (Fin n)) (B : Fin k → Square 𝕜 b) :
    (perm 𝕜 σ)ᴴ * pack (e.trans σ) B * perm 𝕜 σ = pack e B := by ext; simp [perm_star,pack]
end GS.Isometric
