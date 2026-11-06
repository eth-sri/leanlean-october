module

public import GS.Core
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators

namespace GS.UnitaryGeometry

variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

def product2 {n : ℕ} (B₂ P B₁ : CMat n) : CMat n := B₂ * P * B₁

def CSupported (block : Fin n → ℕ) (A : CMat n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

def cPermMatrix (σ : Equiv.Perm (Fin n)) : CMat n :=
  fun i j => if i = σ j then 1 else 0

theorem skewHermitian_zero : IsSkewHermitian (0 : CMat n) := by simp [IsSkewHermitian]

theorem skewHermitian_add {A B : CMat n}
    (hA : IsSkewHermitian A) (hB : IsSkewHermitian B) :
    IsSkewHermitian (A + B) := by
  change Aᴴ = -A at hA; change Bᴴ = -B at hB
  simp only [IsSkewHermitian, Matrix.conjTranspose_add, hA, hB, neg_add]

theorem skewHermitian_real_smul (a : ℝ) {A : CMat n}
    (hA : IsSkewHermitian A) : IsSkewHermitian (a • A) := by
  change Aᴴ = -A at hA
  simp only [IsSkewHermitian, Matrix.conjTranspose_smul, star_trivial, hA, smul_neg]

def supportedSkewSpace (block : Fin n → ℕ) : Submodule ℝ (CMat n) where
  carrier := {A | CSupported block A ∧ IsSkewHermitian A}
  zero_mem' := ⟨fun _ _ _ => rfl, skewHermitian_zero⟩
  add_mem' := fun ⟨hsA, hkA⟩ ⟨hsB, hkB⟩ => ⟨fun i j hij => by simp [hsA i j hij, hsB i j hij], skewHermitian_add hkA hkB⟩
  smul_mem' := fun a _ ⟨hsA, hkA⟩ => ⟨fun i j hij => by simp [hsA i j hij], skewHermitian_real_smul a hkA⟩

theorem conjugate_skewHermitian (B C : CMat n) (hC : IsSkewHermitian C) :
    IsSkewHermitian (B * C * Bᴴ) := by
  unfold IsSkewHermitian at *
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hC, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

abbrev KMat (𝕂 : Type) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕂

def IsUnitary (A : KMat 𝕂 n) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace IsUnitary
variable {A B : KMat 𝕂 n}
theorem conjTranspose (h : IsUnitary A) : IsUnitary Aᴴ := ⟨by simpa using h.2, by simpa using h.1⟩
theorem mul (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1],
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.mul_assoc]
        _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]⟩
end IsUnitary

def KSupported (block : Fin n → ℕ) (A : KMat 𝕂 n) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0

namespace KSupported
variable {block : Fin n → ℕ} {A B : KMat 𝕂 n}
theorem one : KSupported block (1 : KMat 𝕂 n) := by
  intro i j hij; have hne : i ≠ j := fun h => hij (congrArg block h); simp [Matrix.one_apply, hne]
theorem conjTranspose (h : KSupported block A) : KSupported block Aᴴ :=
  fun i j hij => by simp [Matrix.conjTranspose_apply, h j i (Ne.symm hij)]
theorem mul (hA : KSupported block A) (hB : KSupported block B) : KSupported block (A * B) := by
  intro i j hij; rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : block i = block k
  · rw [hB k j (fun h => hij (hik.trans h)), mul_zero]
  · rw [hA i k hik, zero_mul]
end KSupported

def kPermMatrix (𝕂 : Type) [RCLike 𝕂] (σ : Equiv.Perm (Fin n)) : KMat 𝕂 n :=
  fun i j => if i = σ j then 1 else 0

@[simp] theorem kPerm_conjTranspose (σ : Equiv.Perm (Fin n)) :
    (kPermMatrix 𝕂 σ)ᴴ = kPermMatrix 𝕂 σ.symm := by
  ext i j; simp [kPermMatrix, Matrix.conjTranspose_apply, σ.eq_symm_apply, eq_comm]

theorem kPerm_unitary (σ : Equiv.Perm (Fin n)) : IsUnitary (kPermMatrix 𝕂 σ) := by
  have h : (kPermMatrix 𝕂 σ)ᴴ * kPermMatrix 𝕂 σ = 1 := by
    ext i j; simp [kPermMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  exact ⟨h, mul_eq_one_comm.mp h⟩

theorem kPerm_conjugate_apply (σ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) (i j : Fin n) :
    (kPermMatrix 𝕂 σ * A * (kPermMatrix 𝕂 σ)ᴴ) i j = A (σ.symm i) (σ.symm j) := by
  simp only [kPermMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, ← σ.symm_apply_eq]
  simp

theorem kSupported_perm_back {block : Fin n → ℕ} (σ : Equiv.Perm (Fin n))
    {R : KMat 𝕂 n} (hR : KSupported (fun i => block (σ i)) R) :
    KSupported block (kPermMatrix 𝕂 σ * R * (kPermMatrix 𝕂 σ)ᴴ) := by
  intro i j hij; rw [kPerm_conjugate_apply]
  exact hR _ _ (by simpa only [Equiv.apply_symm_apply] using hij)

theorem kPermuted_gram_supported {block : Fin n → ℕ} {B : KMat 𝕂 n}
    (hB : KSupported block B) (σ : Equiv.Perm (Fin n)) :
    KSupported (fun i => block (σ i)) ((kPermMatrix 𝕂 σ)ᴴ * Bᴴ * B * kPermMatrix 𝕂 σ) := by
  have hh : KSupported block (Bᴴ * B) := hB.conjTranspose.mul hB
  intro i j hij
  have he : ((kPermMatrix 𝕂 σ)ᴴ * Bᴴ * B * kPermMatrix 𝕂 σ) i j = (Bᴴ * B) (σ i) (σ j) := by
    rw [kPerm_conjTranspose]
    simpa only [Matrix.mul_assoc, kPerm_conjTranspose, Equiv.symm_symm] using
      kPerm_conjugate_apply σ.symm (Bᴴ * B) i j
  rw [he]; exact hh _ _ hij

theorem kPerm_trans_matrix (σ τ : Equiv.Perm (Fin n)) :
    kPermMatrix 𝕂 (σ.trans τ) = kPermMatrix 𝕂 τ * kPermMatrix 𝕂 σ := by
  ext i j
  simp only [kPermMatrix, Matrix.mul_apply, Equiv.trans_apply, ← τ.symm_apply_eq]
  simp

@[simp] theorem kPerm_refl : kPermMatrix 𝕂 (Equiv.refl (Fin n)) = 1 := by
  ext i j; simp [kPermMatrix, Matrix.one_apply]

def KUpper (A : KMat 𝕂 n) : Prop := A.BlockTriangular (fun i => i.val)

theorem kSupported_blockTriangular {block : Fin n → ℕ} {A : KMat 𝕂 n}
    (h : KSupported block A) : A.BlockTriangular block :=
  fun i j hij => h i j (Ne.symm (Nat.ne_of_lt hij))

theorem kUpper_blockTriangular {b : ℕ} {A : KMat 𝕂 n} (h : KUpper A) :
    A.BlockTriangular (fun i : Fin n => i.val / b) := by
  intro i j hij
  apply h
  by_contra hn
  exact (not_lt_of_ge (Nat.div_le_div_right (Nat.le_of_not_gt hn))) hij

theorem unitary_blockTriangular_supported {block : Fin n → ℕ} {U : KMat 𝕂 n}
    (hU : IsUnitary U) (htri : U.BlockTriangular block) : KSupported block U := by
  letI : Invertible U := { invOf := Uᴴ, invOf_mul_self := hU.1, mul_invOf_self := hU.2 }
  have hi : U⁻¹.BlockTriangular block := Matrix.blockTriangular_inv_of_blockTriangular htri
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa only [Matrix.conjTranspose_apply, star_eq_zero] using hi (i := j) (j := i) hlt
  · exact htri hgt

theorem kSupported_inverse {block : Fin n → ℕ} {A : KMat 𝕂 n}
    (hA : KSupported block A) [Invertible A] : KSupported block A⁻¹ := by
  have hi := Matrix.blockTriangular_inv_of_blockTriangular (kSupported_blockTriangular hA)
  have hit := Matrix.blockTriangular_inv_of_blockTriangular (kSupported_blockTriangular hA.conjTranspose)
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa only [← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply, star_eq_zero] using
      hit (i := j) (j := i) hlt
  · exact hi hgt

theorem unitary_det_ne_zero {Q : KMat 𝕂 n} (hQ : IsUnitary Q) : Q.det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det hQ.1
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hz] at h

theorem exists_ordinary_qr (A : KMat 𝕂 n) :
    ∃ V R : KMat 𝕂 n, IsUnitary V ∧ KUpper R ∧ A = V * R := by
  let e₀ : OrthonormalBasis (Fin n) 𝕂 (EuclideanSpace 𝕂 (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) 𝕂
  let f : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hdim : Module.finrank 𝕂 (EuclideanSpace 𝕂 (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  let V : KMat 𝕂 n := fun i j => ⟪e₀ i, e j⟫_𝕂
  let R : KMat 𝕂 n := fun i j => ⟪e i, f j⟫_𝕂
  have hv : Vᴴ * V = 1 := by
    ext i j
    calc (Vᴴ * V) i j = ∑ k, ⟪e i, e₀ k⟫_𝕂 * ⟪e₀ k, e j⟫_𝕂 := by
          change (∑ k, star (inner 𝕂 (e₀ k) (e i)) * inner 𝕂 (e₀ k) (e j)) = _
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← inner_conj_symm (e i) (e₀ k), RCLike.star_def]
      _ = ⟪e i, e j⟫_𝕂 := e₀.sum_inner_mul_inner _ _
      _ = (1 : KMat 𝕂 n) i j := by
          simpa only [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  have ht : KUpper R := fun i j hij => gramSchmidtOrthonormalBasis_inv_triangular hdim f hij
  refine ⟨V, R, ⟨hv, mul_eq_one_comm.mp hv⟩, ht, ?_⟩
  ext i j
  calc A i j = ⟪e₀ i, f j⟫_𝕂 := by
        symm; simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
    _ = ∑ k, ⟪e₀ i, e k⟫_𝕂 * ⟪e k, f j⟫_𝕂 := (e.sum_inner_mul_inner _ _).symm
    _ = (V * R) i j := rfl

theorem upper_diagonal_ne_zero {R : KMat 𝕂 n} (ht : KUpper R) (hd : R.det ≠ 0)
    (i : Fin n) : R i i ≠ 0 := by
  have hdet : R.det = ∏ j, R j j := Matrix.det_of_upperTriangular (fun j k hjk => ht hjk)
  rw [hdet] at hd
  exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)

theorem upper_supported_of_gram {block : Fin n → ℕ} {R : KMat 𝕂 n}
    (ht : KUpper R) (hd : ∀ i, R i i ≠ 0)
    (hg : KSupported block (Rᴴ * R)) : KSupported block R := by
  have hrows : ∀ m : ℕ, ∀ i : Fin n, i.val = m →
      ∀ j : Fin n, block i ≠ block j → R i j = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him j hij
      have hsum : (Rᴴ * R) i j = star (R i i) * R i j := by
        rw [Matrix.mul_apply]
        change (∑ k : Fin n, star (R k i) * R k j) = star (R i i) * R i j
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_cases hlt : k.val < i.val
          · by_cases hbi : block k = block i
            · rw [ih k.val (by omega) k rfl j (by simpa only [hbi] using hij), mul_zero]
            · rw [ih k.val (by omega) k rfl i hbi, star_zero, zero_mul]
          · have hgt : i.val < k.val := by
              have hv : k.val ≠ i.val := fun he => hki (Fin.ext he)
              omega
            rw [ht hgt, star_zero, zero_mul]
        · intro hn; exact False.elim (hn (Finset.mem_univ i))
      have he : star (R i i) * R i j = 0 := hsum.symm.trans (hg i j hij)
      exact (mul_eq_zero.mp he).resolve_left (by simpa using hd i)
  exact fun i j hij => hrows i.val i rfl j hij

theorem structuredQR (block : Fin n → ℕ) (B : KMat 𝕂 n) (σ : Equiv.Perm (Fin n))
    (hB : KSupported block B) (hdetB : IsUnit B.det) :
    ∃ U R : KMat 𝕂 n, KSupported block U ∧ IsUnitary U ∧ KUpper R ∧
      B * kPermMatrix 𝕂 σ = U * kPermMatrix 𝕂 σ * R := by
  obtain ⟨V, R, hV, ht, hqr⟩ := exists_ordinary_qr (B * kPermMatrix 𝕂 σ)
  let P := kPermMatrix 𝕂 σ
  have hp : IsUnitary P := kPerm_unitary σ
  have hb : B.det ≠ 0 := isUnit_iff_ne_zero.mp hdetB
  have hr : R.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hqr
    exact mul_ne_zero hb (unitary_det_ne_zero hp)
      (by simpa only [Matrix.det_mul, hz, mul_zero] using hh)
  letI : Invertible R := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᴴ * R = Pᴴ * Bᴴ * B * P := by
    calc Rᴴ * R = (V * R)ᴴ * (V * R) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Vᴴ V R, hV.1]; simp
      _ = (B * P)ᴴ * (B * P) := by rw [← hqr]
      _ = Pᴴ * Bᴴ * B * P := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hs : KSupported (fun i : Fin n => block (σ i)) R := by
    apply upper_supported_of_gram ht (upper_diagonal_ne_zero ht hr)
    rw [hgram]; exact kPermuted_gram_supported hB σ
  have hback : KSupported block (P * R⁻¹ * Pᴴ) := kSupported_perm_back σ (kSupported_inverse hs)
  have hu : V * Pᴴ = B * (P * R⁻¹ * Pᴴ) := by
    calc V * Pᴴ = (V * (R * R⁻¹)) * Pᴴ := by simp
      _ = (B * P) * R⁻¹ * Pᴴ := by rw [← Matrix.mul_assoc V R, ← hqr]
      _ = B * (P * R⁻¹ * Pᴴ) := by simp only [Matrix.mul_assoc]
  refine ⟨V * Pᴴ, R, hu ▸ hB.mul hback, hV.mul hp.conjTranspose, ht, ?_⟩
  calc B * P = V * R := hqr
    _ = (V * Pᴴ) * P * R := by simp only [Matrix.mul_assoc, hp.1, Matrix.one_mul]

def cReverseIndex {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by omega⟩
theorem cReverseIndex_involutive (i : Fin n) : cReverseIndex (cReverseIndex i) = i := by
  ext; simp only [cReverseIndex]; omega
def cReversePerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun := cReverseIndex
  invFun := cReverseIndex
  left_inv := cReverseIndex_involutive
  right_inv := cReverseIndex_involutive

theorem upper_reverse_conjTranspose {T : KMat 𝕂 n} (ht : KUpper T) :
    KUpper (kPermMatrix 𝕂 (cReversePerm n) * Tᴴ * (kPermMatrix 𝕂 (cReversePerm n))ᴴ) := by
  intro i j hij
  change j.val < i.val at hij
  rw [kPerm_conjugate_apply]
  change star (T (cReverseIndex j) (cReverseIndex i)) = 0
  rw [ht (by change n - 1 - i.val < n - 1 - j.val; omega), star_zero]

theorem structuredRQ (block : Fin n → ℕ) (B : KMat 𝕂 n) (σ : Equiv.Perm (Fin n))
    (hB : KSupported block B) (hdetB : IsUnit B.det) :
    ∃ U R : KMat 𝕂 n, KSupported block U ∧ IsUnitary U ∧ KUpper R ∧
      kPermMatrix 𝕂 σ * B = R * kPermMatrix 𝕂 σ * U := by
  let ρ := cReversePerm n
  let P := kPermMatrix 𝕂 σ
  let J := kPermMatrix 𝕂 ρ
  let τ := ρ.trans σ.symm
  have hτ : kPermMatrix 𝕂 τ = Pᴴ * J := by
    simpa only [τ, P, J, kPerm_conjTranspose] using kPerm_trans_matrix (𝕂 := 𝕂) ρ σ.symm
  have hdt : IsUnit Bᴴ.det := isUnit_iff_ne_zero.mpr
    (by simpa only [Matrix.det_conjTranspose, star_ne_zero] using isUnit_iff_ne_zero.mp hdetB)
  obtain ⟨V, T, hV, hoV, ht, he⟩ := structuredQR block Bᴴ τ hB.conjTranspose hdt
  let U := Vᴴ
  let R := J * Tᴴ * Jᴴ
  have hJJ : J * Jᴴ = 1 := (kPerm_unitary ρ).2
  have hre : P * B = R * P * U := by
    have hh := congrArg (fun X : KMat 𝕂 n => J * Xᴴ) he
    rw [hτ] at hh
    simpa only [R, U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, hJJ, Matrix.one_mul] using hh
  exact ⟨U, R, hV.conjTranspose, hoV.conjTranspose, upper_reverse_conjTranspose ht, hre⟩

def KBlockDiagonal (b : ℕ) (A : KMat 𝕂 n) : Prop :=
  KSupported (fun i : Fin n => i.val / b) A

def kProduct3 (B₃ P₂ B₂ P₁ B₁ : KMat 𝕂 n) : KMat 𝕂 n := B₃ * P₂ * B₂ * P₁ * B₁

def KInA2 (b₁ b₂ : ℕ) (P A : KMat 𝕂 n) : Prop :=
  ∃ B₁ B₂, KBlockDiagonal b₁ B₁ ∧ KBlockDiagonal b₂ B₂ ∧ A = B₂ * P * B₁

def KInA2Unitary (b₁ b₂ : ℕ) (P A : KMat 𝕂 n) : Prop :=
  ∃ B₁ B₂, KBlockDiagonal b₁ B₁ ∧ KBlockDiagonal b₂ B₂ ∧
    IsUnitary B₁ ∧ IsUnitary B₂ ∧ A = B₂ * P * B₁

def KInA3 (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : KMat 𝕂 n) : Prop :=
  ∃ B₁ B₂ B₃, KBlockDiagonal b₁ B₁ ∧ KBlockDiagonal b₂ B₂ ∧
    KBlockDiagonal b₃ B₃ ∧ A = kProduct3 B₃ P₂ B₂ P₁ B₁

def KInA3Unitary (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : KMat 𝕂 n) : Prop :=
  ∃ B₁ B₂ B₃, KBlockDiagonal b₁ B₁ ∧ KBlockDiagonal b₂ B₂ ∧
    KBlockDiagonal b₃ B₃ ∧ IsUnitary B₁ ∧ IsUnitary B₂ ∧ IsUnitary B₃ ∧
    A = kProduct3 B₃ P₂ B₂ P₁ B₁

def CBlockDiagonal {n : ℕ} (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 {n : ℕ} (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2 {n : ℕ} (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    A = product2 B₂ P B₁

def CInA2Unitary {n : ℕ} (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3 {n : ℕ} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary {n : ℕ} (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

theorem middle_unitary_of_factorization {Q U₃ P₂ M P₁ U₁ : KMat 𝕂 n}
    (hQ : IsUnitary Q) (hU₃ : IsUnitary U₃) (hP₂ : IsUnitary P₂)
    (hP₁ : IsUnitary P₁) (hU₁ : IsUnitary U₁)
    (he : Q = U₃ * P₂ * M * P₁ * U₁) : IsUnitary M := by
  have hm : M = P₂ᴴ * U₃ᴴ * Q * U₁ᴴ * P₁ᴴ := by
    symm
    calc P₂ᴴ * U₃ᴴ * Q * U₁ᴴ * P₁ᴴ =
          (P₂ᴴ * (U₃ᴴ * U₃) * P₂) * M * (P₁ * (U₁ * U₁ᴴ) * P₁ᴴ) := by
            rw [he]; simp only [Matrix.mul_assoc]
      _ = M := by simp [hU₃.1, hU₁.2, hP₂.1, hP₁.2]
  rw [hm]
  exact (((hP₂.conjTranspose.mul hU₃.conjTranspose).mul hQ).mul
    hU₁.conjTranspose).mul hP₁.conjTranspose

theorem threeFactorUnitarization (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) :
    KInA3 b₁ b₂ b₃ (kPermMatrix 𝕂 σ₁) (kPermMatrix 𝕂 σ₂) A ∧ IsUnitary A ↔
      KInA3Unitary b₁ b₂ b₃ (kPermMatrix 𝕂 σ₁) (kPermMatrix 𝕂 σ₂) A := by
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, he⟩, hA⟩
    have hprod : B₃.det * (kPermMatrix 𝕂 σ₂).det * B₂.det *
        (kPermMatrix 𝕂 σ₁).det * B₁.det ≠ 0 := by
      simpa only [he, kProduct3, Matrix.det_mul] using unitary_det_ne_zero hA
    have hdet₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr fun hz => hprod (by simp [hz])
    have hdet₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr fun hz => hprod (by simp [hz])
    obtain ⟨U₃, R₃, hu₃, ho₃, ht₃, eq₃⟩ := structuredQR (fun i : Fin n => i.val / b₃) B₃ σ₂ hb₃ hdet₃
    obtain ⟨U₁, R₁, hu₁, ho₁, ht₁, eq₁⟩ := structuredRQ (fun i : Fin n => i.val / b₁) B₁ σ₁ hb₁ hdet₁
    let P₁ := kPermMatrix 𝕂 σ₁
    let P₂ := kPermMatrix 𝕂 σ₂
    let U₂ := R₃ * B₂ * R₁
    have he' : A = U₃ * P₂ * U₂ * P₁ * U₁ := by
      calc A = (B₃ * P₂) * B₂ * (P₁ * B₁) := by rw [he]; simp only [kProduct3, P₁, P₂, Matrix.mul_assoc]
        _ = (U₃ * P₂ * R₃) * B₂ * (R₁ * P₁ * U₁) := by rw [eq₃, eq₁]
        _ = U₃ * P₂ * U₂ * P₁ * U₁ := by simp only [U₂, Matrix.mul_assoc]
    have ho₂ : IsUnitary U₂ := middle_unitary_of_factorization hA ho₃
      (kPerm_unitary σ₂) (kPerm_unitary σ₁) ho₁ he'
    have ht₂ : U₂.BlockTriangular (fun i : Fin n => i.val / b₂) :=
      ((kUpper_blockTriangular ht₃).mul (kSupported_blockTriangular hb₂)).mul
        (kUpper_blockTriangular ht₁)
    exact ⟨U₁, U₂, U₃, hu₁, unitary_blockTriangular_supported ho₂ ht₂, hu₃, ho₁, ho₂, ho₃, he'⟩
  · rintro ⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, hu₁, hu₂, hu₃, rfl⟩
    exact ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, rfl⟩,
      (((hu₃.mul (kPerm_unitary σ₂)).mul hu₂).mul (kPerm_unitary σ₁)).mul hu₁⟩

theorem kSingleton_block_supported {A : KMat 𝕂 n}
    (hA : KBlockDiagonal 1 A) (block : Fin n → ℕ) : KSupported block A := by
  intro i j hij; apply hA; simp only [Nat.div_one]
  exact fun he => hij (congrArg block (Fin.ext he))

theorem twoFactorUnitarization (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) :
    KInA2 b₁ b₂ (kPermMatrix 𝕂 σ) A ∧ IsUnitary A ↔
      KInA2Unitary b₁ b₂ (kPermMatrix 𝕂 σ) A := by
  constructor
  · rintro ⟨⟨B₁, B₂, hb₁, hb₂, he⟩, hA⟩
    have hmem : KInA3 b₁ b₂ 1 (kPermMatrix 𝕂 σ) (kPermMatrix 𝕂 (Equiv.refl (Fin n))) A :=
      ⟨B₁, B₂, 1, hb₁, hb₂, KSupported.one, by simpa only [kProduct3, kPerm_refl, Matrix.one_mul] using he⟩
    obtain ⟨U₁, U₂, U₃, hu₁, hu₂, hu₃, ho₁, ho₂, ho₃, hprod⟩ :=
      (threeFactorUnitarization b₁ b₂ 1 σ (Equiv.refl _) A).mp ⟨hmem, hA⟩
    have hu₃' : KBlockDiagonal b₂ U₃ := kSingleton_block_supported hu₃ (fun i => i.val / b₂)
    refine ⟨U₁, U₃ * U₂, hu₁, hu₃'.mul hu₂, ho₁, ho₃.mul ho₂, ?_⟩
    simpa only [kProduct3, kPerm_refl, Matrix.mul_one, Matrix.mul_assoc] using hprod
  · rintro ⟨B₁, B₂, hb₁, hb₂, ho₁, ho₂, he⟩
    exact ⟨⟨B₁, B₂, hb₁, hb₂, he⟩, he ▸ (ho₂.mul (kPerm_unitary σ)).mul ho₁⟩

def ofRealMatrix {n : ℕ} (A : Mat n) : CMat n := A.map Complex.ofRealHom

@[simp] theorem ofRealMatrix_apply {n : ℕ} (A : Mat n) (i j : Fin n) :
    ofRealMatrix A i j = (A i j : ℂ) := rfl

@[simp] theorem ofRealMatrix_mul {n : ℕ} (A B : Mat n) :
    ofRealMatrix (A * B) = ofRealMatrix A * ofRealMatrix B := Matrix.map_mul

@[simp] theorem ofRealMatrix_one {n : ℕ} :
    ofRealMatrix (1 : Mat n) = 1 :=
  map_one (Complex.ofRealHom.mapMatrix : Mat n →+* CMat n)

@[simp] theorem ofRealMatrix_transpose {n : ℕ} (A : Mat n) :
    ofRealMatrix Aᵀ = (ofRealMatrix A)ᴴ := by
  ext i j; simp [ofRealMatrix, Matrix.conjTranspose_apply, Matrix.transpose_apply]

theorem ofRealMatrix_unitary {n : ℕ} {A : Mat n} (h : Orthogonal A) :
    Unitary (ofRealMatrix A) :=
  ⟨by simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using congrArg ofRealMatrix h.1,
   by simpa only [ofRealMatrix_mul, ofRealMatrix_transpose, ofRealMatrix_one] using congrArg ofRealMatrix h.2⟩

theorem ofRealMatrix_blockDiagonal {n b : ℕ} {A : Mat n}
    (h : BlockDiagonal b A) : CBlockDiagonal b (ofRealMatrix A) :=
  fun i j hij => by simp [h i j hij]

end GS.UnitaryGeometry
