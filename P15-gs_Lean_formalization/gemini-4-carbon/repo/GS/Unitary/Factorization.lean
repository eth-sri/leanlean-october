module

public import GS.Core
public import GS.Unitary.Support
public import GS.Unitary.Permutations
public import GS.Unitary.GeometryAlgebra
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators

namespace GS.UnitaryGeometry
variable {n : ℕ}

def CBlockDiagonal (b : ℕ) (A : CMat n) : Prop :=
  CSupported (fun i : Fin n => i.val / b) A

def product3 (B₃ P₂ B₂ P₁ B₁ : CMat n) : CMat n :=
  B₃ * P₂ * B₂ * P₁ * B₁

def CInA2 (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧ A = product2 B₂ P B₁

def CInA2Unitary (b₁ b₂ : ℕ) (P A : CMat n) : Prop :=
  ∃ B₁ B₂, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    Unitary B₁ ∧ Unitary B₂ ∧ A = product2 B₂ P B₁

def CInA3 (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ A = product3 B₃ P₂ B₂ P₁ B₁

def CInA3Unitary (b₁ b₂ b₃ : ℕ) (P₁ P₂ A : CMat n) : Prop :=
  ∃ B₁ B₂ B₃, CBlockDiagonal b₁ B₁ ∧ CBlockDiagonal b₂ B₂ ∧
    CBlockDiagonal b₃ B₃ ∧ Unitary B₁ ∧ Unitary B₂ ∧ Unitary B₃ ∧
    A = product3 B₃ P₂ B₂ P₁ B₁

section RCLikeQR
variable {𝕂 : Type*} [RCLike 𝕂]

abbrev KMat (𝕂 : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) 𝕂
def KUni {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α 𝕂) : Prop :=
  Aᴴ * A = 1 ∧ A * Aᴴ = 1
def KSupported {α : Type*} (block : α → ℕ) (A : Matrix α α 𝕂) : Prop :=
  ∀ i j, block i ≠ block j → A i j = 0
def kPerm (σ : Equiv.Perm (Fin n)) : KMat 𝕂 n := fun i j => if i = σ j then 1 else 0

theorem kUnitary_of_left {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α 𝕂}
    (h : Aᴴ * A = 1) : KUni A := ⟨h, mul_eq_one_comm.mp h⟩

theorem kUnitary_mul {α : Type*} [Fintype α] [DecidableEq α] {A B : Matrix α α 𝕂}
    (hA : KUni A) (hB : KUni B) : KUni (A * B) :=
  ⟨by calc (A * B)ᴴ * (A * B) = Bᴴ * (Aᴴ * A) * B := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hA.1, Matrix.mul_one, hB.1],
   by calc (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by rw [hB.2, Matrix.mul_one, hA.2]⟩

theorem kUnitary_conj {α : Type*} [Fintype α] [DecidableEq α] {A : Matrix α α 𝕂}
    (hA : KUni A) : KUni Aᴴ := ⟨by simpa using hA.2, by simpa using hA.1⟩

theorem kUnitary_one {α : Type*} [Fintype α] [DecidableEq α] :
    KUni (1 : Matrix α α 𝕂) := ⟨by simp, by simp⟩

theorem kSupported_mul {α : Type*} [Fintype α] {b : α → ℕ} {A B : Matrix α α 𝕂}
    (hA : KSupported b A) (hB : KSupported b B) : KSupported b (A * B) := fun i j hij => by
  rw [Matrix.mul_apply]; refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : b i = b k
  · rw [hB k j (fun h => hij (hik.trans h)), mul_zero]
  · rw [hA i k hik, zero_mul]

theorem kSupported_conj {α : Type*} {b : α → ℕ} {A : Matrix α α 𝕂}
    (hA : KSupported b A) : KSupported b Aᴴ := fun i j hij => by
  simp [Matrix.conjTranspose_apply, hA j i hij.symm]

theorem kSupported_one {α : Type*} [DecidableEq α] {b : α → ℕ} :
    KSupported b (1 : Matrix α α 𝕂) := fun i j hij => by
  simp [show i ≠ j from fun h => hij (congrArg b h)]

@[simp] theorem kPerm_mul_apply (σ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) (i j : Fin n) :
    (kPerm (𝕂 := 𝕂) σ * A) i j = A (σ.symm i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm i)]
  · simp [kPerm]
  · intro k _ hk; simp [kPerm, show i ≠ σ k from fun h => hk (by simpa using (congrArg σ.symm h).symm)]
  · simp

@[simp] theorem mul_kPerm_apply (A : KMat 𝕂 n) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (A * kPerm (𝕂 := 𝕂) σ) i j = A i (σ j) := by simp [Matrix.mul_apply, kPerm]

@[simp] theorem kPerm_conj (σ : Equiv.Perm (Fin n)) :
    (kPerm (𝕂 := 𝕂) σ)ᴴ = kPerm σ.symm := by
  ext i j
  simp [kPerm, Matrix.conjTranspose_apply,
    show (j = σ i ↔ i = σ.symm j) from ⟨fun h => by simpa using (congrArg σ.symm h).symm,
      fun h => by simpa using (congrArg σ h).symm⟩]

theorem kPerm_unitary (σ : Equiv.Perm (Fin n)) : KUni (kPerm (𝕂 := 𝕂) σ) := by
  refine kUnitary_of_left ?_; ext i j; simp [kPerm_conj, kPerm, Matrix.one_apply]

private theorem kPerm_trans (σ τ : Equiv.Perm (Fin n)) :
    kPerm (𝕂 := 𝕂) (σ.trans τ) = kPerm τ * kPerm σ := by
  ext i j; rw [kPerm_mul_apply]
  by_cases h : i = τ (σ j)
  · subst i; simp [kPerm]
  · simp [kPerm, h, show τ.symm i ≠ σ j from fun hh => h (by simpa using congrArg τ hh)]

private theorem kUnitary_det_ne_zero {Q : KMat 𝕂 n} (hQ : KUni Q) : Q.det ≠ 0 := by
  intro hz; have h := congrArg Matrix.det hQ.1
  simp [Matrix.det_mul, Matrix.det_conjTranspose, hz] at h

private theorem kUnitary_tri_supported {b : Fin n → ℕ} {U : KMat 𝕂 n}
    (hU : KUni U) (ht : U.BlockTriangular b) : KSupported b U := by
  let : Invertible U := ⟨Uᴴ, hU.1, hU.2⟩
  have hi := Matrix.blockTriangular_inv_of_blockTriangular ht
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa [Matrix.conjTranspose_apply] using hi (i := j) (j := i) hlt
  · exact ht hgt

private theorem kSupported_inv {b : Fin n → ℕ} {A : KMat 𝕂 n}
    (hA : KSupported b A) [Invertible A] : KSupported b A⁻¹ := by
  have hi := Matrix.blockTriangular_inv_of_blockTriangular (M := A) (b := b)
    (fun i j h => hA i j h.ne')
  have hit := Matrix.blockTriangular_inv_of_blockTriangular (M := Aᴴ) (b := b)
    (fun i j h => kSupported_conj hA i j h.ne')
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · simpa [← Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_apply] using hit (i := j) (j := i) hlt
  · exact hi hgt

private theorem exists_kqr (A : KMat 𝕂 n) :
    ∃ V R : KMat 𝕂 n, KUni V ∧ R.BlockTriangular Fin.val ∧ A = V * R := by
  let e₀ : OrthonormalBasis (Fin n) 𝕂 (EuclideanSpace 𝕂 (Fin n)) :=
    EuclideanSpace.basisFun (Fin n) 𝕂
  let f : Fin n → EuclideanSpace 𝕂 (Fin n) := fun j => ∑ k, A k j • e₀ k
  have hdim : Module.finrank 𝕂 (EuclideanSpace 𝕂 (Fin n)) = Fintype.card (Fin n) := by simp
  let e := gramSchmidtOrthonormalBasis hdim f
  let V : KMat 𝕂 n := fun i j => ⟪e₀ i, e j⟫_𝕂
  let R : KMat 𝕂 n := fun i j => ⟪e i, f j⟫_𝕂
  refine ⟨V, R, kUnitary_of_left ?_, fun i j hij =>
    gramSchmidtOrthonormalBasis_inv_triangular hdim f hij, ?_⟩
  · ext i j
    calc (Vᴴ * V) i j = ∑ k, ⟪e i, e₀ k⟫_𝕂 * ⟪e₀ k, e j⟫_𝕂 := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [← inner_conj_symm (e i) (e₀ k)]; rfl
      _ = ⟪e i, e j⟫_𝕂 := e₀.sum_inner_mul_inner _ _
      _ = (1 : KMat 𝕂 n) i j := by simpa [Matrix.one_apply] using orthonormal_iff_ite.mp e.orthonormal i j
  · ext i j
    have hc : ⟪e₀ i, f j⟫_𝕂 = A i j := by
      simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
    exact hc.symm.trans (e.sum_inner_mul_inner _ _).symm

private theorem upper_supp_of_gram {b : Fin n → ℕ} {R : KMat 𝕂 n}
    (ht : R.BlockTriangular Fin.val) (hd : R.det ≠ 0)
    (hg : KSupported b (Rᴴ * R)) : KSupported b R := by
  have hdiag (i : Fin n) : R i i ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular fun j k h => ht h] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)
  have hrows : ∀ m (i : Fin n), i.val = m → ∀ j, b i ≠ b j → R i j = 0 := by
    intro m; induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him j hij
      have hsum : (Rᴴ * R) i j = star (R i i) * R i j := by
        rw [Matrix.mul_apply]; refine Finset.sum_eq_single i (fun k _ hki => ?_) (by simp)
        by_cases hlt : k.val < i.val
        · by_cases hbi : b k = b i
          · rw [ih k.val (him ▸ hlt) k rfl j (hbi.symm ▸ hij), mul_zero]
          · rw [Matrix.conjTranspose_apply, ih k.val (him ▸ hlt) k rfl i hbi, star_zero, zero_mul]
        · rw [Matrix.conjTranspose_apply, ht (lt_of_le_of_ne (not_lt.mp hlt) (Fin.val_ne_of_ne hki).symm),
            star_zero, zero_mul]
      exact (mul_eq_zero.mp (hsum.symm.trans (hg i j hij))).resolve_left (star_ne_zero.mpr (hdiag i))
  exact fun i j hij => hrows i.val i rfl j hij

private theorem kStructuredQR (b : Fin n → ℕ) (B : KMat 𝕂 n) (σ : Equiv.Perm (Fin n))
    (hB : KSupported b B) (hdB : IsUnit B.det) :
    ∃ U R : KMat 𝕂 n, KSupported b U ∧ KUni U ∧ R.BlockTriangular Fin.val ∧
      B * kPerm σ = U * kPerm σ * R := by
  let P := kPerm (𝕂 := 𝕂) σ
  have hp := kPerm_unitary (𝕂 := 𝕂) σ
  obtain ⟨V, R, hV, ht, hqr⟩ := exists_kqr (B * P)
  have hr : R.det ≠ 0 := fun hz => mul_ne_zero (isUnit_iff_ne_zero.mp hdB) (kUnitary_det_ne_zero hp)
    (by simpa [Matrix.det_mul, hz] using congrArg Matrix.det hqr)
  let : Invertible R := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᴴ * R = Pᴴ * Bᴴ * B * P := by
    calc Rᴴ * R = (V * R)ᴴ * (V * R) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]; rw [← Matrix.mul_assoc Vᴴ V R, hV.1, Matrix.one_mul]
      _ = Pᴴ * Bᴴ * B * P := by rw [← hqr]; simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hs : KSupported (fun i => b (σ i)) R := upper_supp_of_gram ht hr <| by
    rw [hgram]; intro i j hij
    have he : (Pᴴ * (Bᴴ * B) * P) i j = (Bᴴ * B) (σ i) (σ j) := by
      simp [P, mul_kPerm_apply, kPerm_conj, kPerm_mul_apply]
    rw [show Pᴴ * Bᴴ * B * P = Pᴴ * (Bᴴ * B) * P by simp [Matrix.mul_assoc], he]
    exact kSupported_mul (kSupported_conj hB) hB _ _ hij
  have hback : KSupported b (P * R⁻¹ * Pᴴ) := fun i j hij => by
    simp only [P, mul_kPerm_apply, kPerm_conj, kPerm_mul_apply]
    exact kSupported_inv hs _ _ (by simpa using hij)
  have hu : V * Pᴴ = B * (P * R⁻¹ * Pᴴ) := by
    calc V * Pᴴ = V * (R * R⁻¹) * Pᴴ := by simp
      _ = B * (P * R⁻¹ * Pᴴ) := by rw [← Matrix.mul_assoc V R, ← hqr]; simp [Matrix.mul_assoc]
  exact ⟨V * Pᴴ, R, hu ▸ kSupported_mul hB hback, kUnitary_mul hV (kUnitary_conj hp), ht,
    by calc B * P = V * R := hqr
         _ = V * (Pᴴ * P) * R := by rw [hp.1, Matrix.mul_one]
         _ = V * Pᴴ * P * R := by simp [Matrix.mul_assoc]⟩

private def revPerm (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨n - 1 - i.val, by omega⟩
  invFun i := ⟨n - 1 - i.val, by omega⟩
  left_inv i := by ext; dsimp; omega
  right_inv i := by ext; dsimp; omega

private theorem kStructuredRQ (b : Fin n → ℕ) (B : KMat 𝕂 n) (σ : Equiv.Perm (Fin n))
    (hB : KSupported b B) (hdB : IsUnit B.det) :
    ∃ U R : KMat 𝕂 n, KSupported b U ∧ KUni U ∧ R.BlockTriangular Fin.val ∧
      kPerm σ * B = R * kPerm σ * U := by
  let ρ := revPerm n
  let P := kPerm (𝕂 := 𝕂) σ
  let J := kPerm (𝕂 := 𝕂) ρ
  have hdB' : IsUnit Bᴴ.det := isUnit_iff_ne_zero.mpr <| by
    simpa [Matrix.det_conjTranspose] using isUnit_iff_ne_zero.mp hdB
  obtain ⟨V, T, hV, hoV, ht, he⟩ := kStructuredQR b Bᴴ (ρ.trans σ.symm) (kSupported_conj hB) hdB'
  have hτ : kPerm (𝕂 := 𝕂) (ρ.trans σ.symm) = Pᴴ * J := by
    simpa [P, J] using kPerm_trans (𝕂 := 𝕂) ρ σ.symm
  refine ⟨Vᴴ, J * Tᴴ * Jᴴ, kSupported_conj hV, kUnitary_conj hoV, fun i j hij => ?_, ?_⟩
  · simp only [J, kPerm_conj, mul_kPerm_apply, kPerm_mul_apply,
      Matrix.conjTranspose_apply, star_eq_zero]
    apply ht
    change n - 1 - i.val < n - 1 - j.val
    change j.val < i.val at hij
    omega
  · have hh := congrArg (fun X : KMat 𝕂 n => J * Xᴴ) he
    rw [hτ] at hh
    have hJJ : J * Jᴴ = 1 := (kPerm_unitary (𝕂 := 𝕂) ρ).2
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← Matrix.mul_assoc, hJJ, Matrix.one_mul] using hh

theorem kThreeFactor (b₁ b₂ b₃ : ℕ) (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) :
    ((∃ B₁ B₂ B₃, KSupported (·.val / b₁) B₁ ∧ KSupported (·.val / b₂) B₂ ∧
      KSupported (·.val / b₃) B₃ ∧ A = B₃ * kPerm σ₂ * B₂ * kPerm σ₁ * B₁) ∧ KUni A) ↔
    (∃ B₁ B₂ B₃, KSupported (·.val / b₁) B₁ ∧ KSupported (·.val / b₂) B₂ ∧
      KSupported (·.val / b₃) B₃ ∧ KUni B₁ ∧ KUni B₂ ∧ KUni B₃ ∧
      A = B₃ * kPerm σ₂ * B₂ * kPerm σ₁ * B₁) := by
  let P₁ := kPerm (𝕂 := 𝕂) σ₁; let P₂ := kPerm (𝕂 := 𝕂) σ₂
  have hp₁ := kPerm_unitary (𝕂 := 𝕂) σ₁; have hp₂ := kPerm_unitary (𝕂 := 𝕂) σ₂
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, rfl⟩, hA⟩
    have hprod : (B₃ * P₂ * B₂ * P₁ * B₁).det ≠ 0 := kUnitary_det_ne_zero hA
    simp only [Matrix.det_mul] at hprod
    have hd₁ : IsUnit B₁.det := isUnit_iff_ne_zero.mpr fun hz => hprod (by simp [hz])
    have hd₃ : IsUnit B₃.det := isUnit_iff_ne_zero.mpr fun hz => hprod (by simp [hz])
    obtain ⟨U₃, R₃, hu₃, ho₃, ht₃, eq₃⟩ := kStructuredQR (·.val / b₃) B₃ σ₂ hb₃ hd₃
    obtain ⟨U₁, R₁, hu₁, ho₁, ht₁, eq₁⟩ := kStructuredRQ (·.val / b₁) B₁ σ₁ hb₁ hd₁
    let U₂ := R₃ * B₂ * R₁
    have he : B₃ * P₂ * B₂ * P₁ * B₁ = U₃ * P₂ * U₂ * P₁ * U₁ := by
      calc B₃ * P₂ * B₂ * P₁ * B₁ = (B₃ * P₂) * B₂ * (P₁ * B₁) := by simp [Matrix.mul_assoc]
        _ = U₃ * P₂ * U₂ * P₁ * U₁ := by dsimp [P₁, P₂] at *; rw [eq₃, eq₁]; simp [U₂, Matrix.mul_assoc]
    have hU₂_eq : U₂ = P₂ᴴ * U₃ᴴ * (B₃ * P₂ * B₂ * P₁ * B₁) * U₁ᴴ * P₁ᴴ := by
      symm
      calc P₂ᴴ * U₃ᴴ * (B₃ * P₂ * B₂ * P₁ * B₁) * U₁ᴴ * P₁ᴴ
        _ = (P₂ᴴ * (U₃ᴴ * U₃) * P₂) * U₂ * (P₁ * (U₁ * U₁ᴴ) * P₁ᴴ) := by
          rw [he]; simp only [Matrix.mul_assoc]
        _ = U₂ := by rw [ho₃.1, ho₁.2, Matrix.mul_one, Matrix.mul_one, hp₂.1, hp₁.2, Matrix.one_mul, Matrix.mul_one]
    have ho₂ : KUni U₂ := hU₂_eq ▸ kUnitary_mul
      (kUnitary_mul (kUnitary_mul (kUnitary_mul (kUnitary_conj hp₂) (kUnitary_conj ho₃)) hA) (kUnitary_conj ho₁))
      (kUnitary_conj hp₁)
    have hup {R : KMat 𝕂 n} (h : R.BlockTriangular Fin.val) : R.BlockTriangular (·.val / b₂) :=
      fun i j hij => h (lt_of_not_ge fun hle => (not_lt_of_ge (Nat.div_le_div_right hle)) hij)
    have ht₂ : U₂.BlockTriangular (·.val / b₂) :=
      ((hup ht₃).mul (fun i j h => hb₂ i j h.ne')).mul (hup ht₁)
    exact ⟨U₁, U₂, U₃, hu₁, kUnitary_tri_supported ho₂ ht₂, hu₃, ho₁, ho₂, ho₃, he⟩
  · rintro ⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, hu₁, hu₂, hu₃, rfl⟩
    exact ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, rfl⟩,
      kUnitary_mul (kUnitary_mul (kUnitary_mul (kUnitary_mul hu₃ hp₂) hu₂) hp₁) hu₁⟩

theorem kTwoFactor (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : KMat 𝕂 n) :
    ((∃ B₁ B₂, KSupported (·.val / b₁) B₁ ∧ KSupported (·.val / b₂) B₂ ∧
      A = B₂ * kPerm σ * B₁) ∧ KUni A) ↔
    (∃ B₁ B₂, KSupported (·.val / b₁) B₁ ∧ KSupported (·.val / b₂) B₂ ∧
      KUni B₁ ∧ KUni B₂ ∧ A = B₂ * kPerm σ * B₁) := by
  have hI : kPerm (𝕂 := 𝕂) (Equiv.refl (Fin n)) = 1 := by ext i j; simp [kPerm, Matrix.one_apply]
  constructor
  · rintro ⟨⟨B₁, B₂, hb₁, hb₂, he⟩, hA⟩
    obtain ⟨U₁, U₂, U₃, hu₁, hu₂, hu₃, ho₁, ho₂, ho₃, hp⟩ :=
      (kThreeFactor b₁ b₂ 1 σ (Equiv.refl _) A).mp
        ⟨⟨B₁, B₂, 1, hb₁, hb₂, kSupported_one, by simpa [hI] using he⟩, hA⟩
    have hu₃' : KSupported (·.val / b₂) U₃ := fun i j hij =>
      hu₃ i j (by simp only [Nat.div_one]; exact fun h => hij (congrArg (·.val / b₂) (Fin.ext h)))
    exact ⟨U₁, U₃ * U₂, hu₁, kSupported_mul hu₃' hu₂, ho₁, kUnitary_mul ho₃ ho₂,
      by simpa [hI, Matrix.mul_assoc] using hp⟩
  · rintro ⟨B₁, B₂, hb₁, hb₂, ho₁, ho₂, rfl⟩
    exact ⟨⟨B₁, B₂, hb₁, hb₂, rfl⟩, kUnitary_mul (kUnitary_mul ho₂ (kPerm_unitary σ)) ho₁⟩

end RCLikeQR

theorem threeFactorUnitarization (b₁ b₂ b₃ : ℕ)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA3 b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A ∧ Unitary A ↔
      CInA3Unitary b₁ b₂ b₃ (cPermMatrix σ₁) (cPermMatrix σ₂) A :=
  kThreeFactor (𝕂 := ℂ) b₁ b₂ b₃ σ₁ σ₂ A

theorem twoFactorUnitarization (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : CMat n) :
    CInA2 b₁ b₂ (cPermMatrix σ) A ∧ Unitary A ↔
      CInA2Unitary b₁ b₂ (cPermMatrix σ) A :=
  kTwoFactor (𝕂 := ℂ) b₁ b₂ σ A

@[simp] theorem kUnitary_real_iff {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) :
    KUni A ↔ GS.Orthogonal A := by
  simp [KUni, GS.Orthogonal]

@[simp] theorem kPerm_real_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    kPerm (𝕂 := ℝ) σ = GS.permMatrix σ := rfl

end GS.UnitaryGeometry

namespace GS.Extensions
open GS.UnitaryGeometry

theorem threeFactorOrthogonalization (n : ℕ) (s₁ s₂ s₃ : GS.BlockSpec n)
    (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA3 s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A ∧ GS.Orthogonal A ↔
      GS.InA3Orth s₁.size s₂.size s₃.size (GS.permMatrix σ₁) (GS.permMatrix σ₂) A := by
  simpa only [GS.InA3, GS.InA3Orth, GS.BlockDiagonal, GS.Supported, GS.product3,
    KSupported, kPerm_real_eq, kUnitary_real_iff] using
    kThreeFactor (𝕂 := ℝ) s₁.size s₂.size s₃.size σ₁ σ₂ A

theorem twoFactorOrthogonalization (n : ℕ) (s₁ s₂ : GS.BlockSpec n)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 s₁.size s₂.size (GS.permMatrix σ) A ∧ GS.Orthogonal A ↔
      GS.InA2Orth s₁.size s₂.size (GS.permMatrix σ) A := by
  simpa only [GS.InA2, GS.InA2Orth, GS.BlockDiagonal, GS.Supported, GS.product2,
    KSupported, kPerm_real_eq, kUnitary_real_iff] using
    kTwoFactor (𝕂 := ℝ) s₁.size s₂.size σ A

end GS.Extensions
