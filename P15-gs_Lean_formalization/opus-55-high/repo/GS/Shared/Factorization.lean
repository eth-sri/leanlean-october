module

public import GS.Shared.Base
public import GS.UnitaryCS.ColumnGram

@[expose] public section

/-! Two- and three-factor unitary factorization over `RCLike 𝕜`: structured QR and RQ
supply supported unitary outer factors, and the middle factor is unitary and block
triangular, hence block diagonal. -/

noncomputable section
open Matrix
namespace GS.Shared
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- The permutation matrix with `P e_j = e_(σ j)`. -/
def perm (σ : Equiv.Perm (Fin n)) : 𝕄 := fun i j => if i = σ j then 1 else 0

@[simp] theorem mul_perm_apply (A : 𝕄) (σ : Equiv.Perm (Fin n)) (i j) :
    (A * perm σ : 𝕄) i j = A i (σ j) := by simp [mul_apply, perm]
section
variable (σ : Equiv.Perm (Fin n))
@[simp] theorem perm_mul_apply (A : 𝕄) (i j) :
    (perm σ * A : 𝕄) i j = A (σ.symm i) j := by simp [mul_apply, perm, ← Equiv.symm_apply_eq]
@[simp] theorem perm_conjTranspose : (perm σ : 𝕄)ᴴ = perm σ.symm := by
  ext i j; simp [perm, Equiv.eq_symm_apply, eq_comm, apply_ite]
theorem perm_uni : Uni (perm σ : 𝕄) := by
  constructor <;> ext i j <;> simp [perm, one_apply]

end

abbrev Upper (A : 𝕄) : Prop := A.BlockTriangular (fun i => i.val)

section
variable {block : Fin n → ℕ}
theorem Supp.inv {A : 𝕄} (hA : Supp block A) [Invertible A] :
    Supp block A⁻¹ := fun i j hij => by
  rcases lt_or_gt_of_ne hij with h | h
  · exact blockTriangular_inv_of_blockTriangular (b := OrderDual.toDual ∘ block) (fun i j h => by aesop) h
  · exact blockTriangular_inv_of_blockTriangular (fun i j h => by aesop) h

theorem upper_supported_of_gram {R : 𝕄} (ht : Upper R) (hd : R.det ≠ 0)
    (hg : Supp block (Rᴴ * R)) : Supp block R := by
  rw [det_of_isUpperTriangular ht, Finset.prod_ne_zero_iff] at hd
  intro i
  induction i using WellFoundedLT.induction with
  | _ i ih =>
  intro j hij
  have := hg i j hij
  rw [mul_apply, Finset.sum_eq_single i] at this
  · simp_all
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · by_cases hk : block k = block i
      · grind
      simp_all
    aesop
  simp

end

section
variable (block : Fin n → ℕ) (B : 𝕄) (σ : Equiv.Perm (Fin n))
theorem structuredQR (hB : Supp block B) (hdetB : B.det ≠ 0) :
    ∃ U R : 𝕄, Supp block U ∧ Uni U ∧ Upper R ∧ B * perm σ = U * perm σ * R := by
  obtain ⟨V, R, hV, ht, hqr⟩ := UnitaryCS.exists_qr (B * perm σ)
  have hp := perm_uni (𝕜 := 𝕜) σ
  have hr : R.det ≠ 0 := fun hz => by
    have := congrArg det hqr
    simp [det_mul, hz, hdetB, det_ne_zero_of_left_inverse hp.1] at this
  let := invertibleOfIsUnitDet R (isUnit_iff_ne_zero.2 hr)
  have hu : V * (perm σ)ᴴ = B * (perm σ * R⁻¹ * (perm σ)ᴴ) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hqr, Matrix.mul_assoc V, mul_inv_of_invertible,
      Matrix.mul_one]
  have hg : Rᴴ * R = (perm σ)ᴴ * (Bᴴ * B) * perm σ := by
    have : Rᴴ * R = (V * R)ᴴ * (V * R) := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV.1, Matrix.one_mul]
    rw [this, ← hqr, conjTranspose_mul]; grind
  have hs := (upper_supported_of_gram (block := fun i => block (σ i)) ht hr (by
    rw [hg]; intro i j hij; simpa using (hB.conjTranspose.mul hB) _ _ hij)).inv
  refine ⟨_, R, hu ▸ hB.mul fun i j hij => by aesop, hV.mul hp.conjTranspose,
    ht, by rw [Matrix.mul_assoc V, hp.1, Matrix.mul_one, hqr]⟩

theorem structuredRQ (hB : Supp block B) (hdetB : B.det ≠ 0) :
    ∃ U R : 𝕄, Supp block U ∧ Uni U ∧ Upper R ∧ perm σ * B = R * perm σ * U := by
  obtain ⟨V, T, hV, hoV, ht, he⟩ := structuredQR block Bᴴ (Fin.revPerm.trans σ.symm)
    hB.conjTranspose (by simp_all)
  refine ⟨Vᴴ, perm Fin.revPerm * Tᴴ * (perm Fin.revPerm)ᴴ, hV.conjTranspose, hoV.conjTranspose,
    fun i j hij => ?_, ?_⟩
  · simp [ht (show Fin.rev i < Fin.rev j by grind)]
  · have hτ : (perm (Fin.revPerm.trans σ.symm) : 𝕄) = (perm σ)ᴴ * perm Fin.revPerm := by
      aesop
    have hJ := (perm_uni (𝕜 := 𝕜) (Fin.revPerm : Equiv.Perm (Fin n))).2
    have hh := congrArg (fun X : 𝕄 => perm Fin.revPerm * Xᴴ) he
    rw [hτ] at hh
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc, hJ,
      Matrix.one_mul] using hh

end

/-- Every unitary three-factor product has supported unitary factors. -/
theorem threeFactor (b₁ b₂ b₃ : ℕ) (σ₁ σ₂ : Equiv.Perm (Fin n)) (A : 𝕄) :
    (∃ B₁ B₂ B₃, Supp (fun i : Fin n => i.val / b₁) B₁ ∧ Supp (fun i : Fin n => i.val / b₂) B₂ ∧
      Supp (fun i : Fin n => i.val / b₃) B₃ ∧ A = B₃ * perm σ₂ * B₂ * perm σ₁ * B₁) ∧ Uni A ↔
    ∃ B₁ B₂ B₃, Supp (fun i : Fin n => i.val / b₁) B₁ ∧ Supp (fun i : Fin n => i.val / b₂) B₂ ∧
      Supp (fun i : Fin n => i.val / b₃) B₃ ∧ Uni B₁ ∧ Uni B₂ ∧ Uni B₃ ∧
      A = B₃ * perm σ₂ * B₂ * perm σ₁ * B₁ := by
  have hp₁ := perm_uni (𝕜 := 𝕜) σ₁
  have hp₂ := perm_uni (𝕜 := 𝕜) σ₂
  constructor
  · rintro ⟨⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, rfl⟩, hA⟩
    have hprod := det_ne_zero_of_left_inverse hA.1
    simp only [det_mul, ne_eq, mul_eq_zero, not_or] at hprod
    obtain ⟨U₃, R₃, hu₃, ho₃, ht₃, eq₃⟩ := structuredQR _ B₃ σ₂ hb₃ hprod.1.1.1.1
    obtain ⟨U₁, R₁, hu₁, ho₁, ht₁, eq₁⟩ := structuredRQ _ B₁ σ₁ hb₁ hprod.2
    have he : B₃ * perm σ₂ * B₂ * perm σ₁ * B₁ =
        U₃ * perm σ₂ * (R₃ * B₂ * R₁) * perm σ₁ * U₁ := by
      grind
    have ho₂ : Uni (R₃ * B₂ * R₁) := by
      have := ((ho₃.mul hp₂).conjTranspose.mul (by grind : Uni (U₃ * perm σ₂ * (R₃ * B₂ * R₁) * (perm σ₁ * U₁)))).mul (hp₁.mul ho₁).conjTranspose
      rwa [Matrix.mul_assoc, Matrix.mul_assoc (_ * _), (hp₁.mul ho₁).2, Matrix.mul_one,
        ← Matrix.mul_assoc, (ho₃.mul hp₂).1, Matrix.one_mul] at this
    refine ⟨U₁, _, U₃, hu₁, fun i j hij => ?_, hu₃, ho₁, ho₂, ho₃, he⟩
    have ht : (R₃ * B₂ * R₁).BlockTriangular (fun i : Fin n => i.val / b₂) :=
      .mul (.mul (fun _ _ h => ht₃ (Nat.lt_of_div_lt_div h)) (fun i j h => by aesop))
        (fun _ _ h => ht₁ (Nat.lt_of_div_lt_div h))
    let : Invertible (R₃ * B₂ * R₁) := ⟨_, ho₂.1, ho₂.2⟩
    have hi := blockTriangular_inv_of_blockTriangular ht
    rw [inv_eq_left_inv ho₂.1] at hi
    rcases lt_or_gt_of_ne hij with h | h
    · simpa using hi h
    aesop
  · rintro ⟨B₁, B₂, B₃, hb₁, hb₂, hb₃, hu₁, hu₂, hu₃, rfl⟩
    exact ⟨by grind, (((hu₃.mul hp₂).mul hu₂).mul hp₁).mul hu₁⟩

/-- The two-factor theorem absorbs an extra singleton unitary left layer. -/
theorem twoFactor (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n)) (A : 𝕄) :
    (∃ B₁ B₂, Supp (fun i : Fin n => i.val / b₁) B₁ ∧ Supp (fun i : Fin n => i.val / b₂) B₂ ∧
      A = B₂ * perm σ * B₁) ∧ Uni A ↔
    ∃ B₁ B₂, Supp (fun i : Fin n => i.val / b₁) B₁ ∧ Supp (fun i : Fin n => i.val / b₂) B₂ ∧
      Uni B₁ ∧ Uni B₂ ∧ A = B₂ * perm σ * B₁ := by
  have hI : (perm (Equiv.refl (Fin n)) : 𝕄) = 1 := by rfl
  constructor
  · rintro ⟨⟨B₁, B₂, hb₁, hb₂, rfl⟩, hA⟩
    obtain ⟨U₁, U₂, U₃, hu₁, hu₂, hu₃, ho₁, ho₂, ho₃, hprod⟩ :=
      (threeFactor b₁ b₂ 1 σ (Equiv.refl _) _).mp
        ⟨⟨B₁, B₂, 1, hb₁, hb₂, Supp.one, by grind⟩, hA⟩
    refine ⟨U₁, U₃ * U₂, hu₁, Supp.mul (fun i j h => by aesop) hu₂, ho₁, ho₃.mul ho₂, ?_⟩
    grind
  · rintro ⟨B₁, B₂, hb₁, hb₂, ho₁, ho₂, rfl⟩
    exact ⟨by grind, (ho₂.mul (perm_uni σ)).mul ho₁⟩

end GS.Shared
