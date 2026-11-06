import Mathlib.Data.Fin.Rev

import GS.MatrixFactor.CholeskySupport



/-! Unconditional complex structured QR/RQ: the unitary support conditions
are proved from ordinary complex QR and triangular Gram support recovery. -/
open Matrix GS.MatrixBase
namespace GS.MatrixFactor
variable {𝕜 : Type} [RCLike 𝕜]

variable (block : Fin n → ℕ)

theorem structuredQR  (B : KMat 𝕜 n) (σ : Equiv.Perm (Fin n))
    (hB : CSupported block B) (hdetB : B.det ≠ 0) :
    ∃ U R : KMat 𝕜 n, CSupported block U ∧ Unitary U ∧ CUpper R ∧
      B*cPermMatrix (𝕜 := 𝕜) σ = U*cPermMatrix (𝕜 := 𝕜) σ*R := by
  obtain ⟨V,R,hV,ht,hqr⟩ := exists_ordinary_qr (B*cPermMatrix (𝕜 := 𝕜) σ)
  let P := cPermMatrix (𝕜 := 𝕜) σ
  have hp : Unitary P := cPerm_unitary σ
  have hr : R.det ≠ 0 := by
    have hd := mul_ne_zero hdetB (unitary_det_ne_zero hp)
    rw [← Matrix.det_mul,hqr,Matrix.det_mul] at hd
    exact (mul_ne_zero_iff.mp hd).2
  letI := Matrix.invertibleOfIsUnitDet R (isUnit_iff_ne_zero.mpr hr)
  have hgram : Rᴴ*R = Pᴴ*Bᴴ*B*P := by
    have h := congrArg (fun X : KMat 𝕜 n => Xᴴ*X) hqr
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ V, hV.1, Matrix.one_mul] using h.symm
  have hs : CSupported (fun i : Fin n => block (σ i)) R := by
    apply upper_supported_of_gram ht
      (by simpa [Matrix.det_of_upperTriangular ht, Finset.prod_ne_zero_iff] using hr)
    rw [hgram]
    intro i j hij
    rw [Matrix.mul_assoc Pᴴ]
    simpa [P] using (hB.conjTranspose.mul hB) (σ i) (σ j) hij
  have hsinv := cSupported_inverse hs
  have hback : CSupported block (P*R⁻¹*Pᴴ) := by
    intro i j hij
    simpa [P] using hsinv (σ.symm i) (σ.symm j) (by simpa using hij)
  have hu : V*Pᴴ = B*(P*R⁻¹*Pᴴ) := by
    calc
      _ = (V*R)*R⁻¹*Pᴴ := by aesop
      _ = _ := by grind
  refine ⟨V*Pᴴ,R,?_, hV.mul hp.conjTranspose,ht, ?_⟩
  · rw [hu]
    exact hB.mul hback
  · simpa only [P,Matrix.mul_assoc,(cPerm_unitary (𝕜 := 𝕜) σ).1,Matrix.one_mul] using hqr

theorem upper_reverse_conjTranspose {T : KMat 𝕜 n} (ht : CUpper T) :
    CUpper (cPermMatrix (𝕜 := 𝕜) (Fin.revPerm)*Tᴴ*(cPermMatrix  (Fin.revPerm))ᴴ) := by
  intro i j hij
  
  rw [cPerm_conjugate_apply]
  change star (T (j.rev) (i.rev))=0
  rw [ht (Fin.rev_lt_rev.mpr hij), star_zero]

theorem structuredRQ  (B : KMat 𝕜 n) (σ : Equiv.Perm (Fin n))
    (hB : CSupported block B) (hdetB : B.det ≠ 0) :
    ∃ U R : KMat 𝕜 n, CSupported block U ∧ Unitary U ∧ CUpper R ∧
      cPermMatrix (𝕜 := 𝕜) σ*B = R*cPermMatrix (𝕜 := 𝕜) σ*U := by
  let ρ : Equiv.Perm (Fin n) := Fin.revPerm
  let P := cPermMatrix (𝕜 := 𝕜) σ
  let J := cPermMatrix (𝕜 := 𝕜) ρ
  let τ := ρ.trans σ.symm
  have hτ : cPermMatrix (𝕜 := 𝕜) τ = Pᴴ*J := by aesop
  obtain ⟨V,T,hV,hoV,ht,he⟩ := structuredQR block Bᴴ τ hB.conjTranspose
    (by aesop)
  refine ⟨Vᴴ,J*Tᴴ*Jᴴ,hV.conjTranspose,hoV.conjTranspose,upper_reverse_conjTranspose ht,?_⟩
  have hh := congrArg (fun X : KMat 𝕜 n => J*Xᴴ) he
  rw [hτ] at hh
  simpa only [J, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, (cPerm_unitary (𝕜 := 𝕜) ρ).2, Matrix.one_mul] using hh

end GS.MatrixFactor
