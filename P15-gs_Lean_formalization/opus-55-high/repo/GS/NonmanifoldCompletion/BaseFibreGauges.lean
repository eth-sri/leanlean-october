module

public import GS.NonmanifoldCompletion.BlockRealization

@[expose] public section


/-!
# Exact gauge normalization of every factor tuple above the scalar base matrix

The gauges are fixed diagonal sign matrices. Their values may depend on the
chosen point of the fibre; a continuous global choice on the whole fibre is
neither required nor asserted. This is suited to compact full-fibre coverage.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

def DiagonalTwo (D : Mat 2) : Prop := D 0 1=0 ∧ D 1 0=0

theorem diagonalTwo_transpose {D : Mat 2} (hD : DiagonalTwo D) : DiagonalTwo Dᵀ :=
  ⟨hD.2,hD.1⟩

theorem diagonalTwo_symmetric (D : Mat 2) (hD : DiagonalTwo D) : Dᵀ=D := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hD.1,hD.2]

theorem diagonalTwo_mul {D E : Mat 2} (hD : DiagonalTwo D) (hE : DiagonalTwo E) :
    DiagonalTwo (D*E) := by
  constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

section
variable {D : Mat 2}
theorem diagonalTwo_involution (hd : DiagonalTwo D)
    (ho : Orthogonal D) : D*D=1 := by
  simpa only [diagonalTwo_symmetric D hd] using ho.1

theorem diagonalTwo_entry_sq (hd : DiagonalTwo D)
    (ho : Orthogonal D) (a : Fin 2) : (D a a)^2=1 := by
  have h := congr_fun₂ ho.1 a a
  fin_cases a <;> simpa [Matrix.mul_apply, Fin.sum_univ_two, hd.1, hd.2, pow_two] using h

end

/-- At a nonzero scalar block, the product of the outer factors is diagonal. -/
theorem diagonalTwo_of_scalar_block (U V : Mat 2) (hU : Orthogonal U)
    (hV : Orthogonal V) (a b t : ℝ) (ht : t≠0)
    (he : U * diagTwo a b * V = t • (1 : Mat 2)) : DiagonalTwo (V*U) := by
  have h := congrArg (fun Z => Uᵀ * Z * Vᵀ) he
  simp only [← Matrix.mul_assoc, hU.1, Matrix.one_mul] at h
  rw [Matrix.mul_assoc _ V, hV.2, Matrix.mul_one] at h
  constructor <;> [have := congr_fun₂ h 1 0; have := congr_fun₂ h 0 1] <;>
    simp [diagTwo, Matrix.mul_apply, mul_comm] at this ⊢ <;> grind

section
variable {q : ℕ} (D E : Fin q → Mat 2) (a : Fin 2) (A : Mat q)
/-- A row-and-column gauge on a q-by-q middle factor. -/
def gaugeMiddle : Mat q :=
  Matrix.diagonal (fun i => D i a a) * A * Matrix.diagonal (fun j => E j a a)

@[simp] theorem gaugeMiddle_apply (i j : Fin q) :
    gaugeMiddle D E a A i j = D i a a * A i j * E j a a := by
  simp [gaugeMiddle,Matrix.mul_apply,Matrix.diagonal]

end

section
variable {q : ℕ}
theorem signs_diagonal_orthogonal (s : Fin q → ℝ)
    (hs : ∀ i, (s i)^2=1) : Orthogonal (Matrix.diagonal s) := by
  constructor <;> ext i j <;> by_cases hij : i=j
  all_goals simp [Matrix.mul_apply,Matrix.diagonal,Matrix.transpose_apply,
    Matrix.one_apply,hij,eq_comm,← pow_two,hs]

theorem gaugeMiddle_orthogonal (D E : Fin q → Mat 2)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (a : Fin 2) (A : Mat q) (hA : Orthogonal A) : Orthogonal (gaugeMiddle D E a A) :=
  ((signs_diagonal_orthogonal _ (fun i => diagonalTwo_entry_sq (hD i).1 (hD i).2 a)).mul hA).mul
    (signs_diagonal_orthogonal _ (fun j => diagonalTwo_entry_sq (hE j).1 (hE j).2 a))

end

theorem diagonal_gauge_middle (D E : Mat 2) (hD : DiagonalTwo D)
    (hE : DiagonalTwo E) (a b : ℝ) :
    D * diagTwo a b * E = diagTwo (D 0 0*a*E 0 0) (D 1 1*b*E 1 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagTwo,Matrix.mul_apply,Fin.sum_univ_two,hD.1,hD.2,hE.1,hE.2]

/-- Every full-fibre representative admits constant diagonal gauges normalizing
both middle matrices to Q0 and all relative outer matrices to I. -/
theorem normalize_scalar_base_fibre (hq : 0<q)
    (Q₀ A B : Mat q) (hentries : ∀ i j, Q₀ i j≠0)
    (U V : Fin q → Mat 2) (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hbase : ∀ i j, U i * diagTwo (A i j) (B i j) * V j = Q₀ i j • (1 : Mat 2)) :
    ∃ (S : Mat 2) (D E : Fin q → Mat 2), Orthogonal S ∧
      (∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i)) ∧
      (∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j)) ∧
      (∀ i, U i * D i * S = 1) ∧ (∀ j, Sᵀ * E j * V j = 1) ∧
      gaugeMiddle D E 0 A = Q₀ ∧ gaugeMiddle D E 1 B = Q₀ := by
  obtain ⟨S, hS0⟩ : ∃ S, V ⟨0,hq⟩ = S := by simp
  have hS : Orthogonal S := by grind
  have hdiag i j := diagonalTwo_of_scalar_block (U i) (V j) (hU i) (hV j) _ _ _ (hentries i j) (hbase i j)
  have hdE j : DiagonalTwo (V j*Sᵀ) := by
    convert diagonalTwo_mul (hdiag ⟨0,hq⟩ j) (diagonalTwo_transpose (hdiag ⟨0,hq⟩ ⟨0,hq⟩)) using 1
    simp [← hS0, Matrix.mul_assoc, ← Matrix.mul_assoc (U _), (hU _).2]
  have hdD i : DiagonalTwo (S*U i) := by grind
  have hmiddle i j := (diagonal_gauge_middle _ _ (hdD i) (hdE j) (A i j) (B i j)).symm.trans <| by
    rw [show S*U i * diagTwo (A i j) (B i j) * (V j*Sᵀ) = S*(U i*diagTwo (A i j) (B i j)*V j)*Sᵀ by
      simp [Matrix.mul_assoc], hbase]
  refine ⟨S,fun i => S*U i,fun j => V j*Sᵀ,hS,fun i => ⟨hdD i,hS.mul (hU i)⟩,fun j => ⟨hdE j,(hV j).mul hS.transpose⟩,
    fun i => ?_,fun j => ?_,?_,?_⟩
  · dsimp only; rw [← diagonalTwo_symmetric _ (hdD i)]
    simp [Matrix.mul_assoc, hS.1, (hU i).2]
  · dsimp only; rw [← diagonalTwo_symmetric _ (hdE j)]
    simp [Matrix.mul_assoc, hS.1, (hV j).1]
  all_goals ext i j
  · simpa [diagTwo, hS.2] using congr_fun₂ (hmiddle i j) 0 0
  · simpa [diagTwo, hS.2] using congr_fun₂ (hmiddle i j) 1 1

end GS.NonmanifoldCompletion
