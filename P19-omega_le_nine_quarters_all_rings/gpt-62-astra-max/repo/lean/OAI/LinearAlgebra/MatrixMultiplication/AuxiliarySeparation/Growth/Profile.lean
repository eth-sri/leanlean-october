module

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Comparison

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation

/-- Index the positive dimensions starting at zero: `value i j` is the
profile at sizes `i+1, j+1`. Only the diagonal needs a dimension bound. -/
structure ScalarProfile where
  value : ℕ → ℕ → ℝ
  unit : 1 ≤ value 0 0
  symmetric : ∀ a b, value a b = value b a
  concave : ∀ a h, value a h + value a (h+2) ≤ 2 * value a (h+1)
  tripling : ∀ a h, 3 * value a h ≤ value a (3*h+a+2)

namespace ScalarProfile
variable (P : ScalarProfile)

/-- Bound the tripling secant by the increment at its left endpoint. -/
private theorem row_step (a h : ℕ) :
    (2*h+a+4:ℝ)*P.value a h ≤ (2*h+a+2:ℝ)*P.value a (h+1) := by
  let Δ i := P.value a (i+1) - P.value a i
  have secant (j : ℕ) : Δ (h+j) ≤ Δ h ∧ P.value a (h+j) ≤ P.value a h + j*Δ h := by
    induction j with
    | zero => simp
    | succ j ih => have := P.concave a (h+j); grind
  have hs := (secant (2*h+a+2)).2
  rw [show h+(2*h+a+2) = 3*h+a+2 by omega] at hs
  dsimp [Δ] at hs; push_cast at hs; linarith [P.tripling a h]

/-- Use the two row estimates on either side of a diagonal increment. After
cubing their product, the fourth-power lower bound propagates exactly. -/
theorem diagonal (n : ℕ) : (n+1:ℝ)^4 ≤ P.value n n ^ 3 := by
  induction n with
  | zero => simpa using one_le_pow₀ P.unit
  | succ n ih =>
    let p : ℝ := 3*n+2
    have a := P.row_step n n
    have b := P.row_step (n+1) n
    rw [P.symmetric (n+1) n] at b
    push_cast at b ⊢
    have h : ((p+2)*(p+3))*P.value n n ≤ (p*(p+1))*P.value (n+1) (n+1) := by
      dsimp [p] at *; nlinarith only [mul_le_mul_of_nonneg_left a (by positivity : 0 ≤ (3*n+5:ℝ)),
        mul_le_mul_of_nonneg_left b (by positivity : 0 ≤ (3*n+2:ℝ))]
    apply le_of_mul_le_mul_left (a := (p*(p+1))^3) _ (by positivity)
    calc
      _ ≤ ((p+2)*(p+3))^3 * (n+1)^4 := by dsimp [p]; apply sub_nonneg.mp; ring_nf; positivity
      _ ≤ _ := mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ _ := by simpa [mul_pow] using (Odd.pow_le_pow (by decide)).mpr h

end ScalarProfile
end OAI.MatrixMultiplication.AuxiliarySeparation
