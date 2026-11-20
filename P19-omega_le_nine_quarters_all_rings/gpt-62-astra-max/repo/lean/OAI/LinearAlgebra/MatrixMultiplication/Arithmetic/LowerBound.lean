module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.Comparison

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.Arithmetic

/-- Counting with any zero-one test that rejects free reads and constants
charges at most one to each arithmetic instruction. -/
private theorem count_le {F I : Type*} [Ring F] (P : ((I → F) → F) → Prop)
    (hc : ∀ c, ¬ P (fun _ => c)) (hv : ∀ i, ¬ P (fun x => x i))
    {r : ℕ} (p : Program F I r) [DecidablePred P] :
    (∑ i, if P (fun x => p.eval x i) then 1 else 0) ≤ p.cost := by
  induction p with
  | nil => simp [Program.cost]
  | step p g ih =>
    rw [Fin.sum_univ_succ]; change _ + _ ≤ p.cost + g.cost
    rw [add_comm]; apply add_le_add ih
    cases g <;> simp [Program.eval, Gate.eval, Gate.cost, hc, hv] <;> split <;> decide

variable {F : Type*} [Ring F] [Nontrivial F]

/-- Setting the right input to one distinguishes the outputs. None can
be a free read: zeroing the opposite input kills every product entry. -/
theorem MatrixAlgorithm.output_size_le_cost {n : ℕ} (P : MatrixAlgorithm F n n n)
    (hP : P.Correct) : n ^ 2 ≤ P.cost := by
  classical
  let f (o : Fin n × Fin n) := P.output o.1 o.2
  have e (A B : Matrix (Fin n) (Fin n) F) (o) :
      P.program.eval (matrixInputs A B) (f o) = (A*B) o.1 o.2 := congrFun (congrFun (hP A B) _) _
  have inj : Function.Injective f := by
    intro x y h
    let A := Matrix.of fun i j => if (i,j) = x then (1:F) else 0
    have he := (e A 1 x).symm.trans ((congrArg _ h).trans (e A 1 y))
    by_contra hxy
    simp [A, Ne.symm hxy] at he
  let test (u : (MatrixInput n n n → F) → F) := ∃ o : Fin n × Fin n, ∀ A B, u (matrixInputs A B) = (A*B) o.1 o.2
  let U : Matrix (Fin n) (Fin n) F := Matrix.of fun _ _ => 1
  have h := count_le test (by rintro c ⟨o,h⟩; have := h 0 0; have := h U 1; simp_all [U]) (by
    rintro (i|i) ⟨o,h⟩
    · have := h U 0; simp_all [matrixInputs, U]
    · have := h 0 U; simp_all [matrixInputs, U]) P.program
  apply le_trans _ h
  calc
    n ^ 2 = ∑ _ : Fin n × Fin n, 1 := by simp [sq]
    _ ≤ _ := Finset.sum_le_sum_of_injOn f inj.injOn (Finset.subset_univ _)
      (fun i _ => by have hi : test (fun x => P.program.eval x (f i)) := ⟨i,fun A B => e A B i⟩; simp [hi]) (by simp)

theorem admissibleExponent_two_le {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨C, _, h⟩ := hτ ε hε
  apply AuxiliarySeparation.rpow_exponent_le_of_nat_bound
  intro n hn
  obtain ⟨P, hP, hc⟩ := h n hn
  apply le_trans _ hc
  norm_cast
  exact P.output_size_le_cost hP

universe u
theorem admissibleExponent_bddBelow (F : Type u) [Ring F] [Nontrivial F] :
    BddBelow {τ : ℝ | AdmissibleExponent F τ} :=
  ⟨2, fun _ => admissibleExponent_two_le⟩

end OAI.MatrixMultiplication.Arithmetic
