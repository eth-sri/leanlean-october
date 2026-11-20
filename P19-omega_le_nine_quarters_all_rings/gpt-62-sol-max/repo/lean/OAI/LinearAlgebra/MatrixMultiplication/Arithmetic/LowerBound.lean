module

public import OAI.LinearAlgebra.MatrixMultiplication.Arithmetic.Compiler
public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth

public section

@[expose] section

/-! Division-free arithmetic programs over a ring and their operation counts. -/

namespace OAI.MatrixMultiplication.Arithmetic

noncomputable section

namespace Program

variable {F Input : Type*}

def registerCost : {r : ℕ} → Program F Input r → Fin r → ℕ
  | 0, .nil => Fin.elim0
  | _ + 1, .step p g => Fin.cases g.cost p.registerCost

theorem sum_registerCost {r : ℕ} (p : Program F Input r) :
    ∑ i, p.registerCost i = p.cost := by
  induction p <;> simp_all [Program.cost, registerCost, Fin.sum_univ_succ, Nat.add_comm]

theorem eval_eq_constant_or_input_of_registerCost_eq_zero [Ring F]
    {r : ℕ} (p : Program F Input r) (i : Fin r) (hi : p.registerCost i = 0) :
    (∃ z : F, ∀ inputs, p.eval inputs i = z) ∨
      (∃ a : Input, ∀ inputs, p.eval inputs i = inputs a) := by
  induction p with
  | nil => exact i.elim0
  | step p g ih =>
    refine Fin.cases (fun h => ?_) ih i hi
    cases g <;> tauto

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Ring F] [Nontrivial F] {a b c : ℕ}

theorem output_size_le_cost (P : MatrixAlgorithm F a b c) (hb : 1 ≤ b)
    (hP : P.Correct) : a * c ≤ P.cost := by
  let j : Fin b := ⟨0, hb⟩
  let out (o : Fin a × Fin c) := P.output o.1 o.2
  have ev (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F) (o : Fin a × Fin c) :
      P.program.eval (matrixInputs A B) (out o) = (A * B) o.1 o.2 := congrFun₂ (hP A B) o.1 o.2
  have test (o t : Fin a × Fin c) :
      P.program.eval (matrixInputs (Matrix.single o.1 j 1) (Matrix.single j o.2 1)) (out t) =
        if t = o then 1 else 0 := by
    classical
    simp [ev, Matrix.single_apply, Prod.ext_iff, eq_comm]
  have inj : Function.Injective out := by
    intro o t h
    have H := test o o
    aesop
  have cost (o : Fin a × Fin c) : 1 ≤ P.program.registerCost (out o) := Nat.pos_of_ne_zero fun hz => by
    rcases P.program.eval_eq_constant_or_input_of_registerCost_eq_zero (out o) hz with
      ⟨z, hz⟩ | ⟨⟨x,y⟩ | ⟨y,z⟩, hu⟩
    · have h0 := ev 0 0 o
      have h1 := test o o
      simp_all
    · simpa [hu, matrixInputs] using ev (Matrix.of fun _ _ => 1) 0 o
    · simpa [hu, matrixInputs] using ev 0 (Matrix.of fun _ _ => 1) o
  rw [MatrixAlgorithm.cost, ← Program.sum_registerCost]
  simpa using Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ)
    (f := fun _ => (1 : ℕ)) out inj.injOn (Finset.subset_univ _) (fun o _ => cost o) (fun _ _ _ => Nat.zero_le _)

end MatrixAlgorithm

theorem admissibleExponent_two_le {F : Type*} [Ring F] [Nontrivial F] {τ : ℝ}
    (hτ : AdmissibleExponent F τ) : 2 ≤ τ := by
  by_contra! h
  obtain ⟨C, _, H⟩ := hτ ((2 - τ) / 2) (by linarith)
  have he := AuxiliarySeparation.rpow_exponent_le_of_nat_bound (a := 2) (C := C) (fun n hn => by
    obtain ⟨P, hP, hcost⟩ := H n hn
    have hp := P.output_size_le_cost hn hP
    exact (by exact_mod_cast (by lia : n ^ 2 ≤ P.cost) :
      (n : ℝ) ^ (2 : ℝ) ≤ P.cost).trans hcost)
  linarith

end
end OAI.MatrixMultiplication.Arithmetic
