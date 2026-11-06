module

public import OAI.LinearAlgebra.MatrixMultiplication.Model
public import Mathlib.Algebra.Order.Floor.Semiring

public section

@[expose] section

namespace OAI

/-! Division-free arithmetic programs over a ring and their operation counts. -/

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

namespace Program

variable {F Input : Type*}

@[simp] theorem eval_step_zero [Ring F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) :
    (p.step g).eval inputs 0 = g.eval inputs (p.eval inputs) := rfl

@[simp] theorem eval_step_succ [Ring F] {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) (inputs : Input → F) (i : Fin r) :
    (p.step g).eval inputs i.succ = p.eval inputs i := rfl

@[simp] theorem cost_step {r : ℕ} (p : Program F Input r)
    (g : Gate F Input (Fin r)) : (p.step g).cost = p.cost + g.cost := rfl

end Program

namespace MatrixAlgorithm

variable {F : Type*} [Ring F] {a b c : ℕ}

theorem correct_iff_entries (P : MatrixAlgorithm F a b c) :
    P.Correct ↔ ∀ (A : Matrix (Fin a) (Fin b) F) (B : Matrix (Fin b) (Fin c) F)
      (i : Fin a) (k : Fin c),
      P.program.eval (matrixInputs A B) (P.output i k) = ∑ j, A i j * B j k :=
  ⟨fun h A B i k => congrFun (congrFun (h A B) i) k,
    fun h A B => funext fun i => funext fun k => h A B i k⟩

end MatrixAlgorithm

def scalarAlgorithm (F : Type*) [Ring F] : MatrixAlgorithm F 1 1 1 where
  registers := 3
  program := ((Program.nil.step (.input (.inl (0, 0)))).step
    (.input (.inr (0, 0)))).step (.mul 1 0)
  output := fun _ _ => 0

theorem scalarAlgorithm_correct (F : Type*) [Ring F] : (scalarAlgorithm F).Correct := by
  intro A B
  funext i k
  have hi : i = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst i
  subst k
  change A 0 0 * B 0 0 = (A * B) 0 0
  simp [Matrix.mul_apply]

end MatrixMultiplication.Arithmetic

end

end OAI
