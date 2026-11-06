module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-! # Full-coefficient smoothness, symmetry, and Loewner adapters -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped MatrixOrder

variable (a : ℝ → ℝ → ℝ) {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)

/-- Swapping physical coordinates preserves smoothness for the evolution convention. -/
theorem evolutionCoefficient_smooth  :
    IsSmoothFullKineticCoefficient (evolutionCoefficient A.a) := by
  intro i j
  exact A.smooth.comp
    (((contDiff_apply ℝ ℝ _).comp (contDiff_snd.snd)).prodMk
      ((contDiff_apply ℝ ℝ _).comp (contDiff_snd.fst)))

/-- The evolution coefficient is symmetric too. -/
theorem evolutionCoefficient_symmetric  :
    IsSymmetricFullKineticCoefficient (evolutionCoefficient a) := by
  intro t y z
  rfl

private theorem scalar_matrix_le {a b : ℝ} (hab : a ≤ b) :
    Matrix.diagonal (fun _ : Fin 1 => a) ≤ Matrix.diagonal (fun _ : Fin 1 => b) := by
  rw [Matrix.le_iff]
  simp_all

private theorem scalar_diagonal (a : ℝ) :
    Matrix.diagonal (fun _ : Fin 1 => a) = fun _ _ => a := by
  ext i j
  have hi := Fin.eq_zero i
  have hj := Fin.eq_zero j
  simp_all

private theorem scalar_smul_identity (a : ℝ) :
    a • (1 : PDE.Mat 1) = fun _ _ => a := by
  ext i j
  have hi  := Fin.eq_zero i
  have hj  := Fin.eq_zero j
  simp_all

/-- Pointwise scalar ellipticity is exactly full-matrix Loewner ellipticity in dimension one. -/
theorem autonomousCoefficient_bounds  :
    HasEverywhereLoewnerBounds lam Lam (autonomousCoefficient A.a) := by
  intro t x v
  simp only [scalar_smul_identity]
  have heq : autonomousCoefficient A.a t x v =
      Matrix.diagonal (fun _ : Fin 1 => A.a (x 0) (v 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal, ← scalar_diagonal, heq]
  exact ⟨scalar_matrix_le (A.bounds _ _).1,
    scalar_matrix_le (A.bounds _ _).2⟩

/-- The physical bounds survive the Section Two coordinate exchange. -/
theorem evolutionCoefficient_bounds  :
    HasEverywhereLoewnerBounds lam Lam (evolutionCoefficient A.a) := by
  intro t y z
  simp only [scalar_smul_identity]
  have heq : evolutionCoefficient A.a t y z =
      Matrix.diagonal (fun _ : Fin 1 => A.a (z 0) (y 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal, ← scalar_diagonal, heq]
  exact ⟨scalar_matrix_le (A.bounds _ _).1,
    scalar_matrix_le (A.bounds _ _).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
