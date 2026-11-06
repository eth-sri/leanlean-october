module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ScalarAdapters
public import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem

/-! # Full-coefficient smoothness, symmetry, and Loewner adapters -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open scoped MatrixOrder

/-- Swapping physical coordinates preserves smoothness for the evolution convention. -/
theorem evolutionCoefficient_smooth {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) :
    IsSmoothFullKineticCoefficient (evolutionCoefficient A.a) := by
  intro i j
  exact A.smooth.comp
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.snd)).prodMk
      ((contDiff_apply ℝ ℝ (0 : Fin 1)).comp (contDiff_snd.fst)))

variable (a : ℝ → ℝ → ℝ)



/-- The evolution coefficient is symmetric too. -/
theorem evolutionCoefficient_symmetric  :
    IsSymmetricFullKineticCoefficient (evolutionCoefficient a) := by
  intro t y z
  rfl

private theorem scalar_matrix_le {a b : ℝ} (hab : a ≤ b) :
    Matrix.diagonal (fun _ : Fin 1 => a) ≤ Matrix.diagonal (fun _ : Fin 1 => b) := by
  rw [Matrix.le_iff, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro i
  exact sub_nonneg.mpr hab

variable (a : ℝ)

private theorem scalar_diagonal  :
    Matrix.diagonal (fun _ : Fin 1 => a) = fun _ _ => a := by
  ext i j
  have hi := Fin.eq_zero i
  have hj := Fin.eq_zero j
  subst i
  subst j
  exact Matrix.diagonal_apply_eq _ _

private theorem scalar_smul_identity  :
    a • (1 : PDE.Mat 1) = fun _ _ => a := by
  ext i j
  have hi : i = 0 := Fin.eq_zero i
  have hj : j = 0 := Fin.eq_zero j
  subst i
  subst j
  simp

variable {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)

/-- Pointwise scalar ellipticity is exactly full-matrix Loewner ellipticity in dimension one. -/
theorem autonomousCoefficient_bounds  :
    HasEverywhereLoewnerBounds lam Lam (autonomousCoefficient A.a) := by
  intro t x v
  simp only [scalar_smul_identity]
  have heq : autonomousCoefficient A.a t x v =
      Matrix.diagonal (fun _ : Fin 1 => A.a (x 0) (v 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal lam, ← scalar_diagonal Lam, heq]
  exact ⟨scalar_matrix_le (A.bounds (x 0) (v 0)).1,
    scalar_matrix_le (A.bounds (x 0) (v 0)).2⟩

/-- The physical bounds survive the Section Two coordinate exchange. -/
theorem evolutionCoefficient_bounds  :
    HasEverywhereLoewnerBounds lam Lam (evolutionCoefficient A.a) := by
  intro t y z
  simp only [scalar_smul_identity]
  have heq : evolutionCoefficient A.a t y z =
      Matrix.diagonal (fun _ : Fin 1 => A.a (z 0) (y 0)) :=
    (scalar_diagonal _).symm
  rw [← scalar_diagonal lam, ← scalar_diagonal Lam, heq]
  exact ⟨scalar_matrix_le (A.bounds (z 0) (y 0)).1,
    scalar_matrix_le (A.bounds (z 0) (y 0)).2⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
