module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SignsCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2SpectralSigns
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # The actual cutoff Hessian matrix and transport scalar -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- A bilinear continuous derivative is the quadratic form of its native coordinate matrix. -/
theorem dotProduct_matrix_of_bilinear {d }
    (B : PDE.Vec d →L[ℝ] PDE.Vec d →L[ℝ] ℝ) (w : PDE.Vec d) :
    dotProduct w (Matrix.mulVec (fun i k => B (Pi.single i 1) (Pi.single k 1)) w) = B w w := by
  have heq : w = ∑ i : Fin d, w i • Pi.single i (1 : ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [heq]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [dotProduct, Matrix.mulVec, sum_apply, smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
