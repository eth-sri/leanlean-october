module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib

/-! # Squaring a rectangular array of smooth directional fields -/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Transposition
open scoped ContDiff
variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [Fintype J]

def row (e : I → E) (s : I → E → ℝ) (f : E → ℝ) (x : E) := ∑ j, s j x * fderiv ℝ f x (e j)

theorem row_squares (e : I → E) (s : J → I → E → ℝ) {f : E → ℝ} {x : E}
    (hs : ∀ p j, DifferentiableAt ℝ (s p j) x) (hf : ContDiffAt ℝ 2 f x) :
    ∑ p, row e (s p) (row e (s p) f) x =
      (∑ j, (∑ p, row e (s p) (s p j) x) * fderiv ℝ f x (e j)) +
      ∑ i, ∑ j, (∑ p, s p i x * s p j x) * fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e i) := by
  let g j (y : E) := fderiv ℝ f y (e j)
  have D j : DifferentiableAt ℝ (g j) x := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.clm_apply (differentiableAt_const _)
  have eq jac (i : I) : fderiv ℝ (row e (s jac) f) x (e i) = ∑ j, (s jac j x * fderiv ℝ (g j) x (e i) + g j x * fderiv ℝ (s jac j) x (e i)) := by
    have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ => ((hs jac j).hasFDerivAt.mul (D j).hasFDerivAt)).fderiv
    change fderiv ℝ (fun y => ∑ j, s jac j y * g j y) x (e i) = _
    exact (congrArg (fun L : E →L[ℝ] ℝ => L (e i)) h).trans (by simp [sum_apply])
  simp only [row,eq,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib,mul_add,← mul_assoc]
  have rot (u : J → I → I → ℝ) : ∑ p, ∑ i, ∑ j, u p i j = ∑ j, ∑ p, ∑ i, u p i j :=
    (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm
  have cyc (u : J → I → I → ℝ) : ∑ p, ∑ i, ∑ j, u p i j = ∑ i, ∑ j, ∑ p, u p i j :=
    Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm)
  rw [add_comm]; congr 1
  · rw [rot]; simp only [g,mul_assoc,mul_comm,mul_left_comm]
  · exact cyc _

end HypoellipticAleksandrov.Parabolic.Transposition
