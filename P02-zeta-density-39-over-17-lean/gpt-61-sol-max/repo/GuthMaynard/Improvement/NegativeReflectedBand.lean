module
import Mathlib
public import GuthMaynard.Improvement.ReflectedBandMeanValue

@[expose] public section

open MeasureTheory Finset
open scoped ComplexConjugate
namespace GuthMaynard.Improvement

section
variable (N : ℝ) (a : ℕ → ℂ) (t : ℝ)
include N a t

/-- Literal coefficient conjugation reverses source time, without changing indices. -/
theorem boundedPolynomial_conjugate_time  :
    conj (boundedPolynomial N a t) = boundedPolynomial N (fun n => conj (a n)) (-t) := by
  unfold boundedPolynomial
  simp only [map_sum,map_mul]
  apply sum_congr rfl
  intro n _
  rw [← Complex.exp_conj]
  congr 2
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
  simp_all

theorem boundedPolynomial_norm_reverse  :
    ‖boundedPolynomial N a t‖ = ‖boundedPolynomial N (fun n => conj (a n)) (-t)‖ := by
  rw [← boundedPolynomial_conjugate_time,RCLike.norm_conj]
end



