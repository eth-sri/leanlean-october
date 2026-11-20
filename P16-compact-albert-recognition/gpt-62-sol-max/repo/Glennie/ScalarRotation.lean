module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace Glennie

theorem exists_rotation_improving_energy (a b n : ℝ) (hn : 0 < n) :
    ∃ c s : ℝ, c^2+s^2=1 ∧
      (c^2*a+s^2*b+2*c*s*n)^2 + (s^2*a+c^2*b-2*c*s*n)^2 =
        a^2+b^2+2*n^2 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (⟨a-b,2*n⟩ : ℂ) (n := 2) (by decide)
  have hw₀ : w ≠ 0 := by
    rintro rfl
    have h := congrArg Complex.im hw
    simp at h
    linarith
  have hd := norm_ne_zero_iff.mpr hw₀
  let c := w.re / ‖w‖
  let s := w.im / ‖w‖
  have hc : c^2+s^2 = 1 := by
    dsimp [c,s]
    field_simp
    simpa only [pow_two, Complex.normSq_apply] using (Complex.sq_norm w).symm
  have hs : (c^2-s^2)*n-c*s*(a-b) = 0 := by
    have hr := congrArg Complex.re hw
    have hi := congrArg Complex.im hw
    simp [pow_two, Complex.mul_re] at hr
    simp [pow_two, Complex.mul_im] at hi
    dsimp [c,s]
    field_simp
    linear_combination n*hr - (a-b)/2*hi
  refine ⟨c,s,hc,?_⟩
  linear_combination (a^2+b^2+2*n^2)*(c^2+s^2+1)*hc - 2*((c^2-s^2)*n-c*s*(a-b))*hs

end Glennie
