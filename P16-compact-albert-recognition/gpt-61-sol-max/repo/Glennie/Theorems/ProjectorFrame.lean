module
public import Glennie.LinearSimp
public import Mathlib.Tactic.LinearCombination

public import Glennie.Native.CubicIdentity
public import Glennie.Theorems.CubicNorm
public import Glennie.Theorems.Frames

/- Polynomial projectors for trace-zero norm-two cubic-norm-zero elements.
   These are derived from the native cubic residual and Jordan identity. -/

@[expose] public section
namespace Glennie
noncomputable section

theorem projectorFrame_is_frame (x : Albert) (ht : trace x=0)
    (hn : inner x x=2) (hc : newtonCubicNorm x=0) : Frame (projectorFrame x) := by
  have hc : jordan x (jordan x x) = x := by
    change trace (jordan x x) = 2 at hn
    norm_num [newtonCubicNorm, ht] at hc
    have h := cubicResidual_eq_zero x
    simp [cubicResidual, ht, hn, hc] at h
    linear_combination (norm := module) (1 / 6 : ℝ) • h
  have hs : trace (jordan x x)=2 := hn
  have h4 : jordan (jordan x x) (jordan x x)=jordan x x := by
    rw [jordan_identity x x,hc]
  have hsx : jordan (jordan x x) x=x := by rw [jordan_comm,hc]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [projectorFrame,trace_smul,trace_add,
      trace_sub,trace_unit,ht,hs]
  · intro i
    fin_cases i <;> simp [albert_linear, projectorFrame, jordan_unit_left, jordan_unit_right, hc, h4, hsx] <;> module
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals simp [albert_linear, projectorFrame, jordan_unit_left, jordan_unit_right, hc, h4, hsx]
    all_goals module
  · simp [projectorFrame]
    module

theorem projectorFrame_encoder (x : Albert) : encoder (projectorFrame x)=x := by
  simp only [encoder,projectorFrame,Matrix.cons_val_zero,
    Matrix.cons_val_two,Matrix.tail_cons,Matrix.head_cons]
  module

theorem newtonCubicNorm_smul (a : ℝ) (x : Albert) :
    newtonCubicNorm (a • x)=a^3*newtonCubicNorm x := by
  simp only [newtonCubicNorm,jordan_smul_left,jordan_smul_right,
    trace_smul,smul_smul]
  ring



end
end Glennie
