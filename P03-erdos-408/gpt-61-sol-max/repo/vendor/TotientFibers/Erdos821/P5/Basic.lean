module
public import Mathlib.Tactic

public import Erdos821.Blueprint.Classical

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.P5Core
open Blueprint.Analytic

@[simp] theorem norm_mellin  n t  : ‖mellin n t‖ = 1 := by
  simp [Blueprint.Analytic.mellin, Complex.norm_exp]

@[simp] theorem mellin_one  t  : mellin 1 t = 1 := by
  simp [Blueprint.Analytic.mellin]

theorem mellin_mul  a b t  (ha : 0 < a) (hb : 0 < b) :
    mellin (a * b) t = mellin a t * mellin b t := by
  simp [Blueprint.Analytic.mellin, Real.log_mul ha.ne' hb.ne', mul_add, Complex.exp_add]

theorem mellin_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)  t 
    (hf : ∀ i ∈ s, 0 < f i) : mellin (∏ i ∈ s, f i) t = ∏ i ∈ s, mellin (f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mellin_mul _ _ _ (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_pos (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem continuous_mellin  n  : Continuous (mellin n) := by
  unfold Blueprint.Analytic.mellin
  fun_prop

theorem continuous_dp  s   c  : Continuous (dp s c) := continuous_finsetSum s fun n x => Continuous.mul continuous_const (Erdos821.P5Core.continuous_mellin ↑n)

end Erdos821.P5Core
