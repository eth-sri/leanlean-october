module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxRotatedRapidDecay

noncomputable def logarithmicRadialFlow (t : ℝ) (y : ℂˣ) : ℂˣ :=
  Units.mk0 ((Real.exp (t / 2) : ℂ) * (y : ℂ)) (mul_ne_zero (by exact_mod_cast Real.exp_ne_zero (t / 2)) y.ne_zero)

noncomputable def logarithmicDerivative (F : ℂˣ → ℂ) : ℂˣ → ℂ :=
  fun y => deriv (fun t : ℝ => F (logarithmicRadialFlow t y)) 0

lemma logarithmicRadialFlow_add (s t : ℝ) (z : ℂˣ) :
    logarithmicRadialFlow s (logarithmicRadialFlow t z) =
      logarithmicRadialFlow (s + t) z := by
  apply Units.ext
  simp only [logarithmicRadialFlow, Units.val_mk0]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

@[simp] lemma logarithmicRadialFlow_zero (z : ℂˣ) : logarithmicRadialFlow 0 z = z := by
  simp [logarithmicRadialFlow]

lemma iteratedDeriv_logarithmicRadialFlow (f : ℂˣ → ℂ) (j : ℕ) (z : ℂˣ) (t : ℝ) :
    iteratedDeriv j (fun s => f (logarithmicRadialFlow s z)) t =
      ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow t z) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    rw [iteratedDeriv_succ, Function.iterate_succ_apply', logarithmicDerivative]
    have hfun : (fun s => ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow s z)) =
        iteratedDeriv j (fun s => f (logarithmicRadialFlow s z)) := by
      funext s
      exact (ih s).symm
    simp_rw [logarithmicRadialFlow_add]
    rw [deriv_comp_add_const
      (fun s => ((logarithmicDerivative^[j]) f) (logarithmicRadialFlow s z)) t 0]
    simp only [zero_add]
    rw [hfun]

lemma iteratedDeriv_scale (g : ℝ → ℂ) (c : ℝ) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (fun s => g (c * s)) t =
      (c : ℂ) ^ j * iteratedDeriv j g (c * t) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    have he := funext ih
    rw [iteratedDeriv_succ, he, deriv_const_mul_field]
    rw [deriv_comp_mul_left c (iteratedDeriv j g) t]
    simp [iteratedDeriv_succ] <;> ring

lemma iteratedDeriv_logarithmicRadialFlow_div (f : ℂˣ → ℂ) (r : ℝ) (j : ℕ) (z : ℂˣ) :
    iteratedDeriv j (fun t => f (logarithmicRadialFlow (t / r) z)) 0 =
      (r⁻¹ : ℂ) ^ j * ((logarithmicDerivative^[j]) f) z := by
  have hfun : (fun t => f (logarithmicRadialFlow (t / r) z)) =
      fun t => (fun s => f (logarithmicRadialFlow s z)) (r⁻¹ * t) := by
    funext t
    rw [div_eq_mul_inv, mul_comm t]
  rw [hfun]
  simpa [mul_zero, iteratedDeriv_logarithmicRadialFlow, logarithmicRadialFlow_zero] using (iteratedDeriv_scale (fun s => f (logarithmicRadialFlow s z)) r⁻¹ j 0)

end DedekindZetaZeroFree.KPCplxRotatedRapidDecay
