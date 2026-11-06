module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Whole-plane integration by parts from regular one-dimensional slices -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

variable {f : (ℝ × ℝ) → ℝ} {X v : ℝ}

/-- The position slice derivative is the literal position jet. -/
theorem bellman_hasDerivAt_first 
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun Y => f (Y, v)) (bellmanDx f (X, v)) X := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X v))
  aesop

/-- The velocity slice derivative is the literal velocity jet. -/
theorem bellman_hasDerivAt_second 
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun w => f (X, w)) (bellmanDv f (X, v)) v := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v X).prodMk (hasDerivAt_id v))
  aesop

end HypoellipticAleksandrov.KineticAleksandrov
