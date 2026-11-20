module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Whole-plane integration by parts from regular one-dimensional slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

section
variable {f : (ℝ × ℝ) → ℝ} {X v : ℝ} (hf : DifferentiableAt ℝ f (X, v))
include hf

/-- The position slice derivative is the literal position jet. -/
theorem bellman_hasDerivAt_first :
    HasDerivAt (fun Y => f (Y, v)) (bellmanDx f (X, v)) X := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X v))
  simpa only [bellmanDx, Function.comp_def, id_eq] using hh

/-- The velocity slice derivative is the literal velocity jet. -/
theorem bellman_hasDerivAt_second :
    HasDerivAt (fun w => f (X, w)) (bellmanDv f (X, v)) v := by
  have hh := hf.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v X).prodMk (hasDerivAt_id v))
  simpa only [bellmanDv, Function.comp_def, id_eq] using hh

end

end HypoellipticAleksandrov.KineticAleksandrov
