module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.OriginJetsIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Whole-plane integration by parts from regular one-dimensional slices -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory

/-- The position slice derivative is the literal position jet. -/
theorem bellman_hasDerivAt_first {f X v}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun Y => f (Y, v)) (bellmanDx f (X, v)) X := by
  simpa only [bellmanDx, Function.comp_def, id_eq] using (hf.hasFDerivAt.comp_hasDerivAt X ((hasDerivAt_id X).prodMk (hasDerivAt_const X v)))

/-- The velocity slice derivative is the literal velocity jet. -/
theorem bellman_hasDerivAt_second {f X v}
    (hf : DifferentiableAt ℝ f (X, v)) :
    HasDerivAt (fun w => f (X, w)) (bellmanDv f (X, v)) v := by
  simpa only [bellmanDv, Function.comp_def, id_eq] using (hf.hasFDerivAt.comp_hasDerivAt v ((hasDerivAt_const v X).prodMk (hasDerivAt_id v)))

end HypoellipticAleksandrov.KineticAleksandrov
