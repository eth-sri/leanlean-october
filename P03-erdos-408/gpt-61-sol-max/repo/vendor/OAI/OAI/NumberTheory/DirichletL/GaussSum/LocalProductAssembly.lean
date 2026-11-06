module

public import OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
public import OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization

@[expose] public section

namespace OAI

section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 

namespace ActualEisensteinCubic

open ConcreteTraceCRT
open scoped ComplexConjugate

theorem canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by
  let χ := canonicalSextic P hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six P hgood
  have hval : χ (u : O ⧸ P) ^ 6 = 1 := by
    rw [← χ.pow_apply_coe 6 u, hχ6, MulChar.one_apply_coe]
  exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hval (by decide))

end ActualEisensteinCubic

namespace FourierBridge
open scoped ContDiff    

end FourierBridge

namespace AnalyticBridge

end AnalyticBridge

namespace FourierBridge
 

theorem logPhase_norm  t y  : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)

theorem logPhase_continuous_left  y  :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop

end FourierBridge

namespace AnalyticBridge
 

end AnalyticBridge

namespace PowerExtraction

end PowerExtraction

namespace ActualEisensteinCubic



theorem canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P)  a  :
    canonicalSextic P hgood (Ideal.Quotient.mk P (a ^ 6)) =
      if a ∈ P then 0 else 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  rw [map_pow, ShortDraftSextic.sextic_power_is_unit_mask
    (canonicalSextic P hgood) (canonicalSextic_pow_six P hgood)]
  by_cases ha : a ∈ P
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]
  · simp [ha, isUnit_iff_ne_zero, Ideal.Quotient.eq_zero_iff_mem]

end ActualEisensteinCubic

namespace PoissonFirstLocal

end PoissonFirstLocal

end

end OAI
