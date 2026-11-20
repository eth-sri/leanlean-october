module
public import OAI.NumberTheory.DirichletL.Cusp.MatrixPhases
public import OAI.NumberTheory.DirichletL.GaussSum.SexticNormalization

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
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
open scoped ContDiff FourierTransform SchwartzMap

end FourierBridge

namespace AnalyticBridge

end AnalyticBridge

namespace FourierBridge
open scoped FourierTransform SchwartzMap

theorem logPhase_norm (t y : ℝ) : ‖logPhase t y‖ = 1 := by
  simpa [logPhase] using
    Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * y)

theorem logPhase_continuous_left (y : ℝ) :
    Continuous (fun t : ℝ => logPhase t y) := by
  unfold logPhase
  fun_prop

end FourierBridge

namespace AnalyticBridge
open scoped FourierTransform SchwartzMap

end AnalyticBridge

namespace PowerExtraction

end PowerExtraction

namespace ActualEisensteinCubic

section

open AddChar MulChar

@[instance_reducible] noncomputable def crtIntersectionFintype
    {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hdistinct : Function.Injective (fun i => Ideal.span {p i})) :
    Fintype (O ⧸ ⨅ i, Ideal.span {p i}) := by
  classical
  letI (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  have hcop : Pairwise
      (fun i k => IsCoprime (Ideal.span {p i}) (Ideal.span {p k})) := by
    intro i k hik
    exact Ideal.isCoprime_of_isMaximal (hdistinct.ne hik)
  let e := Ideal.quotientInfRingEquivPiQuotient
    (fun i => Ideal.span {p i}) hcop
  exact Fintype.ofEquiv (∀ i, O ⧸ Ideal.span {p i}) e.symm.toEquiv

end

theorem canonicalSextic_sixth_power_mask (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (a : O) :
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
