module
public import OAI.NumberTheory.DirichletL.Detector.Physical
public import OAI.NumberTheory.DirichletL.Detector.RowAnalytic
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

section
variable (C : CalibrationData) (a : O)
include C a
theorem CalibrationData.residueMonoid_norm_le_one :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

theorem CalibrationData.Xi_norm_one
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    exact (FiniteRayExpansion.norm_char_unit C.residue hu.unit)
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  pm_7600 C.generator a ha
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]
end

theorem physicalRow_integrable (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (rowCoefficient η C.Xi s hs m)
    (fun a => rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ

end SevenEighths.ProbePhysical
end

end OAI
