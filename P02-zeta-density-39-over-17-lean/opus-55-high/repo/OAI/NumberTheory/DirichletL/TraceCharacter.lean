module
public import OAI.NumberTheory.DirichletL.Foundation
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

export OAI.EisensteinSchwartzPoisson (O)

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

section
variable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ)
include χ hχ
theorem transform_eq (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem gaussScalar_norm_sq :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding :
    ‖gaussScalar c χ‖ = ‖eisEmbedding c‖ := by
  rw [gaussScalar_norm c χ hχ, ← eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]
end

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖eisEmbedding c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))]

section
variable (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ)
include W scale hscale χ hχ
theorem primitive_radial_paper_poisson :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  pm_8357

theorem primitive_radial_paper_poisson_normalized :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp
end

end SevenEighths.TraceCharacter

end

end OAI
