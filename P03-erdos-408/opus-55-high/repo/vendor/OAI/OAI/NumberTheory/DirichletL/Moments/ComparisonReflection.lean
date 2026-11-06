module

public import OAI.NumberTheory.DirichletL.Hecke.Primitive
public import OAI.NumberTheory.DirichletL.Hecke.Dyadic
public import OAI.NumberTheory.DirichletL.Detector.RadialMellin

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport

lemma residue_nontrivial (c : HeckeFamily.O) (χ : MulChar (HeckeFamily.O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (HeckeFamily.O⧸Ideal.span {c}) := by
  by_contra h
  have  := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp_all

lemma residue_zero (c : HeckeFamily.O) [NeZero c] (χ : MulChar (HeckeFamily.O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:HeckeFamily.Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : HeckeFamily.O => elementCoeff η z*W (‖eisEmbedding z‖^2/X))) :
    (∑' z : HeckeFamily.O,elementCoeff η z*W (‖eisEmbedding z‖^2/X))=
      6*∑' I : UnrestrictedIdealReindex.NonzeroIdeal,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z : HeckeFamily.O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) hs
    (by simp_all)
    (fun u z => by rw [elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_idealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : HeckeFamily.O => ‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z : HeckeFamily.O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (HeckeFamily.O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : HeckeFamily.O) [NeZero c]
    (χ : MulChar (HeckeFamily.O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:HeckeFamily.Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    (∑' I : UnrestrictedIdealReindex.NonzeroIdeal,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' I : UnrestrictedIdealReindex.NonzeroIdeal,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hQ : 0<‖eisEmbedding c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : HeckeFamily.O => ‖W (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : HeckeFamily.O => ‖paperRadialFourier W
      (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X))‖) := by
    convert paperRadialFourier_lattice_summable_norm W (X/‖eisEmbedding c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : HeckeFamily.O,elementCoeff (character c χ hu) z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' z : HeckeFamily.O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
    change (∑' z : HeckeFamily.O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  grind

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : UnrestrictedIdealReindex.NonzeroIdeal,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : HeckeFamily.O) [NeZero c]
    (χ : MulChar (HeckeFamily.O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:HeckeFamily.Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY : 0<‖eisEmbedding c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  grind

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
