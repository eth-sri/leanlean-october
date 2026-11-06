module

public import OAI.NumberTheory.DirichletL.GaussSum.CubicNormalization

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

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGamma1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

noncomputable def breveGamma3 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood ^ 3)
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

theorem canonicalSextic_pow_three_quadratic (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 3 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.1]
  ext x
  change eisEmbedding ((quadraticChar (O ⧸ P) x : ℤ) : O) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  simp

theorem breveGamma1_gamma2_relation (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (canonicalSextic P hgood
        (Ideal.Quotient.mk P (4 : O)))⁻¹ *
      breveGamma3 P hgood p hP hp *
        (breveGamma2 P hgood p hP hp) ^ 3 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ2 : χ ^ 2 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (2 : ℕ) ≠ 0) (by decide : (2 : ℕ) < 6)
  have hχ4 : χ ^ 4 ≠ 1 := canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
    (by decide : (4 : ℕ) ≠ 0) (by decide : (4 : ℕ) < 6)
  have hχ3 : χ ^ 3 = (quadraticChar (O ⧸ Ideal.span {p})).ringHomComp
      (Int.castRingHom ℂ) := canonicalSextic_pow_three_quadratic (Ideal.span {p}) hgood
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hmul := JacobiQuadratic.normalized_gauss_sextic_relation
    χ ψ hchar hψ hχ1 hχ2 hχ4 hχ3 hχ6 s hs hs0
  have hfour : (4 : O ⧸ Ideal.span {p}) ≠ 0 := by
    have htwo : (2 : O ⧸ Ideal.span {p}) ≠ 0 := Ring.two_ne_zero hchar
    convert pow_ne_zero 2 htwo using 1 ; norm_num
  have hχfour : χ (4 : O ⧸ Ideal.span {p}) ≠ 0 :=
    χ.apply_ne_zero_iff.mpr (isUnit_iff_ne_zero.mpr hfour)
  change χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3 at hmul
  change breveGamma1 (Ideal.span {p}) hgood p rfl hp *
    breveGamma2 (Ideal.span {p}) hgood p rfl hp =
    (χ 4)⁻¹ * breveGamma3 (Ideal.span {p}) hgood p rfl hp *
      breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3
  calc
    breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp =
      (χ 4)⁻¹ * (χ 4 * breveGamma1 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp) := by field_simp
    _ = (χ 4)⁻¹ * (breveGamma3 (Ideal.span {p}) hgood p rfl hp *
        breveGamma2 (Ideal.span {p}) hgood p rfl hp ^ 3) := by rw [hmul]
    _ = _ := by ring

end

section

open EisensteinEmbedding ConcreteTraceCRT IdealGaussCRT

end

section

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveLocalG (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  (canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)))⁻¹ *
    breveGamma3 P hgood p hP hp

theorem breveGamma1_gamma2_eq_neg_alpha_G (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
      (-(eisEmbedding p) / (‖eisEmbedding p‖ : ℂ)) *
        breveLocalG P hgood p hP hp := by
  rw [breveGamma1_gamma2_relation P hgood hchar p hP hp hprimary,
    breveGamma2_cube P hgood p hP hp hprimary]
  unfold breveLocalG
  ring

end

open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE

end ActualEisensteinCubic

namespace ConcreteBreveE

open EisensteinEmbedding ConcreteTraceCRT

noncomputable def normalizedTraceGauss
    (a : O) (ha : a ≠ 0) (χ : MulChar (O ⧸ Ideal.span {a}) ℂ) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  letI : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  exact gaussSum χ (eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates a ha) / (‖eisEmbedding a‖ : ℂ)

end ConcreteBreveE

namespace FixedRayActiveSet

open scoped BigOperators

end FixedRayActiveSet

namespace CubeInversion

end CubeInversion

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace

noncomputable def breveGammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hp : p ≠ 0) : ℂ :=
  gaussSum (canonicalSextic P hgood)⁻¹
    (hP.symm ▸ eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp) /
      (‖eisEmbedding p‖ : ℂ)

private theorem canonicalSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (canonicalSextic P hgood) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  change orderOf (Φ (sexticChar P hgood)) = 6
  rw [orderOf_injective Φ hΦ, sexticChar_order P hgood hchar]

theorem breveGamma1_gammaMinus1 (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * breveGammaMinus1 P hgood p hP hp =
      canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)) := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℂ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hχ6 : χ ^ 6 = 1 := canonicalSextic_pow_six (Ideal.span {p}) hgood
  have horder : orderOf χ = 6 :=
    canonicalSextic_order_six (Ideal.span {p}) hgood hchar
  have hχ5 : χ ^ 5 = χ⁻¹ := by
    apply (inv_eq_of_mul_eq_one_right ?_).symm
    calc
      χ * χ ^ 5 = χ ^ 6 := by group
      _ = 1 := hχ6
  have hprod := gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ1 hψ
  rw [horder, show 6 - 1 = 5 by decide, hχ5] at hprod
  have hs : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    have hnormO := primary_generator_mul_conj_eq_card
      (Ideal.span {p}) hgood p rfl hprimary
    have hnormC := congrArg eisEmbedding hnormO
    rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  change (gaussSum χ ψ / s) * (gaussSum χ⁻¹ ψ / s) = χ (-1)
  field_simp
  rw [hs]
  simpa only [mul_comm] using hprod

end ActualEisensteinCubic

namespace PowerExtraction

end PowerExtraction

end

end OAI
