module

public import OAI.NumberTheory.DirichletL.GaussSum.ThetaLocalRows

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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar

open Filter Asymptotics

namespace TargetLocalReduction

end TargetLocalReduction

namespace ActualEisensteinCubic

open AddChar MulChar

end ActualEisensteinCubic

open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter

namespace ShortDraftHeckeBridge

abbrev O := ActualEisensteinSieve.O

noncomputable def normFiberCoeff (weight : Ideal O → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ I ∈ (Ideal.finite_setOfPred_absNorm_eq (S := O) n).toFinset, weight I

noncomputable def pairInverseCoeff
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ℕ → ℂ :=
  (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) ⍟
    (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ))

theorem normFiber_LSeries_eq_pair_inverse
    {q r : ℕ} (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (s : ℂ) :
    LSeries (normFiberCoeff weight) s = LSeries (pairInverseCoeff χ ψ) s := by
  exact LSeries_congr (fun {n} hn => hcoeff n hn) s

theorem pair_inverse_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * ψ.LFunction s * LSeries (pairInverseCoeff χ ψ) s = 1 := by
  have hχsum : LSeriesSummable (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul χ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hψsum : LSeriesSummable (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s := by
    exact DirichletCharacter.LSeriesSummable_mul ψ
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  rw [pairInverseCoeff, LSeries_convolution' hχsum hψsum,
    χ.LFunction_eq_LSeries hs, ψ.LFunction_eq_LSeries hs]
  have hχ := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hψ := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  change LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hχ
  change LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s = 1 at hψ
  calc
    LSeries (χ ·) s * LSeries (ψ ·) s *
      (LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s *
        LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) =
      (LSeries (χ ·) s * LSeries (fun n : ℕ => χ n * (ArithmeticFunction.moebius n : ℂ)) s) *
      (LSeries (ψ ·) s * LSeries (fun n : ℕ => ψ n * (ArithmeticFunction.moebius n : ℂ)) s) := by ring
    _ = 1 := by rw [hχ, hψ]; ring

end ShortDraftHeckeBridge
private theorem pairing_algebra
    (g1 g2 gm G alpha eps t : ℂ)
    (halpha : alpha * star alpha = 1)
    (hg1 : g1 * star g1 = 1)
    (hprod : g1 * g2 = -alpha * G)
    (hpair : g1 * gm = eps) :
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have h2 : g2 = -(star g1) * alpha * G := by
    calc
      g2 = (g1 * star g1) * g2 := by rw [hg1]; ring
      _ = star g1 * (g1 * g2) := by ring
      _ = star g1 * (-alpha * G) := by rw [hprod]
      _ = _ := by ring
  have hA : star alpha * g2 = (-star g1) * G := by
    rw [h2]
    calc
      star alpha * (-(star g1) * alpha * G) =
          (alpha * star alpha) * ((-star g1) * G) := by ring
      _ = (-star g1) * G := by rw [halpha]; ring
  have hm : gm = eps * star g1 := by
    calc
      gm = (g1 * star g1) * gm := by rw [hg1]; ring
      _ = star g1 * (g1 * gm) := by ring
      _ = eps * star g1 := by rw [hpair]; ring
  have hB : (-gm) * G = eps * (star alpha * g2) := by
    rw [hm, hA]
    ring
  have hC : (-g1) * star G = alpha * star g2 := by
    have h := congrArg (fun z : ℂ => star z) hA
    simp only [star_mul, star_neg, star_star] at h
    calc
      (-g1) * star G = star G * (-g1) := by ring
      _ = star g2 * alpha := h.symm
      _ = alpha * star g2 := by ring
  have hD : (-star gm) * star G = star eps * (alpha * star g2) := by
    have h := congrArg (fun z : ℂ => star z) hB
    simpa only [star_mul, star_neg, star_star, mul_comm, mul_left_comm, mul_assoc] using h
  exact ⟨by rw [hA], by rw [hB], by rw [hC], by rw [hD]⟩

namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
open scoped ComplexConjugate

private theorem breveGamma1_mul_star_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) :
    breveGamma1 P hgood p hP hp * star (breveGamma1 P hgood p hP hp) = 1 := by
  subst P
  let χ := canonicalSextic (Ideal.span {p}) hgood
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates p hp
  let s : ℝ := ‖eisEmbedding p‖
  have hψ : ψ.IsPrimitive :=
    eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp
  have hχ1 : χ ≠ 1 := by
    simpa only [pow_one] using
      (canonicalSextic_pow_ne_one (Ideal.span {p}) hgood hchar
        (by decide : (1 : ℕ) ≠ 0) (by decide : (1 : ℕ) < 6))
  have hnormO := primary_generator_mul_conj_eq_card
    (Ideal.span {p}) hgood p rfl hprimary
  have hnormC := congrArg eisEmbedding hnormO
  rw [map_mul, eisEmbedding_conjO, map_natCast] at hnormC
  have hs : (s : ℂ) ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℂ) := by
    simpa only [s, ← starRingEnd_apply, Complex.mul_conj',
      Nat.card_eq_fintype_card] using hnormC
  have hsreal : s ^ 2 = (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by
    exact Complex.ofReal_injective (by exact_mod_cast hs)
  have hcard : 0 < (Fintype.card (O ⧸ Ideal.span {p}) : ℝ) := by positivity
  have hsroot : s = Real.sqrt (Fintype.card (O ⧸ Ideal.span {p})) := by
    nlinarith [Real.sq_sqrt hcard.le, Real.sqrt_nonneg
      (Fintype.card (O ⧸ Ideal.span {p})), norm_nonneg (eisEmbedding p)]
  have hs0 : s ≠ 0 := by
    dsimp [s]
    exact (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hp))
  have hnorm : ‖breveGamma1 (Ideal.span {p}) hgood p rfl hp‖ = 1 := by
    change ‖gaussSum χ ψ / (s : ℂ)‖ = 1
    rw [norm_div, ShortDraftGauss.norm_gaussSum_eq_sqrt_card χ ψ hχ1 hψ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    rw [← hsroot]
    exact div_self hs0
  rw [← starRingEnd_apply, Complex.mul_conj', hnorm]
  norm_num

theorem first_poisson_prime_sign_pairing
    (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (p : O) (hP : P = Ideal.span {p}) (hp : p ≠ 0)
    (hprimary : lambda ^ 2 ∣ p - 1) (h : O) :
    let alpha : ℂ := eisEmbedding p / (‖eisEmbedding p‖ : ℂ)
    let g1 := breveGamma1 P hgood p hP hp
    let g2 := breveGamma2 P hgood p hP hp
    let gm := breveGammaMinus1 P hgood p hP hp
    let G := breveLocalG P hgood p hP hp
    let t := canonicalSextic P hgood (Ideal.Quotient.mk P h)
    let eps := canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O))
    (-star g1) * G * t = (star alpha * g2) * t ∧
    (-gm) * G * t = eps * (star alpha * g2) * t ∧
    (-g1) * star G * t⁻¹ = (alpha * star g2) * t⁻¹ ∧
    (-star gm) * star G * t⁻¹ = star eps * (alpha * star g2) * t⁻¹ := by
  have hz : eisEmbedding p ≠ 0 := eisEmbedding_ne_zero hp
  have hs : (‖eisEmbedding p‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  have hanorm : ‖eisEmbedding p / (‖eisEmbedding p‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (eisEmbedding p))]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have ha : (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
      star (eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) = 1 := by
    rw [← starRingEnd_apply, Complex.mul_conj', hanorm]
    norm_num
  have hg1 := breveGamma1_mul_star_one P hgood hchar p hP hp hprimary
  have hprod := breveGamma1_gamma2_eq_neg_alpha_G
    P hgood hchar p hP hp hprimary
  have hprod' :
      breveGamma1 P hgood p hP hp * breveGamma2 P hgood p hP hp =
        -(eisEmbedding p / (‖eisEmbedding p‖ : ℂ)) *
          breveLocalG P hgood p hP hp := by
    simpa only [neg_div] using hprod
  have hpair := breveGamma1_gammaMinus1
    P hgood hchar p hP hp hprimary
  dsimp only
  exact pairing_algebra
    (breveGamma1 P hgood p hP hp)
    (breveGamma2 P hgood p hP hp)
    (breveGammaMinus1 P hgood p hP hp)
    (breveLocalG P hgood p hP hp)
    (eisEmbedding p / (‖eisEmbedding p‖ : ℂ))
    (canonicalSextic P hgood (Ideal.Quotient.mk P (-1 : O)))
    (canonicalSextic P hgood (Ideal.Quotient.mk P h))
    ha hg1 hprod' hpair

end ActualEisensteinCubic

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

end ShortDraftLocal

end

end OAI
