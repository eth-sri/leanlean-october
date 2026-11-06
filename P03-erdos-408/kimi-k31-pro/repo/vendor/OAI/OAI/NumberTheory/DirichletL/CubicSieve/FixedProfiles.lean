module

public import OAI.NumberTheory.DirichletL.Eisenstein.FourierCoefficients
public import OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open FirstPassCubeLabels (columnLog)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

end SecondPassArithmetic

namespace SecondPassIntegration

section
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0)

variable [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end


open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

end SecondPassIntegration

namespace SecondPassArithmetic

section
open FirstPassCubeLabels (jLabel)
open SecondPassIntegration (elementNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open FiniteGaussPhase (canonicalProductGauss_cross_factors)
open FirstCauchyArithmetic (activeGaussRowFactor supportMobius)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    activeGaussRowFactor p hp hinj hg S T e 0 = 0 := by
  have hs : (activeSupport S T).Nonempty := by
    by_contra hn
    apply hne
    have he : activeSupport S T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [activeSupport, Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact Finset.Subset.antisymm he.1 he.2
  let : Nonempty (activeSupport S T) := hs.to_subtype
  unfold activeGaussRowFactor
  simp only [finiteSexticRow_zero, star_zero, mul_zero]

theorem activeGaussRowFactor_empty (e k : O) :
    activeGaussRowFactor p hp hinj hg ∅ ∅ e k = 1 := by
  have hempty : activeSupport (∅ : Finset ι) ∅ = ∅ := by simp [activeSupport]
  let : IsEmpty (activeSupport (∅ : Finset ι) ∅) := ⟨fun x => by simpa [hempty] using x.property⟩
  simp only [activeGaussRowFactor, finiteSexticRow, star_one, mul_one,
    canonicalProductGauss_cross_factors, Fintype.prod_empty]

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ =
      star (H₁ ∅) * H₂ ∅ := by
  have hm : supportMobius (fun i => Ideal.span {p i}) ∅ = 1 := by
    change (UniqueFactorizationMonoid.moebius (1 : Ideal O) : ℂ) = 1
    exact_mod_cast UniqueFactorizationMonoid.moebius_one
  simp only [secondGaussTerm, hm, one_mul, secondInputCoefficient, Finset.prod_empty,
    map_one, activeGaussRowFactor_empty, mul_one]
  simp [rowCoprimeMask, finiteSquarefreeRow]

theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * EisensteinSchwartzPoisson.paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [activeGaussRowFactor_zero_of_ne p hp hg hinj T S (Ne.symm hne) e, mul_zero]
  unfold secondFrequencyKernel
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne ((show S = ∅ by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd))
      rw [hz S T hneq]
      simp
    · simp [hd]
  · simp

end SecondPassArithmetic

open MeasureTheory Set Filter

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma symbol_cube_numerator (a d : O) (hd : denominatorCondition (a^3) d) :
    symbol (a^3) d=1 := by
  have hprimary : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd.2
  rw [symbol_pow_numerator a d hprimary 3]
  apply symbol_cube_of_isCoprime a d hprimary
  exact hd.1.of_isCoprime_of_dvd_left ⟨a^2,by ring⟩

theorem arithmeticResidueSum_cube (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3)=(Nat.card (AdmissibleResidue (a^3)):ℂ) := by
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Fintype (AdmissibleResidue (a^3)) := Fintype.ofFinite _
  rw [arithmeticResidueSum,tsum_fintype]
  have hterm (r : AdmissibleResidue (a^3)) :
      eisEmbedding (symbol (a^3) (denominatorRep (a^3) r.1))*
        ShortDraftTrace.breveE (cuspFrequency 0*eisEmbedding (denominatorRep (a^3) r.1)/
          eisEmbedding (a^3))=1 := by
    rw [symbol_cube_numerator a _ r.2,map_one]
    simp [cuspFrequency]
  simp only [hterm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]

lemma admissibleResidue_nonempty (c : O) (hc : c ≠ 0) : Nonempty (AdmissibleResidue c) := by
  let d : AdmissibleDenominator c := ⟨1,isCoprime_one_right,by simp⟩
  exact ⟨((residueDenominatorEquiv c hc).symm d).1⟩

theorem arithmeticResidueSum_cube_ne_zero (a : O) (ha : a ≠ 0) :
    arithmeticResidueSum 0 (a^3) ≠ 0 := by
  rw [arithmeticResidueSum_cube a ha]
  let : Finite (AdmissibleResidue (a^3)) := finite_admissibleResidue _ (pow_ne_zero 3 ha)
  let : Nonempty (AdmissibleResidue (a^3)) := admissibleResidue_nonempty _ (pow_ne_zero 3 ha)
  exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := AdmissibleResidue (a^3))).ne'

lemma denominatorCondition_congr (c d e : O) (h : 3*c ∣ d-e) :
    denominatorCondition c d ↔ denominatorCondition c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact denominatorCondition_shift c e n

lemma denominatorCondition_mul (c d t : O) (hd : denominatorCondition c d)
    (ht : denominatorCondition c t) : denominatorCondition c (d*t) := by
  refine ⟨hd.1.mul_right ht.1,?_⟩
  convert dvd_add (hd.2.mul_right t) ht.2 using 1 ; ring

lemma row_symbol_congr_modulus (c d e : O) (hlevel : (3:O) ∣ c)
    (he : (3:O) ∣ e-1) (h : 3*c ∣ d-e) : symbol c d=symbol c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+3*c*n := by linear_combination hn
  rw [hd]
  exact row_symbol_shift c e n hlevel he

lemma denominatorRep_product_congr (c t : O) (r : DenominatorResidue c) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r)-t*denominatorRep c r := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [denominatorRep_spec,map_mul,denominatorRep_spec]

def residueMultiplication (c t : O) (ht : denominatorCondition c t)
    (r : AdmissibleResidue c) : AdmissibleResidue c :=
  ⟨Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1,
    (denominatorCondition_congr c _ _ (denominatorRep_product_congr c t r.1)).2
      (denominatorCondition_mul c t _ ht r.2)⟩

lemma denominatorCondition_coprime_modulus (c t : O) (ht : denominatorCondition c t) :
    IsCoprime (3*c) t := by
  obtain ⟨n,hn⟩ := ht.2
  have h3 : IsCoprime (3:O) t := ⟨-n,1,by linear_combination hn⟩
  exact h3.mul_left ht.1

lemma residueMultiplication_injective (c t : O) (ht : denominatorCondition c t) :
    Function.Injective (residueMultiplication c t ht) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {3*c}) t) := by
    have hh := (denominatorCondition_coprime_modulus c t ht).map
      (Ideal.Quotient.mk (Ideal.span {3*c}))
    have hz : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    simpa only [hz,isCoprime_zero_left] using hh
  intro r q heq
  apply Subtype.ext
  exact hunit.mul_left_cancel (congrArg Subtype.val heq)

def residueMultiplicationEquiv (c : O) (hc : c ≠ 0) (t : O)
    (ht : denominatorCondition c t) : AdmissibleResidue c ≃ AdmissibleResidue c := by
  letI : Finite (AdmissibleResidue c) := finite_admissibleResidue c hc
  exact Equiv.ofBijective (residueMultiplication c t ht)
    ⟨residueMultiplication_injective c t ht,
      Finite.surjective_of_injective (residueMultiplication_injective c t ht)⟩

lemma residueMultiplication_phase (c : O) (hlevel : (3:O) ∣ c) (t : O)
    (ht : denominatorCondition c t) (r : AdmissibleResidue c) :
    symbol c (denominatorRep c (residueMultiplication c t ht r).1)=
      symbol c t*symbol c (denominatorRep c r.1) := by
  change symbol c (denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) t*r.1))=
    symbol c t*symbol c (denominatorRep c r.1)
  rw [row_symbol_congr_modulus c _ (t*denominatorRep c r.1) hlevel
    (denominatorCondition_mul c t _ ht r.2).2 (denominatorRep_product_congr c t r.1)]
  exact symbol_mul_denominator c t (denominatorRep c r.1)

lemma arithmeticResidueSum_zero (c : O) :
    arithmeticResidueSum 0 c=∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c r.1)) := by
  simp only [arithmeticResidueSum,cuspFrequency,map_zero,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]

theorem arithmeticResidueSum_constant_eigen (c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c)
    (t : O) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum 0 c=arithmeticResidueSum 0 c := by
  rw [arithmeticResidueSum_zero]
  have heq := (residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c => eisEmbedding (symbol c (denominatorRep c r.1)))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t*symbol c (denominatorRep c r.1)) := by
      simp only [map_mul,tsum_mul_left]
    _ = _ := by
      convert heq using 1
      apply tsum_congr
      intro r
      exact congrArg eisEmbedding (residueMultiplication_phase c hlevel t ht r).symm

theorem arithmeticResidueSum_ne_zero_forces_trivial (c : O) (hc : c ≠ 0)
    (hlevel : (3:O) ∣ c) (hA : arithmeticResidueSum 0 c ≠ 0) :
    ∀ t : O, denominatorCondition c t → symbol c t=1 := by
  intro t ht
  apply eisEmbedding_injective
  rw [map_one]
  apply (mul_right_cancel₀ hA)
  rw [arithmeticResidueSum_constant_eigen c hc hlevel t ht,one_mul]

end CubicEisenstein


namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma coprime_of_dvd_sub_one (a b : O) (h : a ∣ b-1) : IsCoprime a b := by
  obtain ⟨r,hr⟩ := h
  exact ⟨-r,1,by linear_combination hr⟩

lemma primary_coprime_three (p : O) (hp : lambda^2 ∣ p-1) : IsCoprime p (3:O) :=
  (coprime_of_dvd_sub_one 3 p (three_dvd_primary_sub_one p hp)).symm

lemma exists_one_mod_and_prescribed (p m x : O) (hpm : IsCoprime p m) :
    ∃ t : O, m ∣ t-1 ∧ p ∣ t-x := by
  obtain ⟨r,u,hu⟩ := hpm
  refine ⟨1+m*u*(x-1),⟨u*(x-1),by ring⟩,⟨-r*(x-1),?_⟩⟩
  linear_combination (x-1)*hu

theorem constant_coefficient_primary_prime_exponent (c p b : O) (n : ℕ)
    (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hp : Prime p) (hprimary : lambda^2 ∣ p-1)
    (hpb : ¬p ∣ b) (hfactor : c=p^n*b) (hA : arithmeticResidueSum 0 c ≠ 0) :
    3 ∣ n := by
  by_contra hn
  let P : Ideal O := Ideal.span {p}
  let : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ P := primary_maximal_divisor_good p hprimary P (Ideal.subset_span (by simp []))
  have hchar : (cubicChar P hg)^n ≠ 1 := by
    intro heq
    have hd := orderOf_dvd_of_pow_eq_one heq
    rw [cubicChar_order P hg] at hd
    exact hn hd
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp hchar
  rw [MulChar.pow_apply_coe] at hu
  obtain ⟨x,hx⟩ := Ideal.Quotient.mk_surjective (u : O ⧸ P)
  have hp9 : IsCoprime p (9:O) := by
    simpa only [show (3:O)^2=9 by norm_num] using (primary_coprime_three p hprimary).pow_right (n := 2)
  have hpm : IsCoprime p (9*b) := hp9.mul_right (hp.coprime_iff_not_dvd.mpr hpb)
  obtain ⟨t,htm,htp⟩ := exists_one_mod_and_prescribed p (9*b) x hpm
  have h9 : (9:O) ∣ t-1 := (dvd_mul_right 9 b).trans htm
  have hb : b ∣ t-1 := (dvd_mul_left b 9).trans htm
  have h3 : (3:O) ∣ t-1 := (show (3:O) ∣ 9 from ⟨3,by norm_num⟩).trans h9
  have htprimary : lambda^2 ∣ t-1 := lambda_sq_dvd_three.trans h3
  have htu : Ideal.Quotient.mk P t=(u : O ⧸ P) := by
    rw [← hx]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr htp)
  have hpt : IsCoprime p t := hp.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hz : Ideal.Quotient.mk P t=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    rw [htu] at hz
    exact Units.ne_zero u hz)
  have hbt : IsCoprime b t := coprime_of_dvd_sub_one b t hb
  have hct : IsCoprime c t := by
    rw [hfactor]
    exact hpt.pow_left.mul_left hbt
  have htriv := arithmeticResidueSum_ne_zero_forces_trivial c hc hlevel hA t ⟨hct,h3⟩
  have hbsym : symbol b t=1 := by
    have hh := symbol_denominator_congr b t 1 htprimary (by simp) h9 hb
    simpa only [symbol_one] using hh
  have hpsym : symbol p t=cubicChar P hg (u : O ⧸ P) := by
    rw [symbol_reciprocity p t hp.ne_zero (primary_ne_zero t htprimary) hprimary htprimary]
    change idealSymbol P t=_
    rw [idealSymbol_prime P hg,htu]
  rw [hfactor,symbol_mul_numerator _ _ t htprimary,symbol_pow_numerator p t htprimary,
    hbsym,mul_one,hpsym] at htriv
  exact hu htriv

end CubicEisenstein

end

end OAI
