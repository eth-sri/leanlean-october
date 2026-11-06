module
public import OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
public import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
import WeylPort.Analytic.RealLaplace

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
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnG columnPrimeCoprime quadraticCrossPhase)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter rayCharacter gCoeff crossCoeff)

def rayMonoid (χ : RayCharacter) : O →* ℂ where
  toFun := rayCharacter χ
  map_one' := by simp [rayCharacter]
  map_mul' := RayFourExpansion.rayCharacter_mul χ

def conjugateRayMonoid (χ : RayCharacter) : O →* ℂ :=
  (starRingEnd ℂ).toMonoidHom.comp (rayMonoid χ)

section
variable (χ : RayCharacter) (a : O)
include χ a
@[simp] theorem rayMonoid_apply :
    rayMonoid χ a = rayCharacter χ a := rfl
@[simp] theorem conjugateRayMonoid_apply :
    conjugateRayMonoid χ a = star (rayCharacter χ a) := rfl
end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem columnG_eq_ray_sum
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i ∈ S, p i) := by
  have h := RayFourExpansion.canonicalProductG_character_expansion
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, Finset.prod_coe_sort] using h

def secondInputCoefficient (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏ i ∈ S, p i) * rowCoprimeMask (fun i => Ideal.span {p i}) S m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c ^ 4 *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * H S

theorem secondColumnMinus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnMinus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e k H S := by
  pm_5428 secondColumnMinus
  pm_3523 secondPreColumn secondInputCoefficient MonoidHom.mul_apply conjugateRayMonoid_apply

theorem secondColumnPlus_ray_expansion
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (S : Finset ι) :
    secondColumnPlus p hp hcop hg (secondInputCoefficient p hg Ψ m c d H) e k S =
      ∑ χ : RayCharacter, star (gCoeff χ) *
        secondPreColumn p hp hcop hg (conjugateRayMonoid χ * Ψ) m c d e (-k) H S := by
  pm_3794 hk S k
  pm_5428 secondColumnPlus
  pm_93 secondPreColumn secondInputCoefficient MonoidHom.mul_apply conjugateRayMonoid_apply hk
  ring

theorem second_gauss_ray_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) (hd : Disjoint S T) :
    star (supportMobius (fun i => Ideal.span {p i}) S * secondInputCoefficient p hg Ψ₁ m c d H₁ S) *
      (supportMobius (fun i => Ideal.span {p i}) T * secondInputCoefficient p hg Ψ₂ m c d H₂ T) *
      activeGaussRowFactor p hp hinj hg T S e k =
    ∑ b : RayCharacter, ∑ a : RayCharacter, ∑ χ : RayCharacter, ∑ η : RayCharacter,
      (crossCoeff χ η * gCoeff a * star (gCoeff b)) *
        star (secondPreColumn p hp hcop hg
          (conjugateRayMonoid η * (conjugateRayMonoid a * Ψ₁)) m c d e k H₁ S) *
        secondPreColumn p hp hcop hg
          (rayMonoid χ * (conjugateRayMonoid b * Ψ₂)) m c d e (-k) H₂ T := by
  rw [mobius_second_gauss_restore p hp hinj hcop hg hc hpr S T hd,
    secondColumnMinus_ray_expansion p hp hcop hg hc hpr,
    secondColumnPlus_ray_expansion p hp hcop hg hc hpr,
    RayFourExpansion.quadraticCrossPhase_character_expansion p hp hcop hg hc T S hd.symm]
  pm_93 star_sum star_mul star_star Finset.sum_mul Finset.mul_sum
  pm_3397 b hb a ha
  pm_3397 χ hχ η hη
  pm_232 secondPreColumn MonoidHom.mul_apply conjugateRayMonoid_apply rayMonoid_apply star_mul star_star
  ring

end

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

abbrev SecondRayIndex := (RayCharacter × RayCharacter) × (RayCharacter × RayCharacter)

def secondRayCoefficient (r : SecondRayIndex) : ℂ :=
  crossCoeff r.2.1 r.2.2 * gCoeff r.1.2 * star (gCoeff r.1.1)

def secondRayMinus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  conjugateRayMonoid r.2.2 * (conjugateRayMonoid r.1.2 * Ψ)

def secondRayPlus (Ψ : O →* ℂ) (r : SecondRayIndex) : O →* ℂ :=
  rayMonoid r.2.1 * (conjugateRayMonoid r.1.1 * Ψ)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondTotalWeight (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (z : SecondRayIndex × Finset ι) : ℂ :=
  secondRayCoefficient z.1 *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ₁ z.1) (secondRayPlus Ψ₂ z.1)
      m r c d e k (-k) z.2

end

open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

namespace CubicJacobiGlobal
open ActualEisensteinCubic CompletedGauss CubicRamified

theorem symbol_ne_zero_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ≠ 0 := by
  classical
  have ha0 := primary_ne_zero a ha
  pm_5026 hI0 a ha0
  rw [symbol, idealSymbol, ite_eq_right hI0]
  apply Multiset.prod_ne_zero
  intro hzero
  obtain ⟨P,hP,hzero⟩ := Multiset.mem_map.mp hzero
  pm_3795
  pm_3796 s hrs
  rw [primeValue_eq P hg] at hzero
  exact cubicValue_ne_zero P hg x hxP hzero

theorem primary_mul (a b : O) (ha : lambda ^ 2 ∣ a-1) (hb : lambda ^ 2 ∣ b-1) :
    lambda ^ 2 ∣ a*b-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left ha b) hb
  convert h using 1 ; ring

theorem primary_add_multiple_three (a c t : O) (ha : lambda ^ 2 ∣ a-1) :
    lambda ^ 2 ∣ (a+3*t*c)-1 := by
  have h := dvd_add ha (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left lambda_sq_dvd_three t) c)
  convert h using 1 ; ring

theorem kubota_mul_of_isCoprime (a b c d e g : O)
    (hdet : a*d-b*c=1) (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hg : (3 : O) ∣ g) (hag : IsCoprime a g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  let productA := a*e+b*g
  let productC := c*e+d*g
  have hA : lambda ^ 2 ∣ productA-1 := by
    pm_6891 h
    pm_4976 h productA
  have hrelation : a*productC-c*productA=g := by
    dsimp [productA,productC]
    linear_combination g*hdet
  have hcop : IsCoprime a productA := by
    obtain ⟨r,s,hrs⟩ := hag
    refine ⟨r+s*productC,-s*c,?_⟩
    linear_combination hrs + s*hrelation
  have hnonzero := symbol_ne_zero_of_isCoprime a productA hA hcop
  have h1 : symbol a productA * symbol productC productA = symbol g productA := by
    rw [← symbol_mul_numerator _ _ productA hA]
    exact symbol_congr ⟨c, by linear_combination hrelation⟩
  have h2 : symbol a productA * symbol c a = symbol g a := by
    rw [symbol_reciprocity a productA (primary_ne_zero a ha) (primary_ne_zero productA hA) ha hA,
      ← symbol_mul_numerator _ _ a ha]
    calc
      symbol (productA*c) a = symbol (-g) a := by
        apply symbol_congr
        refine ⟨productC,?_⟩
        linear_combination -hrelation
      _ = symbol g a := symbol_neg_numerator g a ha
  have h3 : symbol g productA = symbol g a * symbol g e := by
    rw [← symbol_mul_denominator]
    apply symbol_denominator_congr g productA (a*e) hA (primary_mul a e ha he)
    · obtain ⟨b0,hb0⟩ := hb
      obtain ⟨g0,hg0⟩ := hg
      refine ⟨b0*g0,?_⟩
      dsimp [productA]
      rw [hb0,hg0]
      ring
    · exact ⟨b,by dsimp [productA];ring⟩
  change symbol productC productA = _
  apply mul_left_cancel₀ hnonzero
  rw [h1,h3,← h2]
  ring

lemma three_dvd_primary_sub_one (a : O) (ha : lambda ^ 2 ∣ a-1) : (3 : O) ∣ a-1 := by
  pm_5437
  rw [primaryCoord_eq]
  exact ⟨(A : O)+(B : O)*omega,by ring⟩

theorem exists_coprime_three_shift (a c g : O)
    (ha : lambda ^ 2 ∣ a-1) (hac : IsCoprime a c) (hg0 : g ≠ 0) :
    ∃ t : O, IsCoprime (a+3*t*c) g := by
  classical
  let : StrongNormalizationMonoid O := UniqueFactorizationMonoid.strongNormalizationMonoid
  pm_8491 UniqueFactorizationMonoid.normalizedFactors g
  refine ⟨s.prod, ?_⟩
  apply IsCoprime.symm
  pm_6149 hg0 hpg
  · have hp3 : ¬p ∣ (3 : O) := by
      intro h3
      have hsub : p ∣ a-1 := h3.trans (three_dvd_primary_sub_one a ha)
      pm_8647 p hpa hsub
      exact hp.not_dvd_one hone
    have hpc : ¬p ∣ c := by
      intro hpc
      exact hp.not_isUnit (hac.isUnit_of_dvd' hpa hpc)
    have hps : ¬p ∣ s.prod := by
      intro hdiv
      obtain ⟨q,hqs,hpq⟩ := hp.exists_mem_multiset_dvd hdiv
      have hqs' : q ∈ UniqueFactorizationMonoid.normalizedFactors g ∧ ¬q ∣ a :=
        Multiset.mem_filter.mp hqs
      have hqprime := UniqueFactorizationMonoid.prime_of_normalized_factor q hqs'.1
      have hqp : q ∣ p := (hp.associated_of_dvd hqprime hpq).dvd'
      exact hqs'.2 (hqp.trans hpa)
    have hpterm : p ∣ 3*s.prod*c := by
      convert dvd_sub hpnew hpa using 1 ; ring
    rcases hp.dvd_or_dvd hpterm with hleft | hright
    · rcases hp.dvd_or_dvd hleft with h3 | hs
      · exact hp3 h3
      · exact hps hs
    · exact hpc hright
  · obtain ⟨q,hq,hpq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
      hg0 hp.irreducible hpg
    have hqa : ¬q ∣ a := fun hqa => hpa (hpq.dvd.trans hqa)
    have hqs : q ∈ s := Multiset.mem_filter.mpr ⟨hq,hqa⟩
    have hps : p ∣ s.prod := hpq.dvd.trans (Multiset.dvd_prod hqs)
    have hpterm : p ∣ 3*s.prod*c :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hps 3) c
    have hpa' : p ∣ a := by
      convert dvd_sub hpnew hpterm using 1 ; ring
    exact hpa hpa'

lemma symbol_three_shift (c a t : O) (ha : lambda ^ 2 ∣ a-1) (hc : (3 : O) ∣ c) :
    symbol c (a+3*t*c) = symbol c a := by
  apply symbol_denominator_congr c (a+3*t*c) a (primary_add_multiple_three a c t ha) ha
  · obtain ⟨c0,hc0⟩ := hc
    refine ⟨t*c0,?_⟩
    rw [hc0]
    ring
  · exact ⟨3*t,by ring⟩

theorem kubota_mul (a b c d e f g h : O)
    (hdet : a*d-b*c=1) (hdet' : e*h-f*g=1)
    (ha : lambda ^ 2 ∣ a-1) (he : lambda ^ 2 ∣ e-1)
    (hb : (3 : O) ∣ b) (hc : (3 : O) ∣ c) (hg : (3 : O) ∣ g) :
    symbol (c*e+d*g) (a*e+b*g) = symbol c a * symbol g e := by
  by_cases hg0 : g = 0
  · have heh : e*h=1 := by simpa only [hg0,mul_zero,sub_zero] using hdet'
    have he1 : e=1 := A3_primary_unit_eq_one e (IsUnit.of_mul_eq_one h heh) he
    pm_382 hg0 he1 mul_one mul_zero add_zero symbol_one
  have hac : IsCoprime a c := by
    refine ⟨d,-b,?_⟩
    linear_combination hdet
  obtain ⟨t,ht⟩ := exists_coprime_three_shift a c g ha hac hg0
  have hdetShift : (a+3*t*c)*d-(b+3*t*d)*c=1 := by linear_combination hdet
  have hbShift : (3 : O) ∣ b+3*t*d :=
    dvd_add hb (dvd_mul_of_dvd_left (dvd_mul_right 3 t) d)
  have hcalc := kubota_mul_of_isCoprime (a+3*t*c) (b+3*t*d) c d e g
    hdetShift (primary_add_multiple_three a c t ha) he hbShift hg ht
  have hC : (3 : O) ∣ c*e+d*g :=
    dvd_add (dvd_mul_of_dvd_left hc e) (dvd_mul_of_dvd_right hg d)
  have hA : lambda ^ 2 ∣ (a*e+b*g)-1 := by
    pm_6891 hh
    convert hh using 1 ; ring
  calc
    symbol (c*e+d*g) (a*e+b*g) =
        symbol (c*e+d*g) ((a*e+b*g)+3*t*(c*e+d*g)) :=
      (symbol_three_shift _ _ _ hA hC).symm
    _ = symbol c (a+3*t*c) * symbol g e := by
      convert hcalc using 1 ; congr 1 ; ring
    _ = symbol c a * symbol g e := by rw [symbol_three_shift c a t ha hc]

end CubicJacobiGlobal

open scoped BigOperators Classical MatrixGroups

namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified

theorem symbol_cube_of_isCoprime (x a : O) (ha : lambda ^ 2 ∣ a-1)
    (hcop : IsCoprime x a) : symbol x a ^ 3 = 1 := by
  classical
  have hI0 : (Ideal.span {a} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primary_ne_zero a ha)
  rw [symbol, idealSymbol, ite_eq_right hI0, ← Multiset.prod_map_pow]
  apply Multiset.prod_eq_one
  pm_67 y hy P hP Multiset.mem_map.mp
  pm_3795
  pm_3796 t hrt
  rw [primeValue_eq P hg]
  exact cubicValue_cube P hg x hxP
end CubicJacobiGlobal

namespace CubicKubota
export OAI.EisensteinSchwartzPoisson (O)
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified

def levelThree : Subgroup (SL(2, O)) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)}))).ker

section
variable (M : levelThree)
include M
lemma levelThree_entry (i j : Fin 2) :
    (3 : O) ∣ (M : SL(2,O)) i j - (if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3 : O)})) (M : SL(2,O)) = 1 := M.property
  have h := congrArg (fun N : SL(2, O ⧸ (Ideal.span {(3 : O)})) => N i j) hm
  change (Ideal.Quotient.mk (Ideal.span {(3 : O)})) ((M : SL(2,O)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ (Ideal.span {(3 : O)}))) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  pm_99 Matrix.one_apply apply_ite map_one map_zero h

lemma levelThree_primary :
    lambda ^ 2 ∣ (M : SL(2,O)) 0 0 - 1 := by
  exact lambda_sq_dvd_three.trans (by simpa using levelThree_entry M 0 0)
lemma levelThree_upper : (3 : O) ∣ (M : SL(2,O)) 0 1 := by
  simpa using levelThree_entry M 0 1
lemma levelThree_lower : (3 : O) ∣ (M : SL(2,O)) 1 0 := by
  simpa using levelThree_entry M 1 0
end

def value (M : levelThree) : O :=
  symbol ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 0 0)

theorem value_mul (M N : levelThree) : value (M*N) = value M * value N := by
  have hM : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1 * (M : SL(2,O)) 1 0 = 1 := by
    pm_3797
  have hN : (N : SL(2,O)) 0 0 * (N : SL(2,O)) 1 1 -
      (N : SL(2,O)) 0 1 * (N : SL(2,O)) 1 0 = 1 := by
    pm_5396 N O
  have hh := kubota_mul ((M : SL(2,O)) 0 0) ((M : SL(2,O)) 0 1)
    ((M : SL(2,O)) 1 0) ((M : SL(2,O)) 1 1)
    ((N : SL(2,O)) 0 0) ((N : SL(2,O)) 0 1)
    ((N : SL(2,O)) 1 0) ((N : SL(2,O)) 1 1) hM hN
    (levelThree_primary M) (levelThree_primary N)
    (levelThree_upper M) (levelThree_lower M) (levelThree_lower N)
  change symbol (((M : SL(2,O)) * (N : SL(2,O))) 1 0)
    (((M : SL(2,O)) * (N : SL(2,O))) 0 0) = _
  pm_99 value Matrix.SpecialLinearGroup.coe_mul Matrix.mul_apply Fin.sum_univ_two hh

@[simp] theorem value_one : value 1 = 1 := by
  change symbol (0 : O) 1 = 1
  exact symbol_one 0

def character : levelThree →* O where
  toFun := value
  map_one' := value_one
  map_mul' := value_mul

theorem value_zero_lower_left (M : levelThree) (hc : (M : SL(2,O)) 1 0 = 0) :
    value M = 1 := by
  have hm : (M : SL(2,O)) 0 0 * (M : SL(2,O)) 1 1 = 1 := by
    have hd := (M : SL(2,O)).property
    pm_99 Matrix.det_fin_two hc mul_zero sub_zero hd
  have ha := A3_primary_unit_eq_one _ (IsUnit.of_mul_eq_one _ hm) (levelThree_primary M)
  simp only [value, hc, ha, symbol_one]

theorem value_cube (M : levelThree) : value M ^ 3 = 1 := by
  apply symbol_cube_of_isCoprime _ _ (levelThree_primary M)
  pm_3798
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 1 1, ?_⟩
  linear_combination hd

def complexCharacter : levelThree →* ℂ :=
  ConcreteTraceCRT.eisEmbedding.toMonoidHom.comp character

theorem complexCharacter_cube (M : levelThree) : complexCharacter M ^ 3 = 1 := by
  change ConcreteTraceCRT.eisEmbedding (value M) ^ 3 = 1
  rw [← map_pow, value_cube, map_one]

theorem norm_complexCharacter (M : levelThree) : ‖complexCharacter M‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  simpa only [norm_pow, norm_one] using congrArg norm (complexCharacter_cube M)

end CubicKubota

end

end OAI
