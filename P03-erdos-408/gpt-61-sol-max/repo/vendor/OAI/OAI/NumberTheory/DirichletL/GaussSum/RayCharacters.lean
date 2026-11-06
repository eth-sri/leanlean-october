module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.GaussSum.CompletedExpansion

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 

 

namespace RayFourExpansion
open     FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation

theorem prime_unit_mod_four  p  [(Ideal.span {p}).IsMaximal]
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) p) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have h2 : (2 : O) ∉ Ideal.span {p} := by
    intro hm
    have hz : (2 : O ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    apply hchar
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p}) 2).mp hz)
  let : (Ideal.span {(2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  have hcop : IsCoprime (Ideal.span {p}) (Ideal.span {(2 : O)}) := by
    apply Ideal.isCoprime_of_isMaximal
    aesop
  obtain ⟨a, b, hab⟩ := IdealGaussCRT.bezout_of_principal_coprime hcop
  have hcp : IsCoprime p (2 : O) := ⟨a, b, hab⟩
  have hcp4 : IsCoprime p (4 : O) := by
    simpa only [show (2 : O) ^ 2 = 4 by norm_num] using
      (hcp.pow_right : IsCoprime p ((2 : O) ^ 2))
  obtain ⟨a, b, hab⟩ := hcp4
  have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
  simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

section
variable {ι : Type*}
include ι

section
variable (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι)
include p hchar S

theorem prime_product_unit_mod_four    
     
        :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  rw [map_prod]
  simp_all [prime_unit_mod_four]

theorem rayMask_prime_product    
     
        :
    rayMask (∏ i ∈ S, p i) = 1 := by
  rw [rayMask, ite_eq_left (prime_product_unit_mod_four p hchar S)]

end

theorem canonicalProductG_character_expansion
      [Fintype ι] (p : ι → O)  hp 
    [∀ i, (Ideal.span {p i}).IsMaximal]
     hcop 
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) :
    canonicalProductG p hp hcop hgood =
      ∑ χ : RayCharacter, gCoeff χ * rayCharacter χ (∏ i, p i) := by
  rw [canonicalProductG_eq_fixed_quotient p hp hcop hgood hchar hprimary]
  have h := fixedG_character_expansion (∏ i, p i)
  rw [rayMask_prime_product p hchar Finset.univ, one_mul] at h
  exact h

theorem quadraticCrossPhase_character_expansion
      [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) := by
  rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]
  have h := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hchar A, rayMask_prime_product p hchar B, one_mul, one_mul] at h
  exact h

end

end RayFourExpansion

namespace MixedCrossSeparation
open     FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport

section
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (p : ι → O)
include ι κ p

theorem convertedColumnBlock_image
         
      (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
     A   inverse  :
    convertedColumnBlock (fun i => p (e i)) (fun i => hp (e i)) (fun i => hg (e i)) A inverse =
      convertedColumnBlock p hp hg (A.image e) inverse := by
  unfold convertedColumnBlock
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.image_erase he A i, Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

theorem quadraticCrossPhase_image
         
      [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : κ → ι) (he : Function.Injective e)
    (A B : Finset κ) :
    quadraticCrossPhase (fun i => p (e i)) (fun i => hg (e i)) A B =
      quadraticCrossPhase p hg (A.image e) (B.image e) := by
  unfold quadraticCrossPhase
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_image (fun a ha b hb hab => he hab)]
  rfl

end

section
variable {ι : Type*} [DecidableEq ι]
include ι

section
variable (S T : Finset ι)
include S T

private theorem negative_active_image       :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T)).image Subtype.val = S \ T := by
  ext i
  constructor
  · simp_all
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

private theorem positive_active_image       :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)).image Subtype.val = T \ S := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have hm := a.property
    rcases Finset.mem_union.mp hm with hleft | hright
    · exact ((Finset.mem_filter.mp ha).2 hleft).elim
    · exact hright
  · intro hi
    have hn : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩

end

theorem activeConvertedGauss_eq_columnBlocks
        (p : ι → O)  hp 
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)  S T  :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg (S \ T) true *
        convertedColumnBlock p hp hg (T \ S) false *
          quadraticCrossPhase p hg (S \ T) (T \ S) := by
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    quadraticCrossPhase_image p hg Subtype.val Subtype.val_injective,
    negative_active_image, positive_active_image]

end

end MixedCrossSeparation

namespace FirstCauchyArithmetic

section
abbrev O := ActualEisensteinCubic.O
open   CoprimeMobiusExtension

def supportMobius {ι } (P : ι → Ideal O) (S : Finset ι)  :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ)

def supportConjugateSum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ S ∈ B.powerset, supportMobius P S * C S * star (finiteSquarefreeRow P hg S h)

section
variable {ι : Type*}
include ι

theorem supportMobius_sq   [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P)  S  :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

theorem star_supportMobius   (P : ι → Ideal O) (S : Finset ι) :
    star (supportMobius P S) = supportMobius P S := by
  simp [supportMobius]

end

end
section

open     FiniteGaussPhase MixedCrossSeparation RayFourExpansion

def supportRay {ι } (p : ι → O) (χ : RayCharacter) (S : Finset ι)  :=
  rayCharacter χ (∏ i ∈ S, p i)

end

open   ConcretePrimeRowBridge

section
variable {ι : Type*}
include ι

section
variable (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
include P

private theorem family_prime        i  :
    Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance

private theorem family_prod_ne_zero  
         S  :
    (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (family_prime P i).ne_zero)

end

section
variable [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include P hinj

theorem family_prime_dvd_product_iff    
       
       S   i  :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact Finset.dvd_prod_of_mem P

theorem family_product_injective    
       
      : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  grind [family_prime_dvd_product_iff]

end

end

def supportIdealFamily {ι } [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι)  :=
  B.powerset.image (fun S => ∏ i ∈ S, P i)

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
include ι P

theorem supportIdealFamily_pos    
         B  :
    ∀ I ∈ supportIdealFamily P B, I ≠ ⊥ := by
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  exact family_prod_ne_zero P S

private theorem factor_family_product_iff    
         S   Q  :
    Q ∈ UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ S, P i) ↔
      ∃ i ∈ S, Q = P i := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff (family_prod_ne_zero P S)]
  constructor
  · rintro ⟨hQ, hd⟩
    obtain ⟨i, hi, hdiv⟩ := (hQ.dvd_finsetProd_iff P).mp hd
    exact ⟨i, hi, associated_iff_eq.mp (hQ.associated_of_dvd (family_prime P i) hdiv)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨family_prime P i, Finset.dvd_prod_of_mem P hi⟩

theorem supportIdealFamily_good    
       
    (hg : ∀ i, lambda ∉ P i)  B  :
    ∀ I ∈ supportIdealFamily P B,
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ Q := by
  intro I hI Q hQ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨i, hi, rfl⟩ := (factor_family_product_iff P S Q).mp hQ
  exact hg i

end

def recoveredSupport {ι } [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) (I : Ideal O)  :=
  B.filter (fun i => P i ∣ I)

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include ι P hinj

theorem recoveredSupport_product    
       
       B S  (hS : S ⊆ B) :
    recoveredSupport P B (∏ i ∈ S, P i) = S := by
  simp_all [recoveredSupport, family_prime_dvd_product_iff]

section
variable (hg : ∀ i, lambda ∉ P i)
include hg

theorem idealSexticRow_support_product    
       
       
     B S  (hS : S ⊆ B)  h  :
    idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
      (supportIdealFamily_good P hg B) (∏ i ∈ S, P i) h =
      finiteSquarefreeRow P hg S h := by
  let F := supportIdealFamily P B
  have hIF : (∏ i ∈ S, P i) ∈ F :=
    Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hS, rfl⟩
  let idx (i : ι) (hi : i ∈ S) : primePool F :=
    ⟨P i, mem_primePool_iff.mpr ⟨∏ j ∈ S, P j, hIF,
      (factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩⟩⟩
  symm
  unfold idealSexticRow finiteSquarefreeRow
  apply Finset.prod_bij idx
  · intro i hi
    exact (mem_idealSupport_iff F _ (idx i hi)).mpr
      ((factor_family_product_iff P S (P i)).mpr ⟨i, hi, rfl⟩)
  · aesop
  · intro Q hQ
    have hm := (mem_idealSupport_iff F _ Q).mp hQ
    obtain ⟨i, hi, he⟩ := (factor_family_product_iff P S Q.val).mp hm
    exact ⟨i, hi, Subtype.ext he.symm⟩
  · intro i hi
    rfl

theorem supportConjugateSum_eq_conjugateIdealRowSum
           
       
     B   C   h  :
    supportConjugateSum P hg B C h =
      conjugateIdealRowSum (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) (fun I => C (recoveredSupport P B I)) h := by
  let f : Ideal O → ℂ := fun I =>
    mobiusIdealColumn (fun I => C (recoveredSupport P B I)) I *
      star (idealSexticRow (supportIdealFamily P B) (supportIdealFamily_pos P B)
        (supportIdealFamily_good P hg B) I h)
  change supportConjugateSum P hg B C h =
    ∑ I ∈ B.powerset.image (fun S => ∏ i ∈ S, P i), f I
  rw [Finset.sum_image (fun S hS T hT h => family_product_injective P hinj h)]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  have hSB := Finset.mem_powerset.mp hS
  dsimp only [f]
  simp_all [idealSexticRow_support_product, mobiusIdealColumn, supportMobius, recoveredSupport_product]

end

end

end FirstCauchyArithmetic

end

end OAI
