module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights

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
 
 
 
 
 

 
namespace CanonicalQuadraticSieve

section
open     ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex

def lowPrincipalIdeal (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ)  :=
  ∑' A : {A : Ideal O // Supported A},
    (idealZeroMask I (primaryGenerator A.val) * idealZeroMask J (primaryGenerator A.val)) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)

def lowPrincipalLattice (I J : Ideal O) (W : ℝ → ℂ) (X : ℝ)  :=
  ∑' z : O, rowCoprimeMask (fun P : gcdMaskPrimes (I * J) => P.val) Finset.univ z *
    W ((‖eisEmbedding z‖ ^ 2 / X) ^ 2)

section
variable (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J) (W : SchwartzMap ℝ ℂ)
include I J hI hJ W

section
variable (X : ℝ) (hX : 0 < X)
include X hX

theorem lowPrincipalLattice_eq_six_ideal      
          :
    lowPrincipalLattice I J W X = 6 * lowPrincipalIdeal I J W X := by
  let R := fun P : gcdMaskPrimes (I * J) => P.val
  let V := quadraticSquareProfile W
  let f : O → ℂ := fun z => rowCoprimeMask R Finset.univ z * V (‖eisEmbedding z‖ ^ 2 / X)
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖ ^ 2 / X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one R Finset.univ z)
  have h0 : f 0 = 0 := by
    dsimp only [f, R]
    rw [jointMask_zero, zero_mul]
  have hu (u : Oˣ) (z : O) : f (u.val * z) = f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul, norm_eisEmbedding_unit_mul]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hnorm (A : Ideal O) : ‖eisEmbedding (idealGenerator A)‖ ^ 2 = (Ideal.absNorm A : ℝ) := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span, span_idealGenerator]
  simp only [f, V, quadraticSquareProfile_apply, hnorm] at he
  have hid : (∑' A : NonzeroIdeal, rowCoprimeMask R Finset.univ (idealGenerator A.val) *
      W (((Ideal.absNorm A.val : ℝ) / X) ^ 2)) = lowPrincipalIdeal I J W X := by
    let F : Ideal O → ℂ := fun A => if Supported A then
      (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
        W (((Ideal.absNorm A : ℝ) / X) ^ 2) else 0
    calc
      _ = ∑' A : NonzeroIdeal, F A.val := by
        apply tsum_congr
        intro A
        rw [jointMask_generator I J hI hJ]
        by_cases hA : Supported A.val <;> simp [hA, F]
      _ = ∑' A : Ideal O, F A := by
        apply tsum_subtype_eq_of_support_subset
        intro A hA
          hz
        subst A
        exact hA (by simp [F, Supported])
      _ = _ := by
        calc
          _ = ∑' A : Ideal O, ({A : Ideal O | Supported A} : Set (Ideal O)).indicator
              (fun A => (idealZeroMask I (primaryGenerator A) * idealZeroMask J (primaryGenerator A)) *
                W (((Ideal.absNorm A : ℝ) / X) ^ 2)) A := by
            apply tsum_congr
            intro A
            rfl
          _ = _ := (_root_.tsum_subtype _ _).symm
  rw [hid] at he
  exact he

theorem lowPrincipalIdeal_eq_lattice      
          :
    lowPrincipalIdeal I J W X = (6 : ℂ)⁻¹ * lowPrincipalLattice I J W X := by
  grind [lowPrincipalLattice_eq_six_ideal, I]

end

theorem originalPairLow_principal_lattice
         
       M K  (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ))))
      else 0 := by
  rw [originalPairLow_squarefree_tsum I J hI hJ W M K hM]
  apply tsum_congr
  intro B
  by_cases hB : (Ideal.absNorm B.val : ℝ) ≤ K
  · rw [ite_eq_left hB, ite_eq_left hB]
    congr 1
    have hN : 0 < (Ideal.absNorm B.val : ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => B.property.1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm B.val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hN)
    rw [← lowPrincipalIdeal_eq_lattice I J hI hJ W _ hX]
    unfold lowPrincipalIdeal
    apply tsum_congr
    intro A
    congr 2
    grind
  · simp only [ite_eq_right hB]

end

end


open     CompletedGauss

theorem tsum_admissible_norm_cutoff (K : ℝ) (f : Ideal O → ℂ) :
    (∑' B : {B : Ideal O // Admissible B}, if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0) =
      ∑ B : idealRange K, f B.val := by
  let e : idealRange K → {B : Ideal O // Admissible B} :=
    fun B => ⟨B.val, (mem_idealRange.mp B.property).1⟩
  have he : Function.Injective e := by
    intro B C h
    aesop
  let F : {B : Ideal O // Admissible B} → ℂ := fun B =>
    if (Ideal.absNorm B.val : ℝ) ≤ K then f B.val else 0
  have hs : Function.support F ⊆ Set.range e := by
    intro B hB
    have hN : (Ideal.absNorm B.val : ℝ) ≤ K := by
      by_contra hn
      exact hB (ite_eq_right hn)
    exact ⟨⟨B.val, mem_idealRange.mpr ⟨B.property, hN⟩⟩, Subtype.ext rfl⟩
  have ht := he.tsum_eq hs
  change (∑' B, F B) = _
  rw [← ht, tsum_fintype]
  apply Finset.sum_congr rfl
  intro B _
  exact ite_eq_left (mem_idealRange.mp B.property).2

theorem originalPairLow_principal_finite
     I J  (hI : Admissible I) (hJ : Admissible J)
    (W : SchwartzMap ℝ ℂ)  M K  (hM : 0 < M) :
    (∑' lengthScale : Ideal O, originalPairLow I J W M K lengthScale) =
      ∑ B : idealRange K,
        (quadraticRow I (primaryGenerator B.val) * quadraticRow J (primaryGenerator B.val)) *
          ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B.val : ℝ)))) := by
  rw [originalPairLow_principal_lattice I J hI hJ W M K hM]
  exact tsum_admissible_norm_cutoff K (fun B : Ideal O =>
    (quadraticRow I (primaryGenerator B) * quadraticRow J (primaryGenerator B)) *
      ((6 : ℂ)⁻¹ * lowPrincipalLattice I J W (Real.sqrt (M / (Ideal.absNorm B : ℝ)))))

end CanonicalQuadraticSieve

 
namespace SecondPassArithmetic

section
 
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstCauchyArithmetic (activeGaussRowFactor)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

theorem activeGaussRowFactor_norm_le_one
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
     S T   e k  :
    ‖activeGaussRowFactor p hp hinj hg S T e k‖ ≤ 1 := by
  have hr (a : O) : ‖finiteSexticRow (activePrimes (fun i => Ideal.span {p i}) S T)
      (fun i => hg i.val) (activeExponent S T) a‖ ≤ 1 := by
    rw [finiteSexticRow_activeSupport, norm_mul, norm_star]
    exact (mul_le_mul (finiteSquarefreeRow_norm_le_one _ hg _ _)
      (finiteSquarefreeRow_norm_le_one _ hg _ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hGauss := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime (fun i => Ideal.span {p i}) hinj S T)
    (fun i => hg i.val) (fun i => hc i.val) (activeExponent S T)
    (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
  simp only [activeGaussRowFactor, norm_mul, norm_star, hGauss, one_mul]
  exact (mul_le_mul (hr e) (hr k) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end
section

 

def secondExpansionPool {ι } [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) : Finset (SecondExpansionData ι) :=
  F.powerset.biUnion (fun G => G.powerset.biUnion (fun E =>
    F.powerset.biUnion (fun V => (K G E).image (fun k => ⟨G,E,V,k⟩))))

section
variable {ι : Type*} [DecidableEq ι] (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
include ι F K

theorem mem_secondExpansionPool      
      (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  grind

theorem sum_secondExpansionPool      
      (H : SecondExpansionData ι → ℂ) :
    (∑ x ∈ secondExpansionPool F K, H x) =
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ V ∈ F.powerset, ∑ k ∈ K G E, H ⟨G,E,V,k⟩ := by
  unfold secondExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_biUnion]
      · simp_all
      · intro V hV V' hV' hne
        apply Finset.disjoint_left.mpr
        aesop
    · intro E hE E' hE' hne
      apply Finset.disjoint_left.mpr
      grind
  · intro G hG G' hG' hne
    apply Finset.disjoint_left.mpr
    grind

end

def secondExpansionSector {ι } [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι)  :=
  (secondExpansionPool F K).filter (fun x => x.sourceCommon \ x.divisor = R)

theorem sum_secondExpansionSector {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → ℂ) :
    (∑ R ∈ F.powerset, ∑ x ∈ secondExpansionSector F K R, H x) =
      ∑ x ∈ secondExpansionPool F K, H x := by
  simp only [secondExpansionSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hR : x.sourceCommon \ x.divisor ∈ F.powerset :=
    (by grind [mem_secondExpansionPool])
  simp_all

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

section
variable (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O)
include hc hpr F Ψ m c d H W Y K

theorem truncatedSecondSource_eq_expansionPool
     
     
           
          :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, secondExpansionSource p hp hcop hg F Ψ m c d z
        (secondExpansionPool F K) H H W Y := by
  rw [truncatedSecondSource_eq_child_sectors p hp hg hinj hcop hc hpr]
  simp only [secondExpansionSource, sum_secondExpansionPool]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G hG
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_coe_sort (s := G.powerset)]
  apply Finset.sum_congr rfl
  intro E hE
  apply Finset.sum_congr rfl
  intro V hV
  apply Finset.sum_congr rfl
  intro k hk
  have hs : (⟨G,E.val,V,k⟩ : SecondExpansionData ι).divisor ⊆
      (⟨G,E.val,V,k⟩ : SecondExpansionData ι).sourceCommon := Finset.mem_powerset.mp E.property
  simp only [secondExpansionQuotient_of_subset p _ hs]
  simp only [mul_assoc]

theorem truncatedSecondSource_eq_fixed_sectors
     
     
           
          :
    truncatedSecondSource p hp hg hinj F Ψ m c d H W Y K =
      ∑ z : SecondRayIndex, ∑ R ∈ F.powerset,
        secondExpansionSource p hp hcop hg F Ψ m c d z
          (secondExpansionSector F K R) H H W Y := by
  rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [secondExpansionSource, sum_secondExpansionSector]

end

end


 
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)

include hc

theorem secondPairRadialMode_summable_norm (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => ‖secondPairRadialMode p hp hg hinj S T e k W Y‖) := by
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hs : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hn))))
  have hmajor := (EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hs).mul_left
    ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hmajor
  intro k
  have ha : Y * ‖eisEmbedding k‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
      scale * ‖eisEmbedding k‖^2 := by dsimp [scale]; ring
  simp only [secondPairRadialMode, norm_mul]
  change ‖(Y : ℂ)/(‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
  rw [ha]
  exact mul_le_of_le_one_right (by positivity)
    (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k)

end SecondPassArithmetic

end

end OAI
