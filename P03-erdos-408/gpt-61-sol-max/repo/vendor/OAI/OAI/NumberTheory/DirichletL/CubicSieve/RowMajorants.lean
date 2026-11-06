module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.CubicSieve.IntegratedTransfer

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
 
 
 
 
 

 
namespace SecondPassArithmetic


section

 
 
 
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem exists_rowMajorant : ∃ W : 𝓢(ℝ, ℂ),
    (∀ s : ℝ, 0 ≤ (W s).re) ∧
    (∀ s : ℝ, |s| ≤ 1 → W s = 1) ∧
    (∀ s : ℝ, 2 < s → W s = 0) := by
  obtain ⟨U, hUc, hUs, hUone, hUts, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 1 (by norm_num)
  let f : ℝ → ℂ := fun s => U s * star (U s)
  have hfc : HasCompactSupport f := hUc.mul_right
  have hfs : ContDiff ℝ ∞ f := hUs.mul (Complex.conjCLE.contDiff.comp hUs)
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_⟩
  · intro s
    change 0 ≤ (U s * star (U s)).re
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (U s).re, sq_nonneg (U s).im]
  · aesop
  · intro s hs
    change U s * star (U s) = 0
    have hUz : U s = 0 := by
      by_contra hne
      have hu := hUts (subset_tsupport U (hne))
      norm_num at hu
      linarith [hu.2]
    simp [hUz]

def rowMajorant  := Classical.choose exists_rowMajorant

section
variable (s : ℝ)
include s

lemma rowMajorant_nonneg   : 0 ≤ (rowMajorant s).re :=
  (Classical.choose_spec exists_rowMajorant).1 s

lemma rowMajorant_one   (hs : |s| ≤ 1) : rowMajorant s = 1 :=
  (Classical.choose_spec exists_rowMajorant).2.1 s hs

lemma rowMajorant_zero   (hs : 2 < s) : rowMajorant s = 0 :=
  (Classical.choose_spec exists_rowMajorant).2.2 s hs

end

def rowMajorantBall (Y : ℝ)  := ShortDraftLatticeCount.rowNormBall (Nat.ceil (2 * Y))

lemma rowMajorant_zero_outside  Y  (hY : 0 < Y)  z 
    (hz : z ∉ rowMajorantBall Y) : rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) = 0 := by
  have hn : Nat.ceil (2 * Y) < Ideal.absNorm (Ideal.span {z}) := by
    apply Nat.lt_of_not_ge
    intro hn
    exact hz (ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le _ z hn)
  have hn' : (Nat.ceil (2 * Y) : ℝ) < (Ideal.absNorm (Ideal.span {z}) : ℝ) := by exact_mod_cast hn
  apply rowMajorant_zero
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  apply (lt_div_iff₀ hY).2
  linarith [Nat.le_ceil (2 * Y)]

section
variable (P : O → ℂ)
include P

section
variable (Y : ℝ) (hY : 0 < Y)
include Y hY

lemma rowMajorant_tsum_eq_sum       :
    (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) =
      ∑ z ∈ rowMajorantBall Y, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ) := by
  apply tsum_eq_sum
  simp_all [rowMajorant_zero_outside]

lemma rowMajorant_summable       :
    Summable (fun z : O => rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rowMajorantBall Y) ?_).summable
  simp_all [rowMajorant_zero_outside]

end

theorem finite_row_energy_le_rowMajorant    T 
     Y  (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖P z‖ ^ 2) ≤
      (∑' z : O, rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
  have hs := rowMajorant_summable P Y hY
  rw [Complex.re_tsum hs]
  calc
    _ = ∑ z ∈ T, (rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro z hz
      have hratio : |‖eisEmbedding z‖ ^ 2 / Y| ≤ 1 := by
        rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hY.le)]
        apply (div_le_one hY).2
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact hT z hz
      rw [rowMajorant_one _ hratio, one_mul, Complex.ofReal_re]
    _ ≤ _ := by
      apply (Complex.hasSum_re hs.hasSum).summable.sum_le_tsum
      intro z hz
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstCoreInputRow_finite_le_second_poisson
     hp 
     hinj 
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
     F D B   v   ε₁ ε₂ 
     negative   χ   Ψ   m 
     H   V   y   c d 
     r   t   T   Y  (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
        if Disjoint U V' then
          overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
            (m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂) (c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂) d
            (firstCoreTest H V y negative t D) G U V' *
            maskedSecondDual p hg hp hinj G U V' rowMajorant Y
        else 0).re := by
  have he := firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
    negative χ Ψ m H V y c d r t rowMajorant Y hY
  rw [← he]
  exact finite_row_energy_le_rowMajorant _ T Y hY hT

end

 
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ)  :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) S) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) T * K S T else 0

def secondChildKernelPair (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ)  :=
  ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₁) (fun _ => 1) N) *
    secondChildColumn p hp hcop hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₂) (fun _ => 1) M * K (V ∪ N) (V ∪ M)

section
variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreKernelPair_eq_children
     
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
     F   Ψ₁ Ψ₂   m r c d e k₁ k₂ 
     K  :
    secondPreKernelPair p hp hcop hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
      ∑ V ∈ F.powerset, secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  unfold secondPreKernelPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius, prime_product_moebius _ hprime hinj]
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hdN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hdM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondPreColumn_union p hp hcop hg hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hdN,
    secondPreColumn_union p hp hcop hg hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hdM, star_mul]
  ring

def secondKernelPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ)  :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T * K S T else 0

section
variable (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (K : Finset ι → Finset ι → ℂ)
include hc hpr F Ψ₁ Ψ₂ m r c d e k K

theorem secondKernelPair_eq_pre
     
     
     
         
      :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, secondRayCoefficient z *
        secondPreKernelPair p hp hcop hg F (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
          m r c d e k (-k) K := by
  have hterm (S T : Finset ι) :
      (if Disjoint S T then secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
        (fun _ => 1) (fun _ => 1) S T * K S T else 0) =
      ∑ z : SecondRayIndex, secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
    by_cases hd : Disjoint S T
    · simp only [ite_eq_left hd, secondGaussTerm]
      have h := congrArg (fun a : ℂ => a * K S T)
        (second_gauss_ray_expansion p hp hcop hg hinj hc hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k (fun _ => 1) (fun _ => 1) S T hd)
      simpa only [Fintype.sum_prod_type, secondRayCoefficient, secondRayMinus,
        secondRayPlus, Finset.sum_mul, mul_assoc] using h
    · simp [hd]
  unfold secondKernelPair
  simp_rw [hterm]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : SecondRayIndex, ∑ T ∈ F.powerset,
        secondRayCoefficient z * (if Disjoint S T then
        star (secondPreColumn p hp hcop hg (secondRayMinus Ψ₁ z) (m * (e * r)) c d e k (fun _ => 1) S) *
        secondPreColumn p hp hcop hg (secondRayPlus Ψ₂ z) (m * (e * r)) c d e (-k) (fun _ => 1) T * K S T else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondPreKernelPair, Finset.mul_sum]

theorem secondKernelPair_eq_children
     
     
     
         
      :
    secondKernelPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k K =
      ∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hp hcop hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
            m r c d e k (-k) K := by
  rw [secondKernelPair_eq_pre p hp hcop hg hinj hc hpr]
  simp only [secondPreKernelPair_eq_children p hp hcop hg hinj hpr,
    secondTotalWeight, Finset.mul_sum, mul_assoc]

end

end

end SecondPassArithmetic

namespace CubicEisenstein
open scoped     MatrixGroups Matrix

open   CubicKubota   CubicJacobiGlobal

def denominatorCondition (c d : O)  := IsCoprime c d ∧ (3 : O) ∣ d-1
abbrev AdmissibleDenominator (c ) := {d : O // denominatorCondition c d}
abbrev LevelLower := {c : O // (3 : O) ∣ c}

lemma denominatorCondition_shift  c d n  :
    denominatorCondition c (d+3*c*n) ↔ denominatorCondition c d := by
  constructor
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a+b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_sub hd h3 using 1 ; ring
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a-b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert dvd_add hd h3 using 1 ; ring

lemma row_symbol_shift  c d n  (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    symbol c (d+3*c*n)=symbol c d := by
  have hdn : (3 : O) ∣ d+3*c*n-1 := by
    convert dvd_add hd (show (3 : O) ∣ 3*c*n from ⟨c*n,by ring⟩) using 1 ; ring
  have h9 : (9 : O) ∣ d+3*c*n-d := by
    obtain ⟨c0,rfl⟩ := hc
    exact ⟨c0*n,by ring⟩
  exact symbol_denominator_congr c (d+3*c*n) d
    (lambda_sq_dvd_three.trans hdn) (lambda_sq_dvd_three.trans hd) h9
    ⟨3*n,by ring⟩

def primitiveSigmaEquiv : PrimitiveRow ≃ Σ c : LevelLower, AdmissibleDenominator c.1 where
  toFun r := ⟨⟨r.1 0,r.2.2.1⟩,⟨r.1 1,r.2.1,r.2.2.2⟩⟩
  invFun p := ⟨![p.1.1,p.2.1],p.2.2.1,p.1.2,p.2.2.2⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

abbrev DenominatorResidue (c : O) := O ⧸ Ideal.span {3*c}
def denominatorRep (c ) (r : DenominatorResidue c)  :=
  GaussianShiftedPartition.representative (3*c) r
section
variable (c : O)
include c

lemma denominatorRep_spec    r  :
    Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r :=
  GaussianShiftedPartition.representative_spec (3*c) r
abbrev AdmissibleResidue (c ) :=
  {r : DenominatorResidue c // denominatorCondition c (denominatorRep c r)}

section
variable (hc : c ≠ 0)
include hc

lemma finite_admissibleResidue     : Finite (AdmissibleResidue c) := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  infer_instance

def residueDenominatorMap (c ) (p : AdmissibleResidue c × O) : AdmissibleDenominator c :=
  ⟨denominatorRep c p.1.1+3*c*p.2,(denominatorCondition_shift c _ _).2 p.1.2⟩

lemma residueDenominatorMap_bijective     :
    Function.Bijective (residueDenominatorMap c) := by
  have h3c : 3*c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hq (r : DenominatorResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r+3*c*n)=r := by
    have hzero : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hzero, zero_mul, add_zero, denominatorRep_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ heq
    have h := congrArg Subtype.val heq
    change denominatorRep c r.1+3*c*n=denominatorRep c t.1+3*c*m at h
    have hrt : r=t := by
      apply Subtype.ext
      simpa only [hq] using congrArg (Ideal.Quotient.mk (Ideal.span {3*c})) h
    subst t
    have hnm : n=m := mul_left_cancel₀ h3c (add_left_cancel h)
    subst m
    rfl
  · intro d
    let r : DenominatorResidue c := Ideal.Quotient.mk (Ideal.span {3*c}) d.1
    have hr : Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r := denominatorRep_spec c r
    have hdiv : 3*c ∣ d.1-denominatorRep c r := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact hr.symm
    obtain ⟨n,hn⟩ := hdiv
    have hd : d.1=denominatorRep c r+3*c*n := by linear_combination hn
    have hrcond : denominatorCondition c (denominatorRep c r) := by
      apply (denominatorCondition_shift c _ n).1
      rw [← hd]
      exact d.2
    refine ⟨(⟨r,hrcond⟩,n), ?_⟩
    apply Subtype.ext
    exact hd.symm

def residueDenominatorEquiv (c ) (hc : c ≠ 0) :
    AdmissibleResidue c × O ≃ AdmissibleDenominator c :=
  Equiv.ofBijective (residueDenominatorMap c) (residueDenominatorMap_bijective c hc)

def primitiveTerm (z : ℂ) (v : ℝ) (s : ℂ) (c d : O)  :=
  eisEmbedding (symbol c d) *
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

theorem denominator_sum_residues     (f : O → ℂ)
    (hf : Summable (fun d : AdmissibleDenominator c => f d.1)) :
    (∑' d : AdmissibleDenominator c, f d.1)=
      ∑' r : AdmissibleResidue c, ∑' n : O, f (denominatorRep c r.1+3*c*n) := by
  have hsum := (residueDenominatorEquiv c hc).summable_iff.mpr hf
  exact ((residueDenominatorEquiv c hc).tsum_eq
    (fun d : AdmissibleDenominator c => f d.1)).symm.trans hsum.tsum_prod

end

end

lemma primitiveTerm_shift  z   v   s   c d n 
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    primitiveTerm z v s c (d+3*c*n)=
      primitiveTerm (z+3*eisEmbedding n) v s c d := by
  unfold primitiveTerm
  rw [row_symbol_shift c d n hc hd]
  have harg : eisEmbedding c*z+eisEmbedding (d+3*c*n)=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding d := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  rw [harg]

lemma denominator_zero_unique (d : AdmissibleDenominator 0) : d.1=1 := by
  apply A3_primary_unit_eq_one _ _ (lambda_sq_dvd_three.trans d.2.2)
  simpa only [isCoprime_zero_left] using d.2.1

end CubicEisenstein

open     Module
open scoped     ENNReal

namespace CubicEisenstein
open       EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def periodBasis  :=
  Complex.basisOneI.map (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]
lemma periodBasis_one : periodBasis 1=3*omega3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]

def periodLattice  := Submodule.span ℤ (Set.range periodBasis)
def periodDomain  := ZSpan.fundamentalDomain periodBasis

instance : Countable periodLattice := by unfold periodLattice; infer_instance
instance : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)

lemma periodDomain_fundamental : IsAddFundamentalDomain periodLattice periodDomain volume :=
  ZSpan.isAddFundamentalDomain periodBasis volume
lemma periodDomain_measurable : MeasurableSet periodDomain :=
  ZSpan.fundamentalDomain_measurableSet periodBasis

lemma three_embedding_mem  n  : 3*eisEmbedding n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).1 hzero)
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert h using 1
  conv_lhs => rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  simp only [zsmul_eq_mul,]
  ring

def periodPoint (n : O) : periodLattice := ⟨3*eisEmbedding n,three_embedding_mem n⟩
lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply eisEmbedding_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨ActualEisensteinCoordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*eisEmbedding (ActualEisensteinCoordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,eisEmbedding_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring

def periodEquiv  := Equiv.ofBijective _ periodPoint_bijective

theorem integral_eq_period_integrals (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z : ℂ, f z)=∑' n : O,∫ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.integral_eq_tsum'' f hf]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

theorem lintegral_eq_period_lintegrals (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : ℂ, f z)=∑' n : O,∫⁻ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.lintegral_eq_tsum'' f]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setLIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

lemma periodDomain_volume : volume periodDomain=ENNReal.ofReal (9*Real.sqrt 3/2) := by
  have hunit : volume (ZSpan.fundamentalDomain Complex.basisOneI)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  rw [periodDomain,ZSpan.measure_fundamentalDomain periodBasis volume Complex.basisOneI,hunit,mul_one]
  congr 1
  rw [Basis.det_apply,Matrix.det_fin_two]
  norm_num [Basis.toMatrix_apply,periodBasis_zero,periodBasis_one,
    Complex.coe_basisOneI_repr,EisensteinEmbedding.omega3_im]
  rw [abs_of_nonneg (by positivity)]
  ring

end CubicEisenstein

end

end OAI
