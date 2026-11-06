module
public import OAI.NumberTheory.DirichletL.Eisenstein.FredholmAlternative
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

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
open scoped Classical
open scoped Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped Classical SchwartzMap

namespace CanonicalUnitEuler
open ActualEisensteinCubic
open CanonicalRowCompletion
open ConcreteTraceCRT (eisEmbedding)
open UniqueFactorizationMonoid

lemma good_prime_norm_mod_six (P : Ideal ActualEisensteinCubic.O) [P.IsMaximal]
    (hg : lambda∉P) (hc : ringChar (ActualEisensteinCubic.O⧸P)≠2) : Ideal.absNorm P%6=1 := by
  let : Field (ActualEisensteinCubic.O⧸P):=Ideal.Quotient.field P
  let : Fintype (ActualEisensteinCubic.O⧸P):=Fintype.ofFinite _
  obtain ⟨χ,hχ⟩ : ∃χ : MulChar (ActualEisensteinCubic.O⧸P) ActualEisensteinCubic.O,orderOf χ=6 := ⟨_,sexticChar_order P hg hc⟩
  have hdiv:=χ.orderOf_dvd_card_sub_one
  rw [hχ] at hdiv
  have hcard : 1<Fintype.card (ActualEisensteinCubic.O⧸P):=Fintype.one_lt_card
  have hn : Ideal.absNorm P=Fintype.card (ActualEisensteinCubic.O⧸P) := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  rw [hn]
  omega

lemma unit_sixth_exponent_mul (u : ActualEisensteinCubic.Oˣ) (a b : ℕ) (ha : a%6=1) (hb : b%6=1) :
    u.val^((a*b-1)/6)=u.val^((a-1)/6)*u.val^((b-1)/6) := by
  pm_8662 ha' a
  pm_8662 hb' b
  have hab : a*b=6*(a/6+b/6+6*((a/6)*(b/6)))+1 := by
    grind
  have hab' : (a*b-1)/6=a/6+b/6+6*((a/6)*(b/6)):=by omega
  pm_8663 hda a
  pm_8663 hdb b
  rw [hab',hda,hdb,pow_add,pow_add,pow_mul,unit_pow_six,one_pow,mul_one]

private lemma multiset_unit_norm (u : ActualEisensteinCubic.Oˣ) (s : Multiset (Ideal ActualEisensteinCubic.O))
    (hs : ∀P∈s,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    (s.map (localRowValue u.val)).prod =
      eisEmbedding (u.val^(((s.map Ideal.absNorm).prod-1)/6)) ∧
      (s.map Ideal.absNorm).prod%6=1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons P s ih =>
    have hp:=hs P (Multiset.mem_cons_self _ _)
    let : P.IsMaximal:=hp.1
    have htail : ∀Q∈s,Q.IsMaximal ∧ lambda∉Q ∧ ringChar (ActualEisensteinCubic.O⧸Q)≠2:=
      fun Q hQ=>hs Q (Multiset.mem_cons_of_mem hQ)
    obtain ⟨hv,hn⟩:=ih htail
    have hP:=good_prime_norm_mod_six P hp.2.1 hp.2.2
    simp only [Multiset.map_cons,Multiset.prod_cons]
    refine ⟨?_,by rw [Nat.mul_mod,hP,hn]⟩
    rw [localRowValue_good _ P hp.2.1,actualSextic_unit_euler P hp.2.1 hp.2.2,hv]
    have hcard : Nat.card (ActualEisensteinCubic.O⧸P)=Ideal.absNorm P := by
      rw [Ideal.absNorm_apply,Submodule.cardQuot_apply]
    rw [hcard,unit_sixth_exponent_mul u _ _ hP hn,map_mul]

theorem idealRowHom_unit_norm (u : ActualEisensteinCubic.Oˣ) (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    idealRowHom u.val I=eisEmbedding (u.val^((Ideal.absNorm I-1)/6)) := by
  pm_3659
  have hh:=(multiset_unit_norm u (normalizedFactors I) hgood).1
  rw [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh
  change (if I=0 then 0 else _) = _
  rwa [ite_eq_right hI]

lemma ideal_norm_mod_six_of_good (I : Ideal ActualEisensteinCubic.O) (hI : I≠0)
    (hgood : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2) :
    Ideal.absNorm I%6=1 := by
  pm_3659
  have hh:=(multiset_unit_norm (1:ActualEisensteinCubic.Oˣ) (normalizedFactors I) hgood).2
  rwa [hn,Ideal.prod_normalizedFactors_eq_self hI] at hh

theorem idealRowHom_unit_eq_of_norm_mod_thirty_six (u : ActualEisensteinCubic.Oˣ) (I J : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0)
    (hgI : ∀P∈normalizedFactors I,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hgJ : ∀P∈normalizedFactors J,P.IsMaximal ∧ lambda∉P ∧ ringChar (ActualEisensteinCubic.O⧸P)≠2)
    (hmod : Ideal.absNorm I%36=Ideal.absNorm J%36) :
    idealRowHom u.val I=idealRowHom u.val J := by
  rw [idealRowHom_unit_norm u I hI hgI,idealRowHom_unit_norm u J hJ hgJ]
  have hmi:=ideal_norm_mod_six_of_good I hI hgI
  have hmj:=ideal_norm_mod_six_of_good J hJ hgJ
  have hm : (Ideal.absNorm I-1)/6 ≡ (Ideal.absNorm J-1)/6 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  exact congrArg eisEmbedding (pow_eq_pow_of_modEq hm (unit_pow_six u))

end CanonicalUnitEuler

namespace CompletedGauss
open ActualEisensteinCubic CompletedDyadic

end CompletedGauss

namespace CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)

end CanonicalRowCompletion

open Filter MeasureTheory
open scoped Classical Topology ContDiff MatrixGroups

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma rowCoordinates_zero : rowCoordinates (0 : Fin 2 → ActualEisensteinCubic.O)=0 := by
  apply norm_le_zero_iff.mp
  have h := coordinates_norm_bound (0 : Fin 2 → ActualEisensteinCubic.O)
  have he : (fun i : Fin 2 => eisEmbedding ((0 : Fin 2 → ActualEisensteinCubic.O) i))=0 := by
    funext i
    exact map_zero _
  rw [he,norm_zero,mul_zero] at h
  exact h

lemma rowCoordinates_norm_pos {u : Fin 2 → ActualEisensteinCubic.O} (hu : u≠0) :
    0<‖rowCoordinates u‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hu (rowCoordinates_injective (h.trans rowCoordinates_zero.symm))

lemma rowCoordinates_le_horizontal (u : Fin 2 → ActualEisensteinCubic.O) (z : ℂ) (hz : ‖z‖≤1) :
    ‖rowCoordinates u‖≤2*(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+
      ‖eisEmbedding (u 0)‖) := by
  apply (coordinates_norm_bound u).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith [norm_nonneg (eisEmbedding (u 0)*z+eisEmbedding (u 1))]
  · have h : ‖eisEmbedding (u 1)‖≤
        ‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖+‖eisEmbedding (u 0)*z‖ := by
      simpa only [add_sub_cancel_left] using
        norm_sub_le (eisEmbedding (u 0)*z+eisEmbedding (u 1)) (eisEmbedding (u 0)*z)
    rw [norm_mul] at h
    have hm := mul_le_mul_of_nonneg_left hz (norm_nonneg (eisEmbedding (u 0)))
    rw [mul_one] at hm
    exact h.trans (add_le_add_right hm _)

lemma height_times_coordinate_bound (A c v N : ℝ)
    (_hA : 0≤A) (hc : 1≤ c) (hv : 1/2≤v) (hN : N≤2*(A+c)) :
    N*v≤5*(A^2+c^2*v^2) := by
  have hv0 : 0≤v := by linarith
  have hcv : v≤ c*v := by nlinarith
  have hcv0 : 1/2≤ c*v := by linarith
  have hv2 : v^2≤(c*v)^2 := by nlinarith
  have hcross : 2*v*A≤A^2+c^2*v^2 := by nlinarith [sq_nonneg (A-v)]
  have hlin : 2*c*v≤4*(c*v)^2 := by nlinarith
  have hNv := mul_le_mul_of_nonneg_right hN hv0
  nlinarith [sq_nonneg A]

lemma rowHeight_times_coordinates (u : Fin 2 → ActualEisensteinCubic.O) (hu : u 0≠0)
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    (v/(‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
       ‖eisEmbedding (u 0)‖^2*v^2))*‖rowCoordinates u‖≤5 := by
  have hc : 1≤‖eisEmbedding (u 0)‖ := by
    have hh := one_le_normSq_embedding (u 0) hu
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (eisEmbedding (u 0))]
  have hden : 0<‖eisEmbedding (u 0)*z+eisEmbedding (u 1)‖^2+
      ‖eisEmbedding (u 0)‖^2*v^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  simpa only [mul_comm v] using
    height_times_coordinate_bound _ _ _ _ (norm_nonneg _) hc hv
      (rowCoordinates_le_horizontal u z hz)

lemma positive_rpow_of_product_bound (h N C σ : ℝ)
    (hh : 0≤h) (hN : 0<N) (hC : 0≤C) (hσ : 0≤σ) (hb : h*N≤C) :
    h^σ≤C^σ*N^(-σ) := by
  have hdiv : h≤C/N := (le_div_iff₀ hN).mpr hb
  have hr := Real.rpow_le_rpow hh hdiv hσ
  rw [Real.div_rpow hC hN.le,div_eq_mul_inv] at hr
  simpa only [Real.rpow_neg hN.le] using hr

def cuspRemainderProfile (a b : ℝ) (s : ℂ) (v : ℝ) : ℂ :=
  positiveHeightPower s v-cuspSeedProfile a b s v

section
variable (a b : ℝ) (s : ℂ) (v : ℝ)
include a b s v
lemma cuspRemainderProfile_norm_le (hv : 0<v) :
    ‖cuspRemainderProfile a b s v‖≤v^s.re := by
  pm_7422 hnon
  have hle : 1-cuspTransition a b v≤1 := by
    have := Real.smoothTransition.nonneg ((v-a)/(b-a))
    change 0≤ cuspTransition a b v at this
    linarith
  have he : cuspRemainderProfile a b s v=
      ((1-cuspTransition a b v:ℝ):ℂ)*positiveHeightPower s v := by
    pm_3543 cuspRemainderProfile cuspSeedProfile Complex.ofReal_sub Complex.ofReal_one
  rw [he,norm_mul,Complex.norm_of_nonneg hnon,positiveHeightPower_eq_cpow s v hv,
    Complex.norm_cpow_eq_rpow_re_of_pos hv]
  exact mul_le_of_le_one_left (Real.rpow_nonneg hv.le _) hle

lemma cuspRemainderProfile_zero
    (hab : a<b) (hv : 0<v) (hbv : b≤v) : cuspRemainderProfile a b s v=0 := by
  rw [cuspRemainderProfile,cuspSeedProfile_incoming a b s v hab hbv hv,
    positiveHeightPower_eq_cpow s v hv,sub_self]

lemma cuspRemainderProfile_norm_le_bound
    (hab : a<b) (hb : 0≤b) (hv : 0<v) (hs : 0≤ s.re) :
    ‖cuspRemainderProfile a b s v‖≤b^s.re := by
  by_cases h : b≤v
  · rw [cuspRemainderProfile_zero a b s v hab hv h,norm_zero]
    exact Real.rpow_nonneg hb _
  · exact (cuspRemainderProfile_norm_le a b s v hv).trans
      (Real.rpow_le_rpow hv.le (le_of_not_ge h) hs)
end

end

open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

section
variable {u : Fin 2 → ActualEisensteinCubic.O}
include u
lemma integral_row_embedding_ne_zero (hu : u≠0) :
    (eisEmbedding ∘ u)≠0 := by
  intro h
  apply hu
  funext i
  apply eisEmbedding_injective
  simpa only [Function.comp_apply,Pi.zero_apply,map_zero] using congrFun h i

lemma coprime_row_ne_zero (h : IsCoprime (u 0) (u 1)) : u≠0 := by
  intro hz
  have hh : (0 : ActualEisensteinCubic.O)=1 := by
    pm_89 hz Pi.zero_apply isCoprime_zero_left isUnit_zero_iff h
  exact zero_ne_one hh
end

theorem cuspRemainderProfile_row_bound (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (u : Fin 2 → ActualEisensteinCubic.O) (hcop : IsCoprime (u 0) (u 1))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) :
    ‖cuspRemainderProfile a b s (transformedHeight z v (eisEmbedding ∘ u))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates u‖^(-s.re) := by
  have hu := coprime_row_ne_zero hcop
  have hN := rowCoordinates_norm_pos hu
  have hv0 : 0<v := by linarith
  have hh : 0<transformedHeight z v (eisEmbedding ∘ u) :=
    div_pos hv0 (heightDenominator_pos z v hv0 _ (integral_row_embedding_ne_zero hu))
  have hC : 0≤ max 5 (2*b) := (by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)
  by_cases hc : u 0=0
  · have hunit : IsUnit (u 1) := by simpa only [hc,isCoprime_zero_left] using hcop
    obtain ⟨d,hd⟩ := hunit
    have hdnorm : ‖eisEmbedding (u 1)‖=1 := by
      rw [←hd]
      exact GaussGeneratorTransport.norm_eisEmbedding_unit d
    have hn : ‖rowCoordinates u‖≤2 := by
      apply (coordinates_norm_bound u).trans
      have hm : ‖fun i => eisEmbedding (u i)‖≤1 := by
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro i
        fin_cases i
        · change ‖eisEmbedding (u 0)‖≤1
          simp only [hc,map_zero,norm_zero,zero_le_one]
        · exact hdnorm.le
      nlinarith
    apply (cuspRemainderProfile_norm_le_bound a b s _ hab hb hh hs).trans
    exact positive_rpow_of_product_bound b _ _ _ hb hN hC hs
      (by nlinarith [mul_le_mul_of_nonneg_left hn hb,le_max_right (5 : ℝ) (2*b)])
  · apply (cuspRemainderProfile_norm_le a b s _ hh).trans
    apply positive_rpow_of_product_bound _ _ _ _ hh.le hN hC hs
    exact (rowHeight_times_coordinates u hc z hz v hv).trans (le_max_left _ _)

def translatedCuspRow (M : SL(2,ActualEisensteinCubic.O)) (r : CuspCosets) : Fin 2 → ActualEisensteinCubic.O :=
  Matrix.vecMul (cosetRow r) (M : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)

section
variable (M : SL(2,ActualEisensteinCubic.O))
include M
lemma translatedCuspRow_injective : Function.Injective (translatedCuspRow M) := by
  intro r t h
  apply cosetRow_injective
  have hh := congrArg (fun u : Fin 2 → ActualEisensteinCubic.O => Matrix.vecMul u
    ((M⁻¹ : SL(2,ActualEisensteinCubic.O)) : Matrix (Fin 2) (Fin 2) ActualEisensteinCubic.O)) h
  simpa only [translatedCuspRow,Matrix.vecMul_vecMul,←Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel,Matrix.SpecialLinearGroup.coe_one,Matrix.vecMul_one] using hh

lemma integral_bottom_coprime : IsCoprime (M 1 0) (M 1 1) := by
  pm_3250 hd M M.property
  refine ⟨-M 0 1,M 0 0,?_⟩
  linear_combination hd

lemma translatedCuspRow_coprime (r : CuspCosets) :
    IsCoprime (translatedCuspRow M r 0) (translatedCuspRow M r 1) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change IsCoprime (translatedCuspRow M (cosetOf N) 0) (translatedCuspRow M (cosetOf N) 1)
    simpa only [translatedCuspRow,cosetRow_cosetOf,row,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mul_apply,Matrix.vecMul,dotProduct] using integral_bottom_coprime ((N : SL(2,ActualEisensteinCubic.O))*M)

lemma cosetHeight_integral_chart (r : CuspCosets)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    cosetHeight r (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M r) := by
  induction r using Quotient.inductionOn with
  | _ N =>
    change cosetHeight (cosetOf N) (integralComplexMatrix M • upperPoint z v hv)=
      transformedHeight z v (eisEmbedding ∘ translatedCuspRow M (cosetOf N))
    rw [cosetHeight_cosetOf,←integralComplexMatrix_levelThree,
      ←mul_smul,←map_mul,hyperbolicHeight_action_upperPoint]
    simp only [integralComplexMatrix_apply,transformedHeight,heightDenominator,
      Function.comp_apply,translatedCuspRow,cosetRow_cosetOf,row,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Matrix.vecMul,dotProduct]
end

lemma translated_remainder_majorant (a b : ℝ) (s : ℂ)
    (hab : a<b) (hb : 0≤b) (hs : 0≤ s.re)
    (M : SL(2,ActualEisensteinCubic.O)) (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v)
    (hv0 : 0<v) (r : CuspCosets) :
    ‖(cosetCharacter r)⁻¹*cuspRemainderProfile a b s
      (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))‖≤
      (max 5 (2*b))^s.re*‖rowCoordinates (translatedCuspRow M r)‖^(-s.re) := by
  pm_502 norm_mul norm_inv norm_cosetCharacter inv_one one_mul cosetHeight_integral_chart
  exact cuspRemainderProfile_row_bound a b s hab hb hs _
    (translatedCuspRow_coprime M r) z hz v hv

end CubicEisenstein


namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

section
variable (a b : ℝ) (ha : 1≤a) (hab : a<b) (s : ℂ)
include a b ha hab s
lemma cuspCutoffTerm_eq_seedProfile (r : CuspCosets) (w : HyperbolicSpace) :
    cuspCutoffTerm 1 (cuspSeedProfile a b s) r w=
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
  unfold cuspCutoffTerm
  split_ifs with h
  · rfl
  · rw [cuspSeedProfile_zero a b s _ hab ((le_of_not_gt h).trans ha),mul_zero]

lemma cusp_seed_profile_summable (w : HyperbolicSpace) :
    Summable (fun r : CuspCosets => (cosetCharacter r)⁻¹*
      cuspSeedProfile a b s (cosetHeight r w)) :=
  (cuspCutoffTerm_summable 1 le_rfl _ w).congr
    (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)

theorem eisenstein_sub_seed_eq_series (hs : 2< s.re) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w-smoothCuspSeed a b s w=
      ∑'r : CuspCosets,(cosetCharacter r)⁻¹*
        cuspRemainderProfile a b s (cosetHeight r w) := by
  have hE := (height_series_summable_norm s hs w).of_norm
  have hS := cusp_seed_profile_summable a b ha hab s w
  have heq : smoothCuspSeed a b s w=∑'r : CuspCosets,
      (cosetCharacter r)⁻¹*cuspSeedProfile a b s (cosetHeight r w) := by
    unfold smoothCuspSeed cuspCutoffCorrection
    exact tsum_congr (fun r => cuspCutoffTerm_eq_seedProfile a b ha hab s r w)
  rw [hyperbolicEisenstein_eq_height_series,heq,←hE.tsum_sub hS]
  apply tsum_congr
  intro r
  rw [cuspRemainderProfile,positiveHeightPower_eq_cpow s _ (cosetHeight_pos r w)]
  ring
end

def eisensteinRemainderBound (b : ℝ) (s : ℂ) : ℝ :=
  (max 5 (2*b))^s.re * ∑'n : (Fin 2×Fin 2)→ℤ,‖n‖^(-s.re)

lemma eisensteinRemainderBound_nonneg (b : ℝ) (s : ℂ) :
    0≤eisensteinRemainderBound b s :=
  mul_nonneg (Real.rpow_nonneg ((by norm_num : (0:ℝ)≤5).trans (le_max_left _ _)) _)
    (tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _))

theorem eisenstein_sub_seed_chart_bound (a b : ℝ) (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4< s.re) (M : SL(2,ActualEisensteinCubic.O))
    (z : ℂ) (hz : ‖z‖≤1) (v : ℝ) (hv : 1/2≤v) (hv0 : 0<v) :
    ‖hyperbolicEisenstein s (integralComplexMatrix M • upperPoint z v hv0)-
      smoothCuspSeed a b s (integralComplexMatrix M • upperPoint z v hv0)‖≤
      eisensteinRemainderBound b s := by
  pm_3660
  let R : CuspCosets→ℂ := fun r => (cosetCharacter r)⁻¹*cuspRemainderProfile a b s
    (cosetHeight r (integralComplexMatrix M • upperPoint z v hv0))
  pm_1293
  have hb : ∀r,‖R r‖≤G (f r) :=
    translated_remainder_majorant a b s hab (by linarith) (by linarith) M z hz v hv hv0
  have hr : Summable (fun r => ‖R r‖) :=
    (hg.comp_injective hi).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  rw [eisenstein_sub_seed_eq_series a b ha hab s (by linarith)]
  change ‖∑'r,R r‖≤eisensteinRemainderBound b s
  apply (norm_tsum_le_tsum_norm hr).trans
  have hsum : (∑'r,‖R r‖)≤∑'n,G n :=
    Summable.tsum_le_tsum_of_inj f hi (fun _ _ => by dsimp [G]; positivity) hb hr hg
  simpa only [G,tsum_mul_left,eisensteinRemainderBound] using hsum

section
variable (a b : ℝ)
include a b
theorem eisenstein_sub_seed_bounded (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4< s.re) (w : HyperbolicSpace) :
    ‖hyperbolicEisenstein s w-smoothCuspSeed a b s w‖≤eisensteinRemainderBound b s := by pm_3661 eisenstein_sub_seed_chart_bound

lemma cuspRemainderProfile_measurable (s : ℂ) :
    Measurable (cuspRemainderProfile a b s) := by
  unfold cuspRemainderProfile cuspSeedProfile positiveHeightPower logRatioPower cuspTransition
  fun_prop

lemma eisenstein_sub_seed_measurable (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 2< s.re) :
    Measurable (fun w => hyperbolicEisenstein s w-smoothCuspSeed a b s w) := by
  simp_rw [eisenstein_sub_seed_eq_series a b ha hab s hs]
  apply Measurable.tsum
  intro r
  exact measurable_const.mul ((cuspRemainderProfile_measurable a b s).comp
    (cosetHeight_continuous r).measurable)

theorem kernel_eisenstein_sub_seed_memLp (ha : 1≤a) (hab : a<b)
    (s : ℂ) (hs : 4< s.re) :
    MemLp (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) 2 (integralQuotientVolume globalKubotaKernel) := by
  have hmeas : Measurable (fun q => kernelQuotientEisenstein s (by linarith) q-
      kernelQuotientSeed a b s q) :=
    measurable_from_quotient.mpr (eisenstein_sub_seed_measurable a b ha hab s (by linarith))
  apply MemLp.of_bound hmeas.aestronglyMeasurable (eisensteinRemainderBound b s)
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact eisenstein_sub_seed_bounded a b ha hab s hs w
end

end CubicEisenstein

end

end OAI
