module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Eisenstein.WhittakerContinuation

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

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
 
 
 
 
 
 
 
 

section
 
 
 

local notation "O" => ActualEisensteinCubic.O

def cubicBesselNormalizer (h : ActualEisensteinCubic.O)  :=
  (2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)

def cubicResidualFourierCoefficient (h : ActualEisensteinCubic.O)  :=
  cubicBesselNormalizer h*nonzeroScatteringResidue h

lemma sourceFourierKernel_cubic_height (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) :
    (v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  have hv0 : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [sourceFourierKernel_four_thirds _ (mul_ne_zero (cuspFrequency_ne_zero h hh) hv0)]
  have hnorm : ‖cuspFrequency h*(v:ℂ)‖=‖cuspFrequency h‖*v := by
    rw [norm_mul,Complex.norm_of_nonneg hv.le]
  rw [hnorm]
  simp only [Complex.ofReal_mul]
  have hbase : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)*(v:ℂ) := by ring
  have hpow : (2*Real.pi*(‖cuspFrequency h‖*v):ℂ)^(1/3:ℂ)=
      (2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)*(v:ℂ)^(1/3:ℂ) := by
    rw [hbase]
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using
      (Complex.mul_cpow_ofReal_nonneg (a := 2*Real.pi*‖cuspFrequency h‖) (b := v)
        (by positivity) hv.le (1/3:ℂ))
  have hvpow : (v:ℂ)^(-(4/3:ℂ)-1)*(v:ℂ)^(1/3:ℂ)=1/(v:ℂ)^2 := by
    rw [←Complex.cpow_add _ _ hv0,show -(4/3:ℂ)-1+1/3=-(2:ℂ) by ring,
      Complex.cpow_neg,Complex.cpow_ofNat]
    simp only [one_div]
  grind [Real.pi, cuspFrequency, cubicBesselNormalizer, schlafliBesselK]

end



section
 
 
 

local notation "O" => ActualEisensteinCubic.O

lemma upperVertical_tendsto_cubic_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I) 0 := by fun_prop
    simpa only [Complex.ofReal_zero,zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    aesop

end

section

 
open     CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

section
variable (c d e : Eis)

lemma denominatorRep_mk_congr   :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact denominatorRep_spec c _

lemma isCoprime_right_congr_of_dvd   (h : c ∣ d-e) :
    IsCoprime c d ↔ IsCoprime c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+c*n := by linear_combination hn
  rw [hd,IsCoprime.add_mul_left_right_iff]

end

abbrev CubicUnitResidue (b : Eis) :=
  {r : Eis ⧸ Ideal.span {b} // IsUnit r}

def denominatorCRTMap (a b ) (r : AdmissibleResidue (a*b)) :
    AdmissibleResidue a × CubicUnitResidue b :=
  let d:=denominatorRep (a*b) r.1
  (⟨Ideal.Quotient.mk (Ideal.span {3*a}) d,
      (denominatorCondition_congr a _ d (denominatorRep_mk_congr a d)).mpr
        ⟨r.2.1.of_mul_left_left,r.2.2⟩⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr r.2.1.of_mul_left_right⟩)

section
variable (a b : Eis) (hab : IsCoprime (3*a) b)

include hab in
lemma denominatorCRTMap_injective     :
    Function.Injective (denominatorCRTMap a b) := by
  intro r t he
  have h1:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.1.1) he
  have h2:=congrArg (fun z : AdmissibleResidue a × CubicUnitResidue b => z.2.1) he
  change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) t.1) at h1
  change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) r.1)=
    Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) t.1) at h2
  have hdiv : 3*(a*b) ∣ denominatorRep (a*b) r.1-denominatorRep (a*b) t.1 := by
    simpa only [mul_assoc] using hab.mul_dvd
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1))
      (Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h2))
  apply Subtype.ext
  rw [←denominatorRep_spec (a*b) r.1,←denominatorRep_spec (a*b) t.1]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hdiv)

include hab in
lemma denominatorCRTMap_surjective     :
    Function.Surjective (denominatorCRTMap a b) := by
  rintro ⟨r,t⟩
  obtain ⟨u,v,huv⟩ := hab
  let delta:=denominatorRep a r.1
  let xi:=GaussianShiftedPartition.representative b t.1
  let d:=v*b*delta+u*(3*a)*xi
  have hda : 3*a ∣ d-delta := by
    refine ⟨u*(xi-delta),?_⟩
    dsimp [d]
    linear_combination delta*huv
  have hdb : b ∣ d-xi := by
    refine ⟨v*(delta-xi),?_⟩
    dsimp [d]
    linear_combination xi*huv
  have hxi : IsCoprime b xi := by
    apply (isUnit_quotient_span_iff b xi).mp
    simpa only [xi,GaussianShiftedPartition.representative_spec] using t.2
  have had : denominatorCondition a d := (denominatorCondition_congr a d delta hda).mpr r.2
  have hbd : IsCoprime b d := (isCoprime_right_congr_of_dvd b d xi hdb).mpr hxi
  have hd : denominatorCondition (a*b) d := ⟨had.1.mul_left hbd,had.2⟩
  let q : AdmissibleResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {3*(a*b)}) d,
    (denominatorCondition_congr (a*b) _ d (denominatorRep_mk_congr (a*b) d)).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) q.1)=r.1
    rw [←denominatorRep_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : 3*a ∣ denominatorRep (a*b) q.1-d := (show 3*a ∣ 3*(a*b) from ⟨b,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : b ∣ denominatorRep (a*b) q.1-d := (show b ∣ 3*(a*b) from ⟨3*a,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa only [sub_add_sub_cancel] using dvd_add hh hdb

end

def denominatorCRTEquiv (a b ) (hab : IsCoprime (3*a) b) :
    AdmissibleResidue (a*b) ≃ AdmissibleResidue a × CubicUnitResidue b :=
  Equiv.ofBijective (denominatorCRTMap a b)
    ⟨denominatorCRTMap_injective a b hab,denominatorCRTMap_surjective a b hab⟩

def residueAdditive (h c d : Eis)  :=
  ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding d/eisEmbedding c)

lemma residueAdditive_congr  h c d e  (hc : c≠0) (hde : 3*c ∣ d-e) :
    residueAdditive h c d=residueAdditive h c e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+3*c*n:=by linear_combination hn
  have he:eisEmbedding c≠0:=eisEmbedding_ne_zero hc
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency h*eisEmbedding (e+3*c*n)/eisEmbedding c=
      cuspFrequency h*eisEmbedding e/eisEmbedding c+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def cubicUnitGaussSum (h b : Eis)  :=
  ∑' r : CubicUnitResidue b,
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1)

section
variable (h a b alpha beta d e : Eis) (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a) (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1)

include hb in
lemma residueAdditive_three_congr     (hde : b ∣ d-e) :
    residueAdditive (3*h) b d=residueAdditive (3*h) b e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+b*n:=by linear_combination hn
  have he:eisEmbedding b≠0:=eisEmbedding_ne_zero hb
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency (3*h)*eisEmbedding (e+b*n)/eisEmbedding b=
      cuspFrequency (3*h)*eisEmbedding e/eisEmbedding b+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [cuspFrequency,map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

include ha hb hbez in
lemma residueAdditive_crt      
      :
    residueAdditive h (a*b) d=
      residueAdditive (h*alpha) a d*residueAdditive (3*(h*beta)) b d := by
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  congr 1
  have hae:=eisEmbedding_ne_zero ha
  have hbe:=eisEmbedding_ne_zero hb
  have hbeq:=congrArg eisEmbedding hbez
  simp only [map_add,map_mul,map_one,map_ofNat] at hbeq
  simp only [cuspFrequency,map_mul,map_ofNat]
  grind

include ha hb halevel hbprimary hbez in
lemma arithmetic_crt_summand  
         
       
     r  :
    eisEmbedding (symbol (a*b) (denominatorRep (a*b) r.1))*
      residueAdditive h (a*b) (denominatorRep (a*b) r.1)=
    (eisEmbedding (symbol a (denominatorRep a (denominatorCRTMap a b r).1.1))*
      residueAdditive (h*alpha) a (denominatorRep a (denominatorCRTMap a b r).1.1))*
    (eisEmbedding (symbol (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1)) := by
  let d:=denominatorRep (a*b) r.1
  let delta:=denominatorRep a (denominatorCRTMap a b r).1.1
  let xi:=GaussianShiftedPartition.representative b (denominatorCRTMap a b r).2.1
  have hdprimary : lambda^2∣d-1:=lambda_sq_dvd_three.trans r.2.2
  have hdelta : 3*a∣delta-d:=denominatorRep_mk_congr a d
  have hxi : b∣xi-d:=by
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    exact GaussianShiftedPartition.representative_spec b _
  have hchar : symbol (a*b) d=symbol a delta*symbol xi b := by
    rw [symbol_mul_numerator a b d hdprimary,
      symbol_reciprocity b d hb (primary_ne_zero d hdprimary) hbprimary hdprimary,
      ←symbol_congr hxi]
    rw [←row_symbol_congr_modulus a delta d halevel r.2.2 hdelta]
  change eisEmbedding (symbol (a*b) d)*residueAdditive h (a*b) d=
    (eisEmbedding (symbol a delta)*residueAdditive (h*alpha) a delta)*
      (eisEmbedding (symbol xi b)*residueAdditive (3*(h*beta)) b xi)
  rw [hchar,map_mul,residueAdditive_crt h a b alpha beta d ha hb hbez,
    residueAdditive_congr (h*alpha) a delta d ha hdelta,
    residueAdditive_three_congr (h*beta) b xi d hb hxi]
  ring

include ha hb halevel hbprimary hbez in
theorem arithmeticResidueSum_crt  
         
        :
    arithmeticResidueSum h (a*b)=
      arithmeticResidueSum (h*alpha) a*cubicUnitGaussSum (h*beta) b := by
  have hab : IsCoprime (3*a) b:=⟨beta,alpha,by linear_combination hbez⟩
  let f : AdmissibleResidue a→ℂ:=fun r=>
    eisEmbedding (symbol a (denominatorRep a r.1))*residueAdditive (h*alpha) a (denominatorRep a r.1)
  let g : CubicUnitResidue b→ℂ:=fun r=>
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*(h*beta)) b (GaussianShiftedPartition.representative b r.1)
  have heq: arithmeticResidueSum h (a*b)=∑' r : AdmissibleResidue (a*b),
      f (denominatorCRTEquiv a b hab r).1*g (denominatorCRTEquiv a b hab r).2 := by
    unfold arithmeticResidueSum
    apply tsum_congr
    intro r
    exact arithmetic_crt_summand h a b alpha beta ha hb halevel hbprimary hbez r
  rw [heq,(denominatorCRTEquiv a b hab).tsum_eq (fun r=>f r.1*g r.2)]
  let : Finite (AdmissibleResidue a):=finite_admissibleResidue a ha
  let : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  let : Fintype (AdmissibleResidue a):=Fintype.ofFinite _
  let : Fintype (CubicUnitResidue b):=Fintype.ofFinite _
  change (∑' r : AdmissibleResidue a × CubicUnitResidue b,f r.1*g r.2)=
    (∑' r : AdmissibleResidue a,f r)*(∑' t : CubicUnitResidue b,g t)
  simp only [tsum_fintype,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

end

end

 
open     CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

section
variable (h k c t d : Eis) (hc : c≠0) (b : Eis)

lemma residueAdditive_mul   :
    residueAdditive h c (t*d)=residueAdditive (h*t) c d := by
  unfold residueAdditive cuspFrequency
  simp only [map_mul]
  congr 1
  ring

lemma residueAdditive_swap   :
    residueAdditive h c d=residueAdditive d c h := by
  unfold residueAdditive cuspFrequency
  congr 1
  ring

include hc in
lemma arithmeticResidueSum_frequency_congr    
    (hh : 3*c∣h-k) : arithmeticResidueSum h c=arithmeticResidueSum k c := by
  unfold arithmeticResidueSum
  apply tsum_congr
  intro r
  congr 1
  change residueAdditive h c (denominatorRep c r.1)=residueAdditive k c (denominatorRep c r.1)
  grind [residueAdditive_swap, residueAdditive_congr]

include hc in
theorem arithmeticResidueSum_frequency_twist    
    (hlevel : (3:Eis)∣c) (ht : denominatorCondition c t) :
    eisEmbedding (symbol c t)*arithmeticResidueSum (h*t) c=arithmeticResidueSum h c := by
  have heq:=(residueMultiplicationEquiv c hc t ht).tsum_eq
    (fun r : AdmissibleResidue c=>eisEmbedding (symbol c (denominatorRep c r.1))*
      residueAdditive h c (denominatorRep c r.1))
  calc
    _ = ∑' r : AdmissibleResidue c,eisEmbedding (symbol c t)*
      (eisEmbedding (symbol c (denominatorRep c r.1))*residueAdditive (h*t) c (denominatorRep c r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : AdmissibleResidue c,
      eisEmbedding (symbol c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplicationEquiv c hc t ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol c (denominatorRep c (residueMultiplication c t ht r).1))*
        residueAdditive h c (denominatorRep c (residueMultiplication c t ht r).1)
      rw [residueMultiplication_phase c hlevel t ht r,map_mul]
      dsimp only [residueMultiplication]
      rw [residueAdditive_congr h c _ (t*denominatorRep c r.1) hc
        (denominatorRep_product_congr c t r.1),residueAdditive_mul]
      ring
    _ = _ := heq

lemma cubicUnitGaussSum_frequency_congr   (hb : b≠0)
    (hh : b∣h-k) : cubicUnitGaussSum h b=cubicUnitGaussSum k b := by
  unfold cubicUnitGaussSum
  apply tsum_congr
  intro r
  congr 1
  have he (u : Eis) : residueAdditive (3*u) b (GaussianShiftedPartition.representative b r.1)=
      residueAdditive (3*GaussianShiftedPartition.representative b r.1) b u := by
    unfold residueAdditive cuspFrequency
    simp only [map_mul,map_ofNat]
    congr 1
    ring
  grind [residueAdditive_three_congr]

end

def cubicUnitResidueMul (b t ) (ht : IsCoprime b t) (r : CubicUnitResidue b) :
    CubicUnitResidue b :=
  ⟨Ideal.Quotient.mk (Ideal.span {b}) t*r.1,
    ((isUnit_quotient_span_iff b t).mpr ht).mul r.2⟩

lemma cubicUnitResidueMul_injective  b t   ht  :
    Function.Injective (cubicUnitResidueMul b t ht) := by
  intro r q heq
  apply Subtype.ext
  exact ((isUnit_quotient_span_iff b t).mpr ht).mul_left_cancel (congrArg Subtype.val heq)

def cubicUnitResidueMulEquiv (b t ) (hb : b≠0) (ht : IsCoprime b t) :
    CubicUnitResidue b ≃ CubicUnitResidue b := by
  letI : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  exact Equiv.ofBijective (cubicUnitResidueMul b t ht)
    ⟨cubicUnitResidueMul_injective b t ht,
      Finite.surjective_of_injective (cubicUnitResidueMul_injective b t ht)⟩

section
variable (h a b t : Eis) (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a) (hbprimary : lambda^2∣b-1) (ht : IsCoprime b t)

lemma cubicUnitResidueMul_rep_congr    
     r  :
    b∣GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1-
      t*GaussianShiftedPartition.representative b r.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec,map_mul,
    GaussianShiftedPartition.representative_spec]
  rfl

include hb hbprimary ht in
theorem cubicUnitGaussSum_frequency_twist    
        :
    eisEmbedding (symbol t b)*cubicUnitGaussSum (h*t) b=cubicUnitGaussSum h b := by
  have heq:=(cubicUnitResidueMulEquiv b t hb ht).tsum_eq
    (fun r : CubicUnitResidue b=>eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1))
  calc
    _ = ∑' r : CubicUnitResidue b,eisEmbedding (symbol t b)*
      (eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
        residueAdditive (3*(h*t)) b (GaussianShiftedPartition.representative b r.1)) := by
      rw [tsum_mul_left]
      rfl
    _ = ∑' r : CubicUnitResidue b,
      eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b
        (cubicUnitResidueMulEquiv b t hb ht r).1) := by
      apply tsum_congr
      intro r
      change _=eisEmbedding (symbol (GaussianShiftedPartition.representative b
        (cubicUnitResidueMul b t ht r).1) b)*
        residueAdditive (3*h) b (GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1)
      rw [symbol_congr (cubicUnitResidueMul_rep_congr b t ht r),
        symbol_mul_numerator t _ b hbprimary,map_mul]
      rw [residueAdditive_three_congr h b _ (t*GaussianShiftedPartition.representative b r.1)
        hb (cubicUnitResidueMul_rep_congr b t ht r),residueAdditive_mul]
      rw [show (3*h)*t=3*(h*t) by ring]
      ring
    _ = _ := heq

include ha hb halevel hbprimary in
theorem arithmeticResidueSum_coprime_product  
         
      (hab : IsCoprime (3*a) b) :
    arithmeticResidueSum h (a*b)=
      eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        arithmeticResidueSum h a*cubicUnitGaussSum h b := by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez' : alpha*b+beta*(3*a)=1:=by linear_combination hbez
  have hab' : IsCoprime (3*a) b:=⟨beta,alpha,hbez⟩
  have hb3 : (3:Eis)∣b-1:=three_dvd_lambda_sq.trans hbprimary
  have hbt : denominatorCondition a b:=⟨hab'.of_mul_left_right,hb3⟩
  have hA := arithmeticResidueSum_frequency_twist (h*alpha) a b ha halevel hbt
  have hAf : 3*a∣(h*alpha)*b-h:=⟨-h*beta,by linear_combination h*hbez'⟩
  rw [arithmeticResidueSum_frequency_congr _ h a ha hAf] at hA
  have hB := cubicUnitGaussSum_frequency_twist (h*beta) b (3*a) hb hbprimary hab'.symm
  have hBf : b∣(h*beta)*(3*a)-h:=⟨-h*alpha,by linear_combination h*hbez'⟩
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hBf] at hB
  rw [arithmeticResidueSum_crt h a b alpha beta ha hb halevel hbprimary hbez',←hA,←hB]
  ring

end

end CubicEisenstein

end

end OAI
