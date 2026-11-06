module

public import OAI.NumberTheory.DirichletL.Eisenstein.WhittakerContinuation

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ShortDraftLatticeCount
open Filter
open scoped Topology
open ConcreteTraceCRT
open Filter Asymptotics
open Filter
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
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Set
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical

section
open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

def cubicBesselNormalizer (h : ActualEisensteinCubic.O) : ℂ :=
  (2*Real.pi:ℂ)/Complex.Gamma (4/3)*(2*Real.pi*‖cuspFrequency h‖:ℂ)^(1/3:ℂ)

def cubicResidualFourierCoefficient (h : ActualEisensteinCubic.O) : ℂ :=
  cubicBesselNormalizer h*nonzeroScatteringResidue h

lemma sourceFourierKernel_cubic_height (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) :
    (v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v)=
      cubicBesselNormalizer h*
        (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)/(v:ℂ)^2) := by
  have hv0 := Complex.ofReal_ne_zero.mpr hv.ne'
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
  have harg : 4*Real.pi*(‖cuspFrequency h‖*v)=4*Real.pi*‖cuspFrequency h‖*v := by ring
  rw [hpow,harg]
  unfold cubicBesselNormalizer
  grind

end

section
open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

end

section
open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

lemma upperVertical_tendsto_cubic_punctured :
    Tendsto (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I)
      (𝓝[>] (0:ℝ)) (𝓝[≠] (4/3:ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℝ => (4/3:ℂ)+(t:ℂ)*Complex.I) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    change (4/3:ℂ)+(t:ℂ)*Complex.I≠(4/3:ℂ)
    intro he
    simp_all

end

section

open scoped Classical
open CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma denominatorRep_mk_congr (c d : Eis) :
    3*c ∣ denominatorRep c (Ideal.Quotient.mk (Ideal.span {3*c}) d)-d := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  exact denominatorRep_spec c _

lemma isCoprime_right_congr_of_dvd (c d e : Eis) (h : c ∣ d-e) :
    IsCoprime c d ↔ IsCoprime c e := by
  obtain ⟨n,hn⟩ := h
  have hd : d=e+c*n := by linear_combination hn
  simp_all

abbrev CubicUnitResidue (b : Eis) :=
  {r : Eis ⧸ Ideal.span {b} // IsUnit r}

def denominatorCRTMap (a b : Eis) (r : AdmissibleResidue (a*b)) :
    AdmissibleResidue a × CubicUnitResidue b :=
  let d:=denominatorRep (a*b) r.1
  (⟨Ideal.Quotient.mk (Ideal.span {3*a}) d,
      (denominatorCondition_congr a _ d (denominatorRep_mk_congr a d)).mpr
        ⟨r.2.1.of_mul_left_left,r.2.2⟩⟩,
   ⟨Ideal.Quotient.mk (Ideal.span {b}) d,
      (isUnit_quotient_span_iff b d).mpr r.2.1.of_mul_left_right⟩)

lemma denominatorCRTMap_injective (a b : Eis) (hab : IsCoprime (3*a) b) :
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

lemma denominatorCRTMap_surjective (a b : Eis) (hab : IsCoprime (3*a) b) :
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
  have had := (denominatorCondition_congr a d delta hda).mpr r.2
  have hbd := (isCoprime_right_congr_of_dvd b d xi hdb).mpr hxi
  have hd : denominatorCondition (a*b) d := ⟨had.1.mul_left hbd,had.2⟩
  let q : AdmissibleResidue (a*b):=⟨Ideal.Quotient.mk (Ideal.span {3*(a*b)}) d,
    (denominatorCondition_congr (a*b) _ d (denominatorRep_mk_congr (a*b) d)).mpr hd⟩
  refine ⟨q,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change Ideal.Quotient.mk (Ideal.span {3*a}) (denominatorRep (a*b) q.1)=r.1
    rw [←denominatorRep_spec a r.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : 3*a ∣ denominatorRep (a*b) q.1-d :=
      (show 3*a ∣ 3*(a*b) from ⟨b,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa using dvd_add hh hda
  · change Ideal.Quotient.mk (Ideal.span {b}) (denominatorRep (a*b) q.1)=t.1
    rw [←GaussianShiftedPartition.representative_spec b t.1]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton.mpr
    have hh : b ∣ denominatorRep (a*b) q.1-d :=
      (show b ∣ 3*(a*b) from ⟨3*a,by ring⟩).trans (denominatorRep_mk_congr (a*b) d)
    simpa using dvd_add hh hdb

def denominatorCRTEquiv (a b : Eis) (hab : IsCoprime (3*a) b) :
    AdmissibleResidue (a*b) ≃ AdmissibleResidue a × CubicUnitResidue b :=
  Equiv.ofBijective (denominatorCRTMap a b)
    ⟨denominatorCRTMap_injective a b hab,denominatorCRTMap_surjective a b hab⟩

def residueAdditive (h c d : Eis) : ℂ :=
  ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding d/eisEmbedding c)

lemma residueAdditive_congr (h c d e : Eis) (hc : c≠0) (hde : 3*c ∣ d-e) :
    residueAdditive h c d=residueAdditive h c e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+3*c*n:=by linear_combination hn
  have he:=eisEmbedding_ne_zero hc
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency h*eisEmbedding (e+3*c*n)/eisEmbedding c=
      cuspFrequency h*eisEmbedding e/eisEmbedding c+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

def cubicUnitGaussSum (h b : Eis) : ℂ :=
  ∑' r : CubicUnitResidue b,
    eisEmbedding (symbol (GaussianShiftedPartition.representative b r.1) b)*
      residueAdditive (3*h) b (GaussianShiftedPartition.representative b r.1)

lemma residueAdditive_three_congr (h b d e : Eis) (hb : b≠0) (hde : b ∣ d-e) :
    residueAdditive (3*h) b d=residueAdditive (3*h) b e := by
  obtain ⟨n,hn⟩:=hde
  have hd:d=e+b*n:=by linear_combination hn
  have he:=eisEmbedding_ne_zero hb
  unfold residueAdditive
  rw [hd]
  have hh : cuspFrequency (3*h)*eisEmbedding (e+b*n)/eisEmbedding b=
      cuspFrequency (3*h)*eisEmbedding e/eisEmbedding b+cuspFrequency h*(3*eisEmbedding n) := by
    simp only [cuspFrequency,map_add,map_mul,map_ofNat]
    field_simp
  rw [hh,AddChar.map_add_eq_mul,cuspFrequency_period,mul_one]

lemma residueAdditive_crt (h a b alpha beta d : Eis) (ha : a≠0) (hb : b≠0)
    (hbez : alpha*b+beta*(3*a)=1) :
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

lemma arithmetic_crt_summand (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1)
    (r : AdmissibleResidue (a*b)) :
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

theorem arithmeticResidueSum_crt (h a b alpha beta : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hbez : alpha*b+beta*(3*a)=1) :
    arithmeticResidueSum h (a*b)=
      arithmeticResidueSum (h*alpha) a*cubicUnitGaussSum (h*beta) b := by
  have hab : IsCoprime (3*a) b:=⟨beta,alpha,by grind⟩
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

open scoped Classical
open CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

lemma residueAdditive_mul (h c t d : Eis) :
    residueAdditive h c (t*d)=residueAdditive (h*t) c d := by
  unfold residueAdditive cuspFrequency
  grind

lemma residueAdditive_swap (h c d : Eis) :
    residueAdditive h c d=residueAdditive d c h := by
  unfold residueAdditive cuspFrequency
  ring

lemma arithmeticResidueSum_frequency_congr (h k c : Eis) (hc : c≠0)
    (hh : 3*c∣h-k) : arithmeticResidueSum h c=arithmeticResidueSum k c := by
  unfold arithmeticResidueSum
  apply tsum_congr
  intro r
  congr 1
  change residueAdditive h c (denominatorRep c r.1)=residueAdditive k c (denominatorRep c r.1)
  rw [residueAdditive_swap h,residueAdditive_swap k]
  exact residueAdditive_congr _ c h k hc hh

theorem arithmeticResidueSum_frequency_twist (h c t : Eis) (hc : c≠0)
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

lemma cubicUnitGaussSum_frequency_congr (h k b : Eis) (hb : b≠0)
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
  rw [he h,he k]
  exact residueAdditive_three_congr _ b h k hb hh

def cubicUnitResidueMul (b t : Eis) (ht : IsCoprime b t) (r : CubicUnitResidue b) :
    CubicUnitResidue b :=
  ⟨Ideal.Quotient.mk (Ideal.span {b}) t*r.1,
    ((isUnit_quotient_span_iff b t).mpr ht).mul r.2⟩

lemma cubicUnitResidueMul_injective (b t : Eis) (ht : IsCoprime b t) :
    Function.Injective (cubicUnitResidueMul b t ht) := by
  intro r q heq
  apply Subtype.ext
  exact ((isUnit_quotient_span_iff b t).mpr ht).mul_left_cancel (congrArg Subtype.val heq)

def cubicUnitResidueMulEquiv (b t : Eis) (hb : b≠0) (ht : IsCoprime b t) :
    CubicUnitResidue b ≃ CubicUnitResidue b := by
  letI : Finite (Eis ⧸ Ideal.span {b}):=finite_quotient_span hb
  exact Equiv.ofBijective (cubicUnitResidueMul b t ht)
    ⟨cubicUnitResidueMul_injective b t ht,
      Finite.surjective_of_injective (cubicUnitResidueMul_injective b t ht)⟩

lemma cubicUnitResidueMul_rep_congr (b t : Eis) (ht : IsCoprime b t)
    (r : CubicUnitResidue b) :
    b∣GaussianShiftedPartition.representative b (cubicUnitResidueMul b t ht r).1-
      t*GaussianShiftedPartition.representative b r.1 := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  rw [GaussianShiftedPartition.representative_spec,map_mul,
    GaussianShiftedPartition.representative_spec]
  rfl

theorem cubicUnitGaussSum_frequency_twist (h b t : Eis) (hb : b≠0)
    (hbprimary : lambda^2∣b-1) (ht : IsCoprime b t) :
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
      ring
    _ = _ := heq

theorem arithmeticResidueSum_coprime_product (h a b : Eis)
    (ha : a≠0) (hb : b≠0) (halevel : (3:Eis)∣a)
    (hbprimary : lambda^2∣b-1) (hab : IsCoprime (3*a) b) :
    arithmeticResidueSum h (a*b)=
      eisEmbedding (symbol a b)*eisEmbedding (symbol (3*a) b)*
        arithmeticResidueSum h a*cubicUnitGaussSum h b := by
  obtain ⟨beta,alpha,hbez⟩:=hab
  have hbez' : alpha*b+beta*(3*a)=1:=by linear_combination hbez
  have hab' : IsCoprime (3*a) b:=⟨beta,alpha,hbez⟩
  have hb3 : (3:Eis)∣b-1:=three_dvd_lambda_sq.trans hbprimary
  have hbt : denominatorCondition a b:=⟨hab'.of_mul_left_right,hb3⟩
  have hA := arithmeticResidueSum_frequency_twist (h*alpha) a b ha halevel hbt
  have hAf : 3*a∣(h*alpha)*b-h:=⟨-h*beta,by grind⟩
  rw [arithmeticResidueSum_frequency_congr _ h a ha hAf] at hA
  have hB := cubicUnitGaussSum_frequency_twist (h*beta) b (3*a) hb hbprimary hab'.symm
  have hBf : b∣(h*beta)*(3*a)-h:=⟨-h*alpha,by grind⟩
  rw [cubicUnitGaussSum_frequency_congr _ h b hb hBf] at hB
  rw [arithmeticResidueSum_crt h a b alpha beta ha hb halevel hbprimary hbez',←hA,←hB]
  ring

end CubicEisenstein

end

end OAI
