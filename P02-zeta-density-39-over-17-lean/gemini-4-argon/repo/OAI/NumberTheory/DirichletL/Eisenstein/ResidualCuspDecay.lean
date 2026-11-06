module
public import OAI.NumberTheory.DirichletL.Eisenstein.BesselMellinTransform
public import OAI.NumberTheory.DirichletL.Eisenstein.TranslatedFourierResidues

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CubicEisenstein


def residualCuspDecayRate : ℝ := Real.pi*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹/4

lemma residualCuspDecayRate_pos : 0<residualCuspDecayRate := by
  have hd : 0<‖(3:ℂ)*ConcreteTraceCRT.eisLam‖ := norm_pos_iff.mpr
    (mul_ne_zero (by norm_num) ConcreteTraceCRT.eisLam_ne_zero)
  unfold residualCuspDecayRate
  positivity

end CubicEisenstein

namespace ShortDraftCRT
open scoped Matrix

section
variable {R : Type*} [CommRing R]

theorem exists_frequency_lift (N p h : R) (hcop : IsCoprime N p) :
    ∃k : R, N∣k ∧ p∣k-h := by
  obtain ⟨u,v,huv⟩ := hcop
  refine ⟨h*u*N,⟨h*u,by ring⟩,⟨-h*v,?_⟩⟩
  linear_combination h*huv

variable [IsDomain R]

end

variable {R : Type*} [CommRing R] [IsDomain R]

end ShortDraftCRT


namespace ShortDraftCusp

section
open CubicJacobiGlobal CubicKubota

theorem A3_principal_global (a c0 r : Eis)
    (ha : lambda^2∣a-1) (hr : lambda^2∣r-1) :
    symbol (c0*r) a=symbol c0 a*symbol a r := by
  rw [symbol_mul_numerator _ _ a ha,
    symbol_reciprocity r a (primary_ne_zero r hr) (primary_ne_zero a ha) hr ha]

theorem A3_ramified_global (a b cprime d u : Eis)
    (hdet : a*d-b*(u*cprime)=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) :
    symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b)*symbol cprime a := by
  have h1 : symbol a (a-u*b)*symbol (u*cprime-u*d) (a-u*b)=symbol (-u) (a-u*b) := by
    rw [←symbol_mul_numerator _ _ _ hA]
    apply symbol_congr
    refine ⟨u*cprime,?_⟩
    linear_combination -u*hdet
  have h2 : symbol (a-u*b) a*symbol cprime a=1 := by
    rw [←symbol_mul_numerator _ _ _ ha,←symbol_one_numerator a ha]
    apply symbol_congr
    refine ⟨cprime-d,?_⟩
    linear_combination hdet
  rw [symbol_reciprocity a (a-u*b) (primary_ne_zero a ha)
    (primary_ne_zero _ hA) ha hA] at h1
  calc
    _ = (symbol (a-u*b) a*symbol cprime a)*symbol (u*cprime-u*d) (a-u*b) := by rw [h2,one_mul]
    _ = (symbol (a-u*b) a*symbol (u*cprime-u*d) (a-u*b))*symbol cprime a := by ring
    _ = _ := by rw [h1]

theorem A3_ramified_global_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣(a-u*b)-1) (hr : lambda^2∣r-1) :
    symbol (u*(c0*r)-u*d) (a-u*b)=
      (symbol (-u) (a-u*b)*symbol c0 a)*symbol a r := by
  rw [A3_ramified_global a b (c0*r) d u hdet ha hA,
    A3_principal_global a c0 r ha hr]
  ring

theorem A3_unramified_global (a b c d : Eis)
    (hdet : a*d-b*c=1) (hb : lambda^2∣(-b)-1) (hc : lambda^2∣c-1)
    (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c := by
  have hp : lambda^2∣((-b)*c)-1 := primary_mul (-b) c hb hc
  have hprod : symbol d (-b)*symbol d c=1 := by
    rw [←symbol_mul_denominator]
    have hnine : (9:Eis)∣(-b)*c-1 := by
      convert dvd_neg.mpr h9 using 1
      linear_combination hdet
    have hd : d∣(-b)*c-1 := by
      refine ⟨-a,?_⟩
      linear_combination hdet
    rw [symbol_denominator_congr d ((-b)*c) 1 hp (by simp) hnine hd,symbol_one]
  have hother : symbol a c*symbol d c=1 := by
    rw [←symbol_mul_numerator _ _ _ hc,←symbol_one_numerator c hc]
    apply symbol_congr
    refine ⟨b,?_⟩
    linear_combination hdet
  rw [symbol_neg_numerator _ _ hb]
  calc
    symbol d (-b) = symbol d (-b)*(symbol a c*symbol d c) := by rw [hother,mul_one]
    _ = (symbol d (-b)*symbol d c)*symbol a c := by ring
    _ = symbol a c := by rw [hprod,one_mul]

theorem A3_unramified_global_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hb : lambda^2∣(-b)-1)
    (hc : lambda^2∣c0*r-1) (h9 : (9:Eis)∣a*d) :
    symbol (-d) (-b)=symbol a c0*symbol a r := by
  rw [A3_unramified_global a b (c0*r) d hdet hb hc h9,symbol_mul_denominator]

end

open CubicJacobiGlobal CubicKubota

theorem A3_ramified_fixed_factor_congr (M c0 u a a0 b b0 : Eis)
    (h9M : (9:Eis)∣M) (hcM : c0∣M) (huM : u∣M)
    (ha : lambda^2∣a-1) (ha0 : lambda^2∣a0-1)
    (hA : lambda^2∣a-u*b-1) (hA0 : lambda^2∣a0-u*b0-1)
    (hma : M∣a-a0) (hmb : M∣b-b0) :
    symbol (-u) (a-u*b)*symbol c0 a=
      symbol (-u) (a0-u*b0)*symbol c0 a0 := by
  have hdiff : M∣(a-u*b)-(a0-u*b0) := by
    convert dvd_sub hma (dvd_mul_of_dvd_right hmb u) using 1 ; ring
  have hfirst : symbol (-u) (a-u*b)=symbol (-u) (a0-u*b0) := by
    apply symbol_denominator_congr _ _ _ hA hA0 (h9M.trans hdiff)
    exact neg_dvd.mpr (huM.trans hdiff)
  have hsecond := symbol_denominator_congr c0 a a0 ha ha0 (h9M.trans hma) (hcM.trans hma)
  rw [hfirst,hsecond]

theorem A3_unramified_fixed_factor_congr (M c0 a a0 : Eis)
    (hcM : c0∣M) (hma : M∣a-a0) : symbol a c0=symbol a0 c0 :=
  symbol_congr (hcM.trans hma)

theorem norm_embedded_cubic_symbol (x a : Eis)
    (ha : lambda^2∣a-1) (hcop : IsCoprime x a) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol x a)‖=1 := by
  have hcube : ConcreteTraceCRT.eisEmbedding (symbol x a)^3=1 := by
    rw [←map_pow,symbol_cube_of_isCoprime x a ha hcop,map_one]
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3:ℕ)≠0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm hcube

theorem norm_A3_ramified_fixed_factor (a b c0 r d u : Eis)
    (hdet : a*d-b*(u*(c0*r))=1)
    (ha : lambda^2∣a-1) (hA : lambda^2∣a-u*b-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b)*symbol c0 a)‖=1 := by
  have hfirst : ‖ConcreteTraceCRT.eisEmbedding (symbol (-u) (a-u*b))‖=1 := by
    apply norm_embedded_cubic_symbol _ _ hA
    refine ⟨b*(c0*r-d),d,?_⟩
    linear_combination hdet
  have hsecond : ‖ConcreteTraceCRT.eisEmbedding (symbol c0 a)‖=1 := by
    apply norm_embedded_cubic_symbol _ _ ha
    refine ⟨-b*u*r,d,?_⟩
    linear_combination hdet
  rw [map_mul,norm_mul,hfirst,hsecond,one_mul]

theorem norm_A3_unramified_fixed_factor (a b c0 r d : Eis)
    (hdet : a*d-b*(c0*r)=1) (hc : lambda^2∣c0-1) :
    ‖ConcreteTraceCRT.eisEmbedding (symbol a c0)‖=1 := by
  apply norm_embedded_cubic_symbol _ _ hc
  refine ⟨d,-b*r,?_⟩
  linear_combination hdet

end ShortDraftCusp

namespace CubicEisenstein
open CubicJacobiGlobal CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)

lemma cubicUnitGaussSum_norm_le (h c:Eis) (hc:c≠0) (hp:lambda^2∣c-1):
    ‖cubicUnitGaussSum h c‖≤Ideal.absNorm (Ideal.span {c}):=by
  let:Finite (Eis⧸Ideal.span {c}):=finite_quotient_span hc
  let:Fintype (Eis⧸Ideal.span {c}):=Fintype.ofFinite _
  let:Fintype (CubicUnitResidue c):=Fintype.ofFinite _
  have hs (r:CubicUnitResidue c):
      ‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)‖=1:=by
    apply Complex.norm_eq_one_of_pow_eq_one (n:=3) _ (by decide)
    rw [←map_pow,symbol_cube_of_isCoprime _ c hp _ ,map_one]
    apply IsCoprime.symm
    apply (isUnit_quotient_span_iff c _).mp
    simpa only [GaussianShiftedPartition.representative_spec] using r.2
  rw [cubicUnitGaussSum,tsum_fintype]
  calc
    _≤∑r:CubicUnitResidue c,‖eisEmbedding (symbol (GaussianShiftedPartition.representative c r.val) c)*
      residueAdditive (3*h) c (GaussianShiftedPartition.representative c r.val)‖:=norm_sum_le _ _
    _=(Fintype.card (CubicUnitResidue c):ℝ):=by
      simp only [norm_mul,hs,residueAdditive,breveE_norm,
        Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _≤(Fintype.card (Eis⧸Ideal.span {c}):ℝ):=by
      exact_mod_cast Fintype.card_subtype_le (fun r=>IsUnit r)
    _=Ideal.absNorm (Ideal.span {c}):=by
      simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem unramifiedCubicGaussSeries_summable_norm (s:ℂ) (hs:2<s.re) (h:Eis):
    Summable (fun I:GoodIdeal=>‖(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)‖):=by
  have hs':1<(s-1).re:=by simp only [Complex.sub_re,Complex.one_re];linarith
  apply ((unramifiedNormWeight_summable_norm (s-1) hs').subtype
    (fun I:Ideal Eis=>primaryGenerator I≠0)).of_nonneg_of_le (fun _=>norm_nonneg _)
  intro I
  dsimp only [Function.comp_def]
  simp only [unramifiedNormWeight_shift,norm_mul,Complex.norm_natCast,
    unramifiedNormWeight_of_good s I.val I.2]
  have hg:=cubicUnitGaussSum_norm_le h (primaryGenerator I.val) I.2
    (primaryGenerator_spec I.val I.2).2
  rw [(primaryGenerator_spec I.val I.2).1] at hg
  nlinarith [norm_nonneg ((Ideal.absNorm I.val:ℂ)^(-s))]

abbrev PrimeDeletedIdeal (p:Eis):={I:GoodIdeal//¬(Ideal.span {p}:Ideal Eis)∣I.val}

def unramifiedPrimeDeletedSeries (p:Eis) (s:ℂ) (h:Eis):ℂ:=
  ∑'I:PrimeDeletedIdeal p,(Ideal.absNorm I.val.val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator I.val.val)

lemma primaryGenerator_pow (I:Ideal Eis) (n:ℕ):
    primaryGenerator (I^n)=primaryGenerator I^n:=
  map_pow primaryGeneratorHom I n

lemma gaussPrimeIdeal_prime (p:Eis) (hp:Prime p):Prime (Ideal.span {p}:Ideal Eis):=
  Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp)

def gaussPrimeFactorMap (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (q:ℕ×PrimeDeletedIdeal p):GoodIdeal:=
  ⟨(Ideal.span {p})^q.1*q.2.val.val,by
    rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) q.2.val.2⟩

lemma gaussPrimeFactorMap_bijective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    Function.Bijective (gaussPrimeFactorMap p hp hprimary):=by
  let P:Ideal Eis:=Ideal.span {p}
  have hP:Prime P:=gaussPrimeIdeal_prime p hp
  constructor
  · rintro ⟨n,I⟩ ⟨m,J⟩ heq
    have hh:P^n*I.val.val=P^m*J.val.val:=congrArg Subtype.val heq
    have hn:n=m:=by
      have hm:=congrArg (multiplicity P) hh
      rw [prime_power_remainder_multiplicity hP I.2,
        prime_power_remainder_multiplicity hP J.2] at hm
      exact hm
    subst m
    have hIJ:I=J:=Subtype.ext (Subtype.ext
      (mul_left_cancel₀ (pow_ne_zero n hP.ne_zero) hh))
    subst J
    rfl
  · intro I
    obtain ⟨J,hJ,hnot⟩:=(FiniteMultiplicity.of_prime_left hP
      (primaryGenerator_ne_zero_ideal I.val I.2)).exists_eq_pow_mul_and_not_dvd
    have hgood:primaryGenerator J≠0:=by
      intro hzero
      apply I.2
      rw [hJ,primaryGenerator_mul,hzero,mul_zero]
    refine ⟨(multiplicity P I.val,⟨⟨J,hgood⟩,hnot⟩),?_⟩
    exact Subtype.ext hJ.symm

def gaussPrimeFactorEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1):
    ℕ×PrimeDeletedIdeal p≃GoodIdeal:=
  Equiv.ofBijective (gaussPrimeFactorMap p hp hprimary)
    (gaussPrimeFactorMap_bijective p hp hprimary)

lemma primeDeleted_generator_coprime (p:Eis) (hp:Prime p) (I:PrimeDeletedIdeal p):
    IsCoprime p (primaryGenerator I.val.val):=by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  apply I.2
  rw [Ideal.dvd_iff_le,←(primaryGenerator_spec I.val.val I.val.2).1,
    Ideal.span_singleton_le_span_singleton]
  exact hd

lemma primary_pow_congruence (p:Eis) (hprimary:lambda^2∣p-1) (n:ℕ):
    lambda^2∣p^n-1:=by
  simpa only [one_pow] using hprimary.trans (sub_dvd_pow_sub_pow p 1 n)

lemma gaussPrimeFactor_term (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (s:ℂ) (h:Eis) (n:ℕ) (I:PrimeDeletedIdeal p):
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val)=
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
      ((Ideal.absNorm I.val.val:ℂ)^(-s)*cubicUnitGaussSum (h*p^n) (primaryGenerator I.val.val)):=by
  change (Ideal.absNorm ((Ideal.span {p})^n*I.val.val):ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator ((Ideal.span {p})^n*I.val.val))=_
  rw [primaryGenerator_mul,primaryGenerator_pow,primaryGenerator_span p hp.ne_zero hprimary,
    cubicUnitGaussSum_coprime_product h (p^n) (primaryGenerator I.val.val)
      (pow_ne_zero _ hp.ne_zero) I.val.2 (primary_pow_congruence p hprimary n)
      (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).pow_left,
    map_mul,map_pow,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  have he:((Ideal.absNorm (Ideal.span {p})^n:ℕ):ℂ)^(-s)=
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n:=by
    rw [Nat.cast_pow,←Complex.natCast_cpow_natCast_mul,Complex.cpow_nat_mul]
  rw [he]
  ring

theorem unramifiedCubicGaussSeries_prime_reindex (p:Eis) (hp:Prime p)
    (hprimary:lambda^2∣p-1) (s:ℂ) (hs:2<s.re) (h:Eis):
    unramifiedCubicGaussSeries s h=
      ∑'n:ℕ,((Ideal.absNorm (Ideal.span {p}):ℂ)^(-s))^n*cubicUnitGaussSum h (p^n)*
        unramifiedPrimeDeletedSeries p s (h*p^n):=by
  have hsum:Summable (fun I:GoodIdeal=>(Ideal.absNorm I.val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator I.val)):=
    (unramifiedCubicGaussSeries_summable_norm s hs h).of_norm
  have hpull:=(gaussPrimeFactorEquiv p hp hprimary).summable_iff.mpr hsum
  change Summable (fun q:ℕ×PrimeDeletedIdeal p=>
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val)) at hpull
  rw [unramifiedCubicGaussSeries,←(gaussPrimeFactorEquiv p hp hprimary).tsum_eq]
  change (∑'q:ℕ×PrimeDeletedIdeal p,
    (Ideal.absNorm (gaussPrimeFactorMap p hp hprimary q).val:ℂ)^(-s)*
      cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary q).val))=_
  rw [hpull.tsum_prod]
  apply tsum_congr
  intro n
  change (∑'I:PrimeDeletedIdeal p,(Ideal.absNorm (gaussPrimeFactorMap p hp hprimary (n,I)).val:ℂ)^(-s)*
    cubicUnitGaussSum h (primaryGenerator (gaussPrimeFactorMap p hp hprimary (n,I)).val))=_
  simp_rw [gaussPrimeFactor_term p hp hprimary s h n]
  exact tsum_mul_left

lemma unramifiedPrimeDeletedSeries_cube_shift (p:Eis) (hp:Prime p) (s:ℂ) (h:Eis):
    unramifiedPrimeDeletedSeries p s (h*p^3)=unramifiedPrimeDeletedSeries p s h:=by
  apply tsum_congr
  intro I
  congr 1
  exact cubicUnitGaussSum_cube_shift h _ p I.val.2
    (primaryGenerator_spec I.val.val I.val.2).2 (primeDeleted_generator_coprime p hp I).symm
