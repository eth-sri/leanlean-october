module

public import OAI.NumberTheory.DirichletL.RowCompletion.PeriodicRows

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


namespace CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
local instance poolMaximalCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : P.val.IsMaximal :=
  completedReflectionPool_maximal I Q P
noncomputable local instance poolFieldCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Field (Eis⧸P.val) :=
  Ideal.Quotient.field P.val
noncomputable local instance poolFintypeCount (I Q:Ideal Eis) (P:completedReflectionPool I Q) : Fintype (Eis⧸P.val) :=
  Fintype.ofFinite _

end CompletedGauss

namespace CanonicalRowCompletion

section
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "Eis" => ActualEisensteinCubic.O

lemma actualSextic_sixth_one (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P) :
    actualSextic P hg^6=1 := by
  apply MulChar.ext
  intro t
  obtain ⟨n,hn⟩:=Ideal.Quotient.mk_surjective (t:Eis⧸P)
  have hnot:n∉P:=by
    intro hm
    have ht:(t:Eis⧸P)=0:=by rw [←hn];exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
    exact t.ne_zero ht
  have h:=canonicalSextic_sixth_power_mask P hg n
  change actualSextic P hg (Ideal.Quotient.mk P (n^6))=_ at h
  rw [map_pow,map_pow,ite_eq_right hnot] at h
  rw [MulChar.pow_apply_coe,MulChar.one_apply_coe,←hn]
  exact h

lemma actualSextic_power_mod_six (P:Ideal Eis) [P.IsMaximal] (hg:lambda∉P)
    (k:ℕ) (hk:k≠0) (n:Eis) :
    actualSextic P hg (Ideal.Quotient.mk P n)^k=
      (actualSextic P hg^(k%6)) (Ideal.Quotient.mk P n) := by
  rw [←MulChar.pow_apply' _ hk,pow_eq_pow_mod _ (actualSextic_sixth_one P hg)]

lemma idealRowHom_eq_prime_count_product (I:Ideal Eis) (hI:Supported I) (n:Eis) :
    idealRowHom n I=∏P:PrimeIndex I,
      (actualSextic P.val ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1) ^
        ((normalizedFactors I).count P.val%6)) (Ideal.Quotient.mk P.val n) := by
  have he:I=∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val):=by
    change I=∏P:(normalizedFactors I).toFinset,P.val^((normalizedFactors I).count P.val)
    exact ((Ideal.prod_normalizedFactors_eq_self hI.1).symm.trans (Finset.prod_multiset_count _)).trans
      (Finset.prod_coe_sort (normalizedFactors I).toFinset (fun P=>P^((normalizedFactors I).count P))).symm
  calc
    idealRowHom n I = idealRowHom n (∏P:PrimeIndex I,P.val^((normalizedFactors I).count P.val)) :=
      congrArg (idealRowHom n) he
    _ = ∏P:PrimeIndex I,idealRowHom n P.val ^ ((normalizedFactors I).count P.val) := by
      simp only [map_prod,map_pow]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro P hP
      rw [idealRowHom_prime n P.val
        ((supported_factors_good I hI P.val (Multiset.mem_toFinset.mp P.property)).2.1)]
      exact actualSextic_power_mod_six P.val _ _
        (Nat.ne_of_gt (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp P.property))) n

lemma primeIndex_pairwise_coprime (I:Ideal Eis) :
    Pairwise (Function.onFun IsCoprime (fun P:PrimeIndex I=>P.val)) := by
  intro P Q hPQ
  exact Ideal.isCoprime_of_isMaximal (fun he=>hPQ (Subtype.ext he))

end

open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalUnitEuler
local notation "Eis" => ActualEisensteinCubic.O

lemma coprimalityMask_good_part (u:Eisˣ) (a b:ℕ) (r n:Eis)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask (u.val*lambda^a*(2:Eis)^b*r) n=coprimalityMask r n := by
  have hl:IsCoprime lambda n:=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr ((supported_span_iff n).mp hn).1
  have hneg2:IsCoprime (-2:Eis) n:=negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have h2:IsCoprime (2:Eis) n:=hneg2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have hu:IsCoprime u.val n:=⟨(u⁻¹).val,0,by simp⟩
  have hla:IsCoprime (lambda^a) n:=hl.pow_left
  have h2b:IsCoprime ((2:Eis)^b) n:=h2.pow_left
  change (if IsCoprime (u.val*lambda^a*(2:Eis)^b*r) n then (1:ℂ) else 0)=_
  rw [IsCoprime.mul_left_iff,IsCoprime.mul_left_iff,IsCoprime.mul_left_iff]
  simp only [hu,hla,h2b,true_and]
  rfl

lemma idealRowHom_sixth_denominator_mask (r n:Eis) (hr:Supported (Ideal.span {r})) :
    idealRowHom n ((Ideal.span {r})^6)=coprimalityMask r n := by
  rw [map_pow,←idealRowHom_argument_pow n 6 _ hr,idealRowHom_sixth_eq_mask n r hr]
  change (if IsCoprime n r then (1:ℂ) else 0)=(if IsCoprime r n then 1 else 0)
  rw [isCoprime_comm]

lemma mask_times_good_row (m:Eis) (um:Eisˣ) (am bm:ℕ) (g r n:Eis)
    (hg:Supported (Ideal.span {g})) (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (hn:Supported (Ideal.span {n})) :
    coprimalityMask m n*idealRowHom n (Ideal.span {r})=
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [hm,coprimalityMask_good_part um am bm g n hn,map_mul,
    idealRowHom_sixth_denominator_mask g n hg]

theorem rowTwist_eq_fixed_times_good_row_primary
    (Ψ:Eis→*ℂ) (m f z:Eis) (hmLam:lambda∣m) (hm2:(2:Eis)∣m)
    (um:Eisˣ) (am bm:ℕ) (g:Eis) (hg:Supported (Ideal.span {g}))
    (hm:m=um.val*lambda^am*(2:Eis)^bm*g)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r}))
    (hpr:lambda^2∣r-1) (hx:f^4*z=u.val*lambda^a*(2:Eis)^b*r)
    (n:Eis) (hpn:lambda^2∣n-1) :
    rowTwist Ψ m f z n=(Ψ*numeratorBadTwist u a b r hr) n *
      idealRowHom n ((Ideal.span {g})^6*Ideal.span {r}) := by
  rw [rowTwist_eq_actualPeriodicRow_primary Ψ m f z hmLam hm2 u a b r hr hpr hx n hpn]
  by_cases hn:Supported (Ideal.span {n})
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [show ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*idealRowHom n (Ideal.span {r})=
      (Ψ n*numeratorBadTwist u a b r hr n)*(coprimalityMask m n*idealRowHom n (Ideal.span {r})) by ring,
      mask_times_good_row m um am bm g r n hg hm hn]
  · change ((Ψ n*coprimalityMask m n)*numeratorBadTwist u a b r hr n)*_=
      (Ψ n*numeratorBadTwist u a b r hr n)*_
    rw [numeratorBadTwist_zero_of_not_supported u a b r hr n hn]
    simp only [mul_zero,zero_mul]

lemma fixedNumeratorTwist_periodic (Ψ:Eis→*ℂ) (Q:Ideal Eis)
    (hΨ:CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (u:Eisˣ) (a b:ℕ) (r:Eis) (hr:Supported (Ideal.span {r})) :
    CanonicalCoefficientClass.FactorsModulo (Q*Ideal.span {(72:Eis)})
      (Ψ*numeratorBadTwist u a b r hr) := by
  intro x y hxy
  change Ψ x*numeratorBadTwist u a b r hr x=Ψ y*numeratorBadTwist u a b r hr y
  rw [hΨ x y (Ideal.mul_le_left hxy),numeratorBadTwist_periodic u a b r hr x y (Ideal.mul_le_right hxy)]

end CanonicalRowCompletion

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance A4unitsField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P

theorem exists_A4_local_units {ι:Type*} [Fintype ι]
    (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal] (hp:∀i,p i≠0)
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (c0 U w:Eis) (hbez:U*(∏i,p i)+(ramifiedTraceLambda^3*w)*c0=1) :
    ∃σ ε:∀i,(Eis⧸Ideal.span {p i})ˣ,
      (∀i,(σ i:Eis⧸Ideal.span {p i})=
        Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i)) ∧
      ∀i,Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ i:Eis⧸Ideal.span {p i})*(ε i:Eis⧸Ideal.span {p i})=-1 := by
  have hone (i:ι) : ∃σ ε:(Eis⧸Ideal.span {p i})ˣ,
      (σ:Eis⧸Ideal.span {p i})=Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^2*c0*cofactor p i) ∧
      Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0*cofactor p i)*
        (σ:Eis⧸Ideal.span {p i})*(ε:Eis⧸Ideal.span {p i})=-1 := by
    let q:=Ideal.Quotient.mk (Ideal.span {p i})
    have hz:q (∏k,p k)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p (Finset.mem_univ i)))
    have hb:q (ramifiedTraceLambda^3*c0)*q w=1 := by
      have he:=congrArg q hbez
      simp only [map_add,map_mul,map_pow,map_one,hz,mul_zero,zero_add] at he
      simpa only [map_mul,map_pow,mul_assoc,mul_comm,mul_left_comm] using he
    have hb0:q (ramifiedTraceLambda^3*c0)≠0 := by
      intro he
      rw [he,zero_mul] at hb
      exact zero_ne_one hb
    have hc0:q (cofactor p i)≠0 := by
      intro he
      have hi:=productTraceShift_inverse p hp hcop i
      change q (cofactor p i)*_=1 at hi
      rw [he,zero_mul] at hi
      exact zero_ne_one hi
    have hB:q (ramifiedTraceLambda^3*c0*cofactor p i)≠0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 hc0
    have hS:q (ramifiedTraceLambda^2*c0*cofactor p i)≠0 := by
      intro he
      apply hB
      calc
        _=q ramifiedTraceLambda*q (ramifiedTraceLambda^2*c0*cofactor p i) := by
          simp only [map_mul,map_pow]
          ring
        _=0:=by rw [he,mul_zero]
    let σ:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hS
    let B:(Eis⧸Ideal.span {p i})ˣ:=Units.mk0 _ hB
    refine ⟨σ,-(B*σ)⁻¹,rfl,?_⟩
    have hcancel:=congrArg (fun u:(Eis⧸Ideal.span {p i})ˣ=>(u:Eis⧸Ideal.span {p i}))
      (mul_inv_cancel (B*σ))
    simpa only [B,Units.val_mk0,Units.val_mul,Units.val_one,Units.val_neg,mul_neg] using congrArg Neg.neg hcancel
  choose σ ε hσ hε using hone
  exact ⟨σ,ε,hσ,hε⟩

end ShortDraftCusp

section
open scoped BigOperators Classical MatrixGroups Matrix

namespace ShortDraftCusp
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
open CompletedGauss CubicKubota CubicJacobiGlobal LocalReflectionBrackets
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance principalStratumField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance principalStratumFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

end ShortDraftCusp

namespace CubicEisenstein
open ActualEisensteinCubic CubicKubota EisensteinCuspModThree ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein
end

namespace CubicEisenstein
open scoped BigOperators Classical ContDiff MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss CompletedDyadic
open CubicKubota CubicJacobiGlobal ShortDraftCusp LocalReflectionBrackets FiniteGaussPhase
local notation "Eis" => ActualEisensteinCubic.O
noncomputable local instance smoothingField (P:Ideal Eis) [P.IsMaximal] :
    Field (Eis⧸P) := Ideal.Quotient.field P
noncomputable local instance smoothingFintype (P:Ideal Eis) [P.IsMaximal] :
    Fintype (Eis⧸P) := Fintype.ofFinite _

end CubicEisenstein

open scoped Classical BigOperators MatrixGroups

namespace ShortDraftCRT
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT PrimaryIdealUnitReindex
local notation "Eis" => ActualEisensteinCubic.O

lemma exists_primary_unit_multiple (x:Eis) (hx:¬lambda∣x) :
    ∃u:Eisˣ,lambda^2∣u.val*x-1 := by
  have hg:primaryGenerator (Ideal.span {x})≠0:=primaryGenerator_span_ne_zero_iff x |>.mpr hx
  have hspec:=primaryGenerator_spec (Ideal.span {x}) hg
  have ha:Associated x (primaryGenerator (Ideal.span {x})):=
    Ideal.span_singleton_eq_span_singleton.mp hspec.1.symm
  obtain ⟨u,hu⟩:=ha
  refine ⟨u,?_⟩
  rw [mul_comm,hu]
  exact hspec.2

lemma normalize_coprime_pair (a c:Eis) (hcop:IsCoprime a c) :
    ∃u:Eisˣ,IsCoprime (u.val*a) (u.val*c) ∧
      (lambda∣u.val*c→lambda^2∣u.val*a-1) ∧
      (¬lambda∣u.val*c→lambda^2∣u.val*c-1) := by
  have hunit (u:Eisˣ):IsCoprime (u.val*a) (u.val*c) := by
    obtain ⟨r,s,hrs⟩:=hcop
    refine ⟨r*(↑u⁻¹:Eis),s*(↑u⁻¹:Eis),?_⟩
    calc
      _=((↑u⁻¹:Eis)*u.val)*(r*a+s*c):=by ring
      _=1:=by rw [Units.inv_mul,hrs,mul_one]
  have hd (u:Eisˣ):lambda∣u.val*c↔lambda∣c := by
    constructor
    · intro h
      have hh:=dvd_mul_of_dvd_right h (↑u⁻¹:Eis)
      simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
    · intro h
      exact dvd_mul_of_dvd_right h u.val
  by_cases hc:lambda∣c
  · have ha:¬lambda∣a:=fun h=>lambda_prime_actual.not_isUnit (hcop.isUnit_of_dvd' h hc)
    obtain ⟨u,hu⟩:=exists_primary_unit_multiple a ha
    exact ⟨u,hunit u,fun _=>hu,fun hn=>False.elim (hn ((hd u).mpr hc))⟩
  · obtain ⟨u,hu⟩:=exists_primary_unit_multiple c hc
    exact ⟨u,hunit u,fun h=>False.elim (hc ((hd u).mp h)),fun _=>hu⟩

theorem exists_normalized_rational_cusp (a c:Eis) (hc:c≠0) :
    ∃a0 c0:Eis,c0≠0 ∧ c0∣c ∧ IsCoprime a0 c0 ∧
      eisEmbedding a0/eisEmbedding c0=eisEmbedding a/eisEmbedding c ∧
      (lambda∣c0→lambda^2∣a0-1) ∧ (¬lambda∣c0→lambda^2∣c0-1) := by
  let d:Eis:=IsBezout.gcd a c
  obtain ⟨a',ha⟩:=IsBezout.gcd_dvd_left a c
  obtain ⟨c',hc'⟩:=IsBezout.gcd_dvd_right a c
  change a=d*a' at ha
  change c=d*c' at hc'
  have hd:d≠0:=by intro hz; exact hc (by rw [hc',hz,zero_mul])
  have hcp:c'≠0:=by intro hz; exact hc (by rw [hc',hz,mul_zero])
  obtain ⟨r,s,hrs⟩:=IsBezout.gcd_eq_sum a c
  have hred:IsCoprime a' c':=by
    refine ⟨r,s,?_⟩
    apply mul_left_cancel₀ hd
    change d*(r*a'+s*c')=d*1
    calc
      _=r*a+s*c:=by rw [ha,hc'];ring
      _=d:=hrs
      _=_:=by ring
  obtain ⟨u,hu,hua,huc⟩:=normalize_coprime_pair a' c' hred
  refine ⟨u.val*a',u.val*c',mul_ne_zero u.ne_zero hcp,?_,hu,?_,hua,huc⟩
  · refine ⟨d*(↑u⁻¹:Eis),?_⟩
    rw [hc']
    calc
      d*c'=((u.val*(↑u⁻¹:Eis))*d)*c':=by rw [Units.mul_inv,one_mul]
      _=_:=by ring
  · rw [ha,hc',map_mul,map_mul,map_mul,map_mul]
    have he:=eisEmbedding_ne_zero hd
    have hf:=eisEmbedding_ne_zero hcp
    have hu0:=eisEmbedding_ne_zero u.ne_zero
    field_simp

end ShortDraftCRT

end

end OAI
