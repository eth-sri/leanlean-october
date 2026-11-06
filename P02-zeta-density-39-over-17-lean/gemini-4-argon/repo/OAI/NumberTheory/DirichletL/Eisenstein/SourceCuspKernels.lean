module
public import OAI.NumberTheory.DirichletL.Eisenstein.RamifiedValuation

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CubicEisenstein

section
open scoped MatrixGroups

open CubicKubota EisensteinCuspModThree

def sourceCuspCoefficients (j : Fin 3) : SubexponentialBesselCoefficients :=
  ![sourceBesselCoefficients,ramifiedBesselCoefficients false,ramifiedBesselCoefficients true] j

def sourceCuspScale (j : Fin 3) : ℝ := ![1,3,3] j
def sourceCuspBesselConstant (j : Fin 3) : ℂ := ![(3*Real.pi)*constantArithmeticResidue,0,0] j

lemma sourceCuspScale_pos (j : Fin 3) : 0<sourceCuspScale j := by
  fin_cases j <;> norm_num [sourceCuspScale]

lemma ramifiedSource_scaled_fullFunction (side : Bool) (v : ℝ) (hv : 0<v) (z : ℂ) :
    ramifiedSourceFunction (ramifiedCuspRoot side:Eis) (upperPoint z v hv)=
      (ramifiedBesselCoefficients side).fullFunction 0
        (upperPoint (z/3) (v/3) (by positivity)) := by
  rw [ramifiedSource_eq_series]
  simp only [SubexponentialBesselCoefficients.fullFunction,zero_mul,zero_add,
    SubexponentialBesselCoefficients.function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]

theorem sourceCusp_bessel_expansion (j : Fin 3) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint z v hv)=
      (sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (z/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j)
          (div_pos hv (sourceCuspScale_pos j))) := by
  fin_cases j
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      lowerCuspMatrix_zero,sourceBesselFunction] using congrFun cubicSourceResidualFunction_eq_bessel (upperPoint z v hv)
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction false v hv z
  · simpa [sourceCuspCoefficients,sourceCuspBesselConstant,sourceCuspScale,cuspRepresentative,cuspParameter,
      ramifiedSourceFunction,ramifiedCuspRoot,ramifiedOmegaUnit_val] using
      ramifiedSource_scaled_fullFunction true v hv z

def sourceCuspZTerm (j : Fin 3) (z : ℂ) (v : ℝ) (h : Eis) : ℂ :=
  (sourceCuspCoefficients j).scaledConjugateZTerm (sourceCuspScale j) v z h

theorem sourceCuspZFamily_series (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=∑'h:Eis,sourceCuspZTerm j z v h := by
  rw [sourceCuspZFamily,cuspZProfile_positive _ _ _ hv]
  have he : (fun w=>cubicSourceConjugateFunction (integralComplexMatrix (cuspRepresentative j) • upperPoint w v hv))=
      fun w=>star ((sourceCuspCoefficients j).fullFunction (sourceCuspBesselConstant j)
        (upperPoint (w/(sourceCuspScale j:ℂ)) (v/sourceCuspScale j) (div_pos hv (sourceCuspScale_pos j)))) := by
    funext w
    exact congrArg star (sourceCusp_bessel_expansion j v hv w)
  rw [he]
  exact (sourceCuspCoefficients j).scaledConjugate_wirtingerZ (sourceCuspBesselConstant j)
    (sourceCuspScale j) (sourceCuspScale_pos j) v hv z

lemma sourceCuspZTerm_zero (j : Fin 3) (z : ℂ) (v : ℝ) : sourceCuspZTerm j z v 0=0 :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_zero _ _ _

lemma sourceCuspZTerm_bessel (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v)
    (h : Eis) (hh : h≠0) :
    sourceCuspZTerm j z v h=
      (-2*Real.pi*Complex.I*cuspFrequency h/(sourceCuspScale j:ℂ))*
        star ((sourceCuspCoefficients j).value h)*((v/sourceCuspScale j:ℝ):ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*(v/sourceCuspScale j))*
          ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ))) :=
  (sourceCuspCoefficients j).scaledConjugateZTerm_bessel _ (sourceCuspScale_pos j) v hv z h hh

end



def sourceCuspRadialLength (h : Eis) : ℝ := if h=0 then 1 else ‖eisEmbedding h‖^2
def sourceCuspRadialScale (j : Fin 3) : ℝ := thetaBesselScale/sourceCuspScale j

def sourceCuspRadialBaseCoefficient (j : Fin 3) (h : Eis) : ℂ :=
  (-2*Real.pi*Complex.I*cuspFrequency h)*star ((sourceCuspCoefficients j).value h)/
    ((sourceCuspScale j:ℂ)^2*(sourceCuspRadialLength h:ℂ))

def sourceCuspRadialCoefficient (j : Fin 3) (z : ℂ) (h : Eis) : ℂ :=
  sourceCuspRadialBaseCoefficient j h*
    ShortDraftTrace.breveE (-cuspFrequency h*(z/(sourceCuspScale j:ℂ)))

lemma sourceCuspRadialLength_pos (h : Eis) : 0<sourceCuspRadialLength h := by
  by_cases hh:h=0
  · simp only [sourceCuspRadialLength,ite_eq_left hh,zero_lt_one]
  · rw [sourceCuspRadialLength,ite_eq_right hh]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh))

lemma sourceCuspRadialScale_pos (j : Fin 3) : 0<sourceCuspRadialScale j :=
  div_pos thetaBesselScale_pos (sourceCuspScale_pos j)

lemma sourceCuspRadialCoefficient_norm (j : Fin 3) (z : ℂ) (h : Eis) :
    ‖sourceCuspRadialCoefficient j z h‖=‖sourceCuspRadialBaseCoefficient j h‖ := by
  rw [sourceCuspRadialCoefficient,norm_mul,breveE_norm,mul_one]

lemma sourceCuspRadialCoefficient_zero (j : Fin 3) (z : ℂ) :
    sourceCuspRadialCoefficient j z 0=0 := by
  simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,cuspFrequency,
    map_zero,zero_div,mul_zero,zero_mul]

lemma sourceCuspRadialLength_frequency (h : Eis) (hh : h≠0) :
    ‖cuspFrequency h‖=thetaBesselScale*Real.sqrt (sourceCuspRadialLength h) := by
  rw [cuspFrequency_eq_thetaFrequencyScale,norm_mul,sourceCuspRadialLength,ite_eq_right hh,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem sourceCuspZTerm_eq_radial (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) (h : Eis) :
    sourceCuspZTerm j z v h=
      (sourceCuspRadialCoefficient j z h*(sourceCuspRadialLength h:ℂ))*(v:ℂ)*
        schlafliBesselK (1/3) (4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v) := by
  by_cases hh:h=0
  · subst h
    rw [sourceCuspZTerm_zero,sourceCuspRadialCoefficient_zero]
    ring
  · rw [sourceCuspZTerm_bessel j z v hv h hh,sourceCuspRadialLength_frequency h hh]
    have ha : 4*Real.pi*(thetaBesselScale*Real.sqrt (sourceCuspRadialLength h))*(v/sourceCuspScale j)=
        4*Real.pi*sourceCuspRadialScale j*Real.sqrt (sourceCuspRadialLength h)*v := by
      unfold sourceCuspRadialScale
      ring
    rw [ha]
    have hs0 : (sourceCuspScale j:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspScale_pos j).ne'
    have hl0 : (sourceCuspRadialLength h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (sourceCuspRadialLength_pos h).ne'
    simp only [sourceCuspRadialCoefficient,sourceCuspRadialBaseCoefficient,Complex.ofReal_div]
    field_simp [hs0,hl0]

theorem sourceCuspZFamily_eq_radialBesselProfile (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0<v) :
    sourceCuspZFamily j z v=
      radialBesselProfile sourceCuspRadialLength (sourceCuspRadialCoefficient j z) (sourceCuspRadialScale j) v := by
  rw [sourceCuspZFamily_series j z v hv]
  exact tsum_congr (sourceCuspZTerm_eq_radial j z v hv)

end CubicEisenstein


namespace CompletedGauss

lemma positive_nat_pow_cpow (x:ℝ) (hx:0≤x) (n:ℕ) (s:ℂ) :
    ((x^n:ℝ):ℂ)^s=((x:ℂ)^s)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [pow_succ,Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (pow_nonneg hx n) hx,
        hn,pow_succ]

lemma positive_reflection_powers (Q u d X r:ℝ)
    (hQ:0<Q) (hu:0<u) (hd:0<d) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(1+2*w)*(u:ℂ)^(2-2*w)*(2:ℂ)^(4*w)/(d:ℂ)^(2+2*w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(u/d)^2:ℝ):ℂ)*((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^(-w) := by
  have hQ0:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hu0:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
  have hd0:(d:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hd.ne'
  have hX0:(X:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hX.ne'
  have hr0:(r:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hr.ne'
  have hQp:(Q:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0)
  have hup:(u:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hu0)
  have hdp:(d:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hd0)
  have hXp:(X:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hX0)
  have hrp:(r:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl hr0)
  have h2p:(2:ℂ)^w≠0:=Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have h16:((16:ℝ):ℂ)^w=((2:ℂ)^w)^4 := by
    have hh:=positive_nat_pow_cpow 2 (by norm_num) 4 w
    norm_num only [show (2:ℝ)^4=16 by norm_num] at hh
    exact hh
  have hy:((u^2*d^2*X*r/(16*Q^2):ℝ):ℂ)^w=
      (((u:ℂ)^w)^2*((d:ℂ)^w)^2*(X:ℂ)^w*(r:ℂ)^w)/
        (((2:ℂ)^w)^4*((Q:ℂ)^w)^2) := by
    rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) (by positivity)]
    rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) hX.le,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity)]
    rw [positive_nat_pow_cpow u hu.le,positive_nat_pow_cpow d hd.le,
      positive_nat_pow_cpow Q hQ.le,h16]
  rw [Complex.cpow_add _ _ hQ0,Complex.cpow_one,
    Complex.cpow_sub _ _ hu0,Complex.cpow_add _ _ hd0]
  simp only [Complex.cpow_ofNat_mul,Complex.cpow_ofNat]
  rw [Complex.cpow_neg,Complex.cpow_neg,Complex.cpow_neg,hy]
  push_cast
  field_simp

theorem bessel_reflection_scale (q d Q X r:ℝ)
    (hq:0<q) (hd:0<d) (hQ:0<Q) (hX:0<X) (hr:0<r) (w:ℂ) :
    (Q:ℂ)^(2-2*(1/2-w))*besselReflectionFactor q d (1/2-w)*
      (X:ℂ)^(-w)*(r:ℂ)^(-w)=
      ((Q*(q/d)^2:ℝ):ℂ)*
        ((CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2):ℝ):ℂ)^(-w) := by
  have he:=positive_reflection_powers Q (4*Real.pi*q) (4*Real.pi*d) X r
    hQ (by positivity) (by positivity) hX hr w
  have hp:Q*((4*Real.pi*q)/(4*Real.pi*d))^2=Q*(q/d)^2 := by
    field_simp
  have hy:(4*Real.pi*q)^2*(4*Real.pi*d)^2*X*r/(16*Q^2)=
      CubicReflectionKernel.paperScale*(27*q^2*d^2*X*r/Q^2) := by
    unfold CubicReflectionKernel.paperScale
    ring
  rw [hp,hy] at he
  unfold besselReflectionFactor
  convert he using 1 ; congr 2 ; ring_nf

end CompletedGauss


namespace CubicReflectionKernel

lemma paperKernel_three_halves (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (x:ℝ) (hx:0<x) :
    paperKernel V x=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      ((paperScale*x:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
        mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I) := by
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  change paperKernel V x=_
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  simpa only [mellinInv,smul_eq_mul,Complex.real_smul,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using he

lemma paperKernel_three_halves_bound (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V) :
    ∃C:ℝ,0<C ∧ ∀x:ℝ,0<x→‖paperKernel V x‖≤C*(paperScale*x)^(-(3/2:ℝ)) := by
  obtain ⟨C,hC,hb⟩:=mellinInv_euler_line_bound V v0 v1 hv0 hVs hV 2 0
  refine ⟨C,hC,?_⟩
  intro x hx
  have he:=mellinInv_euler_shift V v0 v1 hv0 hVs hV 2 0 (3/2) (by norm_num)
    (paperScale*x) (mul_pos paperScale_pos hx)
  have hl:mellinInv 0 (mellinEulerData V 0) (paperScale*x)=paperKernel V x:=by
    have hf : mellinEulerData V 0=(fun s:ℂ=>mellin V (-s)*gammaMultiplier s) := by
      funext s
      simp only [mellinEulerData,pow_zero,one_mul,mellinData]
    rw [hf]
    rfl
  rw [hl] at he
  rw [he]
  exact hb (3/2) (by norm_num) (paperScale*x) (mul_pos paperScale_pos hx)

end CubicReflectionKernel
namespace CompletedGauss

section
open CubicReflectionKernel

theorem paperKernel_weighted_mellin {α:Type*} [Countable α]
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) :
    (∑'i,a i*paperKernel V (c*r i))=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      (∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
        (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
          mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)) := by
  let M:ℝ→ℂ:=fun t=>((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
    mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I)
  have hM:Integrable M:=by
    simpa only [M,inverseMellinIntegrand,Complex.ofReal_div,Complex.ofReal_ofNat] using
      inverseMellinIntegrand_vertical_integrable V v0 v1 hv0 hVs hV 2 0 (3/2)
        (by norm_num) (paperScale*c) (mul_pos paperScale_pos hc)
  have hi (i:α) : a i*paperKernel V (c*r i)=(1/(2*Real.pi):ℂ)*∫t:ℝ,
      a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I))*M t := by
    rw [paperKernel_three_halves V v0 v1 hv0 hVs hV _ (mul_pos hc (hr i))]
    rw [←mul_assoc,mul_comm (a i),mul_assoc,←integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_pos paperScale_pos hc).le (hr i).le]
    dsimp only [M]
    ring
  simp_rw [hi]
  rw [tsum_mul_left]
  congr 1
  simpa only [M,Complex.ofReal_div,Complex.ofReal_ofNat] using
    weighted_vertical_sum_integral r hr a (3/2) has M hM

end

open CubicEisenstein CubicReflectionKernel

lemma besselSmoothingIntegrand_reflected_kernel_line {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (X:ℝ) (hX:0<X) (t:ℝ) :
    besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
      (A*((Q*(q/d)^2:ℝ):ℂ))*
        ((∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
          (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
            mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))) := by
  let s:ℂ:=(-1:ℂ)+(-t)*Complex.I
  let w:ℂ:=(3/2:ℂ)+t*Complex.I
  have hs:s.re-1/2=-(3/2:ℝ):=by dsimp [s];norm_num
  have hslt:s.re<4/3:=by dsimp [s];norm_num
  have hsum:Summable (fun i=>‖a i‖*(r i)^(s.re-1/2)):=by simpa only [hs] using has
  have hsw:1/2-w=s:=by dsimp [s,w];ring
  have hw:1/2-s=w:=by rw [←hsw];ring
  have hsw':s-1/2=-w:=by rw [←hsw];ring
  have hp:=bessel_reflection_scale q d Q X 1 hq hd hQ hX (by norm_num) w
  simp only [hsw,Complex.ofReal_one,Complex.one_cpow,mul_one] at hp
  have he:=continuedBesselDirichlet_reflection F r hr a q d Q hd hQ A hreflect s hslt hsum
  change besselSmoothingIntegrand F q V X s=_
  rw [besselSmoothingIntegrand,he,hw,hsw']
  change _=(A*((Q*(q/d)^2:ℝ):ℂ))*
    ((∑'i,a i*(r i:ℂ)^(-w))*
      (((paperScale*(27*q^2*d^2*X/Q^2):ℝ):ℂ)^(-w)*mellinEulerData V 0 w))
  rw [mellinEulerData,pow_zero,one_mul,mellinData]
  calc
    _=(A*mellin V (-w)*gammaMultiplier w*(∑'i,a i*(r i:ℂ)^(-w)))*
      ((Q:ℂ)^(2-2*s)*besselReflectionFactor q d s*(X:ℂ)^(-w)):=by ring
    _=_:=by rw [hp];ring

end CompletedGauss


namespace CompletedGauss
open CubicEisenstein CubicReflectionKernel

theorem besselSmoothingIntegral_reflected_kernel {α:Type*} [Countable α]
    (F:ℝ→ℂ) (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (q d Q:ℝ) (hq:0<q) (hd:0<d) (hQ:0<Q) (A:ℂ)
    (hreflect:∀v:ℝ,0<v→F v=A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (X:ℝ) (hX:0<X) :
    (1/(2*Real.pi):ℂ)*∫t:ℝ,besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)=
      (A*(Q:ℂ)*((q/d:ℝ):ℂ)^2)*
        ∑'i,a i*paperKernel V (27*q^2*d^2*X*r i/Q^2) := by
  let c:ℝ:=27*q^2*d^2*X/Q^2
  have hc:0<c:=by dsimp [c];positivity
  let M:ℝ→ℂ:=fun t=>(∑'i,a i*(r i:ℂ)^(-((3/2:ℂ)+t*Complex.I)))*
    (((paperScale*c:ℝ):ℂ)^(-((3/2:ℂ)+t*Complex.I))*
      mellinEulerData V 0 ((3/2:ℂ)+t*Complex.I))
  have hk:=paperKernel_weighted_mellin r hr a has V v0 v1 hv0 hVs hV c hc
  have hpoint (t:ℝ) :
      besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I)=
        (A*((Q*(q/d)^2:ℝ):ℂ))*M t :=
    besselSmoothingIntegrand_reflected_kernel_line F
      r hr a q d Q hq hd hQ A hreflect has V X hX t
  calc
    _=(1/(2*Real.pi):ℂ)*∫t:ℝ,
        besselSmoothingIntegrand F q V X ((-1:ℂ)+(-t)*Complex.I):=by
      congr 1
      simpa only [Complex.ofReal_neg] using
        (integral_neg_eq_self (fun t:ℝ=>
          besselSmoothingIntegrand F q V X ((-1:ℂ)+t*Complex.I)) volume).symm
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*((1/(2*Real.pi):ℂ)*∫t:ℝ,M t):=by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _=(A*((Q*(q/d)^2:ℝ):ℂ))*(∑'i,a i*paperKernel V (c*r i)):=by rw [hk]
    _=_:=by
      push_cast
      congr 1
      · ring
      · apply tsum_congr
        intro i
        congr 2
        dsimp [c]
        ring

theorem paperKernel_weighted_norm_summable {α:Type*}
    (r:α→ℝ) (hr:∀i,0<r i) (a:α→ℂ)
    (has:Summable (fun i=>‖a i‖*(r i)^(-(3/2:ℝ))))
    (V:ℝ→ℂ) (v0 v1:ℝ) (hv0:0<v0)
    (hVs:Function.support V⊆Set.Icc v0 v1) (hV:ContDiff ℝ ∞ V)
    (c:ℝ) (hc:0<c) : Summable (fun i=>‖a i*paperKernel V (c*r i)‖) := by
  obtain ⟨C,hC,hb⟩:=paperKernel_three_halves_bound V v0 v1 hv0 hVs hV
  apply (has.mul_left (C*(paperScale*c)^(-(3/2:ℝ)))).of_nonneg_of_le (fun i=>norm_nonneg _)
  intro i
  rw [norm_mul]
  calc
    _≤‖a i‖*(C*(paperScale*(c*r i))^(-(3/2:ℝ))):=
      mul_le_mul_of_nonneg_left (hb _ (mul_pos hc (hr i))) (norm_nonneg _)
    _=(C*(paperScale*c)^(-(3/2:ℝ)))*(‖a i‖*(r i)^(-(3/2:ℝ))):=by
      rw [show paperScale*(c*r i)=(paperScale*c)*r i by ring,
        Real.mul_rpow (mul_pos paperScale_pos hc).le (hr i).le]
      ring
