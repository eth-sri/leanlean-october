module

public import OAI.NumberTheory.DirichletL.Eisenstein.CuspAverage

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
open Filter
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
open scoped Classical Topology MatrixGroups

section
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma period_integral_fourier_translation (f:ℂ→ℂ)
    (hp:∀(n:Eis)(z:ℂ),f (z+3*eisEmbedding n)=f z) (h:Eis) (b:ℂ) :
    (∫z in periodDomain,f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      ShortDraftTrace.breveE (cuspFrequency h*b)*
        ∫z in periodDomain,f z*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  let g : ℂ→ℂ := fun z=>f z*ShortDraftTrace.breveE (-cuspFrequency h*z)
  have hg : ∀(n:Eis)(z:ℂ),g (z+3*eisEmbedding n)=g z := by
    intro n z
    dsimp only [g]
    rw [hp,cuspFrequency_negative_period]
  have he (z:ℂ) : f (z+b)*ShortDraftTrace.breveE (-cuspFrequency h*z)=
      ShortDraftTrace.breveE (cuspFrequency h*b)*g (b+z) := by
    dsimp only [g]
    rw [mul_left_comm,←AddChar.map_add_eq_mul]
    congr 1
    · ring
    · ring
  simp_rw [he]
  rw [integral_const_mul,period_integral_translation g hg b]

theorem rational_cusp_fourier_right_T (r:SL(2,ℤ)) (n:ℕ) (h:Eis) (s:ℂ) (hs:2<s.re) :
    (∫w in cuspPeriodStrip 5 6,
      hyperbolicEisenstein s (rationalComplex (r*ModularGroup.T^n) • w)*
        cuspFourierPhase h w∂hyperbolicVolume)=
      ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*
        ∫w in cuspPeriodStrip 5 6,
          hyperbolicEisenstein s (rationalComplex r • w)*cuspFourierPhase h w∂hyperbolicVolume := by
  let f : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex (r*ModularGroup.T^n) • w)*cuspFourierPhase h w
  let g : HyperbolicSpace→ℂ := fun w=>hyperbolicEisenstein s
    (rationalComplex r • w)*cuspFourierPhase h w
  have hf : Continuous f := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  have hg : Continuous g := ((hyperbolicEisenstein_continuous s hs).comp
    (continuous_hyperbolic_action _)).mul (cuspFourierPhase_continuous h)
  change (∫w in cuspPeriodStrip 5 6,f w∂hyperbolicVolume)=
    ShortDraftTrace.breveE (cuspFrequency h*(n:ℂ))*∫w in cuspPeriodStrip 5 6,g w∂hyperbolicVolume
  rw [cuspPeriodStrip_integral_coordinates f hf.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable f hf),
    cuspPeriodStrip_integral_coordinates g hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable g hg),
    ←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro v hv
  have hv0 : 0<v := by linarith [hv.1]
  dsimp only
  simp_rw [f,g,cuspCoordinateLift_positive v _ hv0,map_mul,mul_smul,rationalComplex_T_pow_upper,
    cuspFourierPhase,hyperbolicHorizontal_upperPoint]
  rw [period_integral_fourier_translation
    (fun z=>hyperbolicEisenstein s (rationalComplex r • upperPoint z v hv0))
    (fun a z=>hyperbolicEisenstein_rational_periodic r a s hs z v hv0) h (n:ℂ)]
  ring

lemma translatedCuspFourier_residue_scaled_of_initial (h:Eis) (M N:levelTwo) (c:ℂ)
    (he : ∀s:ℂ,4<s.re→0<s.im→
      (∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix M • w)*cuspFourierPhase h w∂hyperbolicVolume)=
      c*∫w in cuspPeriodStrip 5 6,hyperbolicEisenstein s (sourceComplexMatrix N • w)*cuspFourierPhase h w∂hyperbolicVolume) :
    translatedCuspFourier h M cubicEisensteinResidue=
      c*translatedCuspFourier h N cubicEisensteinResidue := by
  let f : ℂ→ℂ := translatedCuspFamily h M 2 3 (by norm_num) (by norm_num)
  let g : ℂ→ℂ := fun s=>c*translatedCuspFamily h N 2 3 (by norm_num) (by norm_num) s
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ f domain := fun s hs=>
    translatedCuspFamily_analyticAt_nonreal h M 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne'
  have hg : AnalyticOnNhd ℂ g domain := fun s hs=>analyticAt_const.mul
    (translatedCuspFamily_analyticAt_nonreal h N 2 3 (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne')
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : f=ᶠ[𝓝 (5+Complex.I:ℂ)]g := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    dsimp only [f,g]
    rw [translatedCuspFamily_initial h M 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2,
      translatedCuspFamily_initial h N 2 3 (by norm_num) (by norm_num) (by norm_num) s hs.1 hs.2]
    exact by grind
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev
  have hl := (translatedCuspFamily_residue_limit h M 2 3 (by norm_num) (by norm_num)).comp
    upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit h N 2 3 (by norm_num) (by norm_num)).const_mul c).comp
    upperVertical_tendsto_cubic_punctured
  apply tendsto_nhds_unique_of_eventuallyEq hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0<t at ht
  have hv:=heq (show (4/3:ℂ)+(t:ℂ)*Complex.I∈domain by
    constructor
    · norm_num
    simp_all)
  grind

lemma translatedCuspFourier_one (h:Eis) (F:KernelQuotientL2) :
    translatedCuspFourier h 1 F=kernelCuspFourier h F := by
  rw [translatedCuspFourier,ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,kernelSourcePullback_one]

def sourceRayPhaseSum (h:Eis) : ℂ :=
  ∑ b:Fin 3,ShortDraftTrace.breveE (cuspFrequency h*(b.val:ℂ))

end

section
open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma sourceRayPhase_cube (h:Eis) :
    ShortDraftTrace.breveE (cuspFrequency h)^3=1 := by
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  have hp:=cuspFrequency_period h (1:Eis)
  grind

lemma sourceRayPhaseSum_formula (h:Eis) :
    sourceRayPhaseSum h=1+ShortDraftTrace.breveE (cuspFrequency h)+
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
  unfold sourceRayPhaseSum
  simp only [Fin.sum_univ_succ,Fin.val_zero,Nat.cast_zero,mul_zero,AddChar.map_zero_eq_one,
    Fin.val_succ,Nat.cast_add,Nat.cast_one,zero_add,mul_one,Fin.sum_univ_zero,add_zero]
  have he : ShortDraftTrace.breveE (cuspFrequency h*(1+1))=
      ShortDraftTrace.breveE (cuspFrequency h)^2 := by
    rw [mul_add,mul_one,AddChar.map_add_eq_mul,pow_two]
  grind

lemma sourceRayPhaseSum_eq (h:Eis) :
    sourceRayPhaseSum h=if ShortDraftTrace.breveE (cuspFrequency h)=1 then 3 else 0 := by
  rw [sourceRayPhaseSum_formula]
  split_ifs with he
  · grind
  · have hc:=sourceRayPhase_cube h
    grind

lemma kernelCuspFourier_residue_horizontal (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ShortDraftTrace.breveE (cuspFrequency h)*kernelCuspFourier h cubicEisensteinResidue := by
  have hh:=translatedCuspFourier_residue_scaled_of_initial h 1 1
    (ShortDraftTrace.breveE (cuspFrequency h)) (by
      intro s hs hi
      have he:=rational_cusp_fourier_right_T (1:SL(2,ℤ)) 1 h s (by linarith)
      have hT (w:HyperbolicSpace) : hyperbolicEisenstein s (rationalComplex ModularGroup.T • w)=hyperbolicEisenstein s w := by
        simpa only [pow_one] using hyperbolicEisenstein_T_pow s 1 w
      simpa only [one_mul,pow_one,map_one,one_smul,Nat.cast_one,mul_one,hT] using he)
  simpa only [translatedCuspFourier_one] using hh

lemma kernelCuspFourier_residue_eq_zero_of_not_horizontal (h:Eis)
    (hh:ShortDraftTrace.breveE (cuspFrequency h)≠1) :
    kernelCuspFourier h cubicEisensteinResidue=0 := by
  have he:=kernelCuspFourier_residue_horizontal h
  grind

end

open CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma oppositeFrequency_cross_identity (h:Eis) :
    Set.EqOn (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s (3*(9*h)))
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) {s:ℂ|1<s.re ∧ 0<s.im} := by
  let domain : Set ℂ := {s | 1<s.re ∧ 0<s.im}
  have hconvex : Convex ℝ domain :=
    ((convex_Ioi (1:ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Ioi (0:ℝ)).linear_preimage Complex.imCLM.toLinearMap)
  have hf : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily h oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s (3*(9*h))) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal h oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt (3*(9*h)) s hs.1)
  have hg : AnalyticOnNhd ℂ (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s*cuspWhittakerHeightFactor s h) domain := by
    intro s hs
    exact (translatedCuspFamily_analyticAt_nonreal (3*(9*h)) oppositeSource 2 3
      (by norm_num) (by norm_num) s hs.1.ne' hs.2.ne').mul
      (cuspWhittakerHeightFactor_analyticAt h s hs.1)
  have hstart : (5+Complex.I:ℂ)∈domain := by norm_num [domain]
  have hopen : IsOpen {s:ℂ | 4<s.re ∧ 0<s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hev : (fun s=>translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) s*
      cuspWhittakerHeightFactor s (3*(9*h)))=ᶠ[𝓝 (5+Complex.I:ℂ)]
      (fun s=>translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) s*
        cuspWhittakerHeightFactor s h) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    rw [translatedCuspFamily_initial h oppositeSource 2 3 (by norm_num) (by norm_num)
      (by norm_num) s hs.1 hs.2,opposite_cusp_fourier_average s (by linarith),
      translatedCuspFamily_opposite_initial (9*h) s hs.1 hs.2]
    ring
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected hstart hev

theorem translatedCuspFourier_unramified_residue (h:Eis) :
    translatedCuspFourier h oppositeSource cubicEisensteinResidue=
      unramifiedGaussResidue (9*h)*cuspWhittakerHeightFactor (4/3:ℂ) h := by
  have hh (k:Eis) : Tendsto (fun s:ℂ=>cuspWhittakerHeightFactor s k)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (cuspWhittakerHeightFactor (4/3:ℂ) k)) :=
    (cuspWhittakerHeightFactor_analyticAt k (4/3) (by norm_num)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hl := ((translatedCuspFamily_residue_limit h oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh (3*(9*h)))).comp upperVertical_tendsto_cubic_punctured
  have hr := ((translatedCuspFamily_residue_limit (3*(9*h)) oppositeSource 2 3
    (by norm_num) (by norm_num)).mul (hh h)).comp upperVertical_tendsto_cubic_punctured
  have hev : (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily h oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) (3*(9*h)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun t:ℝ=>((((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*
      translatedCuspFamily (3*(9*h)) oppositeSource 2 3 (by norm_num) (by norm_num) ((4/3:ℂ)+(t:ℂ)*Complex.I))*
        cuspWhittakerHeightFactor ((4/3:ℂ)+(t:ℂ)*Complex.I) h) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<t at ht
    have he:=oppositeFrequency_cross_identity h (show (4/3:ℂ)+(t:ℂ)*Complex.I∈{s:ℂ|1<s.re ∧ 0<s.im} by
      constructor
      · norm_num
      simp_all)
    linear_combination (((4/3:ℂ)+(t:ℂ)*Complex.I)-4/3)*he
  have heq : translatedCuspFourier h oppositeSource cubicEisensteinResidue*
      cuspWhittakerHeightFactor (4/3:ℂ) (3*(9*h))=
      translatedCuspFourier (3*(9*h)) oppositeSource cubicEisensteinResidue*
        cuspWhittakerHeightFactor (4/3:ℂ) h := tendsto_nhds_unique_of_eventuallyEq hl hr hev
  unfold unramifiedGaussResidue
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff (cuspWhittakerHeightFactor_center_ne_zero (3*(9*h)))).mpr heq

def principalArithmeticResidue (h:Eis) : ℂ :=
  if h=0 then constantArithmeticResidue else nonzeroScatteringResidue h

lemma kernelCuspFourier_principal_residue (h:Eis) :
    kernelCuspFourier h cubicEisensteinResidue=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*principalArithmeticResidue h*
        cuspWhittakerHeightFactor (4/3:ℂ) h := by
  by_cases hh:h=0
  · subst h
    rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average,principalArithmeticResidue,ite_eq_left rfl,
      cuspWhittakerHeightFactor_zero (4/3) (by norm_num),cuspConstantAverageResidue]
    ring
  · rw [principalArithmeticResidue,ite_eq_right hh,nonzeroScatteringResidue]
    field_simp [cuspWhittakerHeightFactor_center_ne_zero h]

def sourceArithmeticResidue (h:Eis) : ℂ :=
  if ShortDraftTrace.breveE (cuspFrequency h)=1 then
    (4:ℂ)⁻¹*(principalArithmeticResidue h+
      3*unramifiedGaussResidue (9*h)/((9*Real.sqrt 3/2:ℝ):ℂ))
  else 0

lemma unramifiedGaussResidue_zero :
    unramifiedGaussResidue 0=((9*Real.sqrt 3/2:ℝ):ℂ)*constantArithmeticResidue := by
  apply mul_right_cancel₀ (cuspWhittakerHeightFactor_center_ne_zero (0:Eis))
  have ht:=translatedCuspFourier_unramified_residue (0:Eis)
  simp only [mul_zero] at ht
  rw [←ht,translatedCuspFourier_opposite_zero_residue]
  have hp:=kernelCuspFourier_principal_residue (0:Eis)
  rw [kernelCuspFourier_zero,cubicEisensteinResidue_cusp_average] at hp
  simpa [principalArithmeticResidue] using hp

lemma sourceArithmeticResidue_zero : sourceArithmeticResidue 0=constantArithmeticResidue := by
  rw [sourceArithmeticResidue]
  simp only [cuspFrequency,map_zero,zero_div,AddChar.map_zero_eq_one,
    principalArithmeticResidue,mul_zero,unramifiedGaussResidue_zero,ite_true]
  field_simp
  ; ring

end

section
open Filter MeasureTheory
open scoped Classical Topology

def horizontalPhaseMultiplier (freq direction : ℂ) : ℂ :=
  (2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))

lemma brevePhase_hasDerivAt (freq z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => ShortDraftTrace.breveE (freq*(z+(x:ℂ)*direction)))
      (horizontalPhaseMultiplier freq direction*
        ShortDraftTrace.breveE (freq*(z+(t:ℂ)*direction))) t := by
  have hz : HasDerivAt (fun x : ℝ => freq*(z+(x:ℂ)*direction)) (freq*direction) t := by
    convert (((Complex.ofRealCLM.hasDerivAt (x:=t)).mul_const direction).const_add z).const_mul freq using 1 <;>
      simp
  have he := ((hz.add hz.star).const_mul (2*Real.pi*Complex.I)).cexp
  change HasDerivAt (fun x : ℝ => Complex.exp ((2*Real.pi*Complex.I)*
    (freq*(z+(x:ℂ)*direction)+star (freq*(z+(x:ℂ)*direction)))))
    ((2*Real.pi*Complex.I)*(freq*direction+star (freq*direction))*
      Complex.exp ((2*Real.pi*Complex.I)*
        (freq*(z+(t:ℂ)*direction)+star (freq*(z+(t:ℂ)*direction))))) t
  simpa only [Pi.add_apply,mul_comm] using he

lemma horizontalPhaseMultiplier_norm (freq direction : ℂ) :
    ‖horizontalPhaseMultiplier freq direction‖≤4*Real.pi*‖freq‖*‖direction‖ := by
  have hc : ‖(2*Real.pi*Complex.I:ℂ)‖=2*Real.pi := by
    norm_num
  unfold horizontalPhaseMultiplier
  rw [norm_mul,hc]
  calc
    _ ≤ (2*Real.pi)*(‖freq*direction‖+‖star (freq*direction)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by rw [norm_star,norm_mul];ring

lemma norm_mul_exp_neg_bound (a r : ℝ) (ha : 0<a) :
    r*Real.exp (-a*r)≤(2/a)*Real.exp (-(a/2)*r) := by
  have hbase := Real.add_one_le_exp ((a/2)*r)
  have hr : r≤(2/a)*Real.exp ((a/2)*r) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).mpr
    nlinarith
  calc
    _ ≤ ((2/a)*Real.exp ((a/2)*r))*Real.exp (-a*r) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by rw [mul_assoc,←Real.exp_add];ring

lemma summable_norm_mul_exp_neg_cuspFrequency (a : ℝ) (ha : 0<a) :
    Summable (fun h : ActualEisensteinCubic.O => ‖cuspFrequency h‖*Real.exp (-a*‖cuspFrequency h‖)) := by
  apply Summable.of_nonneg_of_le (fun h => by positivity)
    (fun h => norm_mul_exp_neg_bound a _ ha)
  exact (summable_exp_neg_cuspFrequency_norm (a/2) (half_pos ha)).mul_left (2/a)

local notation "O" => ActualEisensteinCubic.O

end

open Filter MeasureTheory
open scoped Classical Topology

local notation "O" => ActualEisensteinCubic.O

def horizontalWirtingerBar (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ => f (z+(t:ℂ))) 0+
    Complex.I*deriv (fun t : ℝ => f (z+(t:ℂ)*Complex.I)) 0)

end CubicEisenstein

end

end OAI
