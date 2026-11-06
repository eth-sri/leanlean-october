module
public import OAI.NumberTheory.DirichletL.Eisenstein.ResidualFourierBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

namespace CubicEisenstein

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

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma cuspFrequency_norm_lower (h : ActualEisensteinCubic.O) (hh : h≠0) :
    ‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹≤‖cuspFrequency h‖ := by
  have hn : 1≤‖ConcreteTraceCRT.eisEmbedding h‖^2 := by
    pm_6813 ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span hh
  have hnorm : 1≤‖ConcreteTraceCRT.eisEmbedding h‖ := by simp_all
  rw [cuspFrequency,norm_div,inv_eq_one_div]
  exact div_le_div_of_nonneg_right hnorm (norm_nonneg _)

def cubicBesselUpperAway (deltaLoss : ℝ) : ℝ :=
  (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))

lemma cubicBesselUpperAway_pos (deltaLoss : ℝ) (hδ : 0<deltaLoss) : 0< cubicBesselUpperAway deltaLoss := by
  unfold cubicBesselUpperAway
  positivity

lemma schlafliBesselK_cubic_upper_away (deltaLoss x : ℝ) (hδ : 0<deltaLoss) (hx : deltaLoss≤x) :
    ‖schlafliBesselK (1/3:ℂ) x‖≤ cubicBesselUpperAway deltaLoss*Real.exp (-x/2) := by
  have hxp := hδ.trans_le hx
  rw [schlafliBesselK_cubic_norm_re x hxp,schlafliBesselK_cubic_real x hxp,Complex.ofReal_re]
  pm_3689 hp deltaLoss
  calc
    _ ≤ (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) :=
      mul_le_mul_of_nonneg_left (cubicBesselIntegral_upper x) (by positivity)
    _ ≤ (1/2:ℝ)*(deltaLoss/2)^(-(1:ℝ)/3)*
        (Real.exp (-x/2)*((2:ℝ)^(1/3:ℝ)*Real.Gamma (1/3))) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) (by positivity)
    _ = _ := by unfold cubicBesselUpperAway;ring

def cubicResidualNonzeroTerm (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : ℂ :=
  if h=0 then 0 else nonzeroScatteringResidue h*(p.1:ℂ)^(2/3:ℂ)*
    sourceFourierKernel (4/3) (cuspFrequency h*p.1)*ShortDraftTrace.breveE (cuspFrequency h*p.2)

lemma cubicResidualNonzeroTerm_bessel (h : ActualEisensteinCubic.O) (hh : h≠0) (v : ℝ) (hv : 0<v) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualFourierCoefficient h*(v:ℂ)*
      schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  rw [cubicResidualNonzeroTerm,ite_eq_right hh]
  pm_3548
  pm_3690
  have hker := sourceFourierKernel_cubic_height h hh v hv
  calc
    _ = nonzeroScatteringResidue h*(v:ℂ)^3*
        ((v:ℂ)^(-(4/3:ℂ)-1)*sourceFourierKernel (4/3) (cuspFrequency h*v))*
          ShortDraftTrace.breveE (cuspFrequency h*z) := by rw [←hp];ring
    _ = _ := by
      rw [hker,cubicResidualFourierCoefficient]
      field_simp

lemma cubicResidualNonzeroTerm_continuousOn (h : ActualEisensteinCubic.O) :
    ContinuousOn (cubicResidualNonzeroTerm h) {p : ℝ × ℂ | 0<p.1} := by pm_3691 cubicResidualNonzeroTerm

lemma cubicResidualNonzeroTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(p : ℝ × ℂ),p.1∈Set.Icc a b →
      ‖cubicResidualNonzeroTerm h p‖≤C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖) := by
  have hb : 0<b := ha.trans_le hab
  pm_1294
  let deltaLoss : ℝ := 4*Real.pi*a*‖(3:ℂ)*ConcreteTraceCRT.eisLam‖⁻¹
  pm_3693 hδ deltaLoss
  have hCu : 0< cubicBesselUpperAway deltaLoss := cubicBesselUpperAway_pos deltaLoss hδ
  obtain ⟨C,hC,hcoeff⟩ := cubicResidualFourierCoefficient_subexponential (Real.pi*a) (mul_pos Real.pi_pos ha)
  refine ⟨C*b*cubicBesselUpperAway deltaLoss,mul_nonneg (mul_nonneg hC hb.le) (cubicBesselUpperAway_pos deltaLoss hδ).le,?_⟩
  pm_7523
  pm_982 cubicResidualNonzeroTerm
  pm_3674
  have hx : deltaLoss≤4*Real.pi*‖cuspFrequency h‖*p.1 := by
    have hmul := mul_le_mul (cuspFrequency_norm_lower h hh) hp.1
      ha.le (norm_nonneg (cuspFrequency h))
    dsimp [deltaLoss]
    pm_3692
  pm_1241 cubicResidualNonzeroTerm_bessel
  have hkb := schlafliBesselK_cubic_upper_away deltaLoss (4*Real.pi*‖cuspFrequency h‖*p.1) hδ hx
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*b*
        (cubicBesselUpperAway deltaLoss*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*p.1)/2)) :=
      mul_le_mul (mul_le_mul (hcoeff h hh) hp.2 hv.le (mul_nonneg hC (Real.exp_pos _).le))
        hkb (norm_nonneg _) (by positivity)
    _ = (C*b*cubicBesselUpperAway deltaLoss)*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*p.1)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*p.1)/2 =
        -(4*Real.pi*‖cuspFrequency h‖*p.1/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hp.1 (mul_pos Real.pi_pos hr).le
      nlinarith

def cubicResidualNonzeroSeries (p : ℝ × ℂ) : ℂ := ∑'h : ActualEisensteinCubic.O,cubicResidualNonzeroTerm h p

lemma cubicResidualNonzeroSeries_continuousOn_slab (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | p.1∈Set.Icc a b} := by pm_3694 cubicResidualNonzeroTerm_slab_bound cubicResidualNonzeroTerm_continuousOn

lemma cubicResidualNonzeroSeries_continuousOn :
    ContinuousOn cubicResidualNonzeroSeries {p : ℝ × ℂ | 0<p.1} := by pm_3695 cubicResidualNonzeroSeries_continuousOn_slab

def cubicResidualNonzeroFunction (w : HyperbolicSpace) : ℂ :=
  cubicResidualNonzeroSeries (hyperbolicHeight w,hyperbolicHorizontal w)

lemma cubicResidualNonzeroFunction_continuous : Continuous cubicResidualNonzeroFunction := by pm_3696 cubicResidualNonzeroSeries_continuousOn.continuousAt

lemma cubicResidualNonzeroSeries_period (v : ℝ) (z : ℂ) (n : ActualEisensteinCubic.O) :
    cubicResidualNonzeroSeries (v,z+3*ConcreteTraceCRT.eisEmbedding n)=cubicResidualNonzeroSeries (v,z) := by
  pm_975 cubicResidualNonzeroTerm

end

section
open Filter MeasureTheory
open scoped Classical Topology ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def cubicResidualModeAmplitude (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else cubicResidualFourierCoefficient h*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)

lemma cubicResidualNonzeroTerm_eq_amplitude (v : ℝ) (hv : 0<v) (h : ActualEisensteinCubic.O) (z : ℂ) :
    cubicResidualNonzeroTerm h (v,z)=cubicResidualModeAmplitude v h*ShortDraftTrace.breveE (cuspFrequency h*z) := by
  pm_5558 cubicResidualNonzeroTerm cubicResidualModeAmplitude cubicResidualNonzeroTerm_bessel

lemma integral_cusp_character_product (h k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z))=if h=k then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  have hphase (z : ℂ) : ShortDraftTrace.breveE (cuspFrequency h*z)*
      ShortDraftTrace.breveE (-cuspFrequency k*z)=ShortDraftTrace.breveE (-cuspFrequency (k-h)*z) := by
    rw [←AddChar.map_add_eq_mul]
    congr 1
    unfold cuspFrequency
    rw [map_sub]
    ring
  simp_rw [hphase]
  simpa only [sub_eq_zero,eq_comm] using integral_cusp_character (k-h)

lemma cubicResidualNonzeroSeries_fourier (v : ℝ) (hv : 0<v) (k : ActualEisensteinCubic.O) :
    (∫z in periodDomain,cubicResidualNonzeroSeries (v,z)*ShortDraftTrace.breveE (-cuspFrequency k*z))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicResidualModeAmplitude v k := by pm_3697 cubicResidualModeAmplitude cubicResidualNonzeroTerm_slab_bound cubicResidualNonzeroTerm_eq_amplitude cubicResidualNonzeroTerm

end

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

end

section
open Filter MeasureTheory
open scoped Classical Topology

lemma ae_eq_of_boundedContinuous_height_tests («μ» : Measure ℝ) (f g : ℝ→ℂ)
    (hf : Integrable f «μ») (hg : Integrable g «μ»)
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x,ρ x*f x∂«μ»)=(∫x,ρ x*g x∂«μ»)) : f=ᵐ[«μ»]g := by
  apply ae_eq_of_integral_contDiff_smul_eq hf.locallyIntegrable hg.locallyIntegrable
  intro test htest hsupp
  obtain ⟨C,hC⟩ := hsupp.exists_bound_of_continuous htest.continuous
  let ρ : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup (fun x => (test x:ℂ))
      (Complex.continuous_ofReal.comp htest.continuous) C (fun x => by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using hC x)
  have hh := heq ρ
  change (∫x,(test x:ℂ)*f x∂«μ»)=(∫x,(test x:ℂ)*g x∂«μ») at hh
  simpa only [Complex.real_smul] using hh

lemma interval_ae_eq_of_boundedContinuous_height_tests (a b : ℝ) (f g : ℝ→ℂ)
    (hf : IntegrableOn f (Set.Icc a b)) (hg : IntegrableOn g (Set.Icc a b))
    (heq : ∀ρ : BoundedContinuousFunction ℝ ℂ,
      (∫x in Set.Icc a b,ρ x*f x)=(∫x in Set.Icc a b,ρ x*g x)) :
    f=ᵐ[volume.restrict (Set.Icc a b)]g :=
  ae_eq_of_boundedContinuous_height_tests (volume.restrict (Set.Icc a b)) f g hf hg heq

end

open Filter MeasureTheory
open scoped Classical Topology

def compactHeightMellin (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ∫v in Set.Icc a b,ρ v*(v:ℂ)^s

section
variable (a b : ℝ) (ha : 0<a) (ρ : BoundedContinuousFunction ℝ ℂ)
include a b ha ρ
lemma compactHeightMellin_integrable (s : ℂ) :
    IntegrableOn (fun v : ℝ => ρ v*(v:ℂ)^s) (Set.Icc a b) := by
  apply ContinuousOn.integrableOn_Icc
  apply ρ.continuous.continuousOn.mul
  intro v hv
  exact (Complex.continuousAt_ofReal_cpow_const v s
    (Or.inr (ha.trans_le hv.1).ne')).continuousWithinAt

theorem compactHeightMellin_differentiable : Differentiable ℂ (compactHeightMellin a b ρ) := by
  let heightLog : ℝ→ℂ := fun v => (Real.log (max a v):ℂ)
  have hl : Continuous heightLog := Complex.continuous_ofReal.comp
    ((continuous_const.max continuous_id).log (fun v => (ha.trans_le (le_max_left a v)).ne'))
  let F : ℂ→ℝ→ℂ := fun s v => ρ v*Complex.exp (heightLog v*s)
  let F' : ℂ→ℝ→ℂ := fun s v => ρ v*(Complex.exp (heightLog v*s)*heightLog v)
  have hF : ∀s,Continuous (F s) := fun s=> ρ.continuous.mul ((hl.mul_const s).cexp)
  have hF' : Continuous (fun p : ℂ×ℝ => F' p.1 p.2) := by
    exact (ρ.continuous.comp continuous_snd).mul
      ((((hl.comp continuous_snd).mul continuous_fst).cexp).mul (hl.comp continuous_snd))
  have hder : ∀s v,HasDerivAt (fun w => F w v) (F' s v) s := by
    intro s v
    simpa only [F,F',id_eq,mul_one] using
      (((hasDerivAt_id s).const_mul (heightLog v)).cexp).const_mul (ρ v)
  have heq : compactHeightMellin a b ρ=(fun s=> ∫v in Set.Icc a b,F s v) := by
    funext s
    apply setIntegral_congr_fun measurableSet_Icc
    intro v hv
    dsimp only [compactHeightMellin,F,heightLog]
    rw [max_eq_right hv.1,Complex.ofReal_log (ha.trans_le hv.1).le,
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ha.trans_le hv.1).ne')]
  rw [heq]
  intro s
  obtain ⟨C,hC⟩ := ((isCompact_closedBall s (1:ℝ)).prod (isCompact_Icc : IsCompact (Set.Icc a b))).exists_bound_of_continuousOn hF'.continuousOn
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ»:=volume.restrict (Set.Icc a b)) (F:=F) (F':=F')
    (bound:=fun _ => C) (Metric.ball_mem_nhds s (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall (fun w => (hF w).aestronglyMeasurable))
    ((hF s).continuousOn.integrableOn_Icc)
    ((hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv w hw
      exact hC (w,v) ⟨Metric.ball_subset_closedBall hw,hv⟩)
    (integrable_const C)
    (Eventually.of_forall (fun v w _ => hder w v))
  exact hd.2.differentiableAt

lemma compactHeightMellin_analyticAt (s : ℂ) :
    AnalyticAt ℂ (compactHeightMellin a b ρ) s :=
  (compactHeightMellin_differentiable a b ha ρ).analyticAt s
end


local notation "O" => ActualEisensteinCubic.O

def cuspHeightConstantAverage (a b : ℝ) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*(compactHeightMellin a b ρ (s-3)+
    ((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0*compactHeightMellin a b ρ (-s-1))

section
variable (a b : ℝ) (ha : 0<a) (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ)
include a b ha ρ s
lemma hyperbolicEisenstein_cusp_height_fourier_zero (hs : 2< s.re) :
    (∫w in cuspPeriodStrip a b,hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w∂ hyperbolicVolume)=
      cuspHeightConstantAverage a b ρ s := by
  let g : HyperbolicSpace→ℂ := fun w => hyperbolicEisenstein s w*cuspWeightedFourierPhase ρ 0 w
  have hg : Continuous g := (hyperbolicEisenstein_continuous s hs).mul (cuspWeightedFourierPhase_continuous ρ 0)
  pm_3666
  have hexp : ∀v∈Set.Icc a b,
      ((∫z in periodDomain,g (cuspCoordinateLift (v,z)))/(v:ℂ)^3)=
        ((9*Real.sqrt 3/2:ℝ):ℂ)*
          (ρ v*(v:ℂ)^(s-3)+(((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0)*
            (ρ v*(v:ℂ)^(-s-1))) := by
    pm_3667
    have hinner : (∫z in periodDomain,g (cuspCoordinateLift (v,z)))=
        ρ v*(eisensteinFourierCoefficient v hpos s 0*((9*Real.sqrt 3/2:ℝ):ℂ)) := by
      pm_5167
      have hrearr : (∫z in periodDomain,upperEisenstein z v hpos s *
          (ρ v*ShortDraftTrace.breveE (-cuspFrequency 0*z)))=
          ρ v*(∫z in periodDomain,upperEisenstein z v hpos s*ShortDraftTrace.breveE (-cuspFrequency 0*z)) := by
        pm_6727
      pm_6980
    rw [hinner,eisensteinConstantCoefficient_formula v hpos s hs]
    pm_3058 hv0 v hpos.ne'
    pm_3598
    pm_3635 hm
    rw [hp,hm]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hexp,integral_const_mul,
    integral_add (compactHeightMellin_integrable a b ha ρ _)
      ((compactHeightMellin_integrable a b ha ρ _).const_mul _),integral_const_mul]
  rfl

lemma kernelCuspHeightFourierFamily_zero_initial (hs : 4< s.re) (hi : 0< s.im) :
    kernelCuspHeightFourierFamily a b ha ρ 0 s=cuspHeightConstantAverage a b ρ s := by
  rw [kernelCuspHeightFourierFamily_initial a b ha ρ 0 s hs hi,
    hyperbolicEisenstein_cusp_height_fourier_zero a b ha ρ s (by linarith)]
end

def weightedOutgoingConstant (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) : ℂ :=
  kernelCuspHeightFourierFamily a b ha ρ 0 s -
    ((9*Real.sqrt 3/2:ℝ):ℂ)*compactHeightMellin a b ρ (s-3)

def baseOutgoingConstant (s : ℂ) : ℂ :=
  kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s -
    ((9*Real.sqrt 3/2:ℝ):ℂ)*cuspMainHeightFactor s

lemma weightedOutgoingConstant_analyticAt (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) (s : ℂ) (hs : 1< s.re) (hi : 0< s.im) :
    AnalyticAt ℂ (weightedOutgoingConstant a b ha ρ) s := by
  exact (kernelCuspHeightFourierFamily_analyticAt_nonreal a b ha ρ 0 s hs.ne' hi.ne').sub
    (analyticAt_const.mul ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl))

section
variable (s : ℂ) (hs : 1< s.re)
include s hs
lemma baseOutgoingConstant_analyticAt (hi : 0< s.im) :
    AnalyticAt ℂ baseOutgoingConstant s := by
  pm_8502 hne hi
  have hmain : AnalyticAt ℂ cuspMainHeightFactor s := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [eventually_ne_nhds hne] with z hz
    exact cuspMainHeightFactor_differentiableAt z hz
  exact (kernelCuspAverageFamily_analyticAt_nonreal 2 3 (by norm_num) (by norm_num)
    s hs.ne' hi.ne').sub (analyticAt_const.mul hmain)

lemma cuspScatterHeightFactor_analyticAt :
    AnalyticAt ℂ cuspScatterHeightFactor s := by
  pm_1231 hne
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds hne] with z hz
  exact cuspScatterHeightFactor_differentiableAt z hz
end

lemma weightedOutgoingConstant_cross_identity (a b : ℝ) (ha : 0<a)
    (ρ : BoundedContinuousFunction ℝ ℂ) :
    Set.EqOn (fun s=> weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      (fun s=> baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1))
      {s : ℂ | 1< s.re ∧ 0< s.im} := by
  pm_3668
  have hleft : AnalyticOnNhd ℂ
      (fun s=> weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s) domain := by
    intro s hs
    exact (weightedOutgoingConstant_analyticAt a b ha ρ s hs.1 hs.2).mul
      (cuspScatterHeightFactor_analyticAt s hs.1)
  have hright : AnalyticOnNhd ℂ
      (fun s=> baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) domain := by
    intro s hs
    exact (baseOutgoingConstant_analyticAt s hs.1 hs.2).mul
      ((compactHeightMellin_analyticAt a b ha ρ _).comp_of_eq
        (analyticAt_id.neg.sub analyticAt_const) rfl)
  pm_3577
  have hopen : IsOpen {s : ℂ | 4< s.re ∧ 0< s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hevent : (fun s=> weightedOutgoingConstant a b ha ρ s*cuspScatterHeightFactor s)
      =ᶠ[𝓝 (5+Complex.I:ℂ)]
        (fun s=> baseOutgoingConstant s*compactHeightMellin a b ρ (-s-1)) := by
    filter_upwards [hopen.mem_nhds (by norm_num)] with s hs
    have hb : kernelCuspAverageFamily 2 3 (by norm_num) (by norm_num) s=cuspConstantAverage s := by
      apply (kernelCuspAverageFamily_eq_of_initial_overlap 2 3 (by norm_num) (by norm_num)
        s (by linarith [hs.1])
        (kernelEisensteinL2Correction_initial_overlap 2 3 (by norm_num) (by norm_num) s hs.1 hs.2)).trans
      exact hyperbolicEisenstein_cusp_average_eq s (by linarith [hs.1])
    rw [weightedOutgoingConstant,baseOutgoingConstant,
      kernelCuspHeightFourierFamily_zero_initial a b ha ρ s hs.1 hs.2,hb,
      cuspHeightConstantAverage,cuspConstantAverage]
    ring
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconvex.isPreconnected hstart hevent

end CubicEisenstein

end

end OAI
