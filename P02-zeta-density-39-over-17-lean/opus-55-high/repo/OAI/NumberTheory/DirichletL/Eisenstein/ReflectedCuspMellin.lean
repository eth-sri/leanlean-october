module
public import OAI.NumberTheory.DirichletL.Eisenstein.SourceBesselExpansion
public import OAI.NumberTheory.DirichletL.Eisenstein.InverseCuspCoordinates
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
open Filter MeasureTheory Asymptotics
open scoped Classical Topology

def reflectedCuspProfile (A : ℂ) (Q : ℝ) (g : ℝ→ℂ) (v : ℝ) : ℂ :=
  A*((v:ℂ)^(-2:ℂ)*g ((Q*v)⁻¹))

section
variable (g : ℝ→ℂ) (A s : ℂ) (Q : ℝ) (hQ : 0<Q)
include g A s Q hQ
lemma reflectedCuspProfile_mellin :
    mellin (reflectedCuspProfile A Q g) s =
      A*(Q:ℂ)^(2-s)*mellin g (2-s) := by
  unfold reflectedCuspProfile
  have hh := cusp_mellin_reflection g A (s/2) Q hQ
  grind

lemma reflectedCuspProfile_mellinConvergent (hg : MellinConvergent g (2-s)) :
    MellinConvergent (reflectedCuspProfile A Q g) s := by
  unfold reflectedCuspProfile
  have hinv : MellinConvergent (fun t : ℝ=>g t⁻¹) (s-2) := by
    have hh := (MellinConvergent.comp_rpow (f := g) (s := s-2)
      (a := -1) (by norm_num : (-1:ℝ)≠0)).mpr
        (show MellinConvergent g ((s-2)/(-1:ℝ)) by
          simpa only [show ((s-2)/(-1:ℝ):ℂ)=2-s by push_cast;ring] using hg)
    simpa only [Real.rpow_neg_one] using hh
  have hscale := (MellinConvergent.comp_mul_left (f := fun t : ℝ=>g t⁻¹)
    (s := s-2) hQ).mpr hinv
  have hpow := (MellinConvergent.cpow_smul (f := fun t : ℝ=>g (Q*t)⁻¹)
    (s := s) (a := -2)).mpr (by aesop)
  simpa only [reflectedCuspProfile,smul_eq_mul] using hpow.const_smul A
end

section
variable (f g : ℝ→ℂ) (A : ℂ)
include f g A
lemma cusp_truncation_reflection_ae (Q : ℝ) (hQ : 0<Q)
    (hfg : ∀v : ℝ,0<v→ f v=reflectedCuspProfile A Q g v) :
    f =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun v=>truncatedCuspProfile 1 f v+
        reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) := by
  have hne : ∀ᵐv : ℝ ∂ volume.restrict (Set.Ioi 0),v≠1 :=
    ae_restrict_of_ae (Measure.ae_ne volume 1)
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with v hv hv1
  have hrel : 1/Q<(Q*v)⁻¹ ↔ v<1 := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hQ (mul_pos hQ hv)]
    simp_all
  by_cases hhi : 1<v
  · have hlo : ¬1/Q<(Q*v)⁻¹ := fun hh=>not_lt_of_ge hhi.le (hrel.mp hh)
    simp only [truncatedCuspProfile,ite_eq_left hhi,reflectedCuspProfile,ite_eq_right hlo,
      mul_zero,add_zero]
  · have hlo : 1/Q<(Q*v)⁻¹ := hrel.mpr (lt_of_le_of_ne (le_of_not_gt hhi) hv1)
    simp only [truncatedCuspProfile,ite_eq_right hhi,reflectedCuspProfile,ite_eq_left hlo,zero_add]
    exact hfg v hv

theorem cusp_mellin_entire (Q decayF decayG : ℝ)
    (hQ : 0<Q) (hdecayF : 0<decayF) (hdecayG : 0<decayG)
    (hf : ContinuousOn f (Set.Ioi 0)) (hg : ContinuousOn g (Set.Ioi 0))
    (hfbound : f =O[atTop] (fun v : ℝ=>Real.exp (-decayF*v)))
    (hgbound : g =O[atTop] (fun v : ℝ=>Real.exp (-decayG*v)))
    (hfg : ∀v : ℝ,0<v→ f v=reflectedCuspProfile A Q g v) :
    (∀s : ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f) := by
  obtain ⟨hfc,hfd⟩ := truncatedCuspProfile_mellin_entire 1 decayF (by norm_num) hdecayF f hf hfbound
  obtain ⟨hgc,hgd⟩ := truncatedCuspProfile_mellin_entire (1/Q) decayG
    (by positivity) hdecayG g hg hgbound
  have hae := cusp_truncation_reflection_ae f g A Q hQ hfg
  have hresult (s : ℂ) : HasMellin f s
      (mellin (truncatedCuspProfile 1 f) s +
        A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) := by
    have hr := reflectedCuspProfile_mellinConvergent
      (truncatedCuspProfile (1/Q) g) A s Q hQ (hgc (2-s))
    have hsum := hasMellin_add (hfc s) hr
    constructor
    · apply hsum.1.congr
      filter_upwards [hae] with v hv
      exact congrArg (fun z : ℂ=>(v:ℂ)^(s-1) • z) hv.symm
    · have he : mellin f s=mellin (fun v=>truncatedCuspProfile 1 f v+
          reflectedCuspProfile A Q (truncatedCuspProfile (1/Q) g) v) s := by
        unfold mellin
        apply integral_congr_ae
        filter_upwards [hae] with v hv
        rw [hv]
      rw [he,hsum.2,reflectedCuspProfile_mellin _ _ _ _ hQ]
  refine ⟨fun s=>(hresult s).1,?_⟩
  have he : mellin f=(fun s : ℂ=>mellin (truncatedCuspProfile 1 f) s +
      A*(Q:ℂ)^(2-s)*mellin (truncatedCuspProfile (1/Q) g) (2-s)) :=
    funext (fun s=>(hresult s).2)
  rw [he]
  let : NeZero (Q:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hQ.ne'⟩
  have hp := (differentiable_const_cpow_of_neZero (Q:ℂ)).comp
    ((differentiable_const (2:ℂ)).sub differentiable_id)
  exact hfd.add (((differentiable_const A).mul hp).mul
    (hgd.comp ((differentiable_const (2:ℂ)).sub differentiable_id)))
end

end

section
open Filter MeasureTheory
open scoped Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalTerm (h : ActualEisensteinCubic.O) (v : ℝ) (z direction : ℂ) : ℂ :=
  horizontalPhaseMultiplier (cuspFrequency h) direction*coeff.term h (v,z)

lemma term_horizontal_hasDerivAt (h : ActualEisensteinCubic.O) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))
      (coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (brevePhase_hasDerivAt (cuspFrequency h) z direction t).const_mul
    (coeff.amplitude v h)
  have hf : (fun x : ℝ => coeff.term h (v,z+(x:ℂ)*direction))=
      (fun x : ℝ => coeff.amplitude v h*
        ShortDraftTrace.breveE (cuspFrequency h*(z+(x:ℂ)*direction))) := by
    funext x
    exact coeff.term_eq_amplitude v hv h _
  rw [hf]
  convert hh using 1
  rw [directionalTerm,coeff.term_eq_amplitude v hv h]
  ring

lemma directionalTerm_slab_bound (a b : ℝ) (ha : 0<a) (hab : a≤b)
    (direction : ℂ) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),v∈Set.Icc a b →
      ‖coeff.directionalTerm h v z direction‖≤
        C*(‖cuspFrequency h‖*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) := by
  pm_97 C hC hbound coeff.slab_bound a b ha hab
  pm_6196 hv
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*Real.exp (-(Real.pi*a)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h (v,z) hv)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

section
variable (v : ℝ) (hv : 0<v) (z direction : ℂ)
include v hv z direction
lemma directionalTerm_summable :
    Summable (fun h : ActualEisensteinCubic.O => coeff.directionalTerm h v z direction) := by
  pm_6915
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun h => norm_nonneg _) (fun h => hbound h v z ⟨le_rfl,le_rfl⟩)
  exact (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C

lemma series_horizontal_hasDerivAt (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.series (v,z+(x:ℂ)*direction))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  pm_6915
  have hs := (summable_norm_mul_exp_neg_cuspFrequency (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C
  have hz : Summable (fun h : ActualEisensteinCubic.O => coeff.term h (v,z+(0:ℂ)*direction)) := by
    simpa only [zero_mul,add_zero] using coeff.summable (v,z) hv
  exact hasDerivAt_tsum hs (fun h x => coeff.term_horizontal_hasDerivAt h v hv z direction x)
    (fun h x => hbound h v (z+(x:ℂ)*direction) ⟨le_rfl,le_rfl⟩) hz t
end

lemma fullFunction_horizontal_hasDerivAt (constant : ℂ) (v : ℝ) (hv : 0<v)
    (z direction : ℂ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => coeff.fullFunction constant (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v (z+(t:ℂ)*direction) direction) t := by
  have hh := (coeff.series_horizontal_hasDerivAt v hv z direction t).const_add
    (constant*(v:ℂ)^(2/3:ℂ))
  simpa only [fullFunction,function,
    hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint] using hh

end SubexponentialBesselCoefficients
end

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma term_cusp_bound (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.term h (v,z)‖≤C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) := by
  pm_3556
  have hCu := cubicBesselUpperAway_pos delta hdelta
  pm_3557
  refine ⟨C*cubicBesselUpperAway delta,mul_nonneg hC (cubicBesselUpperAway_pos delta hdelta).le,?_⟩
  intro h v z hav
  have hv : 0<v := ha.trans_le hav
  pm_3558
  pm_3674
  have hx : delta≤4*Real.pi*‖cuspFrequency h‖*v := by
    pm_6889 hav
    pm_3692
  rw [coeff.term_bessel h hh v hv z,norm_mul,norm_mul,norm_mul,
    breveE_norm,mul_one,Complex.norm_of_nonneg hv.le]
  calc
    _ ≤ (C*Real.exp ((Real.pi*a)*‖cuspFrequency h‖))*v*
        (cubicBesselUpperAway delta*Real.exp (-(4*Real.pi*‖cuspFrequency h‖*v)/2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hcoeff h hh) hv.le)
        (schlafliBesselK_cubic_upper_away delta _ hdelta hx) (norm_nonneg _) (by positivity)
    _ = (C*cubicBesselUpperAway delta)*v*Real.exp
        ((Real.pi*a)*‖cuspFrequency h‖-(4*Real.pi*‖cuspFrequency h‖*v)/2) := by
      rw [Real.exp_sub,show -(4*Real.pi*‖cuspFrequency h‖*v)/2=
        -(4*Real.pi*‖cuspFrequency h‖*v/2) by ring,Real.exp_neg]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      pm_8578 hav

section
variable (a : ℝ) (ha : 0<a) (direction : ℂ)
include a ha direction
lemma directionalTerm_cusp_majorant :
    ∃D : ℝ,0≤D ∧ ∀(h : ActualEisensteinCubic.O)(v : ℝ)(z : ℂ),a≤v →
      ‖coeff.directionalTerm h v z direction‖≤
        (D *v*Real.exp (-(2*residualCuspDecayRate)*v))*
          (‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)) := by
  pm_69 C hC hbound coeff.term_cusp_bound a ha
  pm_6196 hav
  have hv : 0<v := ha.trans_le hav
  by_cases hh : h=0
  · subst h
    pm_94 directionalTerm term ite_true mul_zero norm_zero
    positivity
  pm_3674
  pm_3566
  rw [directionalTerm,norm_mul]
  calc
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) :=
      mul_le_mul (horizontalPhaseMultiplier_norm _ _) (hbound h v z hav)
        (norm_nonneg _) (by positivity)
    _ ≤ (4*Real.pi*‖cuspFrequency h‖*‖direction‖)*
        (C*v*(Real.exp (-(2*residualCuspDecayRate)*v)*
          Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖))) := by
      gcongr
    _ = _ := by ring

lemma directionalSeries_cusp_decay :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(z : ℂ),a≤v →
      ‖∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h v z direction‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  pm_114 D hD hbound coeff.directionalTerm_cusp_majorant a ha direction
  have hc := residualCuspDecayRate_pos
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,‖cuspFrequency h‖*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
  have hs := summable_norm_mul_exp_neg_cuspFrequency (Real.pi*a/2) (by positivity)
  refine ⟨D *S*(2/(2*residualCuspDecayRate)),by positivity,?_⟩
  intro v z hav
  have hsum := tsum_of_norm_bounded
    (hs.hasSum.mul_left (D *v*Real.exp (-(2*residualCuspDecayRate)*v)))
    (fun h => hbound h v z hav)
  calc
    _ ≤ (D *v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D *S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D *S)*((2/(2*residualCuspDecayRate))*
        Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      pm_1295
end

theorem fullFunction_wirtingerBar_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by pm_3567 horizontalWirtingerBar norm_add_le

end SubexponentialBesselCoefficients
end

section
open Filter MeasureTheory
open scoped Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

lemma spatialComplexSplit_differentiable : Differentiable ℝ spatialComplexSplit := by
  change Differentiable ℝ (fun p : EuclideanSpatial => (p 2,(p 0:ℂ)+(p 1:ℂ)*Complex.I))
  fun_prop

lemma spatialComplexSplit_symm_differentiable : Differentiable ℝ spatialComplexSplit.symm := by
  change Differentiable ℝ (fun q : ℝ × ℂ => spatialComplexSplit.symm q)
  simp_rw [spatialComplexSplit_symm_eq]
  have hlin := (WithLp.linearEquiv 2 ℝ (Fin 3→ℝ)).symm.toContinuousLinearMap.differentiable
  have hcoords : Differentiable ℝ (fun q : ℝ × ℂ => ![q.2.re,q.2.im,q.1]) := by
    apply differentiable_pi.mpr
    intro j
    fin_cases j
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.re)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.2.im)
      fun_prop
    · change Differentiable ℝ (fun q : ℝ × ℂ => q.1)
      fun_prop
  exact hlin.comp hcoords

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

section
variable (constant : ℂ)
include constant
lemma fullFunction_euclidean_differentiableAt (p : EuclideanSpatial) (hp : 0<p 2) :
    DifferentiableAt ℝ (fun q : EuclideanSpatial => coeff.fullFunction constant (euclideanToHyperbolic q)) p := by
  have hh := (coeff.fullFunction_cusp_differentiableAt constant (spatialComplexSplit p) hp).comp p
    spatialComplexSplit_differentiable.differentiableAt
  simpa only [Function.comp_def,cuspCoordinateLift,spatialComplexSplit.symm_apply_apply] using hh

lemma fullFunction_translate_cusp_differentiableAt (g : SL(2,ℂ))
    (p : ℝ × ℂ) (hp : 0<p.1) :
    DifferentiableAt ℝ (fun q : ℝ × ℂ => coeff.fullFunction constant (g • cuspCoordinateLift q)) p := by
  have hx : 0<(spatialComplexSplit.symm p) 2 := by
    rw [spatialComplexSplit_symm_eq]
    exact hp
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g (spatialComplexSplit.symm p) hx
  have hh := ((coeff.fullFunction_euclidean_differentiableAt constant
    (euclideanAction g (spatialComplexSplit.symm p)) (euclideanAction_positive _ _)).comp _
      hA.differentiableAt).comp p spatialComplexSplit_symm_differentiable.differentiableAt
  pm_89 Function.comp_def euclideanAction euclideanToHyperbolic_coordinates cuspCoordinateLift hh

lemma fullFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => coeff.fullFunction constant (g • cuspCoordinateLift (q.2,q.1))) p := by
  have hswap : DifferentiableAt ℝ (fun q : ℂ × ℝ => (q.2,q.1)) p :=
    differentiableAt_snd.prodMk differentiableAt_fst
  pm_8002 coeff.fullFunction_translate_cusp_differentiableAt
end

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceResidualFunction (g • cuspCoordinateLift (q.2,q.1))) p := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_translate_split_differentiableAt
    ((3*(Real.pi:ℂ))*constantArithmeticResidue) g p hp

lemma cubicSourceResidualFunction_wirtingerBar_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerBar_cusp_decay _ a ha

end

local notation "O" => ActualEisensteinCubic.O

lemma horizontalPhaseMultiplier_wirtingerZ (freq : ℂ) :
    (1/2:ℂ)*(horizontalPhaseMultiplier freq 1-
      Complex.I*horizontalPhaseMultiplier freq Complex.I)=2*Real.pi*Complex.I*freq := by
  pm_1443 horizontalPhaseMultiplier mul_one star_mul Complex.star_def Complex.conj_I
  ring_nf
  norm_num [Complex.I_sq,Complex.I_pow_three]
  ring

lemma horizontalWirtingerBar_star (f : ℂ→ℂ) (z : ℂ) :
    horizontalWirtingerBar (fun w => star (f w)) z=star (horizontalWirtingerZ f z) := by
  unfold horizontalWirtingerBar horizontalWirtingerZ
  rw [deriv.star,deriv.star]
  simp []

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

lemma fullFunction_wirtingerZ (constant : ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) :
    horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z=
      ∑'h : ActualEisensteinCubic.O,(2*Real.pi*Complex.I*cuspFrequency h)*coeff.term h (v,z) := by
  pm_3568
  rw [horizontalWirtingerZ,h1,hI]
  have hs1 := coeff.directionalTerm_summable v hv z 1
  have hsI := (coeff.directionalTerm_summable v hv z Complex.I).mul_left Complex.I
  pm_7130 hs1.tsum_sub
  linear_combination coeff.term h (v,z)*horizontalPhaseMultiplier_wirtingerZ (cuspFrequency h)

lemma fullFunction_wirtingerZ_cusp_decay (constant : ℂ) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => coeff.fullFunction constant (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by pm_3567 horizontalWirtingerZ norm_sub_le

end SubexponentialBesselCoefficients

lemma cubicSourceResidualFunction_wirtingerZ_cusp_decay (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀(v : ℝ)(hv : 0<v)(z : ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => cubicSourceResidualFunction (upperPoint w v hv)) z‖≤
        C*Real.exp (-residualCuspDecayRate*v) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_wirtingerZ_cusp_decay _ a ha

def cubicSourceConjugateFunction (w : HyperbolicSpace) : ℂ := star (cubicSourceResidualFunction w)

lemma cubicSourceConjugateFunction_translate_split_differentiableAt (g : SL(2,ℂ))
    (p : ℂ × ℝ) (hp : 0<p.2) :
    DifferentiableAt ℝ
      (fun q : ℂ × ℝ => cubicSourceConjugateFunction (g • cuspCoordinateLift (q.2,q.1))) p :=
  (cubicSourceResidualFunction_translate_split_differentiableAt g p hp).star

end

open Filter MeasureTheory
open scoped Classical Topology MatrixGroups
open Finset AddChar MulChar EisensteinEmbedding

lemma horizontalWirtingerBar_translate (f : ℂ→ℂ) (a : ℂ) :
    horizontalWirtingerBar (fun z=>f (z+a)) 0=horizontalWirtingerBar f a := by
  unfold horizontalWirtingerBar
  simp only [zero_add]
  have h1 : (fun t : ℝ=>f ((t:ℂ)+a))=(fun t : ℝ=>f (a+(t:ℂ))) := by
    funext t
    rw [add_comm]
  have hI : (fun t : ℝ=>f ((t:ℂ)*Complex.I+a))=(fun t : ℝ=>f (a+(t:ℂ)*Complex.I)) := by
    funext t
    rw [add_comm]
  rw [h1,hI]

lemma cuspDerivative_of_transform (f : HyperbolicSpace→ℂ) (g H : SL(2,ℂ))
    (κ : ℂ) (htransform : ∀w,f (g•w)=κ*f (H•w)) (hc : g 1 0≠0)
    (v : ℝ) (hv : 0<v)
    (hD : DifferentiableAt ℝ
      (fun q : ℂ × ℝ=>f (H•cuspCoordinateLift (q.2,q.1)))
      (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))) :
    horizontalWirtingerBar (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)=
      (κ*(-1/((g 1 0)^2*(v:ℂ)^2)))*
        horizontalWirtingerZ
          (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity)))
          (-g 1 1/g 1 0) := by
  let FH : ℂ × ℝ→ℂ := fun q=>f (H•cuspCoordinateLift (q.2,q.1))
  let base : ℂ × ℝ := (-g 1 1/g 1 0,1/(‖g 1 0‖^2*v))
  let D := fderiv ℝ FH base
  have hF : HasFDerivAt FH D base := hD.hasFDerivAt
  have hscaled : HasFDerivAt (fun q=>κ*FH q) (κ • D) base := hF.const_mul κ
  have he := inverse_cusp_wirtingerBar (g 1 0) (g 1 1) v hc hv
    (fun q=>κ*FH q) (κ • D) hscaled
  have hline : (fun z=>κ*FH (inverseCuspCoordinates (g 1 0) (g 1 1) v z))=
      (fun z=>f (upperPoint (z+g 0 0/g 1 0) v hv)) := by
    funext z
    have ht := htransform (g⁻¹•upperPoint (z+g 0 0/g 1 0) v hv)
    rw [smul_inv_smul,inverse_cusp_action g hc v hv z] at ht
    change κ*f (H•cuspCoordinateLift
      ((inverseCuspCoordinates (g 1 0) (g 1 1) v z).2,
       (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1))=_
    rw [cuspCoordinateLift_positive _ _ (inverseCuspCoordinates_height_pos _ _ _ _ hc hv)]
    exact ht.symm
  rw [hline] at he
  have hshift := horizontalWirtingerBar_translate (fun z=>f (upperPoint z v hv)) (g 0 0/g 1 0)
  rw [hshift] at he
  have hz := horizontalWirtingerZ_eq_fderiv FH D (-g 1 1/g 1 0) (1/(‖g 1 0‖^2*v)) hF
  have hFH : (fun z=>FH (z,1/(‖g 1 0‖^2*v)))=
      (fun z=>f (H•upperPoint z (1/(‖g 1 0‖^2*v)) (by positivity))) := by
    funext z
    exact congrArg (fun w=>f (H•w)) (cuspCoordinateLift_positive _ _ (by positivity))
  rw [hFH] at hz
  rw [hz]
  rw [he]
  simp only [_root_.smul_apply,smul_eq_mul]
  ring

end CubicEisenstein

end

end OAI
