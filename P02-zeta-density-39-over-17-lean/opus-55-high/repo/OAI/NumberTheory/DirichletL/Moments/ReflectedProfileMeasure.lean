module
public import OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
public import OAI.NumberTheory.DirichletL.Moments.HeckeWindowEnergy
public import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedProfileMeasure
open HeckeFamily FourierBridge EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

theorem row_density_energy {ι : Type*} [Fintype ι]
    (density φ : ι→ℝ→ℂ) (rho : ℝ→ℝ) (w : ℝ→ℝ)
    (hrho : ∀v,0< rho v) (hw : ∀v,0<w v)
    (hpoint : ∀i v,‖density i v‖≤ rho v)
    (hint : ∀i,Integrable (fun v=>density i v*φ i v))
    (hmeasure : Integrable (fun v=>rho v*w v))
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀v,(∑i,‖φ i v‖^2)≤E*(w v)^2) :
    (∑i,‖∫v : ℝ,density i v*φ i v‖^2)≤E*(∫v : ℝ,rho v*w v)^2 := by
  let B (v : ℝ) : ℂ := (rho v*w v:ℝ)
  let F (i : ι) (v : ℝ) : ℂ := density i v/B v*φ i v
  have hB0 (v : ℝ) : B v≠0 := Complex.ofReal_ne_zero.mpr (mul_pos (hrho v) (hw v)).ne'
  have hBn (v : ℝ) : ‖B v‖=rho v*w v := by
    exact Complex.norm_of_nonneg (mul_pos (hrho v) (hw v)).le
  have he (i : ι) (v : ℝ) : B v*F i v=density i v*φ i v := by
    dsimp only [F]
    grind
  have hFn (i : ι) (v : ℝ) : ‖F i v‖≤‖φ i v‖/w v := by
    dsimp only [F]
    rw [norm_mul,norm_div,hBn]
    calc
      _≤(rho v/(rho v*w v))*‖φ i v‖ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (hpoint i v) (mul_pos (hrho v) (hw v)).le) (norm_nonneg _)
      _=_ := by grind
  have hb (v : ℝ) : (∑i,‖F i v‖^2)≤E := by
    calc
      _≤∑i,(‖φ i v‖/w v)^2 := Finset.sum_le_sum (fun i _=>
        pow_le_pow_left₀ (norm_nonneg _) (hFn i v) 2)
      _=(∑i,‖φ i v‖^2)/(w v)^2 := by simp only [div_pow,Finset.sum_div]
      _≤E := (div_le_iff₀ (sq_pos_of_pos (hw v))).mpr (henergy v)
  have hh := CompletedGauss.finite_integral_energy_bound B F E hE
    (by simpa only [hBn] using hmeasure) (fun i=>by simpa only [he] using hint i) hb
  simp_all

def logWindow (V : ℝ→ℂ) (x : ℝ) : ℂ := if 0<x then V (Real.log x) else 0

theorem finite_annular_separation (V F : ℝ→ℂ) (s X : ℝ) (hX : 0<X)
    (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v)
    (η : Character) (S : Finset (Ideal O))
    (hS : ∀I∈S,I≠0)
    (hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  have hnorm (I : Ideal O) (hI : I∈S) : 0<(I.absNorm:ℝ)/X := by
    apply div_pos _ hX
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
  have hi (I : Ideal O) : Integrable (fun v : ℝ=>
      density v*(HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    have ht := ((density.integrable (μ:=volume)).mul_bdd
      (logPhase_continuous_left (Real.log ((I.absNorm:ℝ)/X))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun v=>le_of_eq (logPhase_norm v _)))).mul_const
        (HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X))
    apply ht.congr
    filter_upwards [] with v
    ring
  pm_2893 hp hS
  rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 0 S
    (fun I hI h=>hc I hI (mul_ne_zero_iff.mp h).1)]
  pm_3780 HeckeDyadic.shift Complex.ofReal_zero zero_mul sub_self neg_zero Complex.cpow_zero mul_one
  simp_rw [hp]
  have he : (fun v : ℝ=>density v*((X:ℂ)^(-(1/2:ℂ))*
      ∑I∈S,HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)*
        logPhase v (Real.log ((I.absNorm:ℝ)/X)))) =
      (fun v=>(X:ℂ)^(-(1/2:ℂ))*∑I∈S,density v*(HeckeDyadic.coefficient η false I *
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)))) := by
    funext v
    rw [←Finset.mul_sum]
    ring
  rw [he,integral_const_mul,integral_finsetSum S (fun I _=>hi I)]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  have hh := hsep (Real.log ((I.absNorm:ℝ)/X))
  rw [Real.exp_log (hnorm I hI)] at hh
  simp only [logWindow,ite_eq_left (hnorm I hI)]
  rw [hh,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

lemma logWindow_support (V : ℝ→ℂ) (M : ℝ)
    (hV : ∀y,V y≠0 → |y|≤M) :
    Function.support (logWindow V)⊆Set.Icc (Real.exp (-M)) (Real.exp M) := by
  intro x hx
  change logWindow V x≠0 at hx
  by_cases hxp : 0<x
  · have hv : V (Real.log x)≠0 := by simpa only [logWindow,ite_eq_left hxp] using hx
    have hh := abs_le.mp (hV _ hv)
    constructor
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.1
    · simpa only [Real.exp_log hxp] using Real.exp_le_exp.mpr hh.2
  · exact False.elim (hx (by simp only [logWindow,ite_eq_right hxp]))

theorem plain_annular_separation (V F : ℝ→ℂ) (M s X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (density : 𝓢(ℝ,ℂ))
    (hsep : ∀y : ℝ,V y*F (s*Real.exp y)=
      ∫v : ℝ,(V y*logPhase v y)*density v) (η : Character) :
    HeckeDyadic.polynomial η false (fun x=>logWindow V x*F (s*x)) X 0 0 =
      ∫v : ℝ,density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v) := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    pm_6951
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    pm_2894
  exact finite_annular_separation V F s X hX density hsep η S hs hc

end SevenEighths.CenteredMomentReflectedProfileMeasure

end

end OAI
