module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.InitialBound
public import OAI.NumberTheory.DirichletL.Poisson.EisensteinLattice
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

namespace CubicReflectionKernel

section
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

def momentScale : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ u : ℝ, (1 + ‖u‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)

end

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

theorem paperScale_pos : 0 < paperScale := by
  unfold paperScale
  positivity

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)

theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  pm_6054
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  pm_1281

def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)

@[simp] theorem logSchwartz_apply (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (u : ℝ) :
    logSchwartz V a b ha hsupp hV u = V (Real.exp u) := rfl

section
variable (V : ℝ → ℂ)
include V
theorem compact_source_mellin_convergent (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) : MellinConvergent V s := by
  pm_3169
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

theorem mellin_axis_eq_fourier (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (u : ℝ) :
    mellin V (-((2 * Real.pi * u : ℝ) * Complex.I)) = (𝓕 logSource) u := by
  rw [mellin_eq_fourier]
  have hfreq : (-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).im / (2 * Real.pi) = -u := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    field_simp
  rw [hfreq]
  have hfun : (fun v : ℝ => Real.exp
      (-(-((2 * Real.pi * u : ℝ) * Complex.I) : ℂ).re * v) • V (Real.exp (-v))) =
      (logSource : ℝ → ℂ) ∘ LinearIsometryEquiv.neg ℝ := by
    funext v
    simp [hL]
  rw [hfun, Real.fourier_comp_linearIsometry]
  simp
  rfl

theorem paperKernel_eq_logFourier (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (x : ℝ) (hx : 0 < x) :
    paperKernel V x = reflectedLogProfile logSource (Real.log (paperScale * x)) := by
  unfold paperKernel
  pm_8075
  simp only [Complex.ofReal_zero, neg_zero, Complex.cpow_zero, one_smul]
  rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  have hfun : (fun y : ℝ => mellin V (-(0 + 2 * Real.pi * y * Complex.I)) *
      gammaMultiplier (0 + 2 * Real.pi * y * Complex.I)) = spectralProfile logSource := by
    funext y
    have hy : (0 + 2 * Real.pi * y * Complex.I : ℂ) =
        ((2 * Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hy, mellin_axis_eq_fourier V logSource hL]
    exact mul_comm _ _
  rw [hfun]
  rfl
end

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

section
variable (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ) (hL : ∀ u, logSource u = V (Real.exp u))
include V logSource hL
theorem paperKernel_contDiffOn :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) := by
  have hg : ContDiffOn ℝ ∞
      (fun x => reflectedLogProfile logSource (Real.log (paperScale * x))) (Set.Ioi 0) := by
    intro x hx
    apply (reflectedLogProfile_smooth logSource).contDiffAt.comp_contDiffWithinAt x
    exact ((contDiffAt_const.mul contDiffAt_id).log
      (ne_of_gt (mul_pos paperScale_pos hx))).contDiffWithinAt
  apply hg.congr
  intro x hx
  exact paperKernel_eq_logFourier V logSource hL x hx

theorem paperKernel_euler_eq (j : ℕ) (x : ℝ) (hx : 0 < x) :
    LocalLogFourier.eulerDeriv (paperKernel V) j x =
      iteratedDeriv j (reflectedLogProfile logSource) (Real.log (paperScale * x)) := by
  have hfun : (fun t : ℝ => paperKernel V (x * Real.exp t)) =
      (fun t : ℝ => reflectedLogProfile logSource (Real.log (paperScale * x) + t)) := by
    funext t
    rw [paperKernel_eq_logFourier V logSource hL _ (mul_pos hx (Real.exp_pos t))]
    rw [← mul_assoc, Real.log_mul (ne_of_gt (mul_pos paperScale_pos hx))
      (ne_of_gt (Real.exp_pos t)), Real.log_exp]
  rw [LocalLogFourier.eulerDeriv, hfun, iteratedDeriv_comp_const_add]
  simp
end

theorem paperKernel_compact_source_smooth
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (paperKernel V) (Set.Ioi 0) :=
  paperKernel_contDiffOn V (logSchwartz V a b ha hsupp hV) (by intro u; rfl)

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

section
variable (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
include V a b ha hsupp hV
theorem compact_source_mellin_hasDerivAt
    (s : ℂ) :
    HasDerivAt (mellin V) (mellin (fun t => Real.log t • V t) s) s := by
  pm_3169
  exact (mellin_hasDerivAt_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)).2

theorem compact_source_mellin_differentiable :
    Differentiable ℂ (mellin V) :=
  fun s => (compact_source_mellin_hasDerivAt V a b ha hsupp hV s).differentiableAt
end

theorem Gamma_differentiableAt_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z := by
  apply Complex.differentiableAt_Gamma
  intro m hm
  have hr := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  pm_322 hn m
  linarith

theorem gammaMultiplier_differentiableAt (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ gammaMultiplier s := by
  have h1 := (Gamma_differentiableAt_of_re_pos ((7 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h2 := (Gamma_differentiableAt_of_re_pos ((5 / 6 : ℂ) + s) (by
    norm_num [Complex.add_re, Complex.div_re]
    linarith)).comp s (differentiableAt_const _ |>.add differentiableAt_id)
  have h3 := (Complex.differentiable_one_div_Gamma ((7 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  have h4 := (Complex.differentiable_one_div_Gamma ((5 / 6 : ℂ) - s)).comp s
    (differentiableAt_const _ |>.sub differentiableAt_id)
  convert ((h1.mul h2).mul (h3.mul h4)) using 1
  ext z
  pm_93 gammaMultiplier Function.comp_def div_eq_mul_inv mul_inv_rev Pi.mul_apply
  ring

theorem kernelMellinIntegrand_differentiableAt
    (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (s : ℂ) (hs : -(5 / 6 : ℝ) < s.re) :
    DifferentiableAt ℂ (fun t => mellin V (-t) * gammaMultiplier t) s := by
  exact ((compact_source_mellin_differentiable V a b ha hsupp hV (-s)).comp s
    differentiableAt_id.neg).mul (gammaMultiplier_differentiableAt s hs)

end CubicReflectionKernel

namespace DescentWeightedCauchy

section
variable {ι : Type*} (s : Finset ι) (w U V : ι → ℂ)
include ι s w U V
theorem weighted_cauchy_sq :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

theorem weighted_cauchy :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  pm_5409 h1 U
  pm_5409 h2 V
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)
end

section
variable {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ) (f : ι → κ) (w : ι → ℂ) (P : κ → ℂ)
include ι κ s t f w P
theorem weighted_energy_pushforward (B : κ → ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t)
    (hfib : ∀ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) ≤ B y) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, B y * ‖P y‖ ^ 2 := by
  calc
    _ = ∑ y ∈ t, ∑ i ∈ s with f i = y, ‖w i‖ * ‖P (f i)‖ ^ 2 := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmap _
    _ = ∑ y ∈ t, (∑ i ∈ s with f i = y, ‖w i‖) * ‖P y‖ ^ 2 := by
      pm_3170 y hy Finset.sum_mul i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ _ := Finset.sum_le_sum (fun y hy =>
      mul_le_mul_of_nonneg_right (hfib y hy) (sq_nonneg _))

theorem bounded_energy_pushforward (C : ℝ)
    (hmap : ∀ i ∈ s, f i ∈ t) (hw : ∀ i ∈ s, ‖w i‖ ≤ C) :
    (∑ i ∈ s, ‖w i‖ * ‖P (f i)‖ ^ 2) ≤
      ∑ y ∈ t, C * (s.filter (fun i => f i = y)).card * ‖P y‖ ^ 2 := by
  apply weighted_energy_pushforward s t f w P _ hmap
  intro y hy
  calc
    _ ≤ ∑ i ∈ s with f i = y, C := Finset.sum_le_sum
      (fun i hi => hw i (Finset.mem_filter.mp hi).1)
    _ = _ := by simp [mul_comm]
end

export OAI.EisensteinSchwartzPoisson (O)

def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e

theorem firstElementRowMap_label_dvd (e : O) (x : Ideal O × O) :
    x.1 ∣ Ideal.span {firstElementRowMap e x} := by
  rw [← ConcretePrimeRowBridge.span_idealGenerator x.1]
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr
  refine ⟨x.2 * ConcretePrimeRowBridge.idealGenerator x.1 * e, ?_⟩
  simp only [firstElementRowMap]
  ring

end DescentWeightedCauchy

end

end OAI
