module
/-
The termwise Mellin proof is adapted from McColm TypeIICoverage at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. The cutoff X and smoothing
variable x are independent real parameters. No upstream project imports.
-/
public import MathCollab.Density.MollifierDirichlet
public import MathCollab.Density.GammaMellin
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped ArithmeticFunction.Moebius Topology
noncomputable section
namespace MathCollab.Density

theorem integrable_tsum_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, MeasureTheory.Integrable (F n) measure)
    (hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂measure)) :
    MeasureTheory.Integrable (fun x => ∑' n, F n x) measure := by
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) measure := (hFint n).1
  have hNormMeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) measure :=
    (hMeas n).enorm
  have hLIntegral : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂measure ≠ ⊤ := by
    have hEach (n : ℕ) : ∫⁻ x, ‖F n x‖ₑ ∂measure = ‖∫ x, ‖F n x‖ ∂measure‖₊ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hFint n).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
      simp_all
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  have hPointwise : ∀ᵐ x ∂measure, Summable (fun n => (‖F n x‖₊ : ℝ)) := by
    rw [← lintegral_tsum hNormMeas] at hLIntegral
    refine (ae_lt_top' (AEMeasurable.tsum hNormMeas) hLIntegral).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hBoundInt : Integrable (fun x => ∑' n, ‖F n x‖) measure := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hFint n).norm.1), ?_⟩
    dsimp [HasFiniteIntegral]
    have hFinite : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂measure < ⊤ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hLIntegral
    convert hFinite using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  refine hBoundInt.mono' (AEStronglyMeasurable.tsum hMeas) ?_
  filter_upwards [hPointwise] with x hx
  exact norm_tsum_le_tsum_norm hx

def smoothedDetector (ρ : ℂ) (X x : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (mollifierDirichletCoeff X) ρ n *
    Complex.exp (-((n : ℝ) * x))

theorem norm_mollifier_LSeries_term_le_cutoff {ρ : ℂ} (X : ℝ) (n : ℕ)
    (hρ : 0 ≤ ρ.re) :
    ‖LSeries.term (mollifierDirichletCoeff X) ρ n‖ ≤
      (⌊X⌋₊ : ℝ) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hnOneNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    pm_77 hnOne n hnOneNat
    have hPow : 1 ≤ (n : ℝ) ^ ρ.re := Real.one_le_rpow hnOne hρ
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hPow)).2
      ((norm_mollifierDirichletCoeff_le_cutoff X n).trans
        (by nlinarith [show (0 : ℝ) ≤ ⌊X⌋₊ by positivity]))

section
variable {ρ : ℂ} {X x : ℝ} (hx : 0 < x) (hρ : 0 ≤ ρ.re)
include ρ X x hx hρ
/-- Absolute convergence of the smoothed detector at every positive smoothing
parameter, uniformly for `Re ρ ≥ 0`. -/
theorem summable_smoothedDetector :
    Summable (fun n : ℕ =>
      LSeries.term (mollifierDirichletCoeff X) ρ n *
        Complex.exp (-((n : ℝ) * x))) := by
  pm_4306 x
  apply Summable.of_norm
  refine (hGeom.mul_left (⌊X⌋₊ : ℝ)).of_nonneg_of_le
    (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, Complex.norm_exp]
  have hRe : (-(((n : ℝ) : ℂ) * (x : ℂ))).re = -((n : ℝ) * x) := by
    norm_num
  rw [hRe]
  have hExpEq : Real.exp (-((n : ℝ) * x)) = Real.exp (-(n : ℝ) * x) := by
    congr 1
    ring
  rw [← hExpEq]
  apply mul_le_mul_of_nonneg_right
    (norm_mollifier_LSeries_term_le_cutoff X n hρ)
  positivity

theorem hasSum_smoothedDetector :
    HasSum (fun n : ℕ =>
      LSeries.term (mollifierDirichletCoeff X) ρ n *
        Complex.exp (-((n : ℝ) * x)))
      (smoothedDetector ρ X x) := by
  exact (summable_smoothedDetector (X := X) hx hρ).hasSum
end

section
variable (f : ℕ → ℂ) (ρ s : ℂ) (n : ℕ)
include f ρ s n
theorem norm_LSeries_term_div_rpow_eq_add :
    ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re =
      ‖LSeries.term f (ρ + s) n‖ := by
  pm_4961
  · have hnPos : (0 : ℝ) < n := by positivity
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn]
    rw [add_re, Real.rpow_add hnPos]
    grind

theorem Gamma_mul_term_div_cpow_eq_add :
    Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term f (ρ + s) n := by
  pm_4961
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.ofReal_natCast, Complex.cpow_add _ _ hnC]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)]
end

set_option maxHeartbeats 800000 in
/-- Mellin transformation of the smoothed detector on every line where the
underlying zeta--Möbius L-series converges absolutely. -/
theorem mellin_smoothedDetector_eq {ρ s : ℂ} {X : ℝ}
    (hρ : 0 ≤ ρ.re) (hs : 0 < s.re)
    (hAbs : 1 < (ρ + s).re) :
    mellin (smoothedDetector ρ X) s =
      Complex.Gamma s * LSeries (mollifierDirichletCoeff X)
        (ρ + s) := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hSumNorm : Summable (fun n : ℕ =>
      ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n : ℕ => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr (fun n => (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm)
  have hMellin : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s)
      (mellin (smoothedDetector ρ X) s) := by
    apply hasSum_mellin
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · left
        simp
      · right
        exact_mod_cast Nat.pos_of_ne_zero hn
    · exact hs
    · intro x hx
      have hSeries := hasSum_smoothedDetector (X := X) hx hρ
      simpa [f, Complex.ofReal_exp] using hSeries
    · exact hSumNorm
  have hMellin' : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (mellin (smoothedDetector ρ X) s) :=
    hMellin.congr_fun (fun n => (Gamma_mul_term_div_cpow_eq_add f ρ s n).symm)
  have hProduct : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (Complex.Gamma s * LSeries f (ρ + s)) := by
    exact hLS.hasSum.mul_left (Complex.Gamma s)
  exact hMellin'.unique hProduct

/-- A fixed convergent p-series used to dominate all right-line detector
L-series uniformly in the ordinate. -/
def detectorPSeries : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(6 / 5 : ℝ))

theorem summable_detectorPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(6 / 5 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem norm_mollifier_LSeries_le_cutoff_pSeries {z : ℂ} {X : ℝ}
    (hz : 6 / 5 ≤ z.re) :
    ‖LSeries (mollifierDirichletCoeff X) z‖ ≤
      (⌊X⌋₊ : ℝ) * detectorPSeries := by
  pm_4308
  have hTerm (n : ℕ) : ‖LSeries.term f z n‖ ≤
      (⌊X⌋₊ : ℝ) * (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
    pm_4961
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      pm_7032 hnOne n Nat.one_le_iff_ne_zero.mpr
      have hDen : (n : ℝ) ^ (6 / 5 : ℝ) ≤ (n : ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hnOne hz
      pm_4307
      have hRight : (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ (6 / 5 : ℝ) := by
        pm_7850
      exact hLeft.trans hRight
  calc
    ‖LSeries f z‖ ≤ ∑' n : ℕ, ‖LSeries.term f z n‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' n : ℕ, (⌊X⌋₊ : ℝ) *
        (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
      pm_8291 summable_detectorPSeries.mul_left
    _ = (⌊X⌋₊ : ℝ) * detectorPSeries := by
      rw [detectorPSeries, tsum_mul_left]

set_option maxHeartbeats 800000 in
set_option hygiene false in
macro "pf_33" x1:ident x2:term:max x3:term:max x4:ident : tactic => `(tactic| (
  let line : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  let g : ℝ → ℂ := fun u => Complex.Gamma (line u) *
    (riemannZeta (ρ + line u) *
      zetaMollifier X (ρ + line u))
  have hGammaCont : Continuous (fun u : ℝ => Complex.Gamma (line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hNoPole : ∀ m : ℕ, line u ≠ -m := by
      intro m hm
      have hRe := congrArg Complex.re hm
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (Complex.differentiableAt_Gamma _ hNoPole).continuousAt
      (by dsimp [line]; fun_prop)
  have hZetaCont : Continuous (fun u : ℝ => riemannZeta (ρ + line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hzRe : 1 < (ρ + line u).re := by simp [line]; linarith
    have hzNe : ρ + line u ≠ 1 := by
      intro hz
      have hRe := congrArg Complex.re hz
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (differentiableAt_riemannZeta hzNe).continuousAt
      (by dsimp [line]; fun_prop)
  have hMollCont : Continuous (fun u : ℝ => zetaMollifier X (ρ + line u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ + line u)).continuousAt (by
      dsimp [line]; fun_prop)
  have hgCont : Continuous g := by
    exact hGammaCont.mul (hZetaCont.mul hMollCont)
  let C : ℝ := (⌊X⌋₊ : ℝ) * $x1:ident
  have hDom : MeasureTheory.Integrable (fun u : ℝ =>
      C * ‖Complex.Gamma (line u)‖) := by
    have hGammaInt : MeasureTheory.Integrable
        (fun u : ℝ => Complex.Gamma (line u)) := by
      simpa [line, VerticalIntegrable] using GammaMellin.verticalIntegrable_Gamma (sigma := 1/2) (by norm_num)
    exact hGammaInt.norm.const_mul C
  have hg : MeasureTheory.Integrable g := by
    refine MeasureTheory.Integrable.mono' hDom hgCont.aestronglyMeasurable ?_
    filter_upwards with u
    have hzRe : $x2:term / $x3:term ≤ (ρ + line u).re := by simp [line]; linarith
    have hAbs : 1 < (ρ + line u).re := by linarith
    have hLSeries := $x4:ident (X := X) hzRe
    have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
      X hAbs
    dsimp [g]
    rw [norm_mul, hProduct]
    dsimp [C]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hLSeries
      (norm_nonneg (Complex.Gamma (line u)))
  apply hg.congr
  filter_upwards with u
  have hsRe : 0 < (line u).re := by simp [line]
  have hρNonneg : 0 ≤ ρ.re := by linarith
  have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
  rw [mellin_smoothedDetector_eq (X := X) hρNonneg hsRe hAbs]
  dsimp [g]
  rw [riemannZeta_mul_zetaMollifier_eq_LSeries
    X hAbs]))
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
/-- The Mellin transform of the smoothed detector is genuinely integrable on
the right line `Re s = 1/2`, uniformly for the zero-density range `Re ρ ≥ 3/4`. -/
theorem verticalIntegrable_mellin_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 3 / 4 ≤ ρ.re) :
    VerticalIntegrable (mellin (smoothedDetector ρ X)) (1 / 2 : ℝ) := by pf_33 detectorPSeries 6 5 norm_mollifier_LSeries_le_cutoff_pSeries

set_option maxHeartbeats 800000 in
/-- The smoothed detector is continuous at every positive smoothing
parameter.  Uniform convergence is obtained on the neighborhood `[x/2,∞)`
from the same geometric majorant used for absolute convergence. -/
theorem continuousAt_smoothedDetector {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    ContinuousAt (smoothedDetector ρ X) x := by
  let x₀ : ℝ := x / 2
  let term : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (mollifierDirichletCoeff X) ρ n *
      Complex.exp (-((n : ℝ) * y))
  let majorant : ℕ → ℝ := fun n =>
    (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * x₀))
  pm_358 hx₀ x₀
  have hMajorant : Summable majorant := by
    pm_4306 x₀
    simpa [majorant] using hGeom.mul_left (⌊X⌋₊ : ℝ)
  have hTermCont (n : ℕ) : ContinuousOn (term n) (Set.Ici x₀) := by
    apply Continuous.continuousOn
    dsimp [term]
    fun_prop
  have hBound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ici x₀) :
      ‖term n y‖ ≤ majorant n := by
    pm_96 hnNonneg n
    have hArg : -((n : ℝ) * y) ≤ -((n : ℝ) * x₀) := by
      have := hy
      simp only [Set.mem_Ici] at this
      nlinarith
    have hExp : Real.exp (-((n : ℝ) * y)) ≤
        Real.exp (-((n : ℝ) * x₀)) := Real.exp_le_exp.mpr hArg
    dsimp [term, majorant]
    rw [norm_mul, Complex.norm_exp]
    have hRe : (-((n : ℂ) * (y : ℂ))).re = -((n : ℝ) * y) := by
      norm_num
    rw [hRe]
    calc
      ‖LSeries.term (mollifierDirichletCoeff X) ρ n‖ *
          Real.exp (-((n : ℝ) * y))
          ≤ (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * y)) :=
        mul_le_mul_of_nonneg_right
          (norm_mollifier_LSeries_term_le_cutoff X n hρ)
          (Real.exp_pos _).le
      _ ≤ (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * x₀)) :=
        mul_le_mul_of_nonneg_left hExp (by positivity)
  have hContinuousOn : ContinuousOn (smoothedDetector ρ X) (Set.Ici x₀) := by
    change ContinuousOn (fun y => ∑' n : ℕ, term n y) (Set.Ici x₀)
    exact continuousOn_tsum hTermCont hMajorant hBound
  have hNhd : Set.Ici x₀ ∈ nhds x := by
    apply Filter.mem_of_superset
      (Ioi_mem_nhds (show x₀ < x by dsimp [x₀]; linarith))
    exact Set.Ioi_subset_Ici_self
  exact hContinuousOn.continuousAt hNhd

set_option maxHeartbeats 800000 in
set_option maxHeartbeats 800000 in
/-- Absolute convergence in the Mellin variable on `Re s = 1/2`.  The key
summability exponent is `Re ρ + 1/2 > 1`; this is exactly why the detector
works uniformly in the repaired zero-density range `Re ρ ≥ 3/4`. -/
theorem mellinConvergent_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 3 / 4 ≤ ρ.re) :
    MellinConvergent (smoothedDetector ρ X) ((1 / 2 : ℝ) : ℂ) := by pm_4309

/-- Exact inversion for an arbitrary positive smoothing variable. -/
theorem smoothedDetector_eq_mellinInv {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 3/4 ≤ ρ.re) :
    smoothedDetector ρ X x = mellinInv (1/2 : ℝ)
      (fun s => Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) x := by pm_4310 mellinConvergent_smoothedDetector verticalIntegrable_mellin_smoothedDetector

/-- The literal Gamma-zeta-mollifier contour kernel, with independent X and Y. -/
def detectorKernel (ρ : ℂ) (X Y : ℝ) (s : ℂ) : ℂ :=
  (Y : ℂ)^s * Complex.Gamma s * zetaMollifier X (ρ+s) * riemannZeta (ρ+s)

/-- The positive smoothing scale produces the exact right contour, with no
zero or Weyl hypothesis. The factor is 1/(2*pi) for a real vertical parameter. -/
theorem smoothedDetector_eq_rightContour {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 3/4 ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)) := by pm_4311 smoothedDetector_eq_mellinInv

end MathCollab.Density
