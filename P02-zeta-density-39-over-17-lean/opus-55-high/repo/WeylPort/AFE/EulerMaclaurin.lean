module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PoissonFourier
public import WeylPort.Analytic.EulerMaclaurin
public import Mathlib.Analysis.Calculus.Deriv.Shift
import WeylPort.Analytic.RealLaplace

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Euler–Maclaurin for the source's full real-endpoint domain

This module reuses the existing pinned PNT+ Euler–Maclaurin theorem and proves
the integer translation and endpoint bridges needed for arbitrary real a ≤ b.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The pinned upstream Bernoulli function agrees with the periodic sawtooth on its domain. -/
theorem B1_eq_fract {x : ℝ} (hx : 0 ≤ x) : B1 x = Int.fract x - 1 / 2 := by
  unfold B1 Int.fract
  rw [← Int.cast_natCast ⌊x⌋₊, Int.natCast_floor_eq_floor hx]

/-- An integer shift converts the natural-floor sum to the source's integer-floor sum. -/
theorem sum_shift_nat_floor (F : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (k : ℤ) (hk : (k : ℝ) ≤ a) :
    (∑ n ∈ Finset.Ioc ⌊a - k⌋₊ ⌊b - k⌋₊, F ((n : ℝ) + k)) =
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F (n : ℝ) := by
  have hfloor (x : ℝ) (hx : (k : ℝ) ≤ x) :
      (⌊x - k⌋₊ : ℤ) = ⌊x⌋ - k := by
    rw [Int.natCast_floor_eq_floor (sub_nonneg.mpr hx), Int.floor_sub_intCast]
  have hfa := hfloor a hk
  have hfb := hfloor b (hk.trans hab)
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ) + k)
  grind
  grind
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hka : k ≤ ⌊a⌋ := Int.le_floor.mpr hk
    have hmk : 0 ≤ m - k := by omega
    refine ⟨(m - k).toNat, ?_, ?_⟩
    grind
    grind
  simp_all

/-- Exact first-order Euler–Maclaurin with arbitrary real endpoints and the source's (a,b] sum. -/
theorem euler_maclaurin_int {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℂ)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ F x)
    (hc : ContinuousOn (deriv F) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F (n : ℝ)) =
      F a * ((Int.fract a - 1 / 2 : ℝ) : ℂ) - F b * ((Int.fract b - 1 / 2 : ℝ) : ℂ) +
        (∫ x in a..b, F x) + ∫ x in a..b, deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
  let k : ℤ := ⌊a⌋
  have hk : (k : ℝ) ≤ a := Int.floor_le a
  pm_7297 ha0 a k hk
  have hab' : a - k ≤ b - k := sub_le_sub_right hab _
  have hm : Set.MapsTo (fun x : ℝ => x + k) (Set.Icc (a - k) (b - k)) (Set.Icc a b) := by
    pm_8035
  have hd' (x : ℝ) (hx : x ∈ Set.Icc (a - k) (b - k)) :
      DifferentiableAt ℝ (fun u => F (u + k)) x :=
    (hd _ (hm hx)).comp x (differentiableAt_id.add_const _)
  have hc' : ContinuousOn (deriv (fun u => F (u + k))) (Set.uIcc (a - k) (b - k)) := by
    rw [Set.uIcc_of_le hab']
    have heq : deriv (fun u => F (u + k)) = fun u => deriv F (u + k) :=
      funext (fun u => deriv_comp_add_const F (k : ℝ) u)
    rw [heq]
    exact hc.comp (continuousOn_id.add continuousOn_const) hm
  have he := sum_eq_integral_add_integral_deriv ha0 hab' hd' hc'
  rw [sum_shift_nat_floor F hab k hk] at he
  simp only [sub_add_cancel] at he
  rw [B1_eq_fract ha0, B1_eq_fract (ha0.trans hab'), Int.fract_sub_intCast,
    Int.fract_sub_intCast] at he
  rw [intervalIntegral.integral_comp_add_right] at he
  simp only [sub_add_cancel] at he
  have hi : (∫ x in (a - k)..(b - k), deriv (fun u => F (u + k)) x * (B1 x : ℂ)) =
      ∫ x in a..b, deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
    calc
      _ = ∫ x in (a - k)..(b - k),
          deriv F (x + k) * ((Int.fract (x + k) - 1 / 2 : ℝ) : ℂ) := by
        pm_445 intervalIntegral.integral_congr x hx Set.uIcc_of_le hab'
        dsimp only
        rw [deriv_comp_add_const, B1_eq_fract (ha0.trans hx.1), Int.fract_add_intCast]
      _ = _ := by
        simpa only [sub_add_cancel] using
          intervalIntegral.integral_comp_add_right
            (fun x => deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ)) (k : ℝ)
            (a := a - k) (b := b - k)
  refine he.trans ?_
  congr 1

/-- The literal complex boundary term; its norm is the source's G(a,b). -/
noncomputable def poissonBoundary (f g : ℝ → ℝ) (a b : ℝ) : ℂ :=
  weightedWave f g a * ((Int.fract a - 1 / 2 : ℝ) : ℂ) -
    weightedWave f g b * ((Int.fract b - 1 / 2 : ℝ) : ℂ)

/-- The actual (a,b] weighted sum has the source's two Fourier series and complex boundary. -/
theorem weighted_sum_eq_fourier {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) =
      poissonBoundary f g a b + (∫ x in a..b, weightedWave f g x) +
        ((∑' n, negativeCoefficient f g a b n) - ∑' n, positiveCoefficient f g a b n) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :
      DifferentiableAt ℝ (weightedWave f g) x :=
    (weighted_wave_hasDerivAt (h.f_differentiable x hx) (h.g_differentiable x hx)).differentiableAt
  have heq (x : ℝ) (hx : x ∈ Set.Icc a b) :
      waveDerivative f g x = deriv (weightedWave f g) x :=
    waveDerivative_eq_deriv (h.f_differentiable x hx) (h.g_differentiable x hx)
  have hc : ContinuousOn (deriv (weightedWave f g)) (Set.Icc a b) :=
    h.waveDerivative_continuous.congr (fun x hx => (heq x hx).symm)
  have he := euler_maclaurin_int h.lt.le (weightedWave f g) hd hc
  have hi : (∫ x in a..b, deriv (weightedWave f g) x * ((Int.fract x - 1 / 2 : ℝ) : ℂ)) =
      ∫ x in a..b, waveDerivative f g x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
    pm_445 intervalIntegral.integral_congr x hx Set.uIcc_of_le h.lt.le
    dsimp only
    rw [heq x hx]
  rw [hi, integral_waveDerivative_sawtooth h] at he
  exact he

/-- The actual source wave has norm g(x) for a nonnegative weight. -/
theorem norm_weightedWave {f g : ℝ → ℝ} {x : ℝ} (hg : 0 ≤ g x) :
    ‖weightedWave f g x‖ = g x := by
  unfold weightedWave
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ))‖ = 1 := by
    have hp : 2 * (Real.pi : ℂ) * Complex.I * (f x : ℂ) =
        (((2 * Real.pi * f x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [hp, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]

/-- The periodic sawtooth has the source's sharp endpoint bound one half. -/
theorem abs_fract_sub_half_le (x : ℝ) : |Int.fract x - 1 / 2| ≤ 1 / 2 := by
  apply abs_le.mpr
  constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]

end DhimanKadiriQuesadaHerrera2026
