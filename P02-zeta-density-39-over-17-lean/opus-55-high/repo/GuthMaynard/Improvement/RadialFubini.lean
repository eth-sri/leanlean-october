module
public import GuthMaynard.Improvement.RadialCoordinates
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace GuthMaynard.Improvement

def radialIntegrand (a : ℝ → ℂ) (μ : ℝ → ℝ) (L : ℝ)
    (m : ℤ × (ℤ × ℤ)) (r : ℝ) (p : ℝ × ℝ) : ℂ :=
  radialAmplitude a p.1 p.2 r *
    phase (-L*((m.1:ℝ)*p.1+(m.2.1:ℝ)*p.2+(m.2.2:ℝ))*r) * ratioFourierProduct μ p

/-- The actual radial amplitude has fixed compact ratio support. -/
theorem radialAmplitude_support {a : ℝ → ℂ} {l u : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hs : ∀ x, x ∉ Icc l u → a x = 0)
    {r v y : ℝ} (ha : radialAmplitude a v y r ≠ 0) :
    r ∈ Icc l u ∧ (v,y) ∈ Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l) := by
  have hr : a r ≠ 0 := by intro h; apply ha; simp [radialAmplitude,h]
  pm_6371 hv v
  pm_6371 hy y
  have hmem : ∀ x, a x ≠ 0 → x ∈ Icc l u := by
    intro x hx; by_contra hn; exact hx (hs x hn)
  have hrb := hmem r hr
  have hb : ∀ z, a (z*r) ≠ 0 → z ∈ Icc (l/u) (u/l) := by
    intro z hz
    have hzb := hmem (z*r) hz
    have hrp : 0 < r := lt_of_lt_of_le hl hrb.1
    have hzp : 0 < z := (mul_pos_iff_of_pos_right hrp).mp (lt_of_lt_of_le hl hzb.1)
    constructor
    · apply (div_le_iff₀ (lt_of_lt_of_le hl hlu)).mpr
      nlinarith [hzb.1, mul_le_mul_of_nonneg_left hrb.2 hzp.le]
    · apply (le_div_iff₀ hl).mpr
      nlinarith [hzb.2, mul_le_mul_of_nonneg_left hrb.1 hzp.le]
  grind

theorem radialIntegrand_measurable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : Measurable a) (hi : Integrable μ) (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Measurable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a μ L m z.1 z.2) := by
  have hp := phase_measurable
  have hf := ratioFourierProduct_measurable hi
  unfold radialIntegrand radialAmplitude
  fun_prop

/-- Absolute integrability on the full radial/ratio space is proved from
actual compact support and Fourier mass bounds, with no Fubini premise. -/
theorem radialIntegrand_integrable {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => radialIntegrand a μ L m z.1 z.2) := by
  pm_4574
  pm_4577 μ
  pm_4575
  apply (integrableOn_const hE.measure_lt_top.ne (C := C*(∫ t, μ t)^3)).mono'
    (radialIntegrand_measurable ha.continuous.measurable hi L m).aestronglyMeasurable
  pm_4576
  exact mul_le_mul hb' (ratioFourierProduct_bound hm h0 hi z.2) (norm_nonneg _) hC.le

/-- Fubini moves the actual radial integral inside the ratio integral.
The original three Fourier factors and the exact Jacobian are preserved. -/
theorem spatialCubicMode_radial_fubini {a : ℝ → ℂ} {μ : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hs : ∀ x, x ∉ Icc l u → a x = 0)
    (hm : Measurable μ) (h0 : ∀ t, 0 ≤ μ t) (hi : Integrable μ)
    (L : ℝ) (m : ℤ × (ℤ × ℤ)) :
    (∫ r, ∫ x₁, ∫ x₂, spatialCubicMode a μ L m x₁ x₂ r) =
      ∫ p in Icc (l/u) (u/l) ×ˢ Icc (l/u) (u/l),
        radialKernel a L m p * ratioFourierProduct μ p := by pm_4578 hm h0 hi μ

end GuthMaynard.Improvement
