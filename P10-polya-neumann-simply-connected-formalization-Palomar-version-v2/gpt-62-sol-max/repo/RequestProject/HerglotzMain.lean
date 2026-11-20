module

public import RequestProject.HerglotzSplit
public import RequestProject.SmallKernel

/-!
# The principal part of the Herglotz form

Write `T₀ g(θ) = ∫₀^θ g` for the Volterra operator with kernel `1` and `G = T₀ g_a` for the
primitive of the conormal trace. Along the boundary, `g_a = -i h_a' + k q`, where
`q = conj(γ') F₋₁(γ)` (so `k q = 2i ∂̄u_a(γ) conj(γ')`), hence `G = -i (h_a - h_a(0)) + k Q` with
`Q = ∫₀^θ q`. When `∫_Ω u_a = 0` (so that `G(L) = Q(L) = 0`), Green's formula gives the principal
part of the Herglotz form (`re_integral_herglotz_principal`):

  `Re ∫₀^L conj(g_a) (2 h_a + i (T₀ - T₀^*) g_a)
      = 2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q`,

that is `4 ∫_Ω |∇u_a|² + 8 ∫_Ω |∂̄u_a|² − 6k² ∫_Ω |u_a|²` up to the boundary term in `Q`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real Interval

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {γ : ℝ → ℂ} {a : ℝ → ℂ}

/-- The boundary density `q = conj(γ') F₋₁(γ)`. -/
def herglotzQd (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  conj (deriv γ θ) * herglotzCoeff k a (-1) (γ θ)

/-- Its primitive `Q(θ) = ∫₀^θ q`. -/
def herglotzQ (k : ℝ) (a : ℝ → ℂ) (γ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..θ, herglotzQd k a γ t

lemma intervalIntegrable_herglotzQd (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) (u v : ℝ) :
    IntervalIntegrable (herglotzQd k a γ) volume u v :=
  (intervalIntegrable_conj' (intervalIntegrable_lipschitz_deriv hK u v)).mul_continuousOn
    (((continuous_herglotzCoeff ha k (-1)).comp hK.continuous).continuousOn)

lemma continuous_herglotzQ (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) : Continuous (herglotzQ k a γ) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_herglotzQd ha k hK) 0

/-- Along the boundary, `g_a = -i (u_a ∘ γ)' + k q` almost everywhere. -/
lemma herglotzConormal_ae_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∀ᵐ θ, herglotzConormal k a γ θ =
      -Complex.I * deriv (fun s => herglotzCoeff k a 0 (γ s)) θ + k * herglotzQd k a γ θ := by
  filter_upwards [hK.ae_differentiableAt] with θ hθ
  obtain ⟨h0, h0L⟩ := herglotzCoeff_hasFDerivAt' ha k 0 (γ θ)
  have hd : deriv (fun s => herglotzCoeff k a 0 (γ s)) θ =
      fderiv ℝ (herglotzCoeff k a 0) (γ θ) (deriv γ θ) :=
    (h0.comp_hasDerivAt θ hθ.hasDerivAt).deriv
  rw [hd, h0L, herglotzConormal_eq ha, herglotzQd]
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, show (0 : ℤ) - 1 = -1 by norm_num]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `G(θ) = ∫₀^θ g_a = -i (h_a(θ) - h_a(0)) + k Q(θ)`. -/
lemma primitive_herglotzConormal_eq (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) (θ : ℝ) :
    ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s =
      -Complex.I * (herglotzCoeff k a 0 (γ θ) - herglotzCoeff k a 0 (γ 0)) +
        k * herglotzQ k a γ θ := by
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
  have hh : LipschitzWith (C * K) (fun s => herglotzCoeff k a 0 (γ s)) := hC.comp hK
  have hdi := intervalIntegrable_lipschitz_deriv hh 0 θ
  have hqi := intervalIntegrable_herglotzQd ha k hK 0 θ
  rw [intervalIntegral.integral_congr_ae (g := fun s => -Complex.I *
      deriv (fun s => herglotzCoeff k a 0 (γ s)) s + k * herglotzQd k a γ s)
      ((herglotzConormal_ae_eq ha k hK).mono fun s hs _ => hs),
    intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_deriv_of_lipschitz hh, herglotzQ]

/-- Integration by parts against `Q`:
`∫₀^L conj(h') Q = conj(h(L)) Q(L) − ∫₀^L conj(h) q` for `h = u_a ∘ γ`. -/
lemma integral_conj_deriv_mul_herglotzQ (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    {K : NNReal} (hK : LipschitzWith K γ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (deriv (fun s => herglotzCoeff k a 0 (γ s)) θ) *
        herglotzQ k a γ θ =
      conj (herglotzCoeff k a 0 (γ (2 * π))) * herglotzQ k a γ (2 * π) -
        ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzCoeff k a 0 (γ θ)) * herglotzQd k a γ θ := by
  obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
  let h (t : ℝ) := herglotzCoeff k a 0 (γ t)
  have hh : LipschitzWith (C * K) h := hC.comp hK
  have eq (t : ℝ) : conj (h 0) + (∫ s in (0 : ℝ)..t, conj (deriv h s)) = conj (h t) := by
    rw [intervalIntegral.intervalIntegral_conj, integral_deriv_of_lipschitz hh, map_sub]
    ring
  have hi := integral_primitives_by_parts (intervalIntegrable_herglotzQd ha k hK 0 (2 * π))
    (intervalIntegrable_conj' (intervalIntegrable_lipschitz_deriv hh 0 (2 * π))) 0 (conj (h 0))
  simp only [zero_add, eq, zero_mul, sub_zero] at hi
  simpa only [h, mul_comm, herglotzQ] using hi

/-- **Principal part of the Herglotz form.** If `∫_Ω u_a = 0`, then with `G = ∫₀^θ g_a`,

  `Re ∫₀^L conj(g_a) (2 h_a + 2i G) = 2k² ∫_Ω (|F₁|² + 2|F₋₁|² − 3|F₀|²) − 2k² Im ∫₀^L conj(q) Q`.

(Here `2G = (T₀ − T₀^*) g_a` since `∫₀^L g_a = 0`.) -/
theorem re_integral_herglotz_principal (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) (hγ : IsBoundaryParam Ω γ)
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
    (h0 : ∫ z in Ω, herglotzCoeff k a 0 z = 0) :
    (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal k a γ θ) *
        (2 * herglotzWave k a (γ θ) +
          Complex.I * (2 * ∫ s in (0 : ℝ)..θ, herglotzConormal k a γ s))).re =
      2 * k ^ 2 * (∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + 2 * ‖herglotzCoeff k a (-1) z‖ ^ 2 -
        3 * ‖herglotzCoeff k a 0 z‖ ^ 2)) -
      2 * k ^ 2 * (∫ θ in (0 : ℝ)..(2 * π), conj (herglotzQd k a γ θ) * herglotzQ k a γ θ).im := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hclosed : γ (2 * π) = γ 0 := by simpa using hγ.periodic 0
  set g := herglotzConormal k a γ with hgdef
  set h : ℝ → ℂ := fun s => herglotzCoeff k a 0 (γ s) with hhdef
  set q := herglotzQd k a γ with hqdef
  set Q := herglotzQ k a γ with hQdef
  have hcgi := intervalIntegrable_conj' (intervalIntegrable_herglotzConormal ha k hK 0 (2 * π))
  have hhc : Continuous h := (continuous_herglotzCoeff ha k 0).comp hK.continuous
  have hQc : Continuous Q := continuous_herglotzQ ha k hK
  -- vanishing of the endpoint values
  have hgint : ∫ θ in (0 : ℝ)..(2 * π), g θ = 0 := by
    rw [hgdef, integral_herglotzConormal hb hL hγ ha, h0, mul_zero]
  have hQL : Q (2 * π) = 0 := by
    rw [hQdef, herglotzQ]
    simp only [herglotzQd]
    rw [integral_conj_deriv_mul_herglotzCoeff_neg_one hb hL hγ ha, h0, mul_zero]
  have hG : ∀ θ, ∫ s in (0 : ℝ)..θ, g s = -Complex.I * (h θ - h 0) + k * Q θ := fun θ =>
    primitive_herglotzConormal_eq ha k hK θ
  -- the pieces
  have hR1 := integral_conj_herglotzConormal_mul_wave hb hL hγ ha k
  have hX : ∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ =
      ((k * ∫ z in Ω, (‖herglotzCoeff k a (-1) z‖ ^ 2 - ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) :
        ℂ) := integral_conj_wave_mul_herglotzQ' hb hL hγ ha k
  have hibp : ∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ =
      -∫ θ in (0 : ℝ)..(2 * π), conj (h θ) * q θ := by
    rw [integral_conj_deriv_mul_herglotzQ ha k hK,
      show herglotzQ k a γ (2 * π) = 0 from hQL]
    ring
  have hcg0 : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) = 0 := by
    rw [intervalIntegral.intervalIntegral_conj, hgint, map_zero]
  -- `∫ conj(g) Q`
  have hgQ : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * Q θ =
      Complex.I * (∫ θ in (0 : ℝ)..(2 * π), conj (deriv h θ) * Q θ) +
        k * ∫ θ in (0 : ℝ)..(2 * π), conj (q θ) * Q θ := by
    obtain ⟨C, hC⟩ := lipschitzWith_herglotzCoeff ha k 0
    have hh : LipschitzWith (C * K) h := hC.comp hK
    have hdi := (intervalIntegrable_conj' (intervalIntegrable_lipschitz_deriv hh 0 (2 * π))).mul_continuousOn
      hQc.continuousOn
    have hqi := (intervalIntegrable_conj' (intervalIntegrable_herglotzQd ha k hK 0 (2 * π))).mul_continuousOn
      hQc.continuousOn
    have hae : ∫ θ in (0 : ℝ)..(2 * π), conj (g θ) * Q θ = ∫ θ in (0 : ℝ)..(2 * π),
        (Complex.I * (conj (deriv h θ) * Q θ) + (k : ℂ) * (conj (q θ) * Q θ)) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [herglotzConormal_ae_eq ha k hK] with θ hθ _
      rw [hgdef, hθ, hhdef, hqdef]
      simp only [map_add, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hae, intervalIntegral.integral_add (hdi.const_mul _) (hqi.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  -- the integrand
  have hpt : ∀ θ, conj (g θ) * (2 * herglotzWave k a (γ θ) +
      Complex.I * (2 * ∫ s in (0 : ℝ)..θ, g s)) =
      4 * (conj (g θ) * herglotzWave k a (γ θ)) - 2 * h 0 * conj (g θ) +
        2 * Complex.I * k * (conj (g θ) * Q θ) := fun θ => by
    rw [hG θ, herglotzWave_eq]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hi1 : IntervalIntegrable (fun θ => conj (g θ) * herglotzWave k a (γ θ)) volume 0
      (2 * π) := hcgi.mul_continuousOn
    (by
      have : herglotzWave k a = herglotzCoeff k a 0 := funext (herglotzWave_eq k a)
      rw [this]
      exact ((continuous_herglotzCoeff ha k 0).comp hK.continuous).continuousOn)
  have hi3 : IntervalIntegrable (fun θ => conj (g θ) * Q θ) volume 0 (2 * π) :=
    hcgi.mul_continuousOn hQc.continuousOn
  simp_rw [hpt]
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hcgi.const_mul _))
      (hi3.const_mul _), intervalIntegral.integral_sub (hi1.const_mul _) (hcgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcg0, hgQ, hibp, hR1, hX]
  -- the interior integrals
  have e1 := integral_herglotzCoeff_main hb ha k 1 2
  simp only [one_mul] at e1
  rw [e1, integral_sub (integrable_herglotzCoeff_sq hb ha k (-1))
    (integrable_herglotzCoeff_sq hb ha k 0), integral_herglotzCoeff_main hb ha k 2 3]
  set Y := ∫ θ in (0 : ℝ)..(2 * π), conj (q θ) * Q θ
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_im, Complex.zero_re,
    Complex.zero_im]
  ring

end PolyaNeumann

end
