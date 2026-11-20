module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicMellin

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

/-- The Mellin contour integrand, for any Dirichlet series `L`. -/
def mellinIntegrand (L : ℂ → ℂ) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    L (s+shift σ freq)

theorem mellin_vertical_re (x y : ℝ) : ((x : ℂ)+y*I).re=x := by simp

theorem mellinIntegrand_differentiableAt (L : ℂ → ℂ) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) {s : ℂ}
    (hseries : DifferentiableAt ℂ (L) (s+shift σ freq)) :
    DifferentiableAt ℂ (mellinIntegrand L W D σ freq) s := by
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · exact CubicReflectionKernel.compact_source_mellin_differentiable W a b ha hWs hW s
    · exact ((differentiableAt_id.add_const (shift σ freq)).sub_const (1/2)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hD.ne'))
  · exact hseries.comp s (differentiableAt_id.add_const (shift σ freq))

theorem mellinIntegrand_norm (L : ℂ → ℂ) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖mellinIntegrand L W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖L (s+shift σ freq)‖ := by
  unfold mellinIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  simp

theorem mellinIntegrand_vertical_integrable (L : ℂ → ℂ) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (K : ℝ)
    (hd : ∀ t : ℝ, DifferentiableAt ℂ L ((c : ℂ)+t*I+shift σ freq))
    (hb : ∀ t : ℝ, ‖L ((c : ℂ)+t*I+shift σ freq)‖ ≤ K) :
    Integrable (fun t : ℝ => mellinIntegrand L W D σ freq ((c : ℂ)+t*I)) := by
  have hcont : Continuous (fun t : ℝ => mellinIntegrand L W D σ freq ((c : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (mellinIntegrand_differentiableAt L W a b ha hWs hW D σ freq hD
      (hd t)).continuousAt.comp (f := fun x : ℝ => (c : ℂ)+x*I)
    fun_prop
  have hm := (CompletedGauss.compactMellin_vertical_integrable W a b ha hWs hW c).norm
  apply (hm.mul_const (D^(c+σ-1/2)*K)).mono'
    hcont.aestronglyMeasurable
  apply ae_of_all
  intro t
  rw [mellinIntegrand_norm L W D σ freq hD]
  simp only [mellin_vertical_re]
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (hb t)
  positivity

/-- Move the finite vertical segment through a holomorphic rectangle. -/
theorem vertical_segment_shift (F : ℂ → ℂ) (l r T : ℝ)
    (hhol : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T)) :
    (∫ t : ℝ in -T..T, F ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, F ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, F ((x : ℂ)+T*I))) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (F) ((l : ℂ)+(-T)*I) ((r : ℂ)+T*I)
    (by simpa using hhol)
  have hr :
      (∫ x : ℝ in l..r, F ((x : ℂ)+(-T)*I)) -
      (∫ x : ℝ in l..r, F ((x : ℂ)+T*I)) +
      I*(∫ t : ℝ in -T..T, F ((r : ℂ)+t*I)) -
      I*(∫ t : ℝ in -T..T, F ((l : ℂ)+t*I)) = 0 := by
    simpa [smul_eq_mul] using h
  have hh := congrArg (fun z : ℂ => -I*z) hr
  ring_nf at hh ⊢
  simp only [I_sq] at hh
  linear_combination hh

theorem vertical_integral_shift (F : ℂ → ℂ) (l r T : ℝ) (hT : 0≤T)
    (hi : Integrable (fun t : ℝ => F ((r : ℂ)+t*I)))
    (hhol : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T)) :
    (∫ t : ℝ, F ((r : ℂ)+t*I)) =
      (∫ t : ℝ in -T..T, F ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, F ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, F ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, F ((r : ℂ)+t*I) := by
  rw [← integral_add_compl measurableSet_Icc hi, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -T≤T), vertical_segment_shift F l r T hhol]

theorem mellinIntegrand_on_rectangle (L : ℂ → ℂ) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D)
    (hL : ∀ z ∈ (uIcc l r ×ℂ uIcc (-T) T), DifferentiableAt ℂ L (z+shift σ freq)) :
    DifferentiableOn ℂ (mellinIntegrand L W D σ freq) (uIcc l r ×ℂ uIcc (-T) T) :=
  fun z hz => (mellinIntegrand_differentiableAt L W a b ha hWs hW D σ freq hD
    (hL z hz)).differentiableWithinAt

def integrand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

theorem series_norm_le (χ : Character) (inverse : Bool) {b : ℝ} (hb : 1<b)
    {s : ℂ} (hs : b≤s.re) :
    ‖series χ inverse s‖ ≤ HeckeReciprocalBound.bound b := by
  cases inverse
  · exact HeckeStripActual.LFunction_norm_le χ hb hs
  · exact HeckeReciprocalBound.reciprocal_norm_le χ hb hs

theorem series_differentiableAt_right (χ : Character) (inverse : Bool) {s : ℂ}
    (hs : 1<s.re) : DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_differentiableAt χ
      (by intro h; norm_num [h] at hs) (Or.inl (by intro h; norm_num [h] at hs))
  · exact HeckeReciprocal.reciprocal_differentiableAt χ
      (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one hs)

theorem series_differentiableAt_nonprincipal (χ : Character) (hχ : χ.residue≠1)
    (inverse : Bool) {s : ℂ} (hz : inverse=true → LFunction χ s≠0) :
    DifferentiableAt ℂ (series χ inverse) s := by
  cases inverse
  · exact LFunction_entire_nonprincipal χ hχ s
  · have he : series χ true = fun z => (LFunction χ z)⁻¹ := by
      funext z
      simp [series, HeckeReciprocal.reciprocal, hχ]
    rw [he]
    exact (LFunction_entire_nonprincipal χ hχ s).inv (hz rfl)

theorem integrand_norm (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (hD : 0<D) (s : ℂ) :
    ‖integrand χ inverse W D σ freq s‖ =
      ‖mellin W s‖*D^(s.re+σ-1/2)*‖series χ inverse (s+shift σ freq)‖ :=
  mellinIntegrand_norm (series χ inverse) W D σ freq hD s

theorem integrand_vertical_integrable (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0<a) (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D c σ freq : ℝ) (hD : 0<D) (hc : 1<c+σ) :
    Integrable (fun t : ℝ => integrand χ inverse W D σ freq ((c : ℂ)+t*I)) :=
  mellinIntegrand_vertical_integrable (series χ inverse) W a b ha hWs hW D c σ freq hD _
    (fun t => series_differentiableAt_right χ inverse (by simpa using hc))
    (fun t => series_norm_le χ inverse hc (by simp))

theorem polynomial_finite_shift (χ : Character) (hχ : χ.residue≠1) (inverse : Bool)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq l r T : ℝ) (hD : 0<D) (hr : 1<r+σ) (hT : 0≤T)
    (hz : ∀ s ∈ (uIcc l r ×ℂ uIcc (-T) T), inverse=true →
      LFunction χ (s+shift σ freq)≠0) :
    polynomial χ inverse W D σ freq = (1/(2*Real.pi) : ℂ)*
      ((∫ t : ℝ in -T..T, integrand χ inverse W D σ freq ((l : ℂ)+t*I)) +
      I*((∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+(-T)*I)) -
        (∫ x : ℝ in l..r, integrand χ inverse W D σ freq ((x : ℂ)+T*I))) +
      ∫ t : ℝ in (Icc (-T) T)ᶜ, integrand χ inverse W D σ freq ((r : ℂ)+t*I)) := by
  rw [polynomial_mellin χ inverse W a b ha hWs hW D r σ freq hD hr]
  change (1/(2*Real.pi) : ℂ)*(∫ t : ℝ, mellinIntegrand (series χ inverse) W D σ freq ((r : ℂ)+t*I)) = _
  exact congrArg (fun z : ℂ => (1/(2*Real.pi) : ℂ)*z)
    (vertical_integral_shift (mellinIntegrand (series χ inverse) W D σ freq) l r T hT
    (integrand_vertical_integrable χ inverse W a b ha hWs hW D r σ freq hD hr)
    (mellinIntegrand_on_rectangle (series χ inverse) W a b ha hWs hW D σ freq l r T hD
      (fun z hz' => series_differentiableAt_nonprincipal χ hχ inverse (hz z hz'))))

end SevenEighths.HeckeDyadic

end

end OAI
