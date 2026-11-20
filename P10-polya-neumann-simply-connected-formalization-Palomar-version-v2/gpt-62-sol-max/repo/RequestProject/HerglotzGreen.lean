module

public import RequestProject.Herglotz
public import RequestProject.ReconGreen
public import RequestProject.ReconTrace

/-!
# Green's identity for Herglotz waves

For a bounded Lipschitz domain `Ω` with positively oriented boundary parametrization `γ`, the
complex Green formula `∮ F dz = 2i ∫_Ω ∂̄F` extends from compactly supported to bounded
Lipschitz functions (`integral_boundary_eq_dbar_of_bounded`). Applied to products of the
Herglotz coefficients `F_m` (with `∂F_m = -(ik/2) F_{m+1}`, `∂̄F_m = -(ik/2) F_{m-1}`) it gives
the energy identity for Herglotz waves

  `∫₀^{2π} conj(g_a) h_a dθ = (k²/2) ∫_Ω (|F₁|² + |F₋₁|² − 2|F₀|²)
                            = ∫_Ω (|∇u_a|² − k² |u_a|²)`

(`integral_conj_herglotzConormal_mul_wave`), where `h_a = u_a ∘ γ` and `g_a` is the conormal
trace.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ComplexConjugate Real

noncomputable section

namespace PolyaNeumann

/-- `∂̄F = β` when `DF(z) w = α w + β conj(w)`. -/
lemma dbar_eq_of_hasFDerivAt {F : ℂ → ℂ} {L : ℂ →L[ℝ] ℂ} {z α β : ℂ} (hF : HasFDerivAt F L z)
    (hL : ∀ w, L w = α * w + β * conj w) : dbar F z = β := by
  unfold dbar
  rw [hF.fderiv, hL, hL]
  simp only [map_one, mul_one, Complex.conj_I]
  grind [Complex.I_sq]

/-- Green's formula `∮ F dz = 2i ∫_Ω ∂̄F` for bounded Lipschitz `F`. -/
theorem integral_boundary_eq_dbar_of_bounded {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {F : ℂ → ℂ}
    {K : NNReal} (hF : LipschitzWith K F) {C : ℝ} (hC : ∀ z, ‖F z‖ ≤ C) :
    ∫ θ in (0 : ℝ)..(2 * π), F (γ θ) * deriv γ θ = 2 * Complex.I * ∫ z in Ω, dbar F z := by
  obtain ⟨χ, U, hχ, hU, hsub, hχ1⟩ := exists_cutoff_one_bounded hb.closure
  obtain ⟨Kχ, hKχ⟩ := hχ.1.lipschitzWith_of_hasCompactSupport hχ.2.1 (by simp)
  obtain ⟨Cχ, hCχ⟩ := hχ.2.1.exists_bound_of_continuous hχ.1.continuous
  obtain ⟨KG, hKG⟩ := lipschitzWith_mul_of_bounded hKχ hF hCχ hC
  let G (z : ℂ) := χ z * F z
  have hgreen := integral_boundary_eq_dbar hb hL hγ hKG hχ.2.1.mul_right
  have hone : EqOn G F U := fun z hz => by simp [G, hχ1 hz]
  have hint : EqOn (dbar G) (dbar F) Ω := fun z hz => by
    have hev : G =ᶠ[𝓝 z] F := eventually_of_mem (hU.mem_nhds (hsub (subset_closure hz))) hone
    simp only [dbar, hev.fderiv_eq]
  rw [← setIntegral_congr_fun hL.1.1.measurableSet hint, ← hgreen]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  rw [uIcc_of_le Real.two_pi_pos.le] at hθ
  change _ = G (γ θ) * deriv γ θ
  rw [hone (hsub (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ)))]

/-- The derivative of a Herglotz coefficient in Wirtinger form. -/
lemma herglotzCoeff_hasFDerivAt' {a : ℝ → ℂ} (ha : IntervalIntegrable a volume 0 (2 * π))
    (k : ℝ) (m : ℤ) (z : ℂ) :
    HasFDerivAt (herglotzCoeff k a m) (fderiv ℝ (herglotzCoeff k a m) z) z ∧
      ∀ w, fderiv ℝ (herglotzCoeff k a m) z w =
        (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) * w +
          (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) * conj w := by
  refine ⟨(differentiable_herglotzCoeff ha k m z).hasFDerivAt, fun w => ?_⟩
  rw [fderiv_herglotzCoeff_apply ha]
  ring

section

variable {F G : ℂ → ℂ} {LF LG : ℂ →L[ℝ] ℂ} {z αF βF αG βG : ℂ} (hF : HasFDerivAt F LF z) (hFL : ∀ w, LF w = αF * w + βF * conj w) (hG : HasFDerivAt G LG z) (hGL : ∀ w, LG w = αG * w + βG * conj w)
include F G LF LG z αF βF αG βG hF hFL hG hGL

/-- `∂̄` of `conj(F) G` for functions with Wirtinger derivatives. -/
lemma dbar_conj_mul  :
    dbar (fun x => conj (F x) * G x) z = conj (F z) * βG + G z * conj αF := by
  have hcF :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z hF
  have hP := hcF.mul hG
  refine dbar_eq_of_hasFDerivAt (α := conj (F z) * αG + G z * conj βF) hP fun w => ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, hFL, hGL]
  simp  [ContinuousLinearEquiv.coe_coe, map_add, map_mul]
  ring

/-- `∂̄` of `F conj(G)`. -/
lemma dbar_mul_conj  :
    dbar (fun x => F x * conj (G x)) z = F z * conj αG + conj (G z) * βF := by
  have h := dbar_conj_mul hG hGL hF hFL
  grind

end

/-- Split the three adjacent mode contributions to the principal form. -/
lemma integral_herglotzCoeff_main {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k c d : ℝ) :
    (∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + c * ‖herglotzCoeff k a (-1) z‖ ^ 2 -
      d * ‖herglotzCoeff k a 0 z‖ ^ 2)) = (∫ z in Ω, ‖herglotzCoeff k a 1 z‖ ^ 2) +
        c * (∫ z in Ω, ‖herglotzCoeff k a (-1) z‖ ^ 2) - d * ∫ z in Ω, ‖herglotzCoeff k a 0 z‖ ^ 2 := by
  have hI := integrable_herglotzCoeff_sq hb ha k
  rw [integral_sub (f := fun z => ‖herglotzCoeff k a 1 z‖ ^ 2 + c * ‖herglotzCoeff k a (-1) z‖ ^ 2)
      ((hI 1).add ((hI (-1)).const_mul c)) ((hI 0).const_mul d),
    integral_add (hI 1) ((hI (-1)).const_mul c), integral_const_mul, integral_const_mul]

/-- Boundary integrand for neighboring Herglotz coefficients. -/
def herglotzAdjacentBoundary (γ : ℝ → ℂ) (a : ℝ → ℂ) (k : ℝ) (m : ℤ) (θ : ℝ) : ℂ :=
  herglotzCoeff k a (m + 1) (γ θ) * conj (herglotzCoeff k a m (γ θ)) * deriv γ θ

section

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
  {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ}
  (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ)
include hb hL hγ ha k

omit hb hL in
lemma intervalIntegrable_herglotzAdjacentBoundary (m : ℤ) :
    IntervalIntegrable (herglotzAdjacentBoundary γ a k m) volume 0 (2 * π) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  exact intervalIntegrable_comp_mul_deriv hK
    ((continuous_herglotzCoeff ha k (m + 1)).mul
      (Complex.continuous_conj.comp (continuous_herglotzCoeff ha k m)))

/-- Green's formula for a pair of neighboring Herglotz coefficients. -/
lemma integral_herglotzAdjacentBoundary (m : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * π), herglotzAdjacentBoundary γ a k m θ =
      ((k * ∫ z in Ω, ‖herglotzCoeff k a m z‖ ^ 2 - ‖herglotzCoeff k a (m + 1) z‖ ^ 2 : ℝ) : ℂ) := by
  let F := herglotzCoeff k a
  let A := (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..(2 * π), ‖a φ‖
  have hB (m : ℤ) (z : ℂ) : ‖F m z‖ ≤ A := norm_herglotzCoeff_le k m z
  obtain ⟨K, hK⟩ := lipschitzWith_herglotzCoeff ha k (m + 1)
  obtain ⟨L, hL'⟩ := lipschitzWith_herglotzCoeff ha k m
  have hc : ∀ z, ‖conj (F m z)‖ ≤ A := by simpa using hB m
  obtain ⟨M, hM⟩ := lipschitzWith_mul_of_bounded hK
    (Complex.isometry_conj.lipschitz.comp hL') (hB (m + 1)) hc
  let P := fun z => F (m + 1) z * conj (F m z)
  change (∫ θ in (0 : ℝ)..(2 * π), P (γ θ) * deriv γ θ) = _
  rw [integral_boundary_eq_dbar_of_bounded hb hL hγ (F := P) hM (fun z => norm_mul_le_of_le (hB _ z) (hc z))]
  have hd (z : ℂ) : dbar P z = -(Complex.I * k / 2) *
      ((‖F m z‖ ^ 2 - ‖F (m + 1) z‖ ^ 2 : ℝ) : ℂ) := by
    obtain ⟨hm, hmL⟩ := herglotzCoeff_hasFDerivAt' ha k m z
    obtain ⟨hn, hnL⟩ := herglotzCoeff_hasFDerivAt' ha k (m + 1) z
    change dbar (fun w => F (m + 1) w * conj (F m w)) z = _
    rw [dbar_mul_conj hn hnL hm hmL]
    simp only [add_sub_cancel_right, map_mul, map_neg, map_div₀, Complex.conj_I,
      Complex.conj_ofReal, map_ofNat]
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj']
    ring
  simp_rw [hd]
  rw [integral_const_mul, integral_complex_ofReal]
  push_cast
  ring_nf
  simp [F]

end

/-- **Energy identity for Herglotz waves.** With `F_m` the Herglotz coefficients
(`u_a = F₀`, `∂u_a = -(ik/2) F₁`, `∂̄u_a = -(ik/2) F₋₁`, so `|∇u_a|² = (k²/2)(|F₁|² + |F₋₁|²)`),

  `∫₀^{2π} conj(g_a) h_a = (k²/2) ∫_Ω (|F₁|² + |F₋₁|² − 2|F₀|²) = ∫_Ω (|∇u_a|² − k²|u_a|²)`. -/
theorem integral_conj_herglotzConormal_mul_wave {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) {a : ℝ → ℂ}
    (ha : IntervalIntegrable a volume 0 (2 * π)) (k : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), conj (herglotzConormal k a γ θ) * herglotzWave k a (γ θ) =
      ((k ^ 2 / 2 * ∫ z in Ω, (‖herglotzCoeff k a 1 z‖ ^ 2 + ‖herglotzCoeff k a (-1) z‖ ^ 2 -
        2 * ‖herglotzCoeff k a 0 z‖ ^ 2) : ℝ) : ℂ) := by
  have hpt (θ : ℝ) : conj (herglotzConormal k a γ θ) * herglotzWave k a (γ θ) =
      (k / 2 : ℂ) * (herglotzAdjacentBoundary γ a k (-1) θ -
        conj (herglotzAdjacentBoundary γ a k 0 θ)) := by
    rw [herglotzConormal_eq ha, herglotzWave_eq]
    norm_num [herglotzAdjacentBoundary, map_sub, map_mul, map_div₀, map_ofNat]
    ring
  have hi := intervalIntegrable_herglotzAdjacentBoundary hγ ha k
  have hc := intervalIntegrable_conj' (hi 0)
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hi (-1)) hc,
    intervalIntegral.intervalIntegral_conj, integral_herglotzAdjacentBoundary hb hL hγ ha,
    integral_herglotzAdjacentBoundary hb hL hγ ha]
  have hI := integrable_herglotzCoeff_sq hb ha k
  have hm := integral_herglotzCoeff_main hb ha k 1 2
  simp only [one_mul] at hm
  norm_num only [neg_add_cancel, zero_add, Complex.conj_ofReal]
  rw [integral_sub (hI (-1)) (hI 0), integral_sub (hI 0) (hI 1), hm]
  push_cast
  ring

end PolyaNeumann

end
