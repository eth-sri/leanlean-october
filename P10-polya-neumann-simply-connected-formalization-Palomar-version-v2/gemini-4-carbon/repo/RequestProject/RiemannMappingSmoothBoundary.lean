module

public import RequestProject.RiemannMappingInterior
public import RequestProject.JordanWinding
public import RequestProject.WindingJump
public import RequestProject.SmoothDomain
public import RequestProject.LocalConformalH1
public import RequestProject.DiskGeometry
public import RequestProject.SmoothCompactExtension
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.ExtendFrom
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter Complex InnerProductSpace
open scoped Topology ContDiff ComplexConjugate InnerProductSpace RealInnerProductSpace

/-! ### Part 1: Cap winding confinement & full boundary limits -/

private def joinCapArc (P A : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 1 then P u else A (u - 1)

private theorem joinCapArc_lipschitz {P A : ℝ → ℂ} {KP KA : NNReal}
    (hP : LipschitzWith KP P) (hA : LipschitzWith KA A) (hjoin : A 0 = P 1) :
    LipschitzWith (max KP KA) (joinCapArc P A) := by
  have hPK : (KP : ℝ) ≤ (max KP KA : NNReal) := by exact_mod_cast le_max_left KP KA
  have hAK : (KA : ℝ) ≤ (max KP KA : NNReal) := by exact_mod_cast le_max_right KP KA
  have hord (x y : ℝ) (hxy : x ≤ y) :
      dist (joinCapArc P A x) (joinCapArc P A y) ≤ (max KP KA : NNReal) * dist x y := by
    by_cases hy1 : y ≤ 1
    · simp only [joinCapArc, if_pos (hxy.trans hy1), if_pos hy1]
      exact (hP.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right hPK dist_nonneg)
    · by_cases hx1 : x ≤ 1
      · simp only [joinCapArc, if_pos hx1, if_neg hy1]
        have hPx := hP.dist_le_mul x 1
        have hAy := hA.dist_le_mul 0 (y - 1)
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx1), ← hjoin] at hPx
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith [lt_of_not_ge hy1])] at hAy
        have ht := dist_triangle (P x) (P 1) (A (y - 1))
        rw [← hjoin] at ht
        calc _ ≤ (KP : ℝ) * (1 - x) + (KA : ℝ) * (y - 1) := by linarith
          _ ≤ (max KP KA : NNReal) * (1 - x) + (max KP KA : NNReal) * (y - 1) :=
            add_le_add (mul_le_mul_of_nonneg_right hPK (by linarith))
              (mul_le_mul_of_nonneg_right hAK (by linarith [lt_of_not_ge hy1]))
          _ = (max KP KA : NNReal) * dist x y := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
      · simp only [joinCapArc, if_neg hx1, if_neg hy1]
        have h := hA.dist_le_mul (x - 1) (y - 1)
        rw [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq] at h
        exact h.trans (mul_le_mul_of_nonneg_right hAK dist_nonneg)
  exact LipschitzWith.of_dist_le_mul fun x y =>
    (le_total x y).elim (hord x y) fun h => by simpa only [dist_comm] using hord y x h

private theorem joinCapArc_injOn {P A : ℝ → ℂ}
    (hP : InjOn P (Icc 0 1)) (hA : InjOn A (Icc 0 1))
    (hjoin : A 0 = P 1) (hclose : A 1 = P 0)
    (hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1)) :
    InjOn (joinCapArc P A) (Ico 0 2) := by
  have hcross (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Ioo 1 2) : P u ≠ A (v - 1) := fun he => by
    have hv' : v - 1 ∈ Icc 0 1 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · linarith [hv.2, hA (by norm_num : (1 : ℝ) ∈ Icc 0 1) hv' (hclose.trans (by simpa only [← hu0] using he))]
    · rcases lt_or_eq_of_le hu.2 with hu1 | hu1
      · exact Set.disjoint_left.mp hdisj (mem_image_of_mem P ⟨hu0, hu1⟩) ⟨v - 1, hv', he.symm⟩
      · linarith [hv.1, hA (by norm_num : (0 : ℝ) ∈ Icc 0 1) hv' (hjoin.trans (by simpa only [hu1] using he))]
  intro u hu v hv he
  by_cases hu1 : u ≤ 1 <;> by_cases hv1 : v ≤ 1
  · simp only [joinCapArc, if_pos hu1, if_pos hv1] at he; exact hP ⟨hu.1, hu1⟩ ⟨hv.1, hv1⟩ he
  · simp only [joinCapArc, if_pos hu1, if_neg hv1] at he
    exact False.elim (hcross u ⟨hu.1, hu1⟩ v ⟨lt_of_not_ge hv1, hv.2⟩ he)
  · simp only [joinCapArc, if_neg hu1, if_pos hv1] at he
    exact False.elim (hcross v ⟨hv.1, hv1⟩ u ⟨lt_of_not_ge hu1, hu.2⟩ he.symm)
  · simp only [joinCapArc, if_neg hu1, if_neg hv1] at he
    linarith [hA ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩
      ⟨by linarith [lt_of_not_ge hv1], by linarith [hv.2]⟩ he]

private theorem joinCapArc_image {P A : ℝ → ℂ} (hjoin : A 0 = P 1) :
    joinCapArc P A '' Icc 0 2 = P '' Icc 0 1 ∪ A '' Icc 0 1 := by
  ext z; constructor
  · rintro ⟨u, hu, he⟩
    by_cases hu1 : u ≤ 1
    · exact Or.inl ⟨u, ⟨hu.1, hu1⟩, by simpa only [joinCapArc, if_pos hu1] using he⟩
    · exact Or.inr ⟨u - 1, ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩,
        by simpa only [joinCapArc, if_neg hu1] using he⟩
  · rintro (⟨u, hu, he⟩ | ⟨v, hv, he⟩)
    · exact ⟨u, ⟨hu.1, hu.2.trans (by norm_num)⟩, by simpa only [joinCapArc, if_pos hu.2] using he⟩
    · rcases eq_or_lt_of_le hv.1 with hv0 | hv0
      · exact ⟨1, by norm_num, by simpa only [joinCapArc, if_pos (le_refl (1 : ℝ)), ← hjoin, ← hv0] using he⟩
      · exact ⟨v + 1, ⟨by linarith, by linarith [hv.2]⟩,
          by simpa only [joinCapArc, if_neg (by linarith : ¬v + 1 ≤ 1), add_sub_cancel_right] using he⟩

private theorem riemannMapping_notMem_cap_of_source_radius_ne (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} {r a b : ℝ} (hr : 0 ≤ r) (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball (0 : ℂ) 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball (0 : ℂ) 1)) (hGb : G b ∈ frontier (F '' ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hne : ‖z - ζ‖ ≠ r) : F z ∉ G '' Icc a b := by
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
      hF hinj Subset.rfl isOpen_ball
  rintro ⟨θ, hθ, he⟩
  rcases eq_or_lt_of_le hθ.1 with hθa | hθa
  · rw [hopen.frontier_eq] at hGa
    exact hGa.2 ⟨z, hz, by simpa only [← hθa] using he.symm⟩
  · rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · have hs : circleMap ζ r θ = z := hinj (harc ⟨hθa, hθb⟩) hz ((hGeq ⟨hθa, hθb⟩).symm.trans he)
      exact hne (hs ▸ by simpa only [mem_sphere, dist_eq_norm] using circleMap_mem_sphere ζ hr θ)
    · rw [hopen.frontier_eq] at hGb
      exact hGb.2 ⟨z, hz, by simpa only [hθb] using he.symm⟩

private def riemannCapMidpoint (ζ : ℂ) (r : ℝ) : ℂ := (1 - r) • ζ

private theorem riemannCapMidpoint_mem_disk {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) : riemannCapMidpoint ζ r ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith), hζ, mul_one]; linarith

private theorem riemannCap_circle_midpoint {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r : ℝ) :
    circleMap ζ r (riemannCapCenterAngle ζ) = riemannCapMidpoint ζ r := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  simp only [circleMap, he, riemannCapMidpoint, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one]; ring

private theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hdneg : d < 0) : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 := by
  filter_upwards [hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hdneg),
    self_mem_nhdsWithin] with s hs (hspos : 0 < s)
  simp only [zero_add, smul_eq_mul] at hs
  exact sub_neg.mp ((mul_lt_mul_iff_right₀ (inv_pos.mpr hspos)).mp (by simpa only [mul_zero] using hs))

private theorem riemannMapping_winding_normal_values (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ}
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β) (hclosed : β (2 * Real.pi) = β 0)
    (hsub : β '' Icc 0 (2 * Real.pi) ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪ frontier (F '' ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1 ∩ ball ζ r) :
    let q := F (riemannCapMidpoint ζ r)
    let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      windingNumber β (q + s • (Complex.I * T)) = windingNumber β (F z) ∧
      windingNumber β (q - s • (Complex.I * T)) = windingNumber β (F 0) := by
  let Ω := F '' ball (0 : ℂ) 1
  let z₀ := riemannCapMidpoint ζ r
  let q := F z₀
  let N : ℂ := (r : ℂ) * deriv F z₀ * ζ
  have hz₀ : z₀ ∈ ball (0 : ℂ) 1 := riemannCapMidpoint_mem_disk hζ hr hr1
  have hNT : N = Complex.I * riemannCapDerivative F ζ r (riemannCapCenterAngle ζ) := by
    have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
      simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
        using Complex.norm_mul_exp_arg_mul_I (-ζ)
    unfold riemannCapDerivative
    rw [riemannCap_circle_midpoint hζ r]
    unfold riemannInteriorDerivative
    rw [indicator_of_mem hz₀]
    simp only [circleMap, zero_add, he, N]
    calc _ = -(Complex.I * Complex.I) * ((r : ℂ) * deriv F z₀ * ζ) := by rw [Complex.I_mul_I]; ring
      _ = _ := by ring
  obtain ⟨_, _, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have hopen : IsOpen Ω := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hq : q ∈ Ω := ⟨z₀, hz₀, rfl⟩
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  have hJq : J q = z₀ := hJF z₀ hz₀
  have hDF : deriv F z₀ ≠ 0 := RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hz₀
  have hJc : ContinuousAt J q := (hJ.differentiableAt (hopen.mem_nhds hq)).continuousAt
  have hdF : HasDerivAt F (deriv F z₀) (J q) := by
    rw [hJq]; exact (hF.differentiableAt (isOpen_ball.mem_nhds hz₀)).hasDerivAt
  have hdJ : HasDerivAt J (deriv F z₀)⁻¹ q :=
    hdF.of_local_left_inverse hJc hDF (by filter_upwards [hopen.mem_nhds hq] with w hw using hFJ w hw)
  have hdP : HasDerivAt (fun s : ℝ => q + s • N) N 0 := by
    simpa only [one_smul, id] using ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add q
  have hinvN : (deriv F z₀)⁻¹ * N = r • ζ := by
    change (deriv F z₀)⁻¹ * ((r : ℂ) * deriv F z₀ * ζ) = (r : ℂ) * ζ; field_simp [hDF]
  have hdJP : HasDerivAt (fun s : ℝ => J (q + s • N)) (r • ζ) 0 := by
    simpa only [Function.comp_def, hinvN] using hdJ.comp_of_eq 0 hdP (by simp)
  have hJP0 : J (q + (0 : ℝ) • N) = z₀ := by simpa using hJq
  have hzsub : z₀ - ζ = (-r) • ζ := by
    change (1 - r) • ζ - ζ = (-r) • ζ; rw [sub_smul, one_smul, neg_smul]; abel
  have hsqD : HasDerivAt (fun s : ℝ => ‖J (q + s • N) - ζ‖ ^ 2) (-2 * r ^ 2) 0 := by
    have h := (hdJP.sub_const ζ).norm_sq
    rw [hJP0, hzsub, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hζ] at h
    convert h using 1; ring
  have hsq0 : ‖J (q + (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by
    rw [hJP0, hzsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr, hζ, mul_one]
  have hplus : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖J (q + s • N) - ζ‖ ^ 2 < r ^ 2 := by
    simpa only [hsq0] using eventually_lt_of_hasDerivAt_neg hsqD (by nlinarith [sq_pos_of_pos hr])
  have hsqMinusD : HasDerivAt (fun s : ℝ => -‖J (q - s • N) - ζ‖ ^ 2) (-2 * r ^ 2) 0 := by
    have h := (hsqD.comp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)).neg
    convert h using 1
    · funext s; simp only [Function.comp_def, Pi.neg_apply, neg_smul, sub_eq_add_neg]
    · ring
  have hminus : ∀ᶠ s in 𝓝[>] (0 : ℝ), r ^ 2 < ‖J (q - s • N) - ζ‖ ^ 2 := by
    filter_upwards [eventually_lt_of_hasDerivAt_neg hsqMinusD (by nlinarith [sq_pos_of_pos hr])] with s hs
    have h0 : ‖J (q - (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by simpa using hsq0
    linarith
  have hdot₀ : ‖J q‖ ^ 2 < ⟪J q, ζ⟫_ℝ := by
    rw [hJq]
    simp only [z₀, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - r), hζ, mul_one, real_inner_smul_left,
      real_inner_self_eq_norm_sq]; nlinarith
  have hminusC : ContinuousAt (fun s : ℝ => J (q - s • N)) 0 := hJc.comp_of_eq (by fun_prop) (by simp)
  have hdotE : ∀ᶠ s in 𝓝 (0 : ℝ), ‖J (q - s • N)‖ ^ 2 < ⟪J (q - s • N), ζ⟫_ℝ := by
    have hc : ContinuousAt (fun s : ℝ => ⟪J (q - s • N), ζ⟫_ℝ - ‖J (q - s • N)‖ ^ 2) 0 :=
      (hminusC.inner continuousAt_const).sub (hminusC.norm.pow 2)
    have h0 : (0 : ℝ) < ⟪J (q - (0 : ℝ) • N), ζ⟫_ℝ - ‖J (q - (0 : ℝ) • N)‖ ^ 2 := by
      simpa only [zero_smul, sub_zero] using sub_pos.mpr hdot₀
    exact (hc.tendsto.eventually (eventually_gt_nhds h0)).mono fun _ hs => sub_pos.mp hs
  have hΩplus : ∀ᶠ s in 𝓝 (0 : ℝ), q + s • N ∈ Ω :=
    (by simpa only [zero_smul, add_zero] using hdP.continuousAt.tendsto :
      Tendsto (fun s : ℝ => q + s • N) (𝓝 0) (𝓝 q)).eventually (hopen.mem_nhds hq)
  have hΩminus : ∀ᶠ s in 𝓝 (0 : ℝ), q - s • N ∈ Ω := by
    have hp : ContinuousAt (fun s : ℝ => q - s • N) 0 := by fun_prop
    exact (by simpa only [zero_smul, sub_zero] using hp.tendsto :
      Tendsto (fun s : ℝ => q - s • N) (𝓝 0) (𝓝 q)).eventually (hopen.mem_nhds hq)
  change ∀ᶠ s in 𝓝[>] (0 : ℝ),
    windingNumber β (q + s • (Complex.I * riemannCapDerivative F ζ r (riemannCapCenterAngle ζ))) = _ ∧
    windingNumber β (q - s • (Complex.I * riemannCapDerivative F ζ r (riemannCapCenterAngle ζ))) = _
  rw [← hNT]
  filter_upwards [hplus, hminus, hdotE.filter_mono nhdsWithin_le_nhds,
    hΩplus.filter_mono nhdsWithin_le_nhds, hΩminus.filter_mono nhdsWithin_le_nhds]
    with s hsplus hsminus hsdot hsΩplus hsΩminus
  refine ⟨?_, ?_⟩
  · have hsin : J (q + s • N) ∈ ball (0 : ℂ) 1 ∩ ball ζ r :=
      ⟨hJm hsΩplus, by rw [mem_ball, dist_eq_norm]; exact (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsplus⟩
    let S := F '' (ball (0 : ℂ) 1 ∩ ball ζ r)
    have hSc : IsPreconnected S :=
      ((convex_ball (0 : ℂ) 1).inter (convex_ball ζ r)).isPreconnected.image F
        (hF.continuousOn.mono inter_subset_left)
    have hdisj : Disjoint S (β '' Icc 0 (2 * Real.pi)) := Set.disjoint_left.mpr fun v ⟨x, hx, hFx⟩ hvβ => by
      rcases hsub hvβ with hvcap | hvfront
      · exact riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr.le harc hGeq hGa hGb
          hx.1 (ne_of_lt (by simpa only [mem_ball, dist_eq_norm] using hx.2)) (hFx.symm ▸ hvcap)
      · rw [hopen.frontier_eq] at hvfront; exact hvfront.2 ⟨x, hx.1, hFx⟩
    simpa only [hFJ _ hsΩplus] using
      windingNumber_const_of_isPreconnected hKB hclosed hSc hdisj ⟨_, hsin, rfl⟩ ⟨z, hz, rfl⟩
  · let w := J (q - s • N)
    have hwD : w ∈ ball (0 : ℂ) 1 := hJm hsΩminus
    have hfar : r < ‖w - ζ‖ := (sq_lt_sq₀ hr.le (norm_nonneg _)).mp hsminus
    have hm : MapsTo (fun t : ℝ => t • w) (Icc 0 1) (ball (0 : ℂ) 1) := fun t ht => by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg w) ht.2).trans_lt (mem_ball_zero_iff.mp hwD)
    let P : ℝ → ℂ := fun t => F (t • w)
    have hPc : ContinuousOn P (Icc 0 1) := hF.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hm
    have hdisj : Disjoint (P '' Icc 0 1) (β '' Icc 0 (2 * Real.pi)) :=
      Set.disjoint_left.mpr fun u ⟨t, ht, htu⟩ huβ => by
        rcases hsub huβ with hucap | hufront
        · have hrad : ‖w - ζ‖ ≤ ‖t • w - ζ‖ := by
            have heq : ‖t • w - ζ‖ ^ 2 - ‖w - ζ‖ ^ 2 =
                (1 - t) * (2 * ⟪w, ζ⟫_ℝ - (1 + t) * ‖w‖ ^ 2) := by
              rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg ht.1, real_inner_smul_left]; ring
            have hnon : 0 ≤ 2 * ⟪w, ζ⟫_ℝ - (1 + t) * ‖w‖ ^ 2 := by
              nlinarith [hsdot.le, mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg ‖w‖)]
            exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
              (by linarith [mul_nonneg (sub_nonneg.mpr ht.2) hnon])
          dsimp only [P] at htu
          exact riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr.le harc hGeq hGa hGb
            (hm ht) (hfar.trans_le hrad).ne' (htu.symm ▸ hucap)
        · rw [hopen.frontier_eq] at hufront; exact hufront.2 ⟨t • w, hm ht, htu⟩
    have hwF : F w = q - s • N := hFJ _ hsΩminus
    simpa only [hwF] using
      windingNumber_const_of_isPreconnected hKB hclosed (isPreconnected_Icc.image P hPc) hdisj
        ⟨1, by norm_num, by simp [P, hwF]⟩ ⟨0, by norm_num, by simp [P]⟩

private theorem exists_graph_of_local_regular_arc {G V : ℝ → ℂ}
    (hGc : Continuous G) {a t b : ℝ} (ht : t ∈ Ioo a b)
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ)
    (hVc : ContinuousAt V t) (hV : V t ≠ 0)
    (havoid : ∀ θ ∈ Icc a b, θ ≠ t → G θ ≠ G t) :
    ∃ d : ℝ, 0 < d ∧ ∃ f : ℝ → ℝ, ∀ θ ∈ Icc a b,
      ‖G θ - G t‖ < d → ((V t)⁻¹ * (G θ - G t)).im = f ((V t)⁻¹ * (G θ - G t)).re := by
  classical
  let c := (V t)⁻¹
  let x : ℝ → ℝ := fun θ => (c * (G θ - G t)).re
  let xd : ℝ → ℝ := fun θ => (c * V θ).re
  have hxd : ContinuousAt xd t := Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hVc)
  have hxd0 : xd t = 1 := by simp only [xd, c, inv_mul_cancel₀ hV, Complex.one_re]
  have hpos : ∀ᶠ θ in 𝓝 t, 0 < xd θ :=
    hxd.tendsto.eventually (eventually_gt_nhds (by rw [hxd0]; exact one_pos))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (hpos.and (isOpen_Ioo.mem_nhds ht))
  let η := ρ / 2
  have hη : 0 < η := half_pos hρ
  have hηρ : η < ρ := by dsimp [η]; linarith
  have hnear (θ : ℝ) (hθ : θ ∈ Icc (t - η) (t + η)) : 0 < xd θ ∧ θ ∈ Ioo a b :=
    hρsub (by rw [mem_ball, Real.dist_eq]
              exact (abs_le.mpr ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ : |θ - t| ≤ η).trans_lt hηρ)
  have hdx (θ : ℝ) (hθ : θ ∈ Ioo a b) : HasDerivAt x (xd θ) θ := by
    simpa only [x, xd, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (((hd θ hθ).sub_const (G t)).const_mul c)
  have hxc : Continuous x := Complex.continuous_re.comp (continuous_const.mul (hGc.sub continuous_const))
  have hxmono : StrictMonoOn x (Icc (t - η) (t + η)) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hxc.continuousOn fun θ hθ => by
      have hn := hnear θ (interior_subset hθ); rw [(hdx θ hn.2).deriv]; exact hn.1
  let f : ℝ → ℝ := fun y => (c * (G (Function.invFunOn x (Icc (t - η) (t + η)) y) - G t)).im
  have hgraph (θ : ℝ) (hθ : θ ∈ Icc (t - η) (t + η)) :
      (c * (G θ - G t)).im = f (c * (G θ - G t)).re := by
    have hp : Function.invFunOn x (Icc (t - η) (t + η)) (x θ) ∈ Icc (t - η) (t + η) ∧
        x (Function.invFunOn x (Icc (t - η) (t + η)) (x θ)) = x θ :=
      Function.invFunOn_pos ⟨θ, hθ, rfl⟩
    change _ = (c * (G (Function.invFunOn x (Icc (t - η) (t + η)) (x θ)) - G t)).im
    rw [hxmono.injOn hp.1 hθ hp.2]
  obtain ⟨d₁, hd₁, hfar₁⟩ := exists_pos_le_norm_sub hGc (a := a) (b := t - η) fun θ hθ =>
    havoid θ ⟨hθ.1, by linarith [hθ.2, ht.2, hη]⟩ (fun he => by rw [he] at hθ; linarith [hθ.2, hη])
  obtain ⟨d₂, hd₂, hfar₂⟩ := exists_pos_le_norm_sub hGc (a := t + η) (b := b) fun θ hθ =>
    havoid θ ⟨by linarith [hθ.1, ht.1, hη], hθ.2⟩ (fun he => by rw [he] at hθ; linarith [hθ.1, hη])
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, f, fun θ hθ hsmall => hgraph θ ⟨?_, ?_⟩⟩
  · by_contra hn
    exact not_lt_of_ge (hfar₁ θ ⟨hθ.1, (lt_of_not_ge hn).le⟩) (hsmall.trans_le (min_le_left _ _))
  · by_contra hn
    exact not_lt_of_ge (hfar₂ θ ⟨(lt_of_not_ge hn).le, hθ.2⟩) (hsmall.trans_le (min_le_right _ _))

private theorem riemannMapping_cap_loop_local_graph (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    {β : ℝ → ℂ}
    (hsub : β '' Icc 0 (2 * Real.pi) ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪ frontier (F '' ball (0 : ℂ) 1)) :
    let q := F (riemannCapMidpoint ζ r)
    let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
    T ≠ 0 ∧ ∃ d : ℝ, 0 < d ∧ ∃ f : ℝ → ℝ, ∀ w ∈ β '' Icc 0 (2 * Real.pi),
      ‖w - q‖ < d → (T⁻¹ * (w - q)).im = f (T⁻¹ * (w - q)).re := by
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let t := riemannCapCenterAngle ζ
  let q := F (riemannCapMidpoint ζ r)
  let T := riemannCapDerivative F ζ r t
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : t ∈ Ioo a b := ⟨by dsimp [a, t]; linarith, by dsimp [b, t]; linarith⟩
  obtain ⟨_, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have htm : circleMap ζ r t ∈ ball (0 : ℂ) 1 := harc ht
  have hT : T ≠ 0 := riemannCapDerivative_ne_zero_interior F hF hinj ζ hr t htm
  have hGq : G t = q := (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
      hF hinj Subset.rfl isOpen_ball
  have hq : q ∈ F '' ball (0 : ℂ) 1 := ⟨riemannCapMidpoint ζ r, riemannCapMidpoint_mem_disk hζ hr hr1, rfl⟩
  have hGinj : InjOn G (Ico a b) := riemannMapping_cap_injOn_Ico F hF hinj hr.ne' (by linarith) harc hGeq hGa
  have havoid (θ : ℝ) (hθ : θ ∈ Icc a b) (hθt : θ ≠ t) : G θ ≠ G t := fun he => by
    rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · exact hθt (hGinj ⟨hθ.1, hθb⟩ ⟨ht.1.le, ht.2⟩ he)
    · rw [hopen.frontier_eq] at hGb
      exact hGb.2 ((by simpa only [hθb, hGq] using he : G b = q).symm ▸ hq)
  have hd (θ : ℝ) (hθ : θ ∈ Ioo a b) : HasDerivAt G (riemannCapDerivative F ζ r θ) θ :=
    (riemannCapDerivative_hasDerivAt F hF ζ r θ (harc hθ)).congr_of_eventuallyEq
      (by filter_upwards [isOpen_Ioo.mem_nhds hθ] with u hu using hGeq hu)
  obtain ⟨d₁, hd₁, f, hgraph⟩ := exists_graph_of_local_regular_arc hGc ht hd
    (riemannCapDerivative_continuousAt_interior F hF ζ r t htm) hT havoid
  obtain ⟨d₂, hd₂, hball⟩ := Metric.isOpen_iff.mp hopen q hq
  refine ⟨hT, min d₁ d₂, lt_min hd₁ hd₂, f, fun w hw hsmall => ?_⟩
  rcases hsub hw with ⟨θ, hθ, he⟩ | hwfront
  · simpa only [hGq, he] using hgraph θ hθ (by rw [hGq, he]; exact hsmall.trans_le (min_le_left _ _))
  · rw [hopen.frontier_eq] at hwfront
    exact False.elim (hwfront.2 (hball (by rw [mem_ball, dist_eq_norm]; exact hsmall.trans_le (min_le_right _ _))))

private theorem windingNumber_shift {β : ℝ → ℂ}
    (hper : Function.Periodic β (2 * Real.pi)) (t : ℝ) (w : ℂ) :
    windingNumber (fun θ => β (θ + t)) w = windingNumber β w := by
  have hdper : Function.Periodic (deriv β) (2 * Real.pi) := deriv_periodic hper
  have hp : Function.Periodic (fun θ => deriv β θ / (β θ - w)) (2 * Real.pi) := fun θ => by
    change deriv β (θ + 2 * Real.pi) / (β (θ + 2 * Real.pi) - w) = deriv β θ / (β θ - w)
    rw [hdper θ, hper θ]
  have hd : deriv (fun θ => β (θ + t)) = fun θ => deriv β (θ + t) :=
    funext fun θ => deriv_comp_add_const β t θ
  unfold windingNumber; congr 1; rw [hd]
  change (∫ θ in 0..2 * Real.pi, deriv β (θ + t) / (β (θ + t) - w)) =
    ∫ θ in 0..2 * Real.pi, deriv β θ / (β θ - w)
  rw [intervalIntegral.integral_comp_add_right (fun θ => deriv β θ / (β θ - w)) t]
  simpa only [zero_add, add_zero, add_comm] using hp.intervalIntegral_add_eq t 0

private theorem windingNumber_jump_of_local_image_graph {β : ℝ → ℂ} {KB : NNReal}
    (hKB : LipschitzWith KB β) (hper : Function.Periodic β (2 * Real.pi))
    (hinj : InjOn β (Ico 0 (2 * Real.pi))) {t : ℝ} {q T : ℂ}
    (ht : β t = q) (hT : T ≠ 0) {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hgraph : ∀ w ∈ β '' Icc 0 (2 * Real.pi), ‖w - q‖ < d →
      (T⁻¹ * (w - q)).im = f (T⁻¹ * (w - q)).re) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ Tendsto (fun s : ℝ =>
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T))) (𝓝[>] 0) (𝓝 σ) := by
  let ρ : ℝ → ℂ := fun θ => T⁻¹ * (β (θ + t) - q)
  have hρK : LipschitzWith (‖T⁻¹‖₊ * KB) ρ := LipschitzWith.of_dist_le_mul fun x y => by
    have he : ρ x - ρ y = T⁻¹ * (β (x + t) - β (y + t)) := by dsimp [ρ]; ring
    have hb : ‖β (x + t) - β (y + t)‖ ≤ (KB : ℝ) * dist x y := by
      simpa only [dist_eq_norm, Real.dist_eq, add_sub_add_right_eq_sub] using hKB.dist_le_mul (x + t) (y + t)
    rw [dist_eq_norm, he, norm_mul]
    exact (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans
      (by simp only [NNReal.coe_mul, coe_nnnorm]; ring_nf; rfl)
  have hρper : Function.Periodic ρ (2 * Real.pi) := fun θ => by
    dsimp [ρ]; rw [show (θ + 2 * Real.pi) + t = (θ + t) + 2 * Real.pi by ring, hper]
  have hρ0 : ρ 0 = 0 := by simp only [ρ, zero_add, ht, sub_self, mul_zero]
  have hβc : Continuous β := hKB.continuous
  have hn : ContinuousAt (fun θ : ℝ => ‖β (θ + t) - q‖) 0 := by fun_prop
  have he : ∀ᶠ θ in 𝓝 (0 : ℝ), ‖β (θ + t) - q‖ < d :=
    hn.tendsto.eventually (eventually_lt_nhds (by simp only [zero_add, ht, sub_self, norm_zero]; exact hd))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp he
  let η := min (δ / 2) (Real.pi / 2)
  have hη : 0 < η := lt_min (half_pos hδ) (half_pos Real.pi_pos)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hηπ : η < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hg (θ : ℝ) (hθ : θ ∈ Icc (-η) η) : (ρ θ).im = f (ρ θ).re := by
    refine hgraph _ ⟨toIcoMod Real.two_pi_pos 0 (θ + t), ?_, by rw [toIcoMod, hper.sub_zsmul_eq]⟩ ?_
    · have hm := toIcoMod_mem_Ico Real.two_pi_pos 0 (θ + t); rw [zero_add] at hm; exact Ico_subset_Icc_self hm
    · exact hδsub (by rw [mem_ball, Real.dist_eq, sub_zero]; exact (abs_le.mpr ⟨hθ.1, hθ.2⟩).trans_lt hηδ)
  have hρinj : InjOn ρ (Icc (-η) η) := fun x hx y hy heq => by
    have heq' : β (x + t) = β (y + t) := by
      linear_combination mul_left_cancel₀ (inv_ne_zero hT) heq
    have habs : |(x + t) - (y + t)| < 2 * Real.pi := by
      rw [add_sub_add_right_eq_sub]
      exact (abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩ : |x - y| ≤ 2 * η).trans_lt (by linarith)
    linarith [jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq' habs]
  have hfar (θ : ℝ) (hθ : θ ∈ Icc η (2 * Real.pi - η)) : ρ θ ≠ 0 := fun heq => by
    have hh : β (θ + t) = q := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left (inv_ne_zero hT))
    have habs : |(θ + t) - t| < 2 * Real.pi := by
      rw [add_sub_cancel_right, abs_of_pos (hη.trans_le hθ.1)]; linarith [hθ.2]
    linarith [hη.trans_le hθ.1, jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (hh.trans ht.symm) habs]
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump hρK hρper hη hηπ hρ0 hg hρinj hfar
  have hw (s : ℝ) : windingNumber ρ ((s : ℂ) * Complex.I) = windingNumber β (q + s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1; simp only [Complex.real_smul]; ring
  have hw' (s : ℝ) : windingNumber ρ (-((s : ℂ) * Complex.I)) = windingNumber β (q - s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1; simp only [Complex.real_smul]; ring
  exact ⟨σ, hσ, by simpa only [hw, hw'] using hlim⟩

private theorem riemannMapping_cap_image_subset_ball (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) (hinj : InjOn F (ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈ frontier (F '' ball (0 : ℂ) 1))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hper : Function.Periodic β (2 * Real.pi)) (hβinj : InjOn β (Ico 0 (2 * Real.pi)))
    (hcap : G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ⊆ β '' Icc 0 (2 * Real.pi))
    (hsub : β '' Icc 0 (2 * Real.pi) ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪ frontier (F '' ball (0 : ℂ) 1))
    (hzero : windingNumber β (F 0) = 0) {p : ℂ} {R : ℝ}
    (hball : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖β θ - p‖ < R) :
    F '' (ball (0 : ℂ) 1 ∩ ball ζ r) ⊆ ball p R := by
  rintro w ⟨z, hz, rfl⟩
  rw [mem_ball, dist_eq_norm]
  by_contra hn
  have hclosed : β (2 * Real.pi) = β 0 := by simpa only [zero_add] using hper 0
  have hwind := windingNumber_eq_zero_of_image_ball hKB hclosed hball
    (by simpa only [norm_sub_rev] using le_of_not_gt hn)
  let q := F (riemannCapMidpoint ζ r)
  let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : riemannCapCenterAngle ζ ∈
      Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) := ⟨by linarith, by linarith⟩
  have hGq : G (riemannCapCenterAngle ζ) = q :=
    (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  obtain ⟨t, _, hβt⟩ := hcap ⟨riemannCapCenterAngle ζ, Ioo_subset_Icc_self ht, hGq⟩
  obtain ⟨hT, d, hd, f, hg⟩ :=
    riemannMapping_cap_loop_local_graph F hF hinj hζ hr hr1 hGc hGeq hGa hGb hsub
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump_of_local_image_graph hKB hper hβinj hβt hT hd hg
  have he := riemannMapping_winding_normal_values F hF hinj hζ hr hr1 hGeq hGa hGb hKB hclosed hsub hz
  have hconst : Tendsto (fun s : ℝ =>
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T))) (𝓝[>] 0) (𝓝 (windingNumber β (F z))) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [he] with s hs
      dsimp only [q, T]; rw [hs.1, hs.2, hzero, sub_zero])
  have hvalue : windingNumber β (F z) = σ := tendsto_nhds_unique hconst hlim
  rw [hwind] at hvalue
  rcases hσ with rfl | rfl <;> norm_num at hvalue

private theorem riemannMapping_exists_small_cap_region_of_simplyConnected
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r R : ℝ) (p : ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ 0 < R ∧ R < ε ∧
      p ∈ frontier Ω ∧ F '' (ball (0 : ℂ) 1 ∩ ball ζ r) ⊆ ball p R := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hγinj, hγimage⟩ :=
    exists_jordanParam_of_isPreconnected_frontier hb hL
      (isPreconnected_frontier_of_simplyConnected hb hL hsc)
  have hbF : Bornology.IsBounded (F '' ball (0 : ℂ) 1) := himage.symm ▸ hb
  have hopen : IsOpen (F '' ball (0 : ℂ) 1) := himage.symm ▸ hL.1.1
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (F 0) ⟨0, by simp, rfl⟩
  let R := min ε ρ / 2
  have hR : 0 < R := half_pos (lt_min hε hρ)
  have hRε : R < ε := by dsimp [R]; linarith [min_le_left ε ρ]
  have hRρ : R ≤ ρ := by dsimp [R]; linarith [min_le_right ε ρ]
  obtain ⟨η, hη, hshort⟩ := jordanParam_exists_short_arc hK hper hγinj hR
  let ξ := min (η / 2) R
  obtain ⟨r, G, τ, H, hr, hrδ, hr1, hGc, hHlip, hLlen, hLξ,
    hGeq, hGa, hGb, hτm, hτr, hH, hH0, hHL, hHim, hHi⟩ :=
    riemannMapping_exists_small_lipschitz_cap F hF hinj hbF hζ hδ (lt_min (half_pos hη) hR)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let L := riemannCapArcLength F ζ r a b
  obtain ⟨_, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have hLR : L < R := hLξ.trans_le (min_le_right _ _)
  have hLp : R ≤ ‖G a - F 0‖ := by
    have hnot : G a ∉ F '' ball (0 : ℂ) 1 := by rw [hopen.frontier_eq] at hGa; exact hGa.2
    exact hRρ.trans (le_of_not_gt fun h => hnot (hball (by rwa [mem_ball, dist_eq_norm])))
  have hHsmall (u : ℝ) (hu : u ∈ Icc 0 L) : ‖H u - G a‖ < R := by
    have h := hHlip.dist_le_mul u 0
    rw [dist_eq_norm, hH0, Real.dist_eq, sub_zero, abs_of_nonneg hu.1, NNReal.coe_one, one_mul] at h
    exact (h.trans hu.2).trans_lt hLR
  have hfinish {Γ : ℝ → ℂ} {T : ℝ} {C : NNReal} (hΓ : LipschitzWith C Γ)
      (hT : 0 < T) (hcl : Γ T = Γ 0) (hΓi : InjOn Γ (Ico 0 T))
      (hcap : G '' Icc a b ⊆ Γ '' Icc 0 T)
      (hsub : Γ '' Icc 0 T ⊆ G '' Icc a b ∪ frontier (F '' ball (0 : ℂ) 1))
      (hsmall : ∀ u ∈ Icc 0 T, ‖Γ u - G a‖ < R) :
      ∃ (r' R' : ℝ) (p : ℂ), 0 < r' ∧ r' < δ ∧ r' < 1 ∧ 0 < R' ∧ R' < ε ∧
        p ∈ frontier Ω ∧ F '' (ball (0 : ℂ) 1 ∩ ball ζ r') ⊆ ball p R' := by
    obtain ⟨β, ⟨KB, hKB⟩, hp, hii, him⟩ := exists_periodic_of_loop hΓ hT hcl hΓi
    have hβsmall (s : ℝ) (hs : s ∈ Icc 0 (2 * Real.pi)) : ‖β s - G a‖ < R := by
      obtain ⟨u, hu, he⟩ := him ▸ mem_image_of_mem β hs; exact he ▸ hsmall u hu
    have hw := windingNumber_eq_zero_of_image_ball hKB (by simpa using hp 0) hβsmall hLp
    exact ⟨r, R, G a, hr, hrδ, hr1, hR, hRε, himage ▸ hGa,
      riemannMapping_cap_image_subset_ball F hF hinj hζ hr hr1 hGc hGeq hGa hGb
        hKB hp hii (by rwa [him]) (by rwa [him]) hw hβsmall⟩
  by_cases hend : G a = G b
  · exact hfinish hHlip hLlen (by rw [hHL, hH0]; exact hend.symm) hHi
      (by rw [hHim]) (by rw [hHim]; exact subset_union_left) hHsmall
  · have hnear : ‖G b - G a‖ < η := by
      have hd := hHlip.dist_le_mul L 0
      rw [dist_eq_norm, hHL, hH0, Real.dist_eq, sub_zero, abs_of_pos hLlen, NNReal.coe_one, one_mul] at hd
      linarith [hLξ.trans_le (min_le_left (η / 2) R)]
    obtain ⟨A, KA, hA, hA0, hA1, hAm, hAd, hAi⟩ :=
      hshort (G b) (by rwa [hγimage, ← himage]) (G a) (by rwa [hγimage, ← himage]) hnear
    have hAf : MapsTo A (Icc 0 1) (frontier (F '' ball (0 : ℂ) 1)) := by
      simpa only [hγimage, ← himage] using hAm
    have hGi := riemannMapping_cap_injOn_Icc F hF hinj hr.ne' (by linarith) harc hGeq hGa hGb hend
    have hHic : InjOn H (Icc 0 L) := fun u hu v hv he => by
      have hτuv := hGi (hτm u) (hτm v) ((hH u).symm.trans (he.trans (hH v)))
      have hru := hτr u hu; rw [hτuv] at hru; exact hru.symm.trans (hτr v hv)
    let P : ℝ → ℂ := fun u => H (L * u)
    have hP0 : P 0 = G a := by simpa only [P, mul_zero] using hH0
    have hP1 : P 1 = G b := by simpa only [P, mul_one] using hHL
    have hPlip : LipschitzWith (Real.toNNReal L) P := LipschitzWith.of_dist_le_mul fun u v => by
      have h := hHlip.dist_le_mul (L * u) (L * v)
      have hLpos : 0 < L := hLlen
      simpa only [P, NNReal.coe_one, one_mul, Real.coe_toNNReal _ hLpos.le,
        Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hLpos] using h
    have hPim : P '' Icc 0 1 = H '' Icc 0 L := by
      ext z; constructor
      · rintro ⟨u, hu, rfl⟩; exact ⟨L * u, ⟨mul_nonneg hLlen.le hu.1, mul_le_of_le_one_right hLlen.le hu.2⟩, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u / L, ⟨div_nonneg hu.1 hLlen.le, (div_le_one hLlen).mpr hu.2⟩,
          by change H (L * (u / L)) = H u; rw [mul_div_cancel₀ _ hLlen.ne']⟩
    have hPic : InjOn P (Icc 0 1) := fun u hu v hv he => mul_left_cancel₀ hLlen.ne' <|
      hHic ⟨mul_nonneg hLlen.le hu.1, mul_le_of_le_one_right hLlen.le hu.2⟩
        ⟨mul_nonneg hLlen.le hv.1, mul_le_of_le_one_right hLlen.le hv.2⟩ he
    have hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1) :=
      Set.disjoint_left.mpr fun z ⟨u, hu, hPu⟩ ⟨v, hv, hAv⟩ => by
        have hLu : L * u ∈ Ioo 0 L := ⟨mul_pos hLlen hu.1, mul_lt_of_lt_one_right hLlen hu.2⟩
        have hθm := hτm (L * u)
        have hθr := hτr (L * u) (Ioo_subset_Icc_self hLu)
        have hθi : τ (L * u) ∈ Ioo a b :=
          ⟨lt_of_le_of_ne hθm.1 fun he => by
              rw [← he, riemannCapArcLength, intervalIntegral.integral_same] at hθr; linarith [hLu.1],
            lt_of_le_of_ne hθm.2 fun he => by rw [he] at hθr; linarith [hLu.2]⟩
        have hzΩ : z ∈ F '' ball (0 : ℂ) 1 :=
          ⟨circleMap ζ r (τ (L * u)), harc hθi, (hGeq hθi).symm.trans ((hH _).symm.trans hPu)⟩
        have hzf : z ∈ frontier (F '' ball (0 : ℂ) 1) := hAv ▸ hAf hv
        rw [hopen.frontier_eq] at hzf; exact hzf.2 hzΩ
    let Γ := joinCapArc P A
    have hΓcl : Γ 2 = Γ 0 := by
      simp only [Γ, joinCapArc, if_neg (by norm_num : ¬(2 : ℝ) ≤ 1),
        if_pos (by norm_num : (0 : ℝ) ≤ 1), show (2 : ℝ) - 1 = 1 by norm_num, hA1, hP0]
    have hΓim : Γ '' Icc 0 2 = G '' Icc a b ∪ A '' Icc 0 1 := by
      rw [joinCapArc_image (hA0.trans hP1.symm), hPim, hHim]
    exact hfinish (joinCapArc_lipschitz hPlip hA (hA0.trans hP1.symm)) (by norm_num : (0 : ℝ) < 2) hΓcl
      (joinCapArc_injOn hPic (hAi (Ne.symm hend)) (hA0.trans hP1.symm) (hA1.trans hP0.symm) hdisj)
      (by rw [hΓim]; exact subset_union_left)
      (by rw [hΓim]; exact union_subset subset_union_left fun z ⟨u, hu, hzu⟩ => Or.inr (hzu ▸ hAf hu))
      fun u hu => by
        by_cases hu1 : u ≤ 1
        · simp only [Γ, joinCapArc, if_pos hu1, P]
          exact hHsmall (L * u) ⟨mul_nonneg hLlen.le hu.1, mul_le_of_le_one_right hLlen.le hu1⟩
        · simp only [Γ, joinCapArc, if_neg hu1]; rw [← hA1]
          exact hAd (u - 1) ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩ 1 (by norm_num)

private theorem riemannMapping_exists_unique_boundary_limit
    {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃! p : ℂ, p ∈ frontier Ω ∧ Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
  have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff, hζ]
  letI : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have hC : Cauchy (Filter.map F (𝓝[ball (0 : ℂ) 1] ζ)) := by
    refine Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨r, R, p, hr, _, _, _, hRε, _, hcap⟩ :=
      riemannMapping_exists_small_cap_region_of_simplyConnected hb hL hsc F hF hinj
        himage hζ zero_lt_one (half_pos hε)
    refine ⟨ball p R, ?_, fun x hx y hy => ?_⟩
    · change F ⁻¹' ball p R ∈ 𝓝[ball (0 : ℂ) 1] ζ
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds ζ hr)] with z hz hzcap
      exact hcap ⟨z, ⟨hz, hzcap⟩, rfl⟩
    · rw [mem_ball] at hx hy
      have hpy : dist p y < R := by rwa [dist_comm]
      linarith [dist_triangle x p y]
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have hpf : p ∈ frontier Ω := by
    rw [← himage]
    exact riemannMapping_limit_mem_frontier (l := 𝓝[ball (0 : ℂ) 1] ζ) (z := id)
      F hF hinj hζ self_mem_nhdsWithin (tendsto_id.mono_left nhdsWithin_le_nhds) hp
  exact ⟨p, ⟨hpf, hp⟩, fun _ hq => tendsto_nhds_unique hq.2 hp⟩

/-! ### Part 2: Carathéodory closed-disk extension & homeomorphism -/

private theorem circleDensityCauchy_differentiableOn_of_zero_near
    (g : ℝ → ℂ) (hg : Continuous g) {ζ : ℂ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi), ‖circleMap 0 1 θ - ζ‖ < d → g θ = 0) :
    DifferentiableOn ℂ (fun w : ℂ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w)) (ball ζ (d / 2)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) (2 * Real.pi)) hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (g 0)).trans (hM 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hsep (θ : ℝ) (hfar : d ≤ ‖circleMap 0 1 θ - ζ‖) (w : ℂ) (hw : w ∈ ball ζ (d / 2)) :
      d / 2 ≤ ‖circleMap 0 1 θ - w‖ := by
    have hw' : ‖w - ζ‖ < d / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
    have htri : ‖circleMap 0 1 θ - ζ‖ ≤ ‖circleMap 0 1 θ - w‖ + ‖w - ζ‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (circleMap 0 1 θ - w) (w - ζ)
    linarith
  intro w₀ hw₀
  have hmeas (w : ℂ) : AEStronglyMeasurable (fun θ : ℝ => g θ / (circleMap 0 1 θ - w))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (hg.measurable.div ((measurable_circleMap 0 1).sub measurable_const)).aestronglyMeasurable
  have hFi : Integrable (fun θ : ℝ => g θ / (circleMap 0 1 θ - w₀))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) :=
    (integrable_const (M / (d / 2))).mono' (hmeas w₀)
      ((ae_restrict_mem measurableSet_Ioc).mono fun θ hθ => by
        by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
        · rw [hzero θ ⟨hθ.1.le, hθ.2⟩ hn, zero_div, norm_zero]; exact div_nonneg hM0 (half_pos hd).le
        · rw [norm_div]; exact div_le_div₀ hM0 (hM θ ⟨hθ.1.le, hθ.2⟩) (half_pos hd)
            (hsep θ (le_of_not_gt hn) w₀ hw₀))
  have hb : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2), ‖g θ / (circleMap 0 1 θ - w) ^ 2‖ ≤ M / (d / 2) ^ 2 :=
    (ae_restrict_mem measurableSet_Ioc).mono fun θ hθ w hw => by
      by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
      · rw [hzero θ ⟨hθ.1.le, hθ.2⟩ hn, zero_div, norm_zero]; exact div_nonneg hM0 (sq_nonneg _)
      · rw [norm_div, norm_pow]
        exact div_le_div₀ hM0 (hM θ ⟨hθ.1.le, hθ.2⟩) (sq_pos_of_pos (half_pos hd))
          ((sq_le_sq₀ (half_pos hd).le (norm_nonneg _)).mpr (hsep θ (le_of_not_gt hn) w hw))
  have hdif : ∀ᵐ θ ∂volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)),
      ∀ w ∈ ball ζ (d / 2), HasDerivAt (fun v : ℂ => g θ / (circleMap 0 1 θ - v))
        (g θ / (circleMap 0 1 θ - w) ^ 2) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ w hw
    by_cases hn : ‖circleMap 0 1 θ - ζ‖ < d
    · simp only [hzero θ ⟨hθ.1.le, hθ.2⟩ hn, zero_div]; exact hasDerivAt_const w 0
    · have hne : circleMap 0 1 θ - w ≠ 0 :=
        norm_pos_iff.mp ((half_pos hd).trans_le (hsep θ (le_of_not_gt hn) w hw))
      convert (hasDerivAt_const w (g θ)).div
        ((hasDerivAt_const w (circleMap 0 1 θ)).sub (hasDerivAt_id w)) hne using 1
      · funext v; rfl
      · simp
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (F := fun w θ => g θ / (circleMap 0 1 θ - w))
    (F' := fun w θ => g θ / (circleMap 0 1 θ - w) ^ 2)
    (bound := fun _ : ℝ => M / (d / 2) ^ 2)
    (isOpen_ball.mem_nhds hw₀) (Eventually.of_forall hmeas) hFi
    (hg.measurable.div (((measurable_circleMap 0 1).sub measurable_const).pow_const 2)).aestronglyMeasurable
    hb (integrable_const _) hdif
  have ht : HasDerivAt (fun w : ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w₀) ^ 2) w₀ := by
    simpa only [intervalIntegral.integral_of_le Real.two_pi_pos.le] using hdiff.2
  exact ht.differentiableAt.differentiableWithinAt

private theorem diffContOnCl_eq_zero_of_circle_patch
    (G : ℂ → ℂ) (hG : DiffContOnCl ℂ G (ball (0 : ℂ) 1))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {d : ℝ} (hd : 0 < d)
    (hzero : ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → G z = 0) :
    EqOn G 0 (ball (0 : ℂ) 1) := by
  let C : ℂ → ℂ := fun w => circleIntegral (fun z => (z - w)⁻¹ * G z) 0 1
  let g : ℝ → ℂ := fun θ => deriv (circleMap 0 1) θ * G (circleMap 0 1 θ)
  have hgc : Continuous g :=
    ((contDiff_circleMap 0 1 : ContDiff ℝ 1 (circleMap (0 : ℂ) 1)).continuous_deriv_one).mul
      (hG.continuousOn_ball.comp_continuous (continuous_circleMap 0 1) fun θ =>
        sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ))
  have hCd : DifferentiableOn ℂ C (ball ζ (d / 2)) := by
    rw [show C = fun w : ℂ => ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ / (circleMap 0 1 θ - w) from
      funext fun w => intervalIntegral.integral_congr fun θ _ => by
        dsimp [C, g]; simp only [div_eq_mul_inv]; ring]
    exact circleDensityCauchy_differentiableOn_of_zero_near g hgc hd fun θ _ hn => by
      dsimp [g]; rw [hzero _ (circleMap_mem_sphere 0 zero_le_one θ) hn, mul_zero]
  have hCinside (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : C w = (2 * Real.pi * I : ℂ) * G w := by
    simpa only [C, smul_eq_mul] using hG.circleIntegral_sub_inv_smul hw
  have hCoutside (w : ℂ) (hw : 1 < ‖w‖) : C w = 0 := by
    have hne (z : ℂ) (hz : z ∈ closure (ball (0 : ℂ) 1)) : z - w ≠ 0 := fun hzw =>
      (not_le_of_gt hw) ((sub_eq_zero.mp hzw) ▸ mem_closedBall_zero_iff.mp (closure_ball_subset_closedBall hz))
    simpa only [C, Pi.inv_apply, smul_eq_mul, id_eq] using
      (((differentiable_id.sub_const w).diffContOnCl.inv hne).smul hG).circleIntegral_eq_zero zero_le_one
  let e := min (d / 4) (1 / 2 : ℝ)
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have hehalf : e < d / 2 := (min_le_left _ _).trans_lt (by linarith)
  have heone : e < 1 := (min_le_right _ _).trans_lt (by norm_num)
  let wout : ℂ := (1 + e : ℝ) • ζ
  have hwout : wout ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm, show wout - ζ = e • ζ by
        change (1 + e) • ζ - ζ = e • ζ; rw [add_smul, one_smul]; abel,
      norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_of_pos he]
    exact hehalf
  have hCevent : C =ᶠ[𝓝 wout] 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
      (show 1 < ‖wout‖ by
        simp only [wout, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (by linarith : 0 < 1 + e)]; linarith)] with w hw
    exact hCoutside w hw
  have hCzero : EqOn C 0 (ball ζ (d / 2)) :=
    (hCd.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball ζ (d / 2)).isPreconnected hwout hCevent
  let win : ℂ := (1 - e) • ζ
  have hwinD : win ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    simp only [win, norm_smul, Real.norm_eq_abs, hζ, mul_one, abs_of_pos (sub_pos.mpr heone)]; linarith
  have hwinB : win ∈ ball ζ (d / 2) := by
    rw [mem_ball, dist_eq_norm, show win - ζ = (-e) • ζ by
        change (1 - e) • ζ - ζ = (-e) • ζ; rw [sub_smul, one_smul, neg_smul]; abel,
      norm_smul, hζ, mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos he]
    exact hehalf
  have hcne : (2 * Real.pi * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hGevent : G =ᶠ[𝓝 win] 0 := by
    filter_upwards [isOpen_ball.mem_nhds hwinD, isOpen_ball.mem_nhds hwinB] with w hwD hwB
    exact (mul_eq_zero.mp ((hCinside w hwD).symm.trans (hCzero hwB))).resolve_left hcne
  exact (hG.differentiableOn.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected hwinD hGevent

private theorem exists_circle_patch_subset_of_preconnected
    {A : Set ℂ} (hA : IsPreconnected A) (hAs : A ⊆ sphere (0 : ℂ) 1)
    {η : ℂ} (hη : ‖η‖ = 1) (hηA : η ∉ A)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ A) (hz₂ : z₂ ∈ A) (h12 : z₁ ≠ z₂) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧
      ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → z ∈ A := by
  let u : ℂ → ℂ := fun z => -conj η * z
  have hucont : Continuous u := continuous_const.mul continuous_id
  have hηconj : η * conj η = 1 := by rw [mul_conj, normSq_eq_norm_sq, hη]; norm_num
  have huinv (z : ℂ) : (-η) * u z = z := by
    dsimp [u]; rw [show (-η) * (-conj η * z) = (η * conj η) * z by ring, hηconj, one_mul]
  have hunorm {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : ‖u z‖ = 1 := by
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    simp only [u, norm_mul, norm_neg, norm_conj, hη, hzn, one_mul]
  have huslit (z : ℂ) (hz : z ∈ A) : u z ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    have hun := hunorm (hAs hz)
    have hne : u z ≠ -1 := fun he => hηA ((by rw [← huinv z, he]; ring : z = η) ▸ hz)
    by_cases him : (u z).im = 0
    · refine Or.inl ?_
      have hsq : (u z).re * (u z).re = 1 := by
        have ht := normSq_eq_norm_sq (u z); rw [normSq_apply, hun, him] at ht; nlinarith
      have hrne : (u z).re ≠ -1 := fun hr => hne (Complex.ext (by simpa using hr) (by simpa using him))
      rw [(mul_self_eq_mul_self_iff.mp (by simpa only [one_mul] using hsq)).resolve_right hrne]
      exact zero_lt_one
    · exact Or.inr him
  let f : ℂ → ℝ := fun z => arg (u z)
  have hfconn : IsPreconnected (f '' A) := hA.image f fun z hz =>
    ((continuousAt_arg (huslit z hz)).comp hucont.continuousAt).continuousWithinAt
  have hf_inj {z w : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) (hw : w ∈ sphere (0 : ℂ) 1) (he : f z = f w) : z = w := by
    have hue : u z = u w := ext_norm_arg_iff.mpr ⟨(hunorm hz).trans (hunorm hw).symm, he⟩
    exact (huinv z).symm.trans ((congrArg (fun v : ℂ => (-η) * v) hue).trans (huinv w))
  have hbuild (a b : ℝ) (hab : a < b) (ha : a ∈ f '' A) (hb : b ∈ f '' A) :
      ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ d : ℝ, 0 < d ∧ ∀ z ∈ sphere (0 : ℂ) 1, ‖z - ζ‖ < d → z ∈ A := by
    obtain ⟨ζ, hζA, hζm⟩ : (a + b) / 2 ∈ f '' A := hfconn.Icc_subset ha hb ⟨by linarith, by linarith⟩
    have hfζ : ContinuousAt f ζ := (continuousAt_arg (huslit ζ hζA)).comp hucont.continuousAt
    obtain ⟨d, hd, hdb⟩ := Metric.mem_nhds_iff.mp
      (hfζ (isOpen_Ioo.mem_nhds (show f ζ ∈ Ioo a b by rw [hζm]; constructor <;> linarith)))
    refine ⟨ζ, by simpa only [mem_sphere, dist_zero_right] using hAs hζA, d, hd, fun z hzs hzn => ?_⟩
    have hfz : f z ∈ Ioo a b := hdb (by simpa only [mem_ball, dist_eq_norm] using hzn)
    obtain ⟨w, hwA, hwe⟩ := hfconn.Icc_subset ha hb ⟨hfz.1.le, hfz.2.le⟩
    exact (hf_inj hzs (hAs hwA) hwe.symm).symm ▸ hwA
  rcases lt_or_gt_of_ne (fun he => h12 (hf_inj (hAs hz₁) (hAs hz₂) he)) with hlt | hgt
  · exact hbuild (f z₁) (f z₂) hlt (mem_image_of_mem f hz₁) (mem_image_of_mem f hz₂)
  · exact hbuild (f z₂) (f z₁) hgt (mem_image_of_mem f hz₂) (mem_image_of_mem f hz₁)

def riemannMappingClosedExtension (F : ℂ → ℂ) : ℂ → ℂ :=
  extendFrom (ball (0 : ℂ) 1) F

theorem riemannMappingClosedExtension_eqOn (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1)) :
    EqOn (riemannMappingClosedExtension F) F (ball (0 : ℂ) 1) :=
  fun z hz => extendFrom_extends hF.continuousOn z hz

section ClosedExtension

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
include hb hL hsc hF hinj himage

private theorem riemannMapping_exists_limit_closedDisk {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ∃ p : ℂ, Tendsto F (𝓝[ball (0 : ℂ) 1] z) (𝓝 p) := by
  rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hz) with hn | hn
  · obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hb hL hsc F hF hinj himage hn
    exact ⟨p, hp.2⟩
  · exact ⟨F z, hF.continuousOn z (mem_ball_zero_iff.mpr hn)⟩

theorem riemannMappingClosedExtension_continuousOn :
    ContinuousOn (riemannMappingClosedExtension F) (closedBall (0 : ℂ) 1) :=
  continuousOn_extendFrom (by rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0)])
    fun _ hz => riemannMapping_exists_limit_closedDisk hb hL hsc F hF hinj himage hz

theorem riemannMappingClosedExtension_mem_frontier {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    riemannMappingClosedExtension F ζ ∈ frontier Ω := by
  obtain ⟨p, hp, _⟩ := riemannMapping_exists_unique_boundary_limit hb hL hsc F hF hinj himage hζ
  have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff, hζ]
  rw [riemannMappingClosedExtension, extendFrom_eq hζcl hp.2]
  exact hp.1

private theorem riemannMappingClosedExtension_closed_image :
    riemannMappingClosedExtension F '' closedBall (0 : ℂ) 1 = closure Ω := by
  let G := riemannMappingClosedExtension F
  have hG := riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hcl : closure (ball (0 : ℂ) 1) = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
  have him : G '' closedBall (0 : ℂ) 1 = closure (G '' ball (0 : ℂ) 1) := Subset.antisymm
    (by simpa only [hcl] using (show ContinuousOn G (closure (ball (0 : ℂ) 1)) by simpa only [hcl] using hG).image_closure)
    (closure_minimal (by rintro _ ⟨z, hz, rfl⟩; exact ⟨z, ball_subset_closedBall hz, rfl⟩)
      ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hG).isClosed)
  rw [him, (riemannMappingClosedExtension_eqOn F hF).image_eq, himage]

private theorem riemannMappingClosedExtension_sphere_image :
    riemannMappingClosedExtension F '' sphere (0 : ℂ) 1 = frontier Ω := by
  refine Subset.antisymm ?_ fun w hw => ?_
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage
      (by simpa only [mem_sphere, dist_zero_right] using hζ)
  · have hwcl := frontier_subset_closure hw
    rw [← riemannMappingClosedExtension_closed_image hb hL hsc F hF hinj himage] at hwcl
    obtain ⟨z, hz, he⟩ := hwcl
    refine ⟨z, ?_, he⟩
    rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hz) with hn | hn
    · simpa only [mem_sphere, dist_zero_right] using hn
    · have hzD : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hn
      rw [hL.1.1.frontier_eq] at hw
      exact False.elim (hw.2 (himage ▸ ⟨z, hzD, (riemannMappingClosedExtension_eqOn F hF hzD).symm.trans he⟩))

private theorem riemannMappingClosedExtension_mem_domain_iff {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    riemannMappingClosedExtension F z ∈ Ω ↔ z ∈ ball (0 : ℂ) 1 := by
  refine ⟨fun hzin => ?_, fun hzD => by
    rw [riemannMappingClosedExtension_eqOn F hF hzD, ← himage]; exact mem_image_of_mem F hzD⟩
  rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hz) with hn | hn
  · have hfront := riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage hn
    rw [hL.1.1.frontier_eq] at hfront; exact False.elim (hfront.2 hzin)
  · exact mem_ball_zero_iff.mpr hn

private theorem riemannMappingClosedExtension_boundary_fiber_connected {p : ℂ} (hp : p ∈ frontier Ω) :
    IsConnected (closedBall (0 : ℂ) 1 ∩ riemannMappingClosedExtension F ⁻¹' {p}) := by
  let G := riemannMappingClosedExtension F
  let A := closedBall (0 : ℂ) 1 ∩ G ⁻¹' {p}
  have hGc := riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hEq := riemannMappingClosedExtension_eqOn F hF
  have hAk : IsCompact A := (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    (hGc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton) inter_subset_left
  have hAne : A.Nonempty := by
    obtain ⟨ζ, hζ, he⟩ : p ∈ G '' sphere (0 : ℂ) 1 := by
      rwa [riemannMappingClosedExtension_sphere_image hb hL hsc F hF hinj himage]
    exact ⟨ζ, sphere_subset_closedBall hζ, he⟩
  refine ⟨hAne, isPreconnected_iff_subset_of_disjoint_closed.mpr fun u v hu hv hAuv hAdisj => ?_⟩
  have hKdisj : Disjoint (A ∩ u) (A ∩ v) := Set.disjoint_left.mpr fun z hzu hzv => by
    have hz : z ∈ A ∩ (u ∩ v) := ⟨hzu.1, hzu.2, hzv.2⟩; rwa [hAdisj] at hz
  obtain ⟨U, V, hUo, hVo, hKuU, hKvV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hAk.inter_right hu) (hAk.inter_right hv) hKdisj
  have hAUV (z : ℂ) (hz : z ∈ A) : z ∈ U ∪ V :=
    (hAuv hz).elim (fun h => Or.inl (hKuU ⟨hz, h⟩)) fun h => Or.inr (hKvV ⟨hz, h⟩)
  let T := closedBall (0 : ℂ) 1 \ (U ∪ V)
  have hGTk : IsCompact (G '' T) :=
    ((isCompact_closedBall (0 : ℂ) 1).diff (hUo.union hVo)).image_of_continuousOn (hGc.mono diff_subset)
  obtain ⟨d, hd, hdball⟩ := Metric.isOpen_iff.mp hGTk.isClosed.isOpen_compl p
    fun ⟨z, hz, he⟩ => hz.2 (hAUV z ⟨hz.1, he⟩)
  obtain ⟨c, r, h, _, f, hch, hBball⟩ := exists_small_chart hL hp hd
  let B := chartBox p c r h
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  rw [himage] at hJ hJm hFJ
  let S := J '' (Ω ∩ B)
  have hSc : IsPreconnected S := (isPreconnected_chart_inter hch).image J (hJ.continuousOn.mono inter_subset_left)
  have hSUV : S ⊆ U ∪ V := fun z ⟨w, hw, hzw⟩ => by
    by_contra hn
    have hGz : G z = w := by dsimp only [G]; rw [← hzw, hEq (hJm hw.1), hFJ w hw.1]
    exact hdball (hBball (hGz ▸ hw.2)) ⟨z, ⟨hzw ▸ ball_subset_closedBall (hJm hw.1), hn⟩, rfl⟩
  have hAcl : A ⊆ closure S := fun ζ hζ => by
    have hζcl : ζ ∈ closure (ball (0 : ℂ) 1) := by rw [closure_ball (0 : ℂ) one_ne_zero]; exact hζ.1
    letI : NeBot (𝓝[ball (0 : ℂ) 1] ζ) := mem_closure_iff_nhdsWithin_neBot.mp hζcl
    have hlim : Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 p) := by
      have ht := tendsto_extendFrom (riemannMapping_exists_limit_closedDisk hb hL hsc F hF hinj himage hζ.1)
      change Tendsto F (𝓝[ball (0 : ℂ) 1] ζ) (𝓝 (G ζ)) at ht; rwa [show G ζ = p from hζ.2] at ht
    have heS : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] ζ, z ∈ S := by
      filter_upwards [self_mem_nhdsWithin, hlim.eventually ((isOpen_chartBox p c r h).mem_nhds hch.center_mem_box)]
        with z hz hzB
      exact ⟨F z, ⟨himage ▸ mem_image_of_mem F hz, hzB⟩, hJF z hz⟩
    exact mem_closure_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds) heS
  rcases hSc.subset_or_subset hUo hVo hUV hSUV with hSU | hSV
  · refine Or.inl fun z hz => (hAuv hz).resolve_right fun hzv =>
      closure_minimal (hSU.trans hUV.subset_compl_right) hVo.isClosed_compl (hAcl hz) (hKvV ⟨hz, hzv⟩)
  · refine Or.inr fun z hz => (hAuv hz).resolve_left fun hzu =>
      closure_minimal (hSV.trans hUV.symm.subset_compl_right) hUo.isClosed_compl (hAcl hz) (hKuU ⟨hz, hzu⟩)

theorem riemannMappingClosedExtension_injOn :
    InjOn (riemannMappingClosedExtension F) (closedBall (0 : ℂ) 1) := by
  let G := riemannMappingClosedExtension F
  have hGc := riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hEq := riemannMappingClosedExtension_eqOn F hF
  have hGhol : DifferentiableOn ℂ G (ball (0 : ℂ) 1) := hF.congr fun z hz => hEq hz
  have hzeroD : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hhalfD : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; norm_num
  have hdisk_inj {z w : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1) (he : G z = G w) : z = w := by
    dsimp only [G] at he
    have hzΩ := (riemannMappingClosedExtension_mem_domain_iff hb hL hsc F hF hinj himage
      (ball_subset_closedBall hz)).mpr hz
    have hwD := (riemannMappingClosedExtension_mem_domain_iff hb hL hsc F hF hinj himage hw).mp (he ▸ hzΩ)
    exact hinj hz hwD (by rwa [hEq hz, hEq hwD] at he)
  intro z hz w hw he
  by_cases hzD : z ∈ ball (0 : ℂ) 1
  · exact hdisk_inj hzD hw he
  by_cases hwD : w ∈ ball (0 : ℂ) 1
  · exact (hdisk_inj hwD hz he.symm).symm
  have hzn : ‖z‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hz)
    (le_of_not_gt fun hn => hzD (mem_ball_zero_iff.mpr hn))
  by_contra hzw
  let p := G z
  let A := closedBall (0 : ℂ) 1 ∩ G ⁻¹' {p}
  have hp : p ∈ frontier Ω := riemannMappingClosedExtension_mem_frontier hb hL hsc F hF hinj himage hzn
  have hAconn := riemannMappingClosedExtension_boundary_fiber_connected hb hL hsc F hF hinj himage hp
  have hAs : A ⊆ sphere (0 : ℂ) 1 := fun v hv => by
    have hvD : v ∉ ball (0 : ℂ) 1 := fun hvD => by
      have hpin : p ∈ Ω := hv.2 ▸
        (riemannMappingClosedExtension_mem_domain_iff hb hL hsc F hF hinj himage hv.1).mpr hvD
      rw [hL.1.1.frontier_eq] at hp; exact hp.2 hpin
    simpa only [mem_sphere, dist_zero_right] using le_antisymm (mem_closedBall_zero_iff.mp hv.1)
      (le_of_not_gt fun hn => hvD (mem_ball_zero_iff.mpr hn))
  have hpatch_absurd (ζ : ℂ) (hζ : ‖ζ‖ = 1) (d : ℝ) (hd : 0 < d)
      (hsub : ∀ v ∈ sphere (0 : ℂ) 1, ‖v - ζ‖ < d → v ∈ A) : False := by
    have hzero := diffContOnCl_eq_zero_of_circle_patch (fun v => G v - p)
      ((DiffContOnCl.mk_ball hGhol hGc).sub_const p) hζ hd
      fun v hvs hvn => sub_eq_zero.mpr (hsub v hvs hvn).2
    have hval : F 0 = F (1 / 2) := (hEq hzeroD).symm.trans
      ((sub_eq_zero.mp (hzero hzeroD)).trans ((sub_eq_zero.mp (hzero hhalfD)).symm.trans (hEq hhalfD)))
    exact (by norm_num : (0 : ℂ) ≠ 1 / 2) (hinj hzeroD hhalfD hval)
  have hηex : ∃ η : ℂ, ‖η‖ = 1 ∧ η ∉ A := by
    by_contra hno; push_neg at hno
    exact hpatch_absurd 1 (by norm_num) 1 zero_lt_one fun v hvs _ =>
      hno v (by simpa only [mem_sphere, dist_zero_right] using hvs)
  obtain ⟨η, hη, hηA⟩ := hηex
  obtain ⟨ζ, hζ, d, hd, hpatch⟩ :=
    exists_circle_patch_subset_of_preconnected hAconn.2 hAs hη hηA ⟨hz, rfl⟩ ⟨hw, he.symm⟩ hzw
  exact hpatch_absurd ζ hζ d hd hpatch

private theorem exists_riemannMapping_closedDisk_homeomorph :
    ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
      ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = riemannMappingClosedExtension F z := by
  let G := riemannMappingClosedExtension F
  have hGc := riemannMappingClosedExtension_continuousOn hb hL hsc F hF hinj himage
  have hGinj := riemannMappingClosedExtension_injOn hb hL hsc F hF hinj himage
  have hGim := riemannMappingClosedExtension_closed_image hb hL hsc F hF hinj himage
  let f : closedBall (0 : ℂ) 1 → closure Ω := fun z => ⟨G z, hGim ▸ mem_image_of_mem G z.property⟩
  have hfc : Continuous f := hGc.restrict.subtype_mk _
  have hfb : Function.Bijective f :=
    ⟨fun z w he => Subtype.ext (hGinj z.property w.property (congrArg Subtype.val he)),
      fun w => by
        obtain ⟨z, hz, hze⟩ : (w : ℂ) ∈ G '' closedBall (0 : ℂ) 1 := by rw [hGim]; exact w.property
        exact ⟨⟨z, hz⟩, Subtype.ext hze⟩⟩
  letI : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  have hec : Continuous (Equiv.ofBijective f hfb) := hfc
  exact ⟨hec.homeoOfEquivCompactToT2, fun _ => rfl⟩

end ClosedExtension

/-! ### Part 3: Physical Green function, pole removal & Hopf inward ray barrier -/

def riemannMappingClosedInverse (F : ℂ → ℂ) : ℂ → ℂ :=
  Function.invFunOn (riemannMappingClosedExtension F) (closedBall (0 : ℂ) 1)

def riemannMappingGreen (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingClosedInverse F w‖

def riemannMappingInversePoleQuotient (F : ℂ → ℂ) : ℂ → ℂ :=
  dslope (riemannMappingClosedInverse F) (F 0)

def riemannMappingGreenCorrection (F : ℂ → ℂ) (w : ℂ) : ℝ :=
  -Real.log ‖riemannMappingInversePoleQuotient F w‖

private theorem fderiv_neg_log_norm_holomorphic
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => -Real.log ‖f w‖) z v = -⟪f z, deriv f z * v⟫_ℝ / ‖f z‖ ^ 2 := by
  have hr : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have ht := (hr.hasFDerivAt.norm_sq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).const_mul (-(1 / 2 : ℝ))
  rw [show (fun w => -(1 / 2 : ℝ) * Real.log (‖f w‖ ^ 2)) = (fun w => -Real.log ‖f w‖) from
    funext fun w => by rw [Real.log_pow]; ring] at ht
  have hh := congrArg (fun A : ℂ →L[ℝ] ℝ => A v) ht.fderiv
  have hfv : fderiv ℝ f z v = deriv f z * v := by
    rw [hf.fderiv_restrictScalars ℝ]; exact fderiv_eq_deriv_mul
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, smul_eq_mul, hfv] at hh
  calc _ = -(1 / 2 : ℝ) * ((‖f z‖ ^ 2)⁻¹ * (2 * ⟪f z, deriv f z * v⟫_ℝ)) := by
          simpa only [two_smul, two_mul] using hh
    _ = _ := by rw [div_eq_mul_inv]; ring

private theorem norm_fderiv_neg_log_norm_holomorphic_le
    {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hne : f z ≠ 0) (v : ℂ) :
    ‖fderiv ℝ (fun w => -Real.log ‖f w‖) z v‖ ≤ ‖deriv f z‖ * ‖v‖ / ‖f z‖ := by
  have hn : 0 < ‖f z‖ := norm_pos_iff.mpr hne
  rw [fderiv_neg_log_norm_holomorphic hf hne, norm_div, norm_neg, Real.norm_of_nonneg (sq_nonneg _)]
  calc _ ≤ (‖f z‖ * ‖deriv f z * v‖) / ‖f z‖ ^ 2 :=
          div_le_div_of_nonneg_right (norm_inner_le_norm _ _) (sq_nonneg _)
    _ = _ := by rw [norm_mul]; field_simp [hn.ne']

private theorem disk_mobius_norm_sq_difference (a b : ℂ) :
    ‖1 - star a * b‖ ^ 2 - ‖b - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, star_def]; ring

private theorem disk_mobius_denominator_and_norm {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1 - star a * b ≠ 0 ∧ ‖(b - a) / (1 - star a * b)‖ < 1 := by
  have hprod : 0 < (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) :=
    mul_pos (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg b])
  have hsq : ‖b - a‖ ^ 2 < ‖1 - star a * b‖ ^ 2 := by linarith [disk_mobius_norm_sq_difference a b]
  have hnorm : ‖b - a‖ < ‖1 - star a * b‖ := (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hd : 0 < ‖1 - star a * b‖ := (norm_nonneg _).trans_lt hnorm
  exact ⟨norm_ne_zero_iff.mp hd.ne', by rw [norm_div]; exact (div_lt_one hd).mpr hnorm⟩

private theorem disk_mobius_norm_defect {a b : ℂ} {t : ℝ}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hbound : ‖(b - a) / (1 - star a * b)‖ ≤ t) :
    (1 - ‖a‖) ^ 2 / 2 * (1 - t) ≤ 1 - ‖b‖ := by
  let d : ℝ := ‖1 - star a * b‖
  have hdpos : 0 < d := norm_pos_iff.mpr (disk_mobius_denominator_and_norm ha hb).1
  have hnle : ‖b - a‖ ≤ t * d := (div_le_iff₀ hdpos).mp (by rwa [norm_div] at hbound)
  have hn2 : ‖b - a‖ ^ 2 ≤ t ^ 2 * d ^ 2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht0 hdpos.le)).mpr hnle
  have hlow : 1 - ‖a‖ ≤ d := by
    have ht := norm_sub_norm_le (1 : ℂ) (star a * b)
    rw [norm_one, norm_mul, norm_star] at ht
    have hp : ‖a‖ * ‖b‖ ≤ ‖a‖ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hb.le (norm_nonneg a)
    dsimp [d]; simp only [star_def] at ht ⊢; linarith
  have ht2 : t ^ 2 ≤ t := by simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left ht1 ht0
  have hsq : (1 - ‖a‖) ^ 2 ≤ d ^ 2 := (sq_le_sq₀ (sub_nonneg.mpr ha.le) hdpos.le).mpr hlow
  have hmul := mul_le_mul_of_nonneg_right hsq (sub_nonneg.mpr (ht2.trans ht1))
  have hid := disk_mobius_norm_sq_difference a b
  have hup : (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) ≤ 1 - ‖b‖ ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 - ‖a‖ ^ 2 ≤ 1 by nlinarith [sq_nonneg ‖a‖]) (by nlinarith [norm_nonneg b])
  have hlast : (1 - ‖a‖) ^ 2 * (1 - t) ≤ (1 - ‖a‖) ^ 2 * (1 - t ^ 2) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left ht2 1) (sq_nonneg _)
  have hmiddle : d ^ 2 * (1 - t ^ 2) ≤ (1 - ‖a‖ ^ 2) * (1 - ‖b‖ ^ 2) := by
    dsimp [d] at hn2 ⊢; simp only [star_def] at hn2 hid ⊢; nlinarith only [hn2, hid]
  have hh := hlast.trans ((hmul.trans (hmiddle.trans hup)).trans
    (show 1 - ‖b‖ ^ 2 ≤ 2 * (1 - ‖b‖) by nlinarith [sq_nonneg (1 - ‖b‖)]))
  nlinarith only [hh]

section ActualMap

variable {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω)
    (hsc : SimplyConnectedSpace Ω) (F : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)

include hb hS hsc hF hinj himage

local notation "G" => riemannMappingClosedExtension F
local notation "J" => riemannMappingClosedInverse F

omit hb hS hsc hF hinj in
theorem riemannMapping_pole_mem : F 0 ∈ Ω :=
  himage ▸ mem_image_of_mem F (mem_ball_self zero_lt_one)

theorem riemannMappingClosedInverse_mem_right {w : ℂ} (hw : w ∈ closure Ω) :
    J w ∈ closedBall (0 : ℂ) 1 ∧ G (J w) = w :=
  Function.invFunOn_pos (show w ∈ G '' closedBall (0 : ℂ) 1 by
    rwa [riemannMappingClosedExtension_closed_image hb hS.isLipschitzDomain hsc F hF hinj himage])

theorem riemannMappingClosedInverse_left {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    J (G z) = z := by
  have hx := Function.invFunOn_pos (show G z ∈ G '' closedBall (0 : ℂ) 1 from ⟨z, hz, rfl⟩)
  exact riemannMappingClosedExtension_injOn hb hS.isLipschitzDomain hsc F hF hinj himage hx.1 hz hx.2

private theorem riemannMappingClosedInverse_left_interior {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    J (F z) = z := by
  rw [← riemannMappingClosedExtension_eqOn F hF hz]
  exact riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (ball_subset_closedBall hz)

private theorem riemannMappingClosedInverse_zero : J (F 0) = 0 :=
  riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage (mem_ball_self zero_lt_one)

theorem riemannMappingClosedInverse_continuousOn : ContinuousOn J (closure Ω) := by
  obtain ⟨e, he⟩ := exists_riemannMapping_closedDisk_homeomorph
    hb hS.isLipschitzDomain hsc F hF hinj himage
  have hJe (w : closure Ω) : J w = (e.symm w : ℂ) := by
    have hG : G (e.symm w) = (w : ℂ) := by rw [← he (e.symm w), e.apply_symm_apply]
    exact (congrArg J hG.symm).trans
      (riemannMappingClosedInverse_left hb hS hsc F hF hinj himage (e.symm w).property)
  rw [continuousOn_iff_continuous_domRestrict]
  exact (continuous_subtype_val.comp e.symm.continuous).congr fun w => (hJe w).symm

private theorem riemannMappingClosedInverse_injOn : InjOn J (closure Ω) := fun _ hw _ hv he =>
  (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hw).2.symm.trans
    ((congrArg G he).trans (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hv).2)

private theorem riemannMappingClosedInverse_mem_disk {w : ℂ} (hw : w ∈ Ω) :
    J w ∈ ball (0 : ℂ) 1 := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)
  exact (riemannMappingClosedExtension_mem_domain_iff
    hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mp (hj.2.symm ▸ hw)

theorem riemannMappingClosedInverse_differentiableOn : DifferentiableOn ℂ J Ω := by
  obtain ⟨K, hK, hKm, _, hFK⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected hF hinj
  rw [himage] at hK hKm hFK
  exact hK.congr fun w hw => (congrArg J (hFK w hw).symm).trans
    (riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage (hKm hw))

private theorem riemannMappingClosedInverse_image : J '' Ω = ball (0 : ℂ) 1 :=
  Subset.antisymm (by rintro _ ⟨w, hw, rfl⟩; exact riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage hw)
    fun z hz => ⟨F z, himage ▸ mem_image_of_mem F hz,
      riemannMappingClosedInverse_left_interior hb hS hsc F hF hinj himage hz⟩

theorem riemannMappingClosedInverse_nonzero {w : ℂ} (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    J w ≠ 0 := fun hj0 => by
  have he := (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage hw).2
  rw [hj0, riemannMappingClosedExtension_eqOn F hF (mem_ball_self zero_lt_one)] at he
  exact hne he.symm

theorem riemannMappingClosedInverse_norm_frontier {w : ℂ} (hw : w ∈ frontier Ω) : ‖J w‖ = 1 := by
  have hj := riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (frontier_subset_closure hw)
  refine le_antisymm (mem_closedBall_zero_iff.mp hj.1) (le_of_not_gt fun hn => ?_)
  have hwΩ : w ∈ Ω := hj.2 ▸ (riemannMappingClosedExtension_mem_domain_iff
    hb hS.isLipschitzDomain hsc F hF hinj himage hj.1).mpr (mem_ball_zero_iff.mpr hn)
  rw [hS.1.1.frontier_eq] at hw; exact hw.2 hwΩ

private theorem riemannMappingClosedInverse_deriv_nonzero {w : ℂ} (hw : w ∈ Ω) : deriv J w ≠ 0 :=
  RiemannInterior.deriv_ne_zero_of_injOn hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hw

private theorem riemannMappingClosedInverse_deriv_sq_integrable :
    IntegrableOn (fun w => ‖deriv J w‖ ^ 2) Ω := by
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) (J '' Ω) := by
    rw [riemannMappingClosedInverse_image hb hS hsc F hF hinj himage]
    exact integrableOn_const unitDisk_bounded.measure_lt_top.ne
  simpa only [mul_one] using localConformal_integrable_weight hS.1.1
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)
    ((riemannMappingClosedInverse_injOn hb hS hsc F hF hinj himage).mono subset_closure) hc

theorem riemannMappingGreen_frontier {w : ℂ} (hw : w ∈ frontier Ω) : riemannMappingGreen F w = 0 := by
  rw [riemannMappingGreen, riemannMappingClosedInverse_norm_frontier hb hS hsc F hF hinj himage hw,
    Real.log_one, neg_zero]

theorem riemannMappingGreen_continuousOn :
    ContinuousOn (riemannMappingGreen F) (closure Ω \ {F 0}) :=
  (((riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage).mono diff_subset).norm.log
    fun _ hw => norm_ne_zero_iff.mpr
      (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw.1 hw.2)).neg

theorem riemannMappingGreen_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreen F) (Ω \ {F 0}) := fun w hw => by
  have hj := (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd hS.1.1 w hw.1
  have hh := (hj.harmonicAt_log_norm
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw.1) hw.2)).const_smul (c := (-1 : ℝ))
  rwa [show (-1 : ℝ) • (fun x : ℂ => Real.log ‖J x‖) = riemannMappingGreen F from
    funext fun x => by simp [riemannMappingGreen]] at hh

theorem riemannMappingGreen_fderiv {w : ℂ} (hw : w ∈ Ω) (hne : w ≠ F 0) (v : ℂ) :
    fderiv ℝ (riemannMappingGreen F) w v = -⟪J w, deriv J w * v⟫_ℝ / ‖J w‖ ^ 2 :=
  fderiv_neg_log_norm_holomorphic
    ((riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt (hS.1.1.mem_nhds hw))
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure hw) hne) v

private theorem exists_riemannMappingGreen_ball_lower_barrier {v : ℂ} {R : ℝ}
    (hR : 0 < R) (hball : ball v R ⊆ Ω) :
    ∃ A : ℝ, 0 < A ∧ ∀ w ∈ ball v R, w ≠ F 0 →
      A * (R - ‖w - v‖) ≤ riemannMappingGreen F w := by
  let a : ℂ := J v
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball (mem_ball_self hR)))
  let M : ℂ → ℂ := fun w => (J w - a) / (1 - star a * J w)
  have hJb := (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).mono hball
  have hM : DifferentiableOn ℂ M (ball v R) :=
    (hJb.sub_const a).div ((differentiableOn_const (1 : ℂ)).sub ((differentiableOn_const (star a)).mul hJb))
      fun w hw => (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
        (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).1
  have hM0 : M v = 0 := by dsimp [M, a]; rw [sub_self, zero_div]
  have hmaps : MapsTo M (ball v R) (closedBall (M v) 1) := by
    rw [hM0]; exact fun w hw => mem_closedBall_zero_iff.mpr
      (disk_mobius_denominator_and_norm ha (mem_ball_zero_iff.mp
        (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw)))).2.le
  let A : ℝ := (1 - ‖a‖) ^ 2 / (2 * R)
  refine ⟨A, div_pos (sq_pos_of_pos (sub_pos.mpr ha)) (by positivity), fun w hw hne => ?_⟩
  have hn : ‖J w‖ < 1 := mem_ball_zero_iff.mp
    (riemannMappingClosedInverse_mem_disk hb hS hsc F hF hinj himage (hball hw))
  have hd : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
  have hschwarz := Complex.dist_le_div_mul_dist_of_mapsTo_ball hM hmaps hw
  rw [hM0, dist_zero_right, dist_eq_norm] at hschwarz
  have hbound : ‖(J w - a) / (1 - star a * J w)‖ ≤ ‖w - v‖ / R := by
    simpa only [M, one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hschwarz
  have hdefect := disk_mobius_norm_defect ha hn (div_nonneg (norm_nonneg _) hR.le)
    ((div_lt_one hR).mpr hd).le hbound
  have hlog := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage (subset_closure (hball hw)) hne))
  rw [show A * (R - ‖w - v‖) = (1 - ‖a‖) ^ 2 / 2 * (1 - ‖w - v‖ / R) by dsimp [A]; field_simp [hR.ne'],
    riemannMappingGreen]
  exact hdefect.trans (by linarith)

private theorem riemannMappingInversePoleQuotient_differentiableOn :
    DifferentiableOn ℂ (riemannMappingInversePoleQuotient F) Ω :=
  (Complex.differentiableOn_dslope (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))).mpr
    (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage)

private theorem riemannMappingInversePoleQuotient_continuousOn :
    ContinuousOn (riemannMappingInversePoleQuotient F) (closure Ω) :=
  (continuousOn_dslope (mem_of_superset (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage)) subset_closure)).mpr
    ⟨riemannMappingClosedInverse_continuousOn hb hS hsc F hF hinj himage,
      (riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
        (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))⟩

private theorem riemannMappingInversePoleQuotient_nonzero {w : ℂ} (hw : w ∈ closure Ω) :
    riemannMappingInversePoleQuotient F w ≠ 0 := by
  by_cases he : w = F 0
  · subst w; rw [riemannMappingInversePoleQuotient, dslope_same]
    exact riemannMappingClosedInverse_deriv_nonzero hb hS hsc F hF hinj himage (riemannMapping_pole_mem F himage)
  · rw [riemannMappingInversePoleQuotient, dslope_of_ne _ he, slope,
      riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage, vsub_eq_sub, sub_zero, smul_eq_mul]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr he))
      (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw he)

theorem riemannMappingGreenCorrection_continuousOn :
    ContinuousOn (riemannMappingGreenCorrection F) (closure Ω) :=
  ((riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm.log
    fun _ hw => norm_ne_zero_iff.mpr
      (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw)).neg

theorem riemannMappingGreenCorrection_harmonicOnNhd :
    HarmonicOnNhd (riemannMappingGreenCorrection F) Ω := fun w hw => by
  have hq := (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd hS.1.1 w hw
  have hh := (hq.harmonicAt_log_norm
    (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw))).const_smul (c := (-1 : ℝ))
  rwa [show (-1 : ℝ) • (fun x : ℂ => Real.log ‖riemannMappingInversePoleQuotient F x‖) =
    riemannMappingGreenCorrection F from funext fun x => by simp [riemannMappingGreenCorrection]] at hh

theorem riemannMappingGreenCorrection_contDiffOn :
    ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingGreenCorrection F) Ω := fun w hw => by
  have hq := (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).analyticOnNhd hS.1.1 w hw
  have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw)
  exact ((((hq.restrictScalars (𝕜 := ℝ)).contDiffAt).norm ℝ hne).log (norm_ne_zero_iff.mpr hne)).neg.contDiffWithinAt

private theorem riemannMappingInversePoleQuotient_deriv_memLp :
    MemLp (deriv (riemannMappingInversePoleQuotient F)) 2 (volume.restrict Ω) := by
  let Q := riemannMappingInversePoleQuotient F
  have hQ := riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage
  have hQc : ContinuousOn (deriv Q) Ω := (hQ.deriv hS.1.1).continuousOn
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hS.1.1.mem_nhds (riemannMapping_pole_mem F himage))
  obtain ⟨B, _, hB⟩ :=
    ((isCompact_closedBall (F 0) r).image_of_continuousOn (hQc.mono hball)).isBounded.subset_ball_lt 0 (0 : ℂ)
  have hJm : MemLp (deriv J) 2 (volume.restrict Ω) :=
    (memLp_two_iff_integrable_sq_norm
      ((((riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).deriv
        hS.1.1).continuousOn).aestronglyMeasurable hS.1.1.measurableSet)).mpr
      (riemannMappingClosedInverse_deriv_sq_integrable hb hS hsc F hF hinj himage)
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  refine ((hJm.norm.const_mul r⁻¹).add (memLp_const (B + r⁻¹ ^ 2))).mono'
    (hQc.aestronglyMeasurable hS.1.1.measurableSet) ?_
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  dsimp only [Pi.add_apply]
  change ‖deriv Q w‖ ≤ r⁻¹ * ‖deriv J w‖ + (B + r⁻¹ ^ 2)
  by_cases hwball : w ∈ closedBall (F 0) r
  · have hl : ‖deriv Q w‖ ≤ B := (by simpa only [mem_ball, dist_zero_right] using hB (mem_image_of_mem _ hwball) : ‖deriv Q w‖ < B).le
    have hp : 0 ≤ r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by positivity
    linarith
  · have hdist : r ≤ ‖w - F 0‖ := by rw [mem_closedBall, dist_eq_norm, not_le] at hwball; exact hwball.le
    have hdpos : 0 < ‖w - F 0‖ := hr.trans_le hdist
    have hne : w ≠ F 0 := sub_ne_zero.mp (norm_ne_zero_iff.mp hdpos.ne')
    have hQd : deriv Q w = (deriv J w * (w - F 0) - J w) / (w - F 0) ^ 2 := by
      have heq : Q =ᶠ[𝓝 w] (J / fun z => z - F 0) := by
        filter_upwards [eventually_ne_nhds hne] with z hz
        rw [show Q z = dslope J (F 0) z from rfl, dslope_of_ne _ hz, slope,
          riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage, vsub_eq_sub, sub_zero, smul_eq_mul]
        simp only [Pi.div_apply, div_eq_mul_inv, mul_comm]
      rw [heq.deriv_eq]
      have hdj := ((riemannMappingClosedInverse_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
        (hS.1.1.mem_nhds hw)).hasDerivAt
      simpa only [mul_one, id] using (hdj.div ((hasDerivAt_id w).sub_const (F 0)) (sub_ne_zero.mpr hne)).deriv
    have hJn : ‖J w‖ ≤ 1 := mem_closedBall_zero_iff.mp
      (riemannMappingClosedInverse_mem_right hb hS hsc F hF hinj himage (subset_closure hw)).1
    have hstep : ‖deriv Q w‖ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := by
      rw [hQd, norm_div, norm_pow]
      calc _ ≤ (‖deriv J w * (w - F 0)‖ + ‖J w‖) / ‖w - F 0‖ ^ 2 :=
              div_le_div_of_nonneg_right (norm_sub_le _ _) (sq_nonneg _)
        _ = ‖deriv J w‖ / ‖w - F 0‖ + ‖J w‖ / ‖w - F 0‖ ^ 2 := by rw [norm_mul]; field_simp [hdpos.ne']
        _ ≤ ‖deriv J w‖ / r + 1 / r ^ 2 := add_le_add
              (div_le_div_of_nonneg_left (norm_nonneg _) hr hdist)
              ((div_le_div_of_nonneg_right hJn (sq_nonneg _)).trans
                (div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hr) ((sq_le_sq₀ hr.le hdpos.le).mpr hdist)))
    have heq : ‖deriv J w‖ / r + 1 / r ^ 2 = r⁻¹ * ‖deriv J w‖ + r⁻¹ ^ 2 := by
      rw [div_eq_mul_inv, one_div, inv_pow]; ring
    have hB0 : 0 ≤ B := (norm_nonneg (deriv Q (F 0))).trans
      (by simpa only [mem_ball, dist_zero_right] using hB (mem_image_of_mem _ (mem_closedBall_self hr.le)) : ‖deriv Q (F 0)‖ < B).le
    linarith

theorem riemannMappingGreenCorrection_complex_value_memLp :
    MemLp (fun w => (riemannMappingGreenCorrection F w : ℂ)) 2 (volume.restrict Ω) := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  have hcont := Complex.ofRealCLM.continuous.comp_continuousOn
    (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)
  obtain ⟨B, _, hB⟩ := (hb.isCompact_closure.image_of_continuousOn hcont).isBounded.subset_ball_lt 0 (0 : ℂ)
  refine MemLp.of_bound ((hcont.mono subset_closure).aestronglyMeasurable hS.1.1.measurableSet) B ?_
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  exact (show ‖(riemannMappingGreenCorrection F w : ℂ)‖ < B by
    simpa only [mem_ball, dist_zero_right, Function.comp_apply, Complex.ofRealCLM_apply] using
      hB (mem_image_of_mem _ (subset_closure hw))).le

theorem riemannMappingGreenCorrection_complex_gradient_memLp (i : Fin 2) :
    MemLp (dirD (fun z => (riemannMappingGreenCorrection F z : ℂ)) (coordDir i)) 2
      (volume.restrict Ω) := by
  obtain ⟨c, hc, hcn⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ closure Ω, c ≤ ‖riemannMappingInversePoleQuotient F w‖ :=
    hb.isCompact_closure.exists_forall_le'
      (riemannMappingInversePoleQuotient_continuousOn hb hS hsc F hF hinj himage).norm
      fun _ hw => norm_pos_iff.mpr (riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage hw)
  have hQm := riemannMappingInversePoleQuotient_deriv_memLp hb hS hsc F hF hinj himage
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (riemannMappingGreenCorrection F z : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  have hcont : ContinuousOn (dirD (fun z => (riemannMappingGreenCorrection F z : ℂ)) (coordDir i)) Ω :=
    (hs.continuousOn_fderiv_of_isOpen hS.1.1 (by simp)).clm_apply continuousOn_const
  refine (hQm.norm.const_mul c⁻¹).mono' (hcont.aestronglyMeasurable hS.1.1.measurableSet) ?_
  filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with w hw
  have hd : DifferentiableAt ℝ (riemannMappingGreenCorrection F) w :=
    ((riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage).differentiableOn
      (by simp)).differentiableAt (hS.1.1.mem_nhds hw)
  have hc_fd : dirD (fun z => (riemannMappingGreenCorrection F z : ℂ)) (coordDir i) w =
      (fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i) : ℂ) := by
    change fderiv ℝ (Complex.ofRealCLM ∘ riemannMappingGreenCorrection F) w (coordDir i) = _
    rw [fderiv_comp w Complex.ofRealCLM.differentiableAt hd]; simp
  have hQ := (riemannMappingInversePoleQuotient_differentiableOn hb hS hsc F hF hinj himage).differentiableAt
    (hS.1.1.mem_nhds hw)
  have hne := riemannMappingInversePoleQuotient_nonzero hb hS hsc F hF hinj himage (subset_closure hw)
  rw [hc_fd, Complex.norm_real]
  calc ‖fderiv ℝ (riemannMappingGreenCorrection F) w (coordDir i)‖
      ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ * ‖coordDir i‖ /
          ‖riemannMappingInversePoleQuotient F w‖ := norm_fderiv_neg_log_norm_holomorphic_le hQ hne _
    _ ≤ ‖deriv (riemannMappingInversePoleQuotient F) w‖ / c := by
          rw [norm_coordDir, mul_one]
          exact div_le_div_of_nonneg_left (norm_nonneg _) hc (hcn w (subset_closure hw))
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem riemannMappingGreenCorrection_eq {w : ℂ} (hw : w ∈ closure Ω) (hne : w ≠ F 0) :
    riemannMappingGreenCorrection F w = riemannMappingGreen F w + Real.log ‖w - F 0‖ := by
  have hnJ : ‖J w‖ ≠ 0 := norm_ne_zero_iff.mpr
    (riemannMappingClosedInverse_nonzero hb hS hsc F hF hinj himage hw hne)
  have hnd : ‖w - F 0‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  rw [riemannMappingGreenCorrection, riemannMappingInversePoleQuotient,
    dslope_of_ne _ hne, slope, riemannMappingClosedInverse_zero hb hS hsc F hF hinj himage,
    vsub_eq_sub, sub_zero, smul_eq_mul, norm_mul, norm_inv, Real.log_mul (inv_ne_zero hnd) hnJ, Real.log_inv,
    riemannMappingGreen]
  ring

omit hb hS hsc hF hinj himage in
def riemannMappingDirichletRemainder (b : smoothTraceTests) (z : ℂ) : ℂ :=
  (riemannMappingGreenCorrection F z : ℂ) - b z

theorem exists_riemannMapping_zero_boundary_poisson_problem :
    ∃ b : smoothTraceTests,
      ContinuousOn (riemannMappingDirichletRemainder F b) (closure Ω) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (riemannMappingDirichletRemainder F b) Ω ∧
      (∀ z ∈ frontier Ω, riemannMappingDirichletRemainder F b z = 0) ∧
      MemLp (riemannMappingDirichletRemainder F b) 2 (volume.restrict Ω) ∧
      (∀ i : Fin 2, MemLp (dirD (riemannMappingDirichletRemainder F b) (coordDir i))
        2 (volume.restrict Ω)) ∧
      (∀ z ∈ Ω, lap (riemannMappingDirichletRemainder F b) z = -lap (b : ℂ → ℂ) z) := by
  have hlap_eq {g : ℂ → ℂ} {z : ℂ} (hg : ContDiffAt ℝ 2 g z) :
      lap g z = Laplacian.laplacian g z := by
    have hd : DifferentiableAt ℝ (fderiv ℝ g) z :=
      (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have he (v : ℂ) : dirD (dirD g v) v z = fderiv ℝ (fderiv ℝ g) z v v := by
      change fderiv ℝ (fun w => fderiv ℝ g w v) z v = _
      rw [fderiv_clm_apply hd (differentiableAt_const v)]; simp
    rw [lap, he, he, InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hk : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hku : frontier Ω ⊆ ({F 0} : Set ℂ)ᶜ := fun w hw he => by
    rw [show w = F 0 from he, hS.1.1.frontier_eq] at hw
    exact hw.2 (riemannMapping_pole_mem F himage)
  have hs_log : ContDiffOn ℝ (⊤ : ℕ∞) (fun w : ℂ => (Real.log ‖w - F 0‖ : ℂ)) {F 0}ᶜ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn fun w hw =>
      (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hw)).log
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))).contDiffWithinAt
  obtain ⟨b₀, hbtest, hbe⟩ := exists_smooth_compact_extension hk isOpen_compl_singleton hku hs_log
  let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM
  let b : smoothTraceTests := ⟨fun z => ((b₀ z).re : ℂ),
    L.contDiff.comp hbtest.1,
    hbtest.2.1.comp_left (show L (0 : ℂ) = 0 by simp [L]), subset_univ _⟩
  let h : ℂ → ℂ := fun z => (riemannMappingGreenCorrection F z : ℂ)
  have hharm : HarmonicOnNhd h Ω :=
    (riemannMappingGreenCorrection_harmonicOnNhd hb hS hsc F hF hinj himage).comp_CLM
      Complex.ofRealCLM
  have hs : ContDiffOn ℝ (⊤ : ℕ∞) h Ω := Complex.ofRealCLM.contDiff.comp_contDiffOn
    (riemannMappingGreenCorrection_contDiffOn hb hS hsc F hF hinj himage)
  refine ⟨b,
    (Complex.ofRealCLM.continuous.comp_continuousOn
      (riemannMappingGreenCorrection_continuousOn hb hS hsc F hF hinj himage)).sub
        b.property.1.continuous.continuousOn,
    hs.sub b.property.1.contDiffOn,
    fun w hw => by
      change (riemannMappingGreenCorrection F w : ℂ) - ((b₀ w).re : ℂ) = 0
      rw [(hbe w hw).self_of_nhds, Complex.ofReal_re,
        riemannMappingGreenCorrection_eq hb hS hsc F hF hinj himage (frontier_subset_closure hw) (hku hw),
        riemannMappingGreen_frontier hb hS hsc F hF hinj himage hw, zero_add, sub_self],
    (riemannMappingGreenCorrection_complex_value_memLp hb hS hsc F hF hinj himage).sub
      (smoothTraceTests_memLp Ω b),
    fun i => ((riemannMappingGreenCorrection_complex_gradient_memLp hb hS hsc F hF hinj himage i).sub
      (smoothTraceTests_memLp_deriv Ω b i)).ae_eq ?_,
    fun z hz => ?_⟩
  · filter_upwards [ae_restrict_mem hS.1.1.measurableSet] with z hzΩ
    have hh := (hs.differentiableOn (by simp)).differentiableAt (hS.1.1.mem_nhds hzΩ)
    change dirD h (coordDir i) z - dirD (b : ℂ → ℂ) (coordDir i) z = fderiv ℝ (h - (b : ℂ → ℂ)) z (coordDir i)
    rw [fderiv_sub hh ((b.property.1.differentiable (by simp)) z)]; rfl
  · have hh : ContDiffAt ℝ 2 h z := (hharm z hz).1
    have hb₂ : ContDiffAt ℝ 2 (b : ℂ → ℂ) z :=
      b.property.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    change lap (fun w => h w - b w) z = _
    rw [hlap_eq (hh.sub hb₂),
      show (fun w => h w - b w) = h + fun w => (-1 : ℝ) • b w from
        funext fun w => by simp [sub_eq_add_neg],
      hh.laplacian_add (hb₂.const_smul (-1 : ℝ))]
    change Laplacian.laplacian h z + Laplacian.laplacian ((-1 : ℝ) • (b : ℂ → ℂ)) z = _
    rw [laplacian_smul (-1 : ℝ) hb₂, (hharm z hz).2.self_of_nhds, Pi.zero_apply,
      ← hlap_eq hb₂, neg_one_smul, zero_add]

end ActualMap

private theorem exists_smoothDomain_interior_tangent_ball {Ω : Set ℂ} (hS : IsSmoothDomain Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ v : ℂ, ∃ R : ℝ, 0 < R ∧ ball v R ⊆ Ω ∧ p ∈ sphere v R := by
  obtain ⟨c, r, h, _, f, hc, hr, hh, hf, _, hf0, _, hgraph⟩ := hS.2 p hp
  have hd : ContDiff ℝ 1 (deriv f) := (hf.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ (1 + 1 : ℕ) f).deriv'
  obtain ⟨K, hK⟩ := hd.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-1 : ℝ) 1) (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
  have hquad (x : ℝ) (hx : |x| ≤ 1) : |f x - f 0 - deriv f 0 * x| ≤ (K : ℝ) * x ^ 2 := by
    have h0I : (0 : ℝ) ∈ Icc (-1 : ℝ) 1 := by norm_num
    have hsub : uIcc (0 : ℝ) x ⊆ Icc (-1 : ℝ) 1 := uIcc_subset_Icc h0I (abs_le.mp hx)
    let g : ℝ → ℝ := fun y => f y - f 0 - deriv f 0 * y
    have hg (y : ℝ) : HasDerivAt g (deriv f y - deriv f 0) y := by
      convert (((hf.differentiable (by simp) y).hasDerivAt.sub_const (f 0)).sub
        ((hasDerivAt_id y).const_mul (deriv f 0))) using 1
      · funext x; rfl
      · simp only [mul_one]
    have hbd (y : ℝ) (hy : y ∈ uIcc (0 : ℝ) x) : ‖deriv g y‖ ≤ (K : ℝ) * |x| := by
      rw [(hg y).deriv]
      have hh' : ‖deriv f y - deriv f 0‖ ≤ (K : ℝ) * |y| := by
        simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs] using hK.dist_le_mul y (hsub hy) 0 h0I
      have hsmall : |y| ≤ |x| := abs_le.mpr (by
        rcases mem_uIcc.mp hy with hy | hy <;> constructor <;> linarith [neg_abs_le x, le_abs_self x, abs_nonneg x])
      exact hh'.trans (mul_le_mul_of_nonneg_left hsmall K.coe_nonneg)
    simpa only [g, mul_zero, sub_self, sub_zero, Real.norm_eq_abs, mul_assoc, ← pow_two, sq_abs] using
      Convex.norm_image_sub_le_of_norm_deriv_le (fun y _ => (hg y).differentiableAt) hbd
        (convex_uIcc (0 : ℝ) x) left_mem_uIcc right_mem_uIcc
  let a : ℝ := deriv f 0
  let n : ℂ := -(a : ℂ) + Complex.I
  let C : ℝ := ‖n‖
  have hC : 0 < C := norm_pos_iff.mpr fun he => by have him := congrArg Complex.im he; norm_num [n] at him
  have hCsq : C ^ 2 = a ^ 2 + 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [n, Complex.normSq_apply, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.I_re, add_zero, Complex.add_im, Complex.neg_im, Complex.ofReal_im,
      neg_zero, Complex.I_im, zero_add]; ring
  let M : ℝ := K
  have hM : 0 ≤ M := K.coe_nonneg
  let e : ℝ := min (min (r / (2 * C)) (h / (2 * C))) (min (1 / (2 * C)) (1 / (2 * (M + 1))))
  obtain ⟨ρ, hρ, hρe⟩ := exists_between (show 0 < e by dsimp [e]; positivity)
  have hρr : 2 * ρ * C < r := by
    nlinarith [(lt_div_iff₀ (show 0 < 2 * C by positivity)).mp (hρe.trans_le ((min_le_left _ _).trans (min_le_left _ _)))]
  have hρh : 2 * ρ * C < h := by
    nlinarith [(lt_div_iff₀ (show 0 < 2 * C by positivity)).mp (hρe.trans_le ((min_le_left _ _).trans (min_le_right _ _)))]
  have hρ1 : 2 * ρ * C < 1 := by
    nlinarith [(lt_div_iff₀ (show 0 < 2 * C by positivity)).mp (hρe.trans_le ((min_le_right _ _).trans (min_le_left _ _)))]
  have hρM : 2 * ρ * M ≤ 1 := by
    nlinarith [(lt_div_iff₀ (show 0 < 2 * (M + 1) by positivity)).mp (hρe.trans_le ((min_le_right _ _).trans (min_le_right _ _)))]
  let v : ℂ := p + (ρ : ℂ) * n / c
  let R : ℝ := ρ * C
  have hR : 0 < R := mul_pos hρ hC
  have hvc : ‖v - p‖ = R := by
    simp only [v, add_sub_cancel_left, norm_div, norm_mul, hc, div_one,
      Complex.norm_real, Real.norm_of_nonneg hρ.le, R, C]
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  refine ⟨v, R, hR, fun w hw => ?_, by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hvc⟩
  have hwR : ‖w - v‖ < R := by simpa only [mem_ball, dist_eq_norm] using hw
  have hwp : ‖w - p‖ < 2 * ρ * C :=
    (norm_sub_le_norm_sub_add_norm_sub w v p).trans_lt (by rw [hvc]; dsimp [R]; linarith)
  let z : ℂ := c * (w - p)
  have hz : ‖z‖ = ‖w - p‖ := by dsimp [z]; rw [norm_mul, hc, one_mul]
  apply (hgraph w ((Complex.abs_re_le_norm z).trans_lt (hz ▸ hwp.trans hρr))
    ((Complex.abs_im_le_norm z).trans_lt (hz ▸ hwp.trans hρh))).mpr
  have hfx : f z.re ≤ a * z.re + M * z.re ^ 2 := by
    have ht := (abs_le.mp (hquad z.re ((Complex.abs_re_le_norm z).trans_lt (hz ▸ hwp.trans hρ1)).le)).2
    rw [hf0] at ht; dsimp [a, M]; linarith
  have hball : ‖z - (ρ : ℂ) * n‖ < R := by
    rw [show z - (ρ : ℂ) * n = c * (w - v) by dsimp [z, v]; field_simp [hcne]; ring, norm_mul, hc, one_mul]
    exact hwR
  have hs : (z.re + ρ * a) ^ 2 + (z.im - ρ) ^ 2 < ρ ^ 2 * (a ^ 2 + 1) := by
    have ht := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hball
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      show (z - (ρ : ℂ) * n).re = z.re + ρ * a by simp [n],
      show (z - (ρ : ℂ) * n).im = z.im - ρ by simp [n],
      show R ^ 2 = ρ ^ 2 * (a ^ 2 + 1) by dsimp [R]; rw [mul_pow, hCsq]] at ht
    nlinarith
  have hprod := mul_nonneg (show 0 ≤ 1 - 2 * ρ * M by linarith) (sq_nonneg z.re)
  refine hfx.trans_lt (lt_of_not_ge fun hny => ?_)
  have hmul := mul_le_mul_of_nonneg_left hny (show 0 ≤ 2 * ρ by positivity)
  nlinarith [sq_nonneg z.im]

theorem exists_riemannMappingGreen_inward_ray_lower {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hS : IsSmoothDomain Ω) (hsc : SimplyConnectedSpace Ω)
    (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ b : ℂ, ∃ δ A : ℝ, ‖b‖ = 1 ∧ 0 < δ ∧ 0 < A ∧
      ∀ t : ℝ, 0 < t → t < δ → p + (t : ℂ) * b ∈ Ω ∧
        p + (t : ℂ) * b ≠ F 0 ∧ A * t ≤ riemannMappingGreen F (p + (t : ℂ) * b) := by
  obtain ⟨v, R, hR, hball, hpR⟩ := exists_smoothDomain_interior_tangent_ball hS hp
  obtain ⟨A, hA, hbarrier⟩ := exists_riemannMappingGreen_ball_lower_barrier
    hb hS hsc F hF hinj himage hR hball
  have hvp : ‖v - p‖ = R := by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hpR
  let b : ℂ := (R : ℂ)⁻¹ * (v - p)
  have hb1 : ‖b‖ = 1 := by
    dsimp [b]; rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le, hvp, inv_mul_cancel₀ hR.ne']
  have hpne : p ≠ F 0 := fun he => by
    rw [he, hS.1.1.frontier_eq] at hp; exact hp.2 (riemannMapping_pole_mem F himage)
  let δ : ℝ := min R (‖p - F 0‖ / 2)
  refine ⟨b, δ, A, hb1, lt_min hR (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpne)) (by norm_num)),
    hA, fun t ht htδ => ?_⟩
  have htR : t < R := htδ.trans_le (min_le_left _ _)
  have htP : t < ‖p - F 0‖ / 2 := htδ.trans_le (min_le_right _ _)
  have hdist : ‖p + (t : ℂ) * b - v‖ = R - t := by
    have he : p + (t : ℂ) * b - v = ((t / R - 1 : ℝ) : ℂ) * (v - p) := by
      dsimp [b]; push_cast; field_simp [Complex.ofReal_ne_zero.mpr hR.ne']; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr ((div_lt_one hR).mpr htR).le), hvp]
    field_simp [hR.ne']; ring
  have hwball : p + (t : ℂ) * b ∈ ball v R := by rw [mem_ball, dist_eq_norm, hdist]; linarith
  have hwne : p + (t : ℂ) * b ≠ F 0 := fun he => by
    have hn : ‖p + (t : ℂ) * b - p‖ = t := by
      rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, hb1, mul_one]
    rw [he, norm_sub_rev] at hn; nlinarith
  refine ⟨hball hwball, hwne, ?_⟩
  simpa only [hdist, sub_sub_cancel] using hbarrier _ hwball hwne

end PolyaNeumann
end
