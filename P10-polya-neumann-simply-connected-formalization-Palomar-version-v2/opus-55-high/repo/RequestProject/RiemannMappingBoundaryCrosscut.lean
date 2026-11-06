module

public import RequestProject.RiemannMappingBoundaryOscillation
public import RequestProject.BoundaryConnected
public import Mathlib.Topology.Piecewise

/-!
# Actual short boundary arcs and small conformal cap loops

The inverse modulus of an actual periodic Jordan parametrization is
proved by compactness, rather than postulated for the physical boundary.
It closes every sufficiently small genuine conformal cap by an actual
short boundary arc. Coincident cap endpoints are treated separately.

These are constructions of small closed Jordan loops. The assertion
that the image of the entire source cap lies on their bounded side is a
separate planar separation statement, and is not an assumption here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology

variable {γ : ℝ → ℂ} {K : NNReal} (F : ℂ → ℂ)

/-- A periodic Jordan parametrization has no repeated values at
parameters whose separation is strictly less than one period. -/
theorem jordanParam_eq_of_eq_of_abs_sub_lt (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {x y : ℝ}
    (hxy : γ x = γ y) (hlt : |x - y| < 2 * Real.pi) : x = y := by
  have hmem  := fun z => by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    rwa [zero_add] at h
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hper.sub_zsmul_eq]
  have h := hinj (hmem x) (hmem y) (by simp_all)
  simp only [toIcoMod] at h
  let n := toIcoDiv Real.two_pi_pos 0 x
  let m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = (n - m : ℤ) * (2 * Real.pi) := by
    grind
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      nlinarith [Real.two_pi_pos]
    have h2 : |n - m| < 1 := by exact_mod_cast h1
    simp_all
  grind

/-- The genuine inverse modulus, with the two possible short cyclic
directions retained. This includes the identified endpoints `0` and `2π`. -/
theorem jordanParam_uniform_cyclic_inverse (hc : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {η : ℝ}
    (hη : 0 < η) (_hηπ : η < 2 * Real.pi) :
    ∃ δ > 0, ∀ s ∈ Icc 0 (2 * Real.pi), ∀ t ∈ Icc 0 (2 * Real.pi),
      ‖γ s - γ t‖ < δ → ∃ d : ℝ, |d| < η ∧ γ (s + d) = γ t := by
  let S  :=
    (Icc 0 (2 * Real.pi) ×ˢ Icc 0 (2 * Real.pi)) ∩
      {p | η ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 * Real.pi - η}
  have hSc : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs).inter
      (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const)
  have hpos : ∀ p ∈ S, 0 < ‖γ p.1 - γ p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    intro he
    have ha := hp.2.1
    rw [jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (sub_eq_zero.mp he)
      (lt_of_le_of_lt hp.2.2 (by linarith)), sub_self, abs_zero] at ha
    linarith
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖γ p.1 - γ p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · grind
    · obtain ⟨p, hp, hmin⟩ := hSc.exists_isMinOn hne ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm.continuousOn
      exact ⟨_, hpos p hp, fun q hq => hmin hq⟩
  refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
  have hshort : |s - t| < η ∨ 2 * Real.pi - |s - t| < η := by
    by_contra h
    push_neg at h
    have hbad : (s, t) ∈ S := ⟨⟨hs, ht⟩, h.1, by linarith ⟩
    grind
  rcases hshort with h | h
  · refine ⟨t - s, ?_, by ring⟩
    grind
  · by_cases hst' : s ≤ t
    · refine ⟨t - s - 2 * Real.pi, ?_, ?_⟩
      · grind
      · rw [show s + (t - s - 2 * Real.pi) = t - 2 * Real.pi by ring]
        exact hper.sub_eq t
    · refine ⟨t - s + 2 * Real.pi, ?_, ?_⟩
      · grind
      simp_all [show s + (t - s + 2 * Real.pi) = t + 2 * Real.pi by ring]

private theorem jordanParam_mem_image (hper : Function.Periodic γ (2 * Real.pi)) (s : ℝ) :
    γ s ∈ γ '' Icc 0 (2 * Real.pi) := by
  refine ⟨toIcoMod Real.two_pi_pos 0 s, ?_, ?_⟩
  · have h := toIcoMod_mem_Ico Real.two_pi_pos 0 s
    grind
  · rw [toIcoMod, hper.sub_zsmul_eq]

/-- Nearby points on the actual physical Jordan boundary are joined by
an actual short Lipschitz boundary arc. When they differ, that arc is
injective on its entire closed parameter interval. -/
theorem jordanParam_exists_short_arc (hK : LipschitzWith K γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : InjOn γ (Ico 0 (2 * Real.pi))) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ γ '' Icc 0 (2 * Real.pi), ∀ q ∈ γ '' Icc 0 (2 * Real.pi),
      ‖p - q‖ < δ → ∃ (A : ℝ → ℂ) (C : NNReal), LipschitzWith C A ∧
        A 0 = p ∧ A 1 = q ∧ MapsTo A (Icc 0 1) (γ '' Icc 0 (2 * Real.pi)) ∧
        (∀ u ∈ Icc 0 1, ∀ v ∈ Icc 0 1, ‖A u - A v‖ < ε) ∧
        (p ≠ q → InjOn A (Icc 0 1)) := by
  let η  := min Real.pi (ε / (K + 1))
  have hηπ : η < 2 * Real.pi :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨δ, hδ, hmod⟩ := jordanParam_uniform_cyclic_inverse hK.continuous hper hinj (lt_min Real.pi_pos (div_pos hε (by positivity))) hηπ
  refine ⟨δ, hδ, ?_⟩
  rintro p ⟨s, hs, hsp⟩ q ⟨t, ht, htq⟩ hpq
  obtain ⟨d, hd, hend⟩ := hmod s hs t ht (by simp_all)
  let A  := fun u => γ (s + d * u)
  let C  := K * Real.toNNReal |d|
  have hAC : LipschitzWith C A := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    simpa only [C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d),
      Real.dist_eq, show s + d * u - (s + d * v) = d * (u - v) by ring,
      abs_mul, mul_assoc] using hK.dist_le_mul (s + d * u) (s + d * v)
  have huv (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Icc 0 1) :
      |u - v| ≤ 1 := abs_le.2 ⟨by grind, by grind⟩
  refine ⟨A, C, hAC, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro u _
    exact jordanParam_mem_image hper _
  · intro u hu v hv
    have h := hAC.dist_le_mul u v
    rw [dist_eq_norm] at h
    have hC : C = K * |d| := by
      simp [C]
    exact (h.trans (mul_le_of_le_one_right (by positivity) (huv u hu v hv))).trans_lt (by
    have h1 : (K + 1) * |d| < (K + 1) * η :=
      mul_lt_mul_of_pos_left hd (by positivity)
    have h2 : (K + 1) * η ≤ ε := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp (min_le_right Real.pi (ε / (K + 1)))
    have h3 : K * |d| ≤ (K + 1) * |d| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg d)
    linarith)
  · intro hpq u hu v hv heq
    have hd0 : d ≠ 0 := by
      intro he
      simp_all
    have he := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq (by
      rw [show (s + d * u) - (s + d * v) = d * (u - v) by ring, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg d) (huv u hu v hv)).trans_lt (hd.trans hηπ))
    simp_all

private theorem riemannMapping_image_isOpen (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) : IsOpen (F '' ball (0 : ℂ) 1) :=
  RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hF hinj Subset.rfl isOpen_ball

/-- The genuine cap is injective before its terminal endpoint, including
its first frontier endpoint. No distinction between the two endpoint
limits is assumed. -/
theorem riemannMapping_cap_injOn_Ico (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball 0 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball 0 1)) : InjOn G (Ico a b) := by
  have hnot : G a ∉ F '' ball 0 1 := by
    simp_all [(riemannMapping_image_isOpen F hF hinj).frontier_eq]
  intro x hx y hy heq
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · linarith
    · exfalso
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply hnot
      refine ⟨circleMap ζ r y, harc hyi, ?_⟩
      exact (hGeq hyi).symm.trans (heq.symm.trans (congrArg G hxa.symm))
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exfalso
      have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      apply hnot
      refine ⟨circleMap ζ r x, harc hxi, ?_⟩
      exact (hGeq hxi).symm.trans (heq.trans (congrArg G hya.symm))
    · have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply injOn_circleMap_of_abs_sub_le' hr hwidth hx hy
      apply hinj (harc hxi) (harc hyi)
      exact (hGeq hxi).symm.trans (heq.trans (hGeq hyi))

/-- When the two physical endpoints differ, the full closed cap is an
injective arc. The endpoint exclusion uses the actual open image. -/
theorem riemannMapping_cap_injOn_Icc (hF : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) (ball 0 1))
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' ball 0 1))
    (hGb : G b ∈ frontier (F '' ball 0 1)) (hab : G a ≠ G b) :
    InjOn G (Icc a b) := by
  have hnot : G b ∉ F '' ball 0 1 := by
    simp_all [(riemannMapping_image_isOpen F hF hinj).frontier_eq]
  intro x hx y hy heq
  rcases lt_or_eq_of_le hx.2 with hxb | hxb
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · exact riemannMapping_cap_injOn_Ico F hF hinj hr hwidth harc hGeq hGa ⟨hx.1, hxb⟩ ⟨hy.1, hyb⟩ heq
    · rcases eq_or_lt_of_le hx.1 with hxa | hxa
      · simp_all
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r x, harc ⟨hxa, hxb⟩, ?_⟩
        exact (hGeq ⟨hxa, hxb⟩).symm.trans (heq.trans (congrArg G hyb))
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · rcases eq_or_lt_of_le hy.1 with hya | hya
      · simp_all
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r y, harc ⟨hya, hyb⟩, ?_⟩
        exact (hGeq ⟨hya, hyb⟩).symm.trans (heq.symm.trans (congrArg G hxb))
    linarith

/-- A closed Lipschitz loop lying in a genuine ball has zero winding at
every point outside that ball. The logarithm branch is constructed on
the actual loop, using the unit ball about `1` in the slit plane. -/
theorem windingNumber_eq_zero_of_image_ball (hK : LipschitzWith K γ) (hclosed : γ (2 * Real.pi) = γ 0)
    {p z : ℂ} {R : ℝ}
    (hball : ∀ θ ∈ Icc 0 (2 * Real.pi), ‖γ θ - p‖ < R)
    (hfar : R ≤ ‖p - z‖) : windingNumber γ z = 0 := by
  have hdpos  := ((norm_nonneg _).trans_lt (hball 0 ⟨le_rfl, Real.two_pi_pos.le⟩)).trans_le hfar
  have hd  := norm_pos_iff.mp hdpos
  simp [hclosed, windingNumber, integral_deriv_div_eq_log_sub hK Real.two_pi_pos.le (inv_ne_zero hd) (by
    intro θ hθ
    have heq : (p - z)⁻¹ * (γ θ - z) = 1 + (γ θ - p) / (p - z) := by
      field_simp ; ring
    rw [heq]
    exact Complex.mem_slitPlane_of_norm_lt_one (by
      rw [norm_div]
      exact (div_lt_one hdpos).mpr ((hball θ hθ).trans_le hfar)))]

end PolyaNeumann

end
