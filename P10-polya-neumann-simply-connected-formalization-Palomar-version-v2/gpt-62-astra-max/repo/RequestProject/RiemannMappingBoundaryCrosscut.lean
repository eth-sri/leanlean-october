module

public import RequestProject.RiemannMappingBoundaryOscillation
public import RequestProject.BoundaryConnected
public import Mathlib.Topology.Piecewise
public import RequestProject.PlanarNotation

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

/-- A periodic Jordan parametrization has no repeated values at
parameters whose separation is strictly less than one period. -/
theorem jordanParam_eq_of_eq_of_abs_sub_lt {γ : ℝ → ℂ}
    (hper : Function.Periodic γ anglePeriod)
    (hinj : InjOn γ angleIco) {x y : ℝ}
    (hxy : γ x = γ y) (hlt : |x - y| < anglePeriod) : x = y := by
  have hmem  := fun z => by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    rwa [zero_add] at h
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hper.sub_zsmul_eq]
  have h := hinj (hmem x) (hmem y) (by simp [hval, hxy])
  simp only [toIcoMod] at h
  let n := toIcoDiv Real.two_pi_pos 0 x
  let m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = ((n - m : ℤ) : ℝ) * anglePeriod := by
    grind
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      nlinarith [Real.two_pi_pos]
    rw [← Int.cast_abs] at h1
    
    apply Int.abs_lt_one_iff.mp
    exact_mod_cast h1
  rw [hk] at hd
  simp at hd
  linarith

/-- The genuine inverse modulus, with the two possible short cyclic
directions retained. This includes the identified endpoints `0` and `2π`. -/
theorem jordanParam_uniform_cyclic_inverse {γ : ℝ → ℂ}
    (hc : Continuous γ) (hper : Function.Periodic γ anglePeriod)
    (hinj : InjOn γ angleIco) {η : ℝ}
    (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ angleInterval, ∀ t ∈ angleInterval,
      ‖γ s - γ t‖ < δ → ∃ d : ℝ, |d| < η ∧ γ (s + d) = γ t := by
  let S  :=
    (angleInterval ×ˢ angleInterval) ∩
      {p | η ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ anglePeriod - η}
  have hSc : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs).inter
      (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const)
  have hn  :=
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm
  have hpos : ∀ p ∈ S, 0 < ‖γ p.1 - γ p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    intro he
    grind [jordanParam_eq_of_eq_of_abs_sub_lt]
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖γ p.1 - γ p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · grind
    · obtain ⟨p, hp, hmin⟩ := hSc.exists_isMinOn hne hn.continuousOn
      exact ⟨_, hpos p hp, fun q hq => hmin hq⟩
  refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
  have hshort : |s - t| < η ∨ anglePeriod - |s - t| < η := by
    by_contra h
    push_neg at h
    have hbad : (s, t) ∈ S := ⟨⟨hs, ht⟩, h.1, by linarith⟩
    exact (not_lt_of_ge (hbound _ hbad)) hst
  rcases hshort with h | h
  · refine ⟨t - s, ?_, by ring⟩
    simpa [abs_sub_comm] using h
  · by_cases hst' : s ≤ t
    · refine ⟨t - s - anglePeriod, ?_, ?_⟩
      · grind
      · rw [show s + (t - s - anglePeriod) = t - anglePeriod by ring]
        exact hper.sub_eq t
    · have hts  := le_of_not_ge hst'
      refine ⟨t - s + anglePeriod, ?_, ?_⟩
      · grind
      · rw [show s + (t - s + anglePeriod) = t + anglePeriod by ring]
        exact hper t

/-- Nearby points on the actual physical Jordan boundary are joined by
an actual short Lipschitz boundary arc. When they differ, that arc is
injective on its entire closed parameter interval. -/
theorem jordanParam_exists_short_arc {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ anglePeriod)
    (hinj : InjOn γ angleIco) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ γ '' angleInterval, ∀ q ∈ γ '' angleInterval,
      ‖p - q‖ < δ → ∃ (A : ℝ → ℂ) (C : NNReal), LipschitzWith C A ∧
        A 0 = p ∧ A 1 = q ∧ MapsTo A (Icc 0 1) (γ '' angleInterval) ∧
        (∀ u ∈ Icc 0 1, ∀ v ∈ Icc 0 1, ‖A u - A v‖ < ε) ∧
        (p ≠ q → InjOn A (Icc 0 1)) := by
  let η  := min Real.pi (ε / (K + 1))
  have hη : 0 < η := (by positivity)
  have hηπ : η < anglePeriod :=
    (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])
  obtain ⟨δ, hδ, hmod⟩ := jordanParam_uniform_cyclic_inverse hK.continuous hper hinj hη
  refine ⟨δ, hδ, ?_⟩
  rintro p ⟨s, hs, hsp⟩ q ⟨t, ht, htq⟩ hpq
  obtain ⟨d, hd, hend⟩ := hmod s hs t ht (by simpa only [hsp, htq] using hpq)
  let A  := fun u => γ (s + d * u)
  let C  := K * Real.toNNReal |d|
  have hAC : LipschitzWith C A := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    
    simpa only [A, C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d),
      Real.dist_eq, show s + d * u - (s + d * v) = d * (u - v) by ring,
      abs_mul, mul_assoc] using hK.dist_le_mul (s + d * u) (s + d * v)
  have hsmall : K * |d| < ε := by
    
    have h2 : ((K : ℝ) + 1) * η ≤ ε := by
      have h := min_le_right Real.pi (ε / ((K : ℝ) + 1))
      simpa [mul_comm] using (le_div_iff₀ (by positivity)).mp h
    nlinarith
  have huv (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Icc 0 1) :
      |u - v| ≤ 1 := abs_le.2 ⟨by grind, by grind⟩
  refine ⟨A, C, hAC, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [A] using hsp
  · simpa [A] using hend.trans htq
  · intro u _
    exact mem_image_Icc_of_periodic hper _
  · intro u hu v hv
    have h := hAC.dist_le_mul u v
    rw [dist_eq_norm, Real.dist_eq] at h
    have hC : (C : ℝ) = (K : ℝ) * |d| := by
      simp [C, NNReal.coe_mul]
    rw [hC] at h
    exact (h.trans (mul_le_of_le_one_right (by positivity) (huv u hu v hv))).trans_lt hsmall
  · intro hpq u hu v hv heq
    
    have hdist : |(s + d * u) - (s + d * v)| < anglePeriod := by
      rw [show (s + d * u) - (s + d * v) = d * (u - v) by ring, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg d) (huv u hu v hv)).trans_lt (hd.trans hηπ)
    have he := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq hdist
    refine mul_left_cancel₀ ?_ (add_left_cancel he)
    grind

section

variable (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk)
include hF hinj

private theorem riemannMapping_image_isOpen : IsOpen (F '' unitDisk) :=
  RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj

/-- The genuine cap is injective before its terminal endpoint, including
its first frontier endpoint. No distinction between the two endpoint
limits is assumed. -/
theorem riemannMapping_cap_injOn_Ico {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ anglePeriod)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' unitDisk)) : InjOn G (Ico a b) := by
  
  have hnot : G a ∉ F '' unitDisk := by
    rw [(riemannMapping_image_isOpen F hF hinj).frontier_eq] at hGa
    exact hGa.2
  intro x hx y hy heq
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exact (by grind)
    · exfalso
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply hnot
      refine ⟨circleMap ζ r y, harc hyi, ?_⟩
      grind
  · rcases eq_or_lt_of_le hy.1 with hya | hya
    · exfalso
      have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      apply hnot
      refine ⟨circleMap ζ r x, harc hxi, ?_⟩
      grind
    · have hxi : x ∈ Ioo a b := ⟨hxa, hx.2⟩
      have hyi : y ∈ Ioo a b := ⟨hya, hy.2⟩
      apply injOn_circleMap_of_abs_sub_le' hr hwidth hx hy
      apply hinj (harc hxi) (harc hyi)
      grind

/-- When the two physical endpoints differ, the full closed cap is an
injective arc. The endpoint exclusion uses the actual open image. -/
theorem riemannMapping_cap_injOn_Icc {ζ : ℂ} {r a b : ℝ}
    (hr : r ≠ 0) (hwidth : b - a ≤ anglePeriod)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' unitDisk))
    (hGb : G b ∈ frontier (F '' unitDisk)) (hab : G a ≠ G b) :
    InjOn G (Icc a b) := by
  
  have hnot : G b ∉ F '' unitDisk := by
    rw [(riemannMapping_image_isOpen F hF hinj).frontier_eq] at hGb
    exact hGb.2
  
  intro x hx y hy heq
  rcases lt_or_eq_of_le hx.2 with hxb | hxb
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · exact (riemannMapping_cap_injOn_Ico F hF hinj hr hwidth harc hGeq hGa) ⟨hx.1, hxb⟩ ⟨hy.1, hyb⟩ heq
    · rcases eq_or_lt_of_le hx.1 with hxa | hxa
      · exact False.elim (hab (by simpa only [← hxa, hyb] using heq))
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r x, harc ⟨hxa, hxb⟩, ?_⟩
        exact (hGeq ⟨hxa, hxb⟩).symm.trans ((by grind))
  · rcases lt_or_eq_of_le hy.2 with hyb | hyb
    · rcases eq_or_lt_of_le hy.1 with hya | hya
      · exact False.elim (hab (by simpa only [hxb, ← hya] using heq.symm))
      · exfalso
        apply hnot
        refine ⟨circleMap ζ r y, harc ⟨hya, hyb⟩, ?_⟩
        exact (hGeq ⟨hya, hyb⟩).symm.trans ((by grind))
    · simp [*]

end

/-- A closed Lipschitz loop lying in a genuine ball has zero winding at
every point outside that ball. The logarithm branch is constructed on
the actual loop, using the unit ball about `1` in the slit plane. -/
theorem windingNumber_eq_zero_of_image_ball {γ : ℝ → ℂ} {K : NNReal}
    (hK : LipschitzWith K γ) (hclosed : γ anglePeriod = γ 0)
    {p z : ℂ} {R : ℝ}
    (hball : ∀ θ ∈ angleInterval, ‖γ θ - p‖ < R)
    (hfar : R ≤ ‖p - z‖) : windingNumber γ z = 0 := by
  have hR  := (norm_nonneg _).trans_lt (hball 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hdpos  := hR.trans_le hfar
  have hd  := norm_pos_iff.mp hdpos
  have hslit : ∀ θ ∈ angleInterval,
      (p - z)⁻¹ * (γ θ - z) ∈ Complex.slitPlane := by
    intro θ hθ
    have hsmall : ‖(γ θ - p) / (p - z)‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one hdpos).mpr ((hball θ hθ).trans_le hfar)
    have heq : (p - z)⁻¹ * (γ θ - z) = 1 + (γ θ - p) / (p - z) := by
      field_simp [hd]; ring
    rw [heq]
    exact Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hi := integral_deriv_div_eq_log_sub hK Real.two_pi_pos.le hslit
  simp [hclosed, sub_self, windingNumber, hi]

end PolyaNeumann

end
