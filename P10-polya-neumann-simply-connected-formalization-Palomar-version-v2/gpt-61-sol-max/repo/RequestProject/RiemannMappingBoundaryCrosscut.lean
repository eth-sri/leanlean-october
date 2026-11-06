module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section



namespace PolyaNeumann

open MeasureTheory Set Metric Filter

section
variable {γ : ComplexCurve}
include γ

/-- A periodic Jordan parametrization has no repeated values at
parameters whose separation is strictly less than one period. -/
theorem jordanParam_eq_of_eq_of_abs_sub_lt
    (hper : Function.Periodic γ circlePeriod)
    (hinj : InjOn γ (Ico 0 circlePeriod)) 
    (hxy : γ x = γ y) (hlt : |x - y| < 2 * Real.pi) : x = y := by
  have hmem  := fun z => by
    have h := toIcoMod_mem_Ico Real.two_pi_pos 0 z
    rwa [zero_add] at h
  have hval : ∀ z, γ (toIcoMod Real.two_pi_pos 0 z) = γ z := fun z => by
    rw [toIcoMod, hper.sub_zsmul_eq]
  have h := hinj (hmem x) (hmem y) (by rw [hval, hval, hxy])
  simp only [toIcoMod] at h
  let n := toIcoDiv Real.two_pi_pos 0 x
  let m := toIcoDiv Real.two_pi_pos 0 y
  have hd : x - y = ((n - m : ℤ) : ℝ) * circlePeriod := by
    grind
  have hk : n - m = 0 := by
    rw [hd, abs_mul, abs_of_pos Real.two_pi_pos] at hlt
    have h1 : |((n - m : ℤ) : ℝ)| < 1 := by
      nlinarith [Real.two_pi_pos]
    have h2 : |n - m| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  grind

/-- The genuine inverse modulus, with the two possible short cyclic
directions retained. This includes the identified endpoints `0` and `2π`. -/
theorem jordanParam_uniform_cyclic_inverse
    (hc : Continuous γ) (hper : Function.Periodic γ circlePeriod)
    (hinj : InjOn γ (Ico 0 circlePeriod)) 
    (hη : 0 < η) :
    ∃ δ > 0, ∀ s ∈ boundaryInterval, ∀ t ∈ boundaryInterval,
      ‖γ s - γ t‖ < δ → ∃ d : ℝ, |d| < η ∧ γ (s + d) = γ t := by
  let S  :=
    (boundaryInterval ×ˢ boundaryInterval) ∩
      {p | η ≤ |p.1 - p.2| ∧ |p.1 - p.2| ≤ 2 * Real.pi - η}
  have hSc : IsCompact S := by
    apply (isCompact_Icc.prod isCompact_Icc).inter_right
    exact (isClosed_le continuous_const (continuous_fst.sub continuous_snd).abs).inter
      (isClosed_le (continuous_fst.sub continuous_snd).abs continuous_const)
  have hn  :=
    ((hc.comp continuous_fst).sub (hc.comp continuous_snd)).norm
  have hpos : ∀ p ∈ S, 0 < ‖γ p.1 - γ p.2‖ := by
    intro p hp
    apply norm_pos_iff.mpr
    grind [jordanParam_eq_of_eq_of_abs_sub_lt]
  obtain ⟨δ, hδ, hbound⟩ : ∃ δ > 0, ∀ p ∈ S, δ ≤ ‖γ p.1 - γ p.2‖ := by
    rcases S.eq_empty_or_nonempty with he | hne
    · exact ⟨1, zero_lt_one, by simp [he]⟩
    · obtain ⟨p, hp, hmin⟩ := hSc.exists_isMinOn hne hn.continuousOn
      tauto
  refine ⟨δ, hδ, fun s hs t ht hst => ?_⟩
  have hshort : |s - t| < η ∨ 2 * Real.pi - |s - t| < η := by
    by_contra h
    push_neg at h
    have hbad : (s, t) ∈ S := ⟨⟨hs, ht⟩, h.1, by linarith [h.2]⟩
    exact (not_lt_of_ge (hbound _ hbad)) hst
  rcases hshort with h | h
  · refine ⟨t - s, ?_, by ring⟩
    simpa only [abs_sub_comm] using h
  · by_cases hst' : s ≤ t
    · refine ⟨t - s - 2 * Real.pi, ?_, ?_⟩
      · grind
      · rw [show s + (t - s - 2 * Real.pi) = t - 2 * Real.pi by ring]
        exact hper.sub_eq t
    · have hts  := le_of_not_ge hst'
      refine ⟨t - s + 2 * Real.pi, ?_, ?_⟩
      · rw [abs_of_nonneg (sub_nonneg.mpr hts)] at h
        grind
      · rw [show s + (t - s + 2 * Real.pi) = t + 2 * Real.pi by ring]
        exact hper t

theorem common_jordanParam_mem_image
    (hper : Function.Periodic γ circlePeriod) s :
    γ s ∈ γ '' boundaryInterval := by
  refine ⟨toIcoMod Real.two_pi_pos 0 s, ?_, ?_⟩
  · have h := toIcoMod_mem_Ico Real.two_pi_pos 0 s
    grind
  · rw [toIcoMod, hper.sub_zsmul_eq]

/-- Nearby points on the actual physical Jordan boundary are joined by
an actual short Lipschitz boundary arc. When they differ, that arc is
injective on its entire closed parameter interval. -/
theorem jordanParam_exists_short_arc 
    (hK : LipschitzWith K γ) (hper : Function.Periodic γ circlePeriod)
    (hinj : InjOn γ (Ico 0 circlePeriod))  (hε : 0 < ε) :
    ∃ δ > 0, ∀ p ∈ γ '' boundaryInterval, ∀ q ∈ γ '' boundaryInterval,
      ‖p - q‖ < δ → ∃ (A : ComplexCurve) (C : NNReal), LipschitzWith C A ∧
        A 0 = p ∧ A 1 = q ∧ MapsTo A (Icc 0 1) (γ '' boundaryInterval) ∧
        (∀ u ∈ Icc 0 1, ∀ v ∈ Icc 0 1, ‖A u - A v‖ < ε) ∧
        (p ≠ q → InjOn A (Icc 0 1)) := by
  let η  := min Real.pi (ε / (K + 1))
  have hη : 0 < η := lt_min Real.pi_pos (div_pos hε (by positivity))
  obtain ⟨δ, hδ, hmod⟩ := jordanParam_uniform_cyclic_inverse hK.continuous hper hinj hη
  refine ⟨δ, hδ, ?_⟩
  rintro p ⟨s, hs, hsp⟩ q ⟨t, ht, htq⟩ hpq
  obtain ⟨d, hd, hend⟩ := hmod s hs t ht (by simpa only [hsp, htq] using hpq)
  let A  := fun u => γ (s + d * u)
  let C  := K * Real.toNNReal |d|
  have hAC : LipschitzWith C A := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    have h := hK.dist_le_mul (s + d * u) (s + d * v)
    simpa only [C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d), Real.dist_eq, show s + d * u - (s + d * v) = d * (u - v) by ring, abs_mul, mul_assoc] using h
  have hsmall : (K : ℝ) * |d| < ε := by
    have h1 : ((K : ℝ) + 1) * |d| < ((K : ℝ) + 1) * η :=
      mul_lt_mul_of_pos_left hd (by positivity)
    have h2 : ((K : ℝ) + 1) * η ≤ ε := by
      have h := min_le_right Real.pi (ε / (K + 1))
      simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp h
    nlinarith
  have huv (u : ℝ) (hu : u ∈ Icc 0 1) (v : ℝ) (hv : v ∈ Icc 0 1) :
      |u - v| ≤ 1 := abs_le.2 ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
  refine ⟨A, C, hAC, ?_, ?_, ?_, ?_, ?_⟩
  · grind
  · grind
  · intro u _
    exact common_jordanParam_mem_image hper _
  · intro u hu v hv
    have h := hAC.dist_le_mul u v
    rw [dist_eq_norm, Real.dist_eq] at h
    have hC : (C : ℝ) = (K : ℝ) * |d| := by
      simp only [C, NNReal.coe_mul, Real.coe_toNNReal _ (abs_nonneg d)]
    rw [hC] at h
    exact (h.trans (mul_le_of_le_one_right (by positivity) (huv u hu v hv))).trans_lt hsmall
  · intro hpq u hu v hv heq
    have hd0 : d ≠ 0 := by
      grind
    have hdist : |(s + d * u) - (s + d * v)| < 2 * Real.pi := by
      rw [show (s + d * u) - (s + d * v) = d * (u - v) by ring, abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg d) (huv u hu v hv)).trans_lt ((hd.trans_le (min_le_left _ _)).trans (by linarith [Real.pi_pos]))
    grind only [jordanParam_eq_of_eq_of_abs_sub_lt]

end


private theorem riemannMapping_image_isOpen (F : PlaneMap)
    (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk) : IsOpen (F '' unitDisk) :=
  RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball (0 : ℂ) 1).isPreconnected
    hF hinj Subset.rfl isOpen_ball

section
variable (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {ζ } {r a b } (hr : r ≠ 0) (hwidth : b - a ≤ 2 * Real.pi) (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk) {G : ComplexCurve} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b)) (hGa : G a ∈ frontier (F '' unitDisk))
include F hF hinj ζ r a b hr hwidth harc G hGeq hGa

/-- The genuine cap is injective before its terminal endpoint, including
its first frontier endpoint. No distinction between the two endpoint
limits is assumed. -/
theorem riemannMapping_cap_injOn_Ico : InjOn G (Ico a b) := by
  have hopen := riemannMapping_image_isOpen F hF hinj
  have hnot : G a ∉ F '' unitDisk := by
    rw [hopen.frontier_eq] at hGa
    exact hGa.2
  intro x hx y hy heq
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · grind [Set.InjOn, Set.MapsTo, Set.EqOn]
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
theorem riemannMapping_cap_injOn_Icc
    (hGb : G b ∈ frontier (F '' unitDisk)) (hab : G a ≠ G b) :
    InjOn G (Icc a b) := by
  have hopen := riemannMapping_image_isOpen F hF hinj
  have hnot : G b ∉ F '' unitDisk := by
    rw [hopen.frontier_eq] at hGb
    exact hGb.2
  have hi := riemannMapping_cap_injOn_Ico F hF hinj hr hwidth harc hGeq hGa
  grind [Set.InjOn, Set.MapsTo, Set.EqOn]

end


/-- A closed Lipschitz loop lying in a genuine ball has zero winding at
every point outside that ball. The logarithm branch is constructed on
the actual loop, using the unit ball about `1` in the slit plane. -/
theorem windingNumber_eq_zero_of_image_ball  
    (hK : LipschitzWith K γ) (hclosed : γ circlePeriod = γ 0)
     
    (hball : ∀ θ ∈ boundaryInterval, ‖γ θ - p‖ < R)
    (hfar : R ≤ ‖p - z‖) : windingNumber γ z = 0 := by
  have hR  := (norm_nonneg _).trans_lt (hball 0 ⟨le_rfl, Real.two_pi_pos.le⟩)
  have hdpos  := hR.trans_le hfar
  have hd  := norm_pos_iff.mp hdpos
  have hslit : ∀ θ ∈ boundaryInterval,
      (p - z)⁻¹ * (γ θ - z) ∈ Complex.slitPlane := by
    intro θ hθ
    have hsmall : ‖(γ θ - p) / (p - z)‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one hdpos).mpr ((hball θ hθ).trans_le hfar)
    have heq : (p - z)⁻¹ * (γ θ - z) = 1 + (γ θ - p) / (p - z) := by
      field_simp; ring
    rw [heq]
    exact Complex.mem_slitPlane_of_norm_lt_one hsmall
  have hi := integral_deriv_div_eq_log_sub hK Real.two_pi_pos.le (inv_ne_zero hd) hslit
  grind only [windingNumber]

end PolyaNeumann
