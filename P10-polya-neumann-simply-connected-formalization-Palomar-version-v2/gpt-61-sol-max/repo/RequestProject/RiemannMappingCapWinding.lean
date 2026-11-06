module

public import RequestProject.RiemannMappingBoundaryCrosscut


public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

public import RequestProject.RiemannMappingCapArclength
public import RequestProject.JordanWinding
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import RequestProject.WindingJump
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Genuine winding confinement and finite boundary limits

The actual finite-length cap is parametrized by its proved arclength
and closed by an actual short physical boundary arc. Its periodic
Lipschitz Jordan parametrization is constructed, not assumed.
The actual interior conformal inverse proves the midpoint normal
crossing. A proved local graph and the existing winding jump then
confine the entire cap image to a small physical ball. Completeness
gives the unique limit for every full interior boundary approach.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

private def joinCapArc (P A : ComplexCurve) u  :=
  if u ≤ 1 then P u else A (u - 1)

private theorem joinCapArc_lipschitz  
    (hP : LipschitzWith KP P) (hA : LipschitzWith KA A) (hjoin : A 0 = P 1) :
    LipschitzWith (max KP KA) (joinCapArc P A) := by
  have hPK : (KP : ℝ) ≤ (max KP KA : NNReal) := by exact_mod_cast le_max_left KP KA
  have hAK : (KA : ℝ) ≤ (max KP KA : NNReal) := by exact_mod_cast le_max_right KP KA
  have hord : ∀ x y : ℝ, x ≤ y →
      dist (joinCapArc P A x) (joinCapArc P A y) ≤ (max KP KA : NNReal) * dist x y := by
    intro x y hxy
    by_cases hy1 : y ≤ 1
    · have hx1 := hxy.trans hy1
      simp  [joinCapArc, if_pos hx1, if_pos hy1]
      exact (hP.dist_le_mul x y).trans
        (mul_le_mul_of_nonneg_right hPK dist_nonneg)
    · by_cases hx1 : x ≤ 1
      · simp only [joinCapArc, if_pos hx1, if_neg hy1]
        have hPx := hP.dist_le_mul x 1
        have hAy := hA.dist_le_mul 0 (y - 1)
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx1)] at hPx
        rw [← hjoin] at hPx
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith [lt_of_not_ge hy1])] at hAy
        have ht := dist_triangle (P x) (P 1) (A (y - 1))
        rw [← hjoin] at ht
        calc
          _ ≤ KP * (1 - x) + KA * (y - 1) := by linarith
          _ ≤ (max KP KA) * (1 - x) + (max KP KA) * (y - 1) :=
            add_le_add (mul_le_mul_of_nonneg_right hPK (by linarith))
              (mul_le_mul_of_nonneg_right hAK (by linarith [lt_of_not_ge hy1]))
          _ = (max KP KA) * dist x y := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
      · simp only [joinCapArc, if_neg hx1, if_neg hy1]
        have h := hA.dist_le_mul (x - 1) (y - 1)
        rw [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq] at h
        exact h.trans (mul_le_mul_of_nonneg_right hAK dist_nonneg)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with h | h
  · exact hord x y h
  · simpa  [dist_comm] using hord y x h

private theorem joinCapArc_injOn 
    (hP : InjOn P (Icc 0 1)) (hA : InjOn A (Icc 0 1))
    (hjoin : A 0 = P 1) (hclose : A 1 = P 0)
    (hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1)) :
    InjOn (joinCapArc P A) (Ico 0 2) := by
  have hcross : ∀ u ∈ Icc 0 1, ∀ v ∈ Ioo 1 2, P u ≠ A (v - 1) := by
    intro u hu v hv he
    have hv' : v - 1 ∈ Icc 0 1 := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · grind [Set.InjOn]
    · rcases lt_or_eq_of_le hu.2 with hu1 | hu1
      · exact Set.disjoint_left.mp hdisj (mem_image_of_mem P ⟨hu0, hu1⟩)
          ⟨v - 1, hv', he.symm⟩
      grind [Set.InjOn]
  intro u hu v hv he
  by_cases hu1 : u ≤ 1
  · by_cases hv1 : v ≤ 1
    · simp  [joinCapArc, if_pos hu1, if_pos hv1] at he
      grind [Set.InjOn]
    simp_all [joinCapArc]
  · by_cases hv1 : v ≤ 1
    · grind [joinCapArc]
    · simp only [joinCapArc, if_neg hu1, if_neg hv1] at he
      grind [Set.InjOn]

private theorem joinCapArc_image  (hjoin : A 0 = P 1) :
    joinCapArc P A '' Icc 0 2 = P '' Icc 0 1 ∪ A '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨u, hu, he⟩
    by_cases hu1 : u ≤ 1
    · left
      exact ⟨u, ⟨hu.1, hu1⟩, by simpa  [joinCapArc, if_pos hu1] using he⟩
    · right
      exact ⟨u - 1, ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩,
        by simpa  [joinCapArc, if_neg hu1] using he⟩
  · rintro (⟨u, hu, he⟩ | ⟨v, hv, he⟩)
    · exact ⟨u, ⟨hu.1, hu.2.trans (by norm_num)⟩,
        by simpa  [joinCapArc, if_pos hu.2] using he⟩
    · rcases eq_or_lt_of_le hv.1 with hv0 | hv0
      · refine ⟨1, by norm_num, ?_⟩
        simp_all [joinCapArc]
      · refine ⟨v + 1, ⟨by linarith, by linarith [hv.2]⟩, ?_⟩
        simp_all [joinCapArc]

private theorem normalized_lipschitz_cap {H : ComplexCurve} 
    (hH : LipschitzWith 1 H) (hL : 0 < L) :
    LipschitzWith (Real.toNNReal L) (fun u : ℝ => H (L * u)) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  have h := hH.dist_le_mul (L * u) (L * v)
  simpa  [Real.coe_toNNReal _ hL.le, Real.dist_eq, ← mul_sub, abs_of_pos hL] using h

private theorem normalized_lipschitz_cap_image {H : ComplexCurve}  (hL : 0 < L) :
    (fun u : ℝ => H (L * u)) '' Icc 0 1 = H '' Icc 0 L := by
  ext z
  constructor
  · aesop
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u / L, ⟨div_nonneg hu.1 hL.le, (div_le_one hL).mpr hu.2⟩, ?_⟩
    grind

/-- True finite-energy caps close to genuine periodic Lipschitz Jordan
loops, and the entire cap curve remains in their actual image. The
fixed interior point is outside the small ball containing the loop. -/
theorem riemannMapping_exists_small_lipschitz_cap_loop F
    (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hb : Bornology.IsBounded (F '' unitDisk))
      (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ circlePeriod)
    (hγinj : InjOn γ (Ico 0 circlePeriod))
    (himage : γ '' boundaryInterval = frontier (F '' unitDisk))
     (hζ : ‖ζ‖ = 1)  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G β : ComplexCurve) (KB : NNReal) (p : ℂ) (R : ℝ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ LipschitzWith KB β ∧
      Function.Periodic β circlePeriod ∧ InjOn β (Ico 0 circlePeriod) ∧
      0 < R ∧ R < ε ∧ R ≤ ‖p - F 0‖ ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' unitDisk) ∧
      G b ∈ frontier (F '' unitDisk) ∧ p = G a ∧
      G '' Icc a b ⊆ β '' boundaryInterval ∧
      β '' boundaryInterval ⊆ G '' Icc a b ∪ frontier (F '' unitDisk) ∧
      (∀ s ∈ boundaryInterval, ‖β s - p‖ < R) ∧ windingNumber β (F 0) = 0 := by
  let Ω := F '' ball 0 1
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball 0 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hF0 : F 0 ∈ Ω := ⟨0, by simp, rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (F 0) hF0
  let R := min ε ρ / 2
  have hR  := half_pos (lt_min hε hρ)
  have hRε : R < ε := by grind
  have hRρ : R ≤ ρ := by grind
  obtain ⟨η, hη, hshort⟩ := jordanParam_exists_short_arc hK hper hγinj hR
  let ξ := min (η / 2) R
  have hξ  := lt_min (half_pos hη) hR
  obtain ⟨r, G, τ, H, hr, hrδ, hr1, hGc, _hτc, hHlip, _hi, hL, hLξ,
    hGeq, hGa, hGb, hτm, hτr, _hτl, hH, hH0, hHL, hHim, hHi⟩ :=
    riemannMapping_exists_small_lipschitz_cap F hF hinj hb hζ hδ hξ
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let L := riemannCapArcLength F ζ r a b
  obtain ⟨hab, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have hwidth' : b - a ≤ 2 * Real.pi := by linarith
  have hLR  := hLξ.trans_le (min_le_right _ _)
  have hLp : R ≤ ‖G a - F 0‖ := by
    have hnot : G a ∉ Ω := by rw [hopen.frontier_eq] at hGa; exact hGa.2
    have hρp : ρ ≤ ‖G a - F 0‖ := by
      by_contra h
      exact hnot (hball (by rw [mem_ball, dist_eq_norm]; exact lt_of_not_ge h))
    exact hRρ.trans hρp
  have hHsmall : ∀ u ∈ Icc 0 L, ‖H u - G a‖ < R := by
    intro u hu
    have h := hHlip.dist_le_mul u 0
    rw [dist_eq_norm, hH0, Real.dist_eq, sub_zero, abs_of_nonneg hu.1,
      NNReal.coe_one, one_mul] at h
    exact (h.trans hu.2).trans_lt hLR
  have hfinish {Γ : ComplexCurve} {T : ℝ} {C : NNReal} (hΓ : LipschitzWith C Γ)
      (hT : 0 < T) (hcl : Γ T = Γ 0) (hΓi : InjOn Γ (Ico 0 T))
      (hcap : G '' Icc a b ⊆ Γ '' Icc 0 T)
      (hsub : Γ '' Icc 0 T ⊆ G '' Icc a b ∪ frontier Ω)
      (hsmall : ∀ u ∈ Icc 0 T, ‖Γ u - G a‖ < R) :
      ∃ (β : ComplexCurve) (KB : NNReal), LipschitzWith KB β ∧
        Function.Periodic β circlePeriod ∧ InjOn β (Ico 0 circlePeriod) ∧
        G '' Icc a b ⊆ β '' boundaryInterval ∧
        β '' boundaryInterval ⊆ G '' Icc a b ∪ frontier Ω ∧
        (∀ s ∈ boundaryInterval, ‖β s - G a‖ < R) ∧ windingNumber β (F 0) = 0 := by
    obtain ⟨β, ⟨KB, hKB⟩, hp, hii, him⟩ := exists_periodic_of_loop hΓ hT hcl hΓi
    have hβsmall : ∀ s ∈ boundaryInterval, ‖β s - G a‖ < R := by
      intro s hs
      obtain ⟨u, hu, he⟩ := him ▸ mem_image_of_mem β hs
      exact he ▸ hsmall u hu
    refine ⟨β, KB, hKB, hp, hii, ?_, ?_, hβsmall, ?_⟩
    · rwa [him]
    · rwa [him]
    · exact windingNumber_eq_zero_of_image_ball hKB (by simpa using hp 0) hβsmall hLp
  by_cases hend : G a = G b
  · obtain ⟨β, KB, hKB, hp, hii, hcap, hsub, hsmall, hw⟩ := hfinish hHlip hL
      (by rw [hHL, hH0]; exact hend.symm) hHi
      (by intro z hz; rw [hHim]; exact hz) (by rw [hHim]; exact subset_union_left) hHsmall
    exact ⟨r, G, β, KB, G a, R, hr, hrδ, hr1, hGc, hKB, hp, hii,
      hR, hRε, hLp, hGeq, hGa, hGb, rfl, hcap, hsub, hsmall, hw⟩
  · have hnear : ‖G b - G a‖ < η := by
      have hd := hHlip.dist_le_mul L 0
      rw [dist_eq_norm, hHL, hH0, Real.dist_eq, sub_zero, abs_of_pos hL,
        NNReal.coe_one, one_mul] at hd
      have hξη : ξ ≤ η / 2 := min_le_left _ _
      linarith
    obtain ⟨A, KA, hA, hA0, hA1, hAm, hAd, hAi⟩ :=
      hshort (G b) (by simpa only [himage] using hGb)
        (G a) (by simpa only [himage] using hGa) hnear
    have hAf : MapsTo A (Icc 0 1) (frontier Ω) := by simpa only [himage] using hAm
    have hGi := riemannMapping_cap_injOn_Icc F hF hinj hr.ne' hwidth' harc hGeq hGa hGb hend
    have hHic : InjOn H (Icc 0 L) := by
      intro u hu v hv he
      have hτuv := hGi (hτm u) (hτm v) ((hH u).symm.trans (he.trans (hH v)))
      grind
    let P := fun u => H (L * u)
    have hP0 : P 0 = G a := by simpa only [P, mul_zero] using hH0
    have hP1 : P 1 = G b := by simpa only [P, mul_one] using hHL
    have hPlip := normalized_lipschitz_cap hHlip hL
    have hPim : P '' Icc 0 1 = H '' Icc 0 L := normalized_lipschitz_cap_image hL
    have hPic : InjOn P (Icc 0 1) := by
      intro u hu v hv he
      have h := hHic ⟨mul_nonneg hL.le hu.1, mul_le_of_le_one_right hL.le hu.2⟩
        ⟨mul_nonneg hL.le hv.1, mul_le_of_le_one_right hL.le hv.2⟩ he
      exact mul_left_cancel₀ hL.ne' h
    have hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨u, hu, hPu⟩ ⟨v, hv, hAv⟩
      have hLu : L * u ∈ Ioo 0 L := ⟨mul_pos hL hu.1, mul_lt_of_lt_one_right hL hu.2⟩
      have hθm := hτm (L * u)
      have hθr := hτr (L * u) (Ioo_subset_Icc_self hLu)
      have hθi : τ (L * u) ∈ Ioo a b := by
        constructor
        · apply lt_of_le_of_ne hθm.1
          intro he
          rw [← he, riemannCapArcLength, intervalIntegral.integral_same] at hθr
          linarith [hLu.1]
        grind
      have hzΩ : z ∈ Ω := by
        refine ⟨circleMap ζ r (τ (L * u)), harc hθi, ?_⟩
        grind
      have hzf := hAv ▸ hAf hv
      rw [hopen.frontier_eq] at hzf
      exact hzf.2 hzΩ
    let Γ := joinCapArc P A
    have hΓlip := joinCapArc_lipschitz hPlip hA (hA0.trans hP1.symm)
    have hΓcl : Γ 2 = Γ 0 := by
      grind only [joinCapArc]
    have hΓi := joinCapArc_injOn hPic (hAi (Ne.symm hend))
      (hA0.trans hP1.symm) (hA1.trans hP0.symm) hdisj
    have hΓim : Γ '' Icc 0 2 = G '' Icc a b ∪ A '' Icc 0 1 := by
      grind only [joinCapArc_image]
    have hΓsmall : ∀ u ∈ Icc 0 2, ‖Γ u - G a‖ < R := by
      intro u hu
      by_cases hu1 : u ≤ 1
      · simp only [Γ, joinCapArc, if_pos hu1, P]
        exact hHsmall (L * u) ⟨mul_nonneg hL.le hu.1, mul_le_of_le_one_right hL.le hu1⟩
      · simp only [Γ, joinCapArc, if_neg hu1]
        grind
    obtain ⟨β, KB, hKB, hp, hii, hcap, hsub, hsmall, hw⟩ := hfinish hΓlip
      (by norm_num : (0 : ℝ) < 2) hΓcl hΓi
      (by rw [hΓim]; exact subset_union_left)
      (by rw [hΓim]; exact union_subset subset_union_left (fun z hz => Or.inr (by
        obtain ⟨u, hu, rfl⟩ := hz; exact hAf hu))) hΓsmall
    exact ⟨r, G, β, KB, G a, R, hr, hrδ, hr1, hGc, hKB, hp, hii,
      hR, hRε, hLp, hGeq, hGa, hGb, rfl, hcap, hsub, hsmall, hw⟩

/-- An actual radial segment remains on the farther side of the cap
circle under the displayed source-coordinate inequality. This is a
direct norm identity, not a planar separation premise. -/
theorem norm_sub_le_norm_radial_sub {z ζ : ℂ}
    (hdot : ‖z‖ ^ 2 ≤ ⟪z, ζ⟫_ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖z - ζ‖ ≤ ‖t • z - ζ‖ := by
  have heq : ‖t • z - ζ‖ ^ 2 - ‖z - ζ‖ ^ 2 =
      (1 - t) * (2 * ⟪z, ζ⟫_ℝ - (1 + t) * ‖z‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0, real_inner_smul_left]
    ring
  have hnon : 0 ≤ 2 * ⟪z, ζ⟫_ℝ - (1 + t) * ‖z‖ ^ 2 := by
    nlinarith
  have hsq : ‖z - ζ‖ ^ 2 ≤ ‖t • z - ζ‖ ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

section
variable (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {ζ } {r a b } (hr : 0 ≤ r) (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk) {G : ComplexCurve} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b)) (hGa : G a ∈ frontier (F '' unitDisk)) (hGb : G b ∈ frontier (F '' unitDisk))
include F hF hinj ζ r a b hr harc G hGeq hGa hGb

/-- An interior source point whose cap radius differs from `r` cannot
map to the actual cap curve, including its finite frontier endpoints. -/
theorem riemannMapping_notMem_cap_of_source_radius_ne
     (hz : z ∈ unitDisk) (hne : ‖z - ζ‖ ≠ r) :
    F z ∉ G '' Icc a b := by
  have hopen  :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball 0 1).isPreconnected
      hF hinj Subset.rfl isOpen_ball
  have hzΩ : F z ∈ F '' unitDisk := ⟨z, hz, rfl⟩
  rintro ⟨θ, hθ, he⟩
  rcases eq_or_lt_of_le hθ.1 with hθa | hθa
  · rw [hopen.frontier_eq] at hGa
    simp_all
  · rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · have hs  := hinj (harc ⟨hθa, hθb⟩) hz
        ((hGeq ⟨hθa, hθb⟩).symm.trans he)
      aesop
    · rw [hopen.frontier_eq] at hGb
      aesop

section
variable {β } {KB } (hKB : LipschitzWith KB β) (hclosed : β circlePeriod = β 0) (hsub : β '' boundaryInterval ⊆
      G '' Icc a b ∪ frontier (F '' unitDisk))
include β KB hKB hclosed hsub

/-- The actual conformal image of a proved source radial path avoids
the cap loop. Thus its winding is exactly the winding at the genuine
fixed interior point. This is the non-cap side selection used later. -/
theorem riemannMapping_winding_eq_at_zero_of_radial_side
     (hz : z ∈ unitDisk) (hfar : r < ‖z - ζ‖)
    (hdot : ‖z‖ ^ 2 ≤ ⟪z, ζ⟫_ℝ) : windingNumber β (F z) = windingNumber β (F 0) := by
  let Ω := F '' ball 0 1
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball 0 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hm : MapsTo (fun t : ℝ => t • z) (Icc 0 1) unitDisk := by
    intro t ht
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt (mem_ball_zero_iff.mp hz)
  let P : ComplexCurve := fun t => F (t • z)
  have hPc  := hF.continuousOn.comp
    (continuous_id.smul continuous_const).continuousOn hm
  have hdisj : Disjoint (P '' Icc 0 1) (β '' boundaryInterval) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨t, ht, htw⟩ hwβ
    have htΩ : w ∈ Ω := ⟨t • z, hm ht, htw⟩
    rcases hsub hwβ with hwcap | hwfront
    · have htr  := hfar.trans_le (norm_sub_le_norm_radial_sub hdot ht.1 ht.2)
      apply riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr harc hGeq hGa hGb
        (hm ht) htr.ne'
      grind
    · rw [hopen.frontier_eq] at hwfront
      exact hwfront.2 htΩ
  apply windingNumber_const_of_isPreconnected hKB hclosed
    (isPreconnected_Icc.image P hPc) hdisj
  · exact ⟨1, by norm_num, by simp [P]⟩
  · exact ⟨0, by norm_num, by simp [P]⟩

/-- The entire actual source cap has a single winding value, because
its true conformal image is connected and avoids the constructed loop.
This proves the propagation step without any region separation premise. -/
theorem riemannMapping_winding_const_on_source_cap
     (hz : z ∈ unitDisk ∩ ball ζ r)
    (hw : w ∈ unitDisk ∩ ball ζ r) :
    windingNumber β (F z) = windingNumber β (F w) := by
  let Ω := F '' ball 0 1
  let S := F '' (ball 0 1 ∩ ball ζ r)
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball 0 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  have hSc  :=
    ((convex_ball 0 1).inter (convex_ball ζ r)).isPreconnected.image F
      (hF.continuousOn.mono inter_subset_left)
  have hdisj : Disjoint S (β '' boundaryInterval) := by
    apply Set.disjoint_left.mpr
    rintro v ⟨x, hx, hFx⟩ hvβ
    rcases hsub hvβ with hvcap | hvfront
    · apply riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr harc hGeq hGa hGb
        hx.1 (ne_of_lt (by simpa  [dist_eq_norm] using hx.2))
      exact hFx.symm ▸ hvcap
    · rw [hopen.frontier_eq] at hvfront
      exact hvfront.2 ⟨x, hx.1, hFx⟩
  exact windingNumber_const_of_isPreconnected hKB hclosed hSc hdisj
    ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩

end


end


/-- The actual source midpoint of the circular cap. -/
def riemannCapMidpoint (ζ : ℂ) (r : ℝ)  := (1 - r) • ζ

/-- The inward physical normal obtained from the actual conformal
derivative, before choosing any boundary extension of the conformal map. -/
def riemannCapNormal F ζ (r : ℝ)  :=
  (r : ℂ) * deriv F (riemannCapMidpoint ζ r) * ζ

theorem riemannCapMidpoint_mem_disk  (hζ : ‖ζ‖ = 1) 
    (hr : 0 < r) (hr1 : r < 1) : riemannCapMidpoint ζ r ∈ unitDisk := by
  rw [mem_ball_zero_iff, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith), hζ, mul_one]
  linarith

theorem riemannCap_circle_midpoint  (hζ : ‖ζ‖ = 1) r :
    circleMap ζ r (riemannCapCenterAngle ζ) = riemannCapMidpoint ζ r := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa  [riemannCapCenterAngle, hζ]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  simp  [circleMap, he, riemannCapMidpoint]
  ring

/-- The midpoint normal is exactly `I` times the actual oriented cap
tangent. Its sign is fixed by the source circle and conformal orientation. -/
theorem riemannCapNormal_eq_I_mul_tangent F 
    (hζ : ‖ζ‖ = 1)  (hr : 0 < r) (hr1 : r < 1) :
    riemannCapNormal F ζ r = Complex.I *
      riemannCapDerivative F ζ r (riemannCapCenterAngle ζ) := by
  have hmid := riemannCapMidpoint_mem_disk hζ hr hr1
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa  [riemannCapCenterAngle, hζ]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  unfold riemannCapDerivative
  rw [riemannCap_circle_midpoint hζ r]
  unfold riemannInteriorDerivative
  rw [indicator_of_mem hmid]
  simp  [circleMap, he, riemannCapNormal]
  calc
    _ = -(Complex.I * Complex.I) * (r * deriv F (riemannCapMidpoint ζ r) * ζ) := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by ring

section
variable {f : RealMap} {d } (hd : HasDerivAt f d 0)
include f d hd

private theorem eventually_lt_of_hasDerivAt_neg (hdneg : d < 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 := by
  have he := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hdneg)
  filter_upwards [he, self_mem_nhdsWithin] with s hs hspos
  simp   at hs
  have hspos'  := hspos
  have hsub : f s - f 0 < 0 :=
    (mul_lt_mul_iff_right₀ (inv_pos.mpr hspos')).mp (by simpa   using hs)
  exact sub_neg.mp hsub

private theorem eventually_gt_of_hasDerivAt_pos (hdpos : 0 < d) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f 0 < f s := by
  have he := hd.tendsto_slope_zero_right.eventually (eventually_gt_nhds hdpos)
  filter_upwards [he, self_mem_nhdsWithin] with s hs hspos
  simp_all

end


section
variable (F : PlaneMap) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1)

section
include F hF hinj ζ hζ r hr hr1

/-- Genuine local normal crossing of the actual circular source cap.
The inverse is constructed on the open image; both crossing inequalities
follow from its proved derivative, rather than a separation premise. -/
theorem riemannMapping_exists_inverse_normal_crossing :
    ∃ J : PlaneMap, DifferentiableOn ℂ J (F '' unitDisk) ∧
      MapsTo J (F '' unitDisk) unitDisk ∧
      (∀ z ∈ unitDisk, J (F z) = z) ∧
      (∀ w ∈ F '' unitDisk, F (J w) = w) ∧
      let q := F (riemannCapMidpoint ζ r)
      let N := riemannCapNormal F ζ r
      N ≠ 0 ∧ HasDerivAt (fun s : ℝ => J (q + s • N)) (r • ζ) 0 ∧
      ∀ᶠ s in 𝓝[>] (0 : ℝ),
        J (q + s • N) ∈ unitDisk ∩ ball ζ r ∧
        J (q - s • N) ∈ unitDisk ∧ r < ‖J (q - s • N) - ζ‖ ∧
        ‖J (q - s • N)‖ ^ 2 < ⟪J (q - s • N), ζ⟫_ℝ ∧
        F (J (q + s • N)) = q + s • N ∧ F (J (q - s • N)) = q - s • N := by
  let Ω := F '' ball 0 1
  let z₀ := riemannCapMidpoint ζ r
  let q := F z₀
  let N := riemannCapNormal F ζ r
  have hz₀  := riemannCapMidpoint_mem_disk hζ hr hr1
  have hq : q ∈ Ω := ⟨z₀, hz₀, rfl⟩
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball
    (convex_ball 0 1).isPreconnected hF hinj Subset.rfl isOpen_ball
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball (convex_ball 0 1).isPreconnected hF hinj
  have hJq  := hJF z₀ hz₀
  have hDF : deriv F z₀ ≠ 0 :=
    RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hz₀
  have hζne : ζ ≠ 0 := by
    intro h
    simp_all
  have hN : N ≠ 0 := mul_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hDF) hζne
  have hJc  := (hJ.differentiableAt (hopen.mem_nhds hq)).continuousAt
  have hdF : HasDerivAt F (deriv F z₀) (J q) := by
    rw [hJq]
    exact (hF.differentiableAt (isOpen_ball.mem_nhds hz₀)).hasDerivAt
  have heFJ : ∀ᶠ w in 𝓝 q, F (J w) = w := by
    filter_upwards [hopen.mem_nhds hq] with w hw using hFJ w hw
  have hdJ  :=
    hdF.of_local_left_inverse hJc hDF heFJ
  have hdP : HasDerivAt (fun s : ℝ => q + s • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add q
    simp_all
  have hinvN : (deriv F z₀)⁻¹ * N = r • ζ := by
    change (deriv F z₀)⁻¹ * (r * deriv F z₀ * ζ) = r * ζ
    field_simp [hDF]
  have hdJP : HasDerivAt (fun s : ℝ => J (q + s • N)) (r • ζ) 0 := by
    simpa only [Function.comp_def, hinvN] using hdJ.comp_of_eq 0 hdP (by simp)
  have hJP0 : J (q + (0 : ℝ) • N) = z₀ := by simpa using hJq
  have hzsub : z₀ - ζ = (-r) • ζ := by
    change (1 - r) • ζ - ζ = (-r) • ζ
    module
  have hsqD : HasDerivAt (fun s : ℝ => ‖J (q + s • N) - ζ‖ ^ 2) (-2 * r ^ 2) 0 := by
    have h := (hdJP.sub_const ζ).norm_sq
    simp_all
  have hsq0 : ‖J (q + (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by
    simp_all
  have hplus : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖J (q + s • N) - ζ‖ ^ 2 < r ^ 2 := by
    simpa only [hsq0] using eventually_lt_of_hasDerivAt_neg hsqD (by nlinarith [sq_pos_of_pos hr])
  have hsqMinusD : HasDerivAt (fun s : ℝ => ‖J (q - s • N) - ζ‖ ^ 2)
      (2 * r ^ 2) 0 := by
    have h := hsqD.comp_of_eq 0 (hasDerivAt_neg (0 : ℝ)) (by simp)
    convert h using 1
    · ext <;> simp_all <;> ring
    · ring
  have hsqMinus0 : ‖J (q - (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by
    simp_all
  have hminus : ∀ᶠ s in 𝓝[>] (0 : ℝ), r ^ 2 < ‖J (q - s • N) - ζ‖ ^ 2 := by
    have he := eventually_gt_of_hasDerivAt_pos hsqMinusD (by nlinarith [sq_pos_of_pos hr])
    simpa only [hsqMinus0] using he
  have hdot₀ : ‖J q‖ ^ 2 < ⟪J q, ζ⟫_ℝ := by
    rw [hJq]
    simp only [z₀, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - r), hζ, mul_one, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    nlinarith
  have hminusC : ContinuousAt (fun s : ℝ => J (q - s • N)) 0 :=
    hJc.comp_of_eq (by fun_prop) (by simp)
  have hdotC : ContinuousAt (fun s : ℝ =>
      ⟪J (q - s • N), ζ⟫_ℝ - ‖J (q - s • N)‖ ^ 2) 0 :=
    (hminusC.inner continuousAt_const).sub (hminusC.norm.pow 2)
  have hdotE : ∀ᶠ s in 𝓝 (0 : ℝ),
      ‖J (q - s • N)‖ ^ 2 < ⟪J (q - s • N), ζ⟫_ℝ := by
    have hdot0 : (0 : ℝ) <
        ⟪J (q - (0 : ℝ) • N), ζ⟫_ℝ - ‖J (q - (0 : ℝ) • N)‖ ^ 2 := by
      simp_all
    have he := hdotC.tendsto.eventually (eventually_gt_nhds hdot0)
    exact he.mono fun s hs => sub_pos.mp hs
  have hΩplus : ∀ᶠ s in 𝓝 (0 : ℝ), q + s • N ∈ Ω := by
    have hp : Tendsto (fun s : ℝ => q + s • N) (𝓝 0) (𝓝 q) := by
      simpa only [zero_smul, add_zero] using hdP.continuousAt.tendsto
    exact hp.eventually (hopen.mem_nhds hq)
  have hΩminus : ∀ᶠ s in 𝓝 (0 : ℝ), q - s • N ∈ Ω := by
    have hp : ContinuousAt (fun s : ℝ => q - s • N) 0 := by fun_prop
    have hpt : Tendsto (fun s : ℝ => q - s • N) (𝓝 0) (𝓝 q) := by
      simpa only [zero_smul, sub_zero] using hp.tendsto
    exact hpt.eventually (hopen.mem_nhds hq)
  refine ⟨J, hJ, hJm, hJF, hFJ, hN, hdJP, ?_⟩
  filter_upwards [hplus, hminus, hdotE.filter_mono nhdsWithin_le_nhds,
    hΩplus.filter_mono nhdsWithin_le_nhds, hΩminus.filter_mono nhdsWithin_le_nhds]
    with s hsplus hsminus hsdot hsΩplus hsΩminus
  refine ⟨⟨hJm hsΩplus, ?_⟩, hJm hsΩminus, ?_, hsdot, hFJ _ hsΩplus, hFJ _ hsΩminus⟩
  · rw [mem_ball, dist_eq_norm]
    nlinarith
  · exact (sq_lt_sq₀ hr.le (norm_nonneg _)).mp hsminus

/-- Along the two genuine physical normals, winding is already constant:
the inward value is the winding on the entire source cap, and the outward
value equals the proved winding at `F 0`. No winding jump is assumed here. -/
theorem riemannMapping_winding_normal_values
    
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
      (hKB : LipschitzWith KB β)
    (hclosed : β circlePeriod = β 0)
    (hsub : β '' boundaryInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk))
     (hz : z ∈ unitDisk ∩ ball ζ r) :
    let q := F (riemannCapMidpoint ζ r)
    let N := riemannCapNormal F ζ r
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      windingNumber β (q + s • N) = windingNumber β (F z) ∧
      windingNumber β (q - s • N) = windingNumber β (F 0) := by
  obtain ⟨_, _, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  obtain ⟨J, _hJ, _hJm, _hJF, _hFJ, _hN, _hdJ, hcross⟩ :=
    riemannMapping_exists_inverse_normal_crossing F hF hinj hζ hr hr1
  filter_upwards [hcross] with s hs
  refine ⟨?_, ?_⟩
  · have hwind := riemannMapping_winding_const_on_source_cap F hF hinj hr.le
      harc hGeq hGa hGb hKB hclosed hsub hs.1 hz
    simp_all
  · have hwind := riemannMapping_winding_eq_at_zero_of_radial_side F hF hinj hr.le
      harc hGeq hGa hGb hKB hclosed hsub hs.2.1 hs.2.2.1 hs.2.2.2.1.le
    simp_all

end


private theorem exists_graph_of_local_regular_arc {G V : ComplexCurve}
    (hGc : Continuous G)  (ht : t ∈ Ioo a b)
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ)
    (hVc : ContinuousAt V t) (hV : V t ≠ 0)
    (havoid : ∀ θ ∈ Icc a b, θ ≠ t → G θ ≠ G t) :
    ∃ d : ℝ, 0 < d ∧ ∃ f : RealMap, ∀ θ ∈ Icc a b,
      ‖G θ - G t‖ < d →
        ((V t)⁻¹ * (G θ - G t)).im = f ((V t)⁻¹ * (G θ - G t)).re := by
  classical
  let c := (V t)⁻¹
  let x  := fun θ => (c * (G θ - G t)).re
  let xd  := fun θ => (c * V θ).re
  have hxd : ContinuousAt xd t :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hVc)
  have hxd0 : xd t = 1 := by simp only [xd, c, inv_mul_cancel₀ hV, Complex.one_re]
  have hpos  :=
    hxd.tendsto.eventually (eventually_gt_nhds (by rw [hxd0]; exact one_pos))
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    (hpos.and (isOpen_Ioo.mem_nhds ht))
  let η := ρ / 2
  have hη : 0 < η := half_pos hρ
  have hnear (θ : ℝ) (hθ : θ ∈ Icc (t - η) (t + η)) :
      0 < xd θ ∧ θ ∈ Ioo a b := by
    apply hρsub
    rw [mem_ball, Real.dist_eq]
    grind
  have hdx (θ : ℝ) (hθ : θ ∈ Ioo a b) : HasDerivAt x (xd θ) θ := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (((hd θ hθ).sub_const (G t)).const_mul c)
  have hxc : Continuous x :=
    Complex.continuous_re.comp (continuous_const.mul (hGc.sub continuous_const))
  have hxmono  :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hxc.continuousOn fun θ hθ => by
      have hn := hnear θ (interior_subset hθ)
      rw [(hdx θ hn.2).deriv]
      exact hn.1
  let f  := fun y => (c * (G (Function.invFunOn x (Icc (t - η) (t + η)) y) - G t)).im
  have hgraph (θ : ℝ) (hθ : θ ∈ Icc (t - η) (t + η)) :
      (c * (G θ - G t)).im = f (c * (G θ - G t)).re := by
    have hp : Function.invFunOn x (Icc (t - η) (t + η)) (x θ) ∈ Icc (t - η) (t + η) ∧
        x (Function.invFunOn x (Icc (t - η) (t + η)) (x θ)) = x θ :=
      Function.invFunOn_pos ⟨θ, hθ, rfl⟩
    have hi := hxmono.injOn hp.1 hθ hp.2
    grind
  have hleft : ∀ θ ∈ Icc a (t - η), G θ ≠ G t := by
    intro θ hθ
    exact havoid θ ⟨hθ.1, by linarith [hθ.2, ht.2]⟩ (by grind)
  have hright : ∀ θ ∈ Icc (t + η) b, G θ ≠ G t := by
    intro θ hθ
    exact havoid θ ⟨by linarith [hθ.1, ht.1], hθ.2⟩ (by grind)
  obtain ⟨d₁, hd₁, hfar₁⟩ := exists_pos_le_norm_sub hGc hleft
  obtain ⟨d₂, hd₂, hfar₂⟩ := exists_pos_le_norm_sub hGc hright
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, f, ?_⟩
  intro θ hθ hsmall
  apply hgraph
  constructor
  · by_contra hn
    have hθl : θ ∈ Icc a (t - η) := ⟨hθ.1, (lt_of_not_ge hn).le⟩
    exact not_lt_of_ge (hfar₁ θ hθl) (hsmall.trans_le (min_le_left _ _))
  · by_contra hn
    have hθr : θ ∈ Icc (t + η) b := ⟨(lt_of_not_ge hn).le, hθ.2⟩
    exact not_lt_of_ge (hfar₂ θ hθr) (hsmall.trans_le (min_le_right _ _))

include F hF hinj ζ hζ r hr hr1 in
/-- The actual cap loop is a local graph at its genuine physical
midpoint. The closing boundary arc stays away from this interior point;
all other cap parameters stay away by compactness and actual injectivity. -/
theorem riemannMapping_cap_loop_local_graph  (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    
    (hsub : β '' boundaryInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk)) :
    let q := F (riemannCapMidpoint ζ r)
    let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
    T ≠ 0 ∧ ∃ d : ℝ, 0 < d ∧ ∃ f : RealMap, ∀ w ∈ β '' boundaryInterval,
      ‖w - q‖ < d → (T⁻¹ * (w - q)).im = f (T⁻¹ * (w - q)).re := by
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let t := riemannCapCenterAngle ζ
  let q := F (riemannCapMidpoint ζ r)
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : t ∈ Ioo a b := ⟨by linarith, by linarith⟩
  obtain ⟨_, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have htm  := harc ht
  have hT  := riemannCapDerivative_ne_zero_interior F hF hinj ζ hr t htm
  have hGq  := (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  have hopen  :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball (convex_ball 0 1).isPreconnected
      hF hinj Subset.rfl isOpen_ball
  have hq : q ∈ F '' unitDisk :=
    ⟨riemannCapMidpoint ζ r, riemannCapMidpoint_mem_disk hζ hr hr1, rfl⟩
  have hGinj  := riemannMapping_cap_injOn_Ico F hF hinj hr.ne'
    (by linarith) harc hGeq hGa
  have havoid : ∀ θ ∈ Icc a b, θ ≠ t → G θ ≠ G t := by
    intro θ hθ hθt he
    rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · grind [Set.InjOn, Set.MapsTo, Set.EqOn]
    · rw [hopen.frontier_eq] at hGb
      grind
  have hd : ∀ θ ∈ Ioo a b, HasDerivAt G (riemannCapDerivative F ζ r θ) θ := by
    intro θ hθ
    apply (riemannCapDerivative_hasDerivAt F hF ζ r θ (harc hθ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with u hu using hGeq hu
  obtain ⟨d₁, hd₁, f, hgraph⟩ := exists_graph_of_local_regular_arc hGc ht hd
    (riemannCapDerivative_continuousAt_interior F hF ζ r t htm) hT havoid
  obtain ⟨d₂, hd₂, hball⟩ := Metric.isOpen_iff.mp hopen q hq
  refine ⟨hT, min d₁ d₂, lt_min hd₁ hd₂, f, ?_⟩
  intro w hw hsmall
  rcases hsub hw with ⟨θ, hθ, he⟩ | hwfront
  · grind
  · have hwΩ  := hball (by
      rw [mem_ball, dist_eq_norm]
      exact hsmall.trans_le (min_le_right _ _))
    rw [hopen.frontier_eq] at hwfront
    exact False.elim (hwfront.2 hwΩ)

end


section
variable {β : ComplexCurve} (hper : Function.Periodic β circlePeriod)
include β hper

private theorem windingNumber_shift t w :
    windingNumber (fun θ => β (θ + t)) w = windingNumber β w := by
  have hdper  := deriv_periodic hper
  have hp : Function.Periodic (fun θ => deriv β θ / (β θ - w)) circlePeriod := by
    simp_all
  have hd : deriv (fun θ => β (θ + t)) = fun θ => deriv β (θ + t) := by
    funext θ
    exact deriv_comp_add_const β t θ
  unfold windingNumber
  congr 1
  rw [hd]
  rw [intervalIntegral.integral_comp_add_right (fun θ => deriv β θ / (β θ - w)) t]
  simpa  [add_comm] using hp.intervalIntegral_add_eq t 0

end


private theorem windingNumber_jump_of_local_image_graph  
    (hKB : LipschitzWith KB β) (hper : Function.Periodic β circlePeriod)
    (hinj : InjOn β (Ico 0 circlePeriod))  
    (ht : β t = q) (hT : T ≠ 0)  (hd : 0 < d) {f : RealMap}
    (hgraph : ∀ w ∈ β '' boundaryInterval, ‖w - q‖ < d →
      (T⁻¹ * (w - q)).im = f (T⁻¹ * (w - q)).re) :
    ∃ σ : ℂ, (σ = 1 ∨ σ = -1) ∧ Tendsto (fun s : ℝ =>
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T))) (𝓝[>] 0) (𝓝 σ) := by
  let ρ  := fun θ => T⁻¹ * (β (θ + t) - q)
  have hρK : LipschitzWith (‖T⁻¹‖₊ * KB) ρ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : ρ x - ρ y = T⁻¹ * (β (x + t) - β (y + t)) := by ring
    have hb : ‖β (x + t) - β (y + t)‖ ≤ (KB : ℝ) * dist x y := by
      simpa only [dist_eq_norm, Real.dist_eq, add_sub_add_right_eq_sub] using
        hKB.dist_le_mul (x + t) (y + t)
    rw [dist_eq_norm, he, norm_mul]
    calc
      _ ≤ ‖T⁻¹‖ * (KB * dist x y) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
  have hρper : Function.Periodic ρ circlePeriod := by
    intro θ
    dsimp [ρ]
    rw [show (θ + 2 * Real.pi) + t = (θ + t) + 2 * Real.pi by ring, hper]
  have hρ0 : ρ 0 = 0 := by measurability
  have hβc  := hKB.continuous
  have hn : ContinuousAt (fun θ : ℝ => ‖β (θ + t) - q‖) 0 := by
    fun_prop
  have hn0 : ‖β ((0 : ℝ) + t) - q‖ = 0 := by bound
  have he  :=
    hn.tendsto.eventually (eventually_lt_nhds (by rw [hn0]; exact hd))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp he
  let η := min (δ / 2) (Real.pi / 2)
  have hη  := lt_min (half_pos hδ) (half_pos Real.pi_pos)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hηπ : η < Real.pi := (min_le_right _ _).trans_lt (by linarith [Real.pi_pos])
  have hg : ∀ θ ∈ Icc (-η) η, (ρ θ).im = f (ρ θ).re := by
    intro θ hθ
    apply hgraph _ (common_jordanParam_mem_image hper (θ + t))
    apply hδsub
    rw [mem_ball, Real.dist_eq, sub_zero]
    grind
  have hρinj : InjOn ρ (Icc (-η) η) := by
    intro x hx y hy heq
    have heq' : β (x + t) = β (y + t) := by
      grind
    have habs : |(x + t) - (y + t)| < 2 * Real.pi := by
      grind
    have hh := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj heq' habs
    linarith
  have hfar : ∀ θ ∈ Icc η (2 * Real.pi - η), ρ θ ≠ 0 := by
    intro θ hθ heq
    have hh := sub_eq_zero.mp
      ((mul_eq_zero.mp heq).resolve_left (inv_ne_zero hT))
    have hθpos := hη.trans_le hθ.1
    have habs : |(θ + t) - t| < 2 * Real.pi := by
      grind [Set.InjOn]
    have hh' := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (hh.trans ht.symm) habs
    linarith
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump hρK hρper hη hηπ hρ0 hg hρinj hfar
  have hw (s : ℝ) : windingNumber ρ ((s : ℂ) * Complex.I) =
      windingNumber β (q + s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hw' (s : ℝ) : windingNumber ρ (-((s : ℂ) * Complex.I)) =
      windingNumber β (q - s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1
    simp only [Complex.real_smul]
    ring
  refine ⟨σ, hσ, ?_⟩
  simpa only [hw, hw'] using hlim

section
variable (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) {ζ } (hζ : ‖ζ‖ = 1) {r } (hr : 0 < r) (hr1 : r < 1) {G } (hGc : Continuous G) (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r))) (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk)) (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk)) {β } {KB } (hKB : LipschitzWith KB β) (hper : Function.Periodic β circlePeriod) (hβinj : InjOn β (Ico 0 circlePeriod)) (hcap : G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ⊆ β '' boundaryInterval) (hsub : β '' boundaryInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk)) (hzero : windingNumber β (F 0) = 0)
include F hF hinj ζ hζ r hr hr1 G hGc hGeq hGa hGb β KB hKB hper hβinj hcap hsub hzero

/-- The winding on the actual conformal cap is `±1`. The sign is
deduced from the genuine graph jump and inverse normal crossing, while
the other side is selected by its proved radial path to `F 0`. -/
theorem riemannMapping_cap_winding_pm_one
     (hz : z ∈ unitDisk ∩ ball ζ r) :
    windingNumber β (F z) = 1 ∨ windingNumber β (F z) = -1 := by
  let q := F (riemannCapMidpoint ζ r)
  let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : riemannCapCenterAngle ζ ∈
      Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) := ⟨by linarith, by linarith⟩
  have hGq  :=
    (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  have hqβ  :=
    hcap ⟨riemannCapCenterAngle ζ, Ioo_subset_Icc_self ht, hGq⟩
  obtain ⟨t, _ht, hβt⟩ := hqβ
  obtain ⟨hT, d, hd, f, hg⟩ :=
    riemannMapping_cap_loop_local_graph F hF hinj hζ hr hr1 hGc hGeq hGa hGb hsub
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump_of_local_image_graph hKB hper hβinj hβt hT hd hg
  have hclosed : β circlePeriod = β 0 := by simpa   using hper 0
  have he := riemannMapping_winding_normal_values F hF hinj hζ hr hr1
    hGeq hGa hGb hKB hclosed hsub hz
  change ∀ᶠ s in 𝓝[>] 0,
    windingNumber β (q + s • riemannCapNormal F ζ r) = windingNumber β (F z) ∧
    windingNumber β (q - s • riemannCapNormal F ζ r) = windingNumber β (F 0) at he
  rw [riemannCapNormal_eq_I_mul_tangent F hζ hr hr1] at he
  have heq : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T)) = windingNumber β (F z) := by
    filter_upwards [he] with s hs
    rw [hs.1, hs.2, hzero, sub_zero]
  have hconst : Tendsto (fun s : ℝ =>
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T))) (𝓝[>] 0)
      (𝓝 (windingNumber β (F z))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with s hs using hs.symm
  have hvalue  := tendsto_nhds_unique hconst hlim
  grind

/-- A genuine cap loop contained in a physical ball confines the
entire conformal cap to that ball. A point outside the ball has winding
zero by the proved logarithm formula, contradicting the actual jump. -/
theorem riemannMapping_cap_image_subset_ball  
    (hball : ∀ θ ∈ boundaryInterval, ‖β θ - p‖ < R) :
    F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  rintro w ⟨z, hz, rfl⟩
  rw [mem_ball, dist_eq_norm]
  by_contra hn
  have hwind := windingNumber_eq_zero_of_image_ball hKB
    (by simpa   using hper 0) hball
    (by simpa  [norm_sub_rev] using le_of_not_gt hn)
  rcases riemannMapping_cap_winding_pm_one F hF hinj hζ hr hr1 hGc hGeq hGa hGb
      hKB hper hβinj hcap hsub hzero hz with h | h
  · rw [hwind] at h
    norm_num at h
  · rw [hwind] at h
    norm_num at h

end


/-- Genuine Courant–Lebesgue region oscillation. Arbitrarily small
source caps have their entire conformal images in arbitrarily small
physical balls centered on the actual frontier. No closed-disk extension
or endpoint injectivity of the conformal map is a premise. -/
theorem riemannMapping_exists_small_cap_region F
    (hF : DifferentiableOn ℂ F unitDisk)
    (hinj : InjOn F unitDisk)
    (hb : Bornology.IsBounded (F '' unitDisk))
      (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ circlePeriod)
    (hγinj : InjOn γ (Ico 0 circlePeriod))
    (himage : γ '' boundaryInterval = frontier (F '' unitDisk))
     (hζ : ‖ζ‖ = 1)  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r R : ℝ) (p : ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ 0 < R ∧ R < ε ∧
      p ∈ frontier (F '' unitDisk) ∧
      F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  obtain ⟨r, G, β, KB, p, R, hr, hrδ, hr1, hGc, hKB, hβper, hβinj,
    hR, hRε, _hRfar, hGeq, hGa, hGb, hp, hcap, hsub, hball, hzero⟩ :=
    riemannMapping_exists_small_lipschitz_cap_loop F hF hinj hb hK hper hγinj himage hζ hδ hε
  refine ⟨r, R, p, hr, hrδ, hr1, hR, hRε, hp.symm ▸ hGa, ?_⟩
  exact riemannMapping_cap_image_subset_ball F hF hinj hζ hr hr1 hGc hGeq hGa hGb
    hKB hβper hβinj hcap hsub hzero hball

section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) (hsc : SimplyConnectedSpace Ω) (F ) (hF : DifferentiableOn ℂ F unitDisk) (hinj : InjOn F unitDisk) (himage : F '' unitDisk = Ω) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
include Ω hb hL hsc F hF hinj himage ζ hζ

/-- The region estimate for an actual bounded simply connected
Lipschitz domain. Its physical Jordan boundary is constructed by the
proved domain topology; no additional curve is an assumption. -/
theorem riemannMapping_exists_small_cap_region_of_simplyConnected  (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r R : ℝ) (p : ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ 0 < R ∧ R < ε ∧
      p ∈ frontier Ω ∧ F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hγinj, hγimage⟩ :=
    exists_jordanParam_of_isPreconnected_frontier hb hL
      (isPreconnected_frontier_of_simplyConnected hb hL hsc)
  have hbF  := himage.symm ▸ hb
  have hγF : γ '' boundaryInterval = frontier (F '' unitDisk) := by
    simpa  [himage] using hγimage
  simpa  [himage] using riemannMapping_exists_small_cap_region F hF hinj hbF
    hK hper hγinj hγF hζ hδ hε

/-- Every actual boundary source point has a unique finite physical
frontier limit. Small-cap region confinement makes the full interior
approach filter Cauchy; no radial-only or normal-only limit is used. -/
theorem riemannMapping_exists_unique_boundary_limit :
    ∃! p : ℂ, p ∈ frontier Ω ∧ Tendsto F (𝓝[unitDisk] ζ) (𝓝 p) := by
  have hζcl : ζ ∈ closure unitDisk := by
    rw [closure_ball 0 one_ne_zero, mem_closedBall_zero_iff, hζ]
  letI  := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have hC : Cauchy (Filter.map F (𝓝[unitDisk] ζ)) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨r, R, p, hr, _hrδ, _hr1, _hR, hRε, _hp, hcap⟩ :=
      riemannMapping_exists_small_cap_region_of_simplyConnected hb hL hsc F hF hinj
        himage hζ zero_lt_one (half_pos hε)
    have hmem : ball p R ∈ Filter.map F (𝓝[unitDisk] ζ) := by
      change F ⁻¹' ball p R ∈ 𝓝[ball 0 1] ζ
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds ζ hr)] with z hz hzcap
      exact hcap ⟨z, ⟨hz, hzcap⟩, rfl⟩
    refine ⟨ball p R, hmem, ?_⟩
    intro x hx y hy
    have hxp : dist x p < R := hx
    have hyp : dist y p < R := hy
    have hpy : dist p y < R := by simpa  [dist_comm] using hyp
    have ht := dist_triangle x p y
    linarith
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have hpf : p ∈ frontier Ω := by
    rw [← himage]
    exact riemannMapping_limit_mem_frontier (l := 𝓝[ball 0 1] ζ)
      (z := id) F hF hinj hζ self_mem_nhdsWithin
      ((tendsto_id).mono_left nhdsWithin_le_nhds) hp
  refine ⟨p, ⟨hpf, hp⟩, ?_⟩
  intro q hq
  exact tendsto_nhds_unique hq.2 hp

end


end PolyaNeumann

end
