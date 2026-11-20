module

public import RequestProject.RiemannMappingCapArclength
public import Mathlib.Analysis.Convex.Contractible
public import RequestProject.JordanWinding
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import RequestProject.WindingJump
public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Filter
open scoped Topology InnerProductSpace RealInnerProductSpace

private def joinCapArc (P A : ℝ → ℂ) (u : ℝ) : ℂ :=
  if u ≤ 1 then P u else A (u - 1)

private theorem joinCapArc_lipschitz {P A : ℝ → ℂ} {KP KA : NNReal}
    (hP : LipschitzWith KP P) (hA : LipschitzWith KA A) (hjoin : A 0 = P 1) :
    LipschitzWith (max KP KA) (joinCapArc P A) := by
  have hPK : KP ≤ (max KP KA) := by simp
  have hAK : KA ≤ (max KP KA) := by simp
  have hord : ∀ x y : ℝ, x ≤ y →
      dist (joinCapArc P A x) (joinCapArc P A y) ≤ (max KP KA) * dist x y := by
    intro x y hxy
    by_cases hy1 : y ≤ 1
    · 
      simp only [joinCapArc, if_pos (hxy.trans hy1), if_pos hy1]
      exact (hP.dist_le_mul x y).trans
        (mul_le_mul_of_nonneg_right hPK dist_nonneg)
    · by_cases hx1 : x ≤ 1
      · simp only [joinCapArc, if_pos hx1, if_neg hy1]
        have hPx := hP.dist_le_mul x 1
        have hAy := hA.dist_le_mul 0 (y - 1)
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx1)] at hPx
        rw [← hjoin] at hPx
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith)] at hAy
        have ht := dist_triangle (P x) (P 1) (A (y - 1))
        rw [← hjoin] at ht
        calc
          _ ≤ KP * (1 - x) + KA * (y - 1) := by linarith
          _ ≤ (max KP KA) * (1 - x) + (max KP KA) * (y - 1) :=
            (by bound)
          _ = _ := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
            ring
      · simp [joinCapArc, if_neg hx1, if_neg hy1]
        have h := hA.dist_le_mul (x - 1) (y - 1)
        rw [Real.dist_eq, sub_sub_sub_cancel_right, ← Real.dist_eq] at h
        exact h.trans (mul_le_mul_of_nonneg_right hAK dist_nonneg)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with h | h
  · exact hord x y h
  · simpa [dist_comm] using hord y x h

section

variable (F : ℂ → ℂ) (hF : DifferentiableOn ℂ F unitDisk) (ζ : ℂ) (hinj : InjOn F unitDisk)
    (r : ℝ) (hb : Bornology.IsBounded (F '' unitDisk))

private theorem joinCapArc_injOn {P A : ℝ → ℂ}
    (hP : InjOn P (Icc 0 1)) (hA : InjOn A (Icc 0 1))
    (hjoin : A 0 = P 1) (hclose : A 1 = P 0)
    (hdisj : Disjoint (P '' Ioo 0 1) (A '' Icc 0 1)) :
    InjOn (joinCapArc P A) (Ico 0 2) := by
  have hcross : ∀ u ∈ Icc 0 1, ∀ v ∈ Ioo 1 2, P u ≠ A (v - 1) := by
    intro u hu v hv he
    have hv' : v - 1 ∈ Icc 0 1 := (by grind)
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · have h := hA (show (1 : ℝ) ∈ Icc 0 1 by norm_num) hv'
        (hclose.trans (by simpa only [← hu0] using he))
      linarith [hv.2]
    · rcases lt_or_eq_of_le hu.2 with hu1 | hu1
      · exact Set.disjoint_left.mp hdisj ((by grind))
          ⟨v - 1, hv', he.symm⟩
      · have h := hA (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hv'
          (hjoin.trans (by simpa only [hu1] using he))
        linarith [hv.1]
  intro u hu v hv he
  by_cases hu1 : u ≤ 1
  · by_cases hv1 : v ≤ 1
    · simp [joinCapArc, if_pos hu1, if_pos hv1] at he
      exact hP ⟨hu.1, hu1⟩ ⟨hv.1, hv1⟩ he
    · simp [joinCapArc, if_pos hu1, if_neg hv1] at he
      exact (by grind)
  · by_cases hv1 : v ≤ 1
    · simp [joinCapArc, if_neg hu1, if_pos hv1] at he
      exact (by grind)
    · simp [joinCapArc, if_neg hu1, if_neg hv1] at he
      have h := hA ⟨by linarith [lt_of_not_ge hu1], by linarith [hu.2]⟩
        ⟨by linarith [lt_of_not_ge hv1], by linarith [hv.2]⟩ he
      linarith

private theorem joinCapArc_image {P A : ℝ → ℂ} (hjoin : A 0 = P 1) :
    joinCapArc P A '' Icc 0 2 = P '' Icc 0 1 ∪ A '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨u, hu, he⟩
    by_cases hu1 : u ≤ 1
    · left
      exact ⟨u, ⟨hu.1, hu1⟩, by simpa only [joinCapArc, if_pos hu1] using he⟩
    · right
      exact ⟨u - 1, (by grind),
        by simpa only [joinCapArc, if_neg hu1] using he⟩
  · rintro (⟨u, hu, he⟩ | ⟨v, hv, he⟩)
    · exact ⟨u, (by grind),
        by simpa only [joinCapArc, if_pos hu.2] using he⟩
    · rcases eq_or_lt_of_le hv.1 with hv0 | hv0
      · refine ⟨1, by norm_num, ?_⟩
        simpa only [joinCapArc, if_pos (by norm_num : (1 : ℝ) ≤ 1), ← hjoin, ← hv0] using he
      · refine ⟨v + 1, (by grind), ?_⟩
        simpa only [joinCapArc, if_neg (by linarith : ¬v + 1 ≤ 1), add_sub_cancel_right] using he

private theorem normalized_lipschitz_cap {H : ℝ → ℂ} {L : ℝ}
    (hH : LipschitzWith 1 H) (hL : 0 < L) :
    LipschitzWith (Real.toNNReal L) (fun u : ℝ => H (L * u)) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  
  simpa only [NNReal.coe_one, one_mul, Real.coe_toNNReal _ hL.le,
    Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hL] using hH.dist_le_mul (L * u) (L * v)

private theorem normalized_lipschitz_cap_image {H : ℝ → ℂ} {L : ℝ} (hL : 0 < L) :
    (fun u : ℝ => H (L * u)) '' Icc 0 1 = H '' Icc 0 L := by
  ext z
  constructor
  · aesop
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u / L, ⟨div_nonneg hu.1 hL.le, (div_le_one hL).mpr hu.2⟩, ?_⟩
    change H (L * (u / L)) = H u
    rw [mul_div_cancel₀ _ hL.ne']

include hF hb hinj in
/-- True finite-energy caps close to genuine periodic Lipschitz Jordan
loops, and the entire cap curve remains in their actual image. The
fixed interior point is outside the small ball containing the loop. -/
theorem riemannMapping_exists_small_lipschitz_cap_loop
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod)
    (hγinj : InjOn γ angleIco)
    (himage : γ '' angleInterval = frontier (F '' unitDisk))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r : ℝ) (G β : ℝ → ℂ) (KB : NNReal) (p : ℂ) (R : ℝ),
      0 < r ∧ r < δ ∧ r < 1 ∧ Continuous G ∧ LipschitzWith KB β ∧
      Function.Periodic β anglePeriod ∧ InjOn β angleIco ∧
      0 < R ∧ R < ε ∧ R ≤ ‖p - F 0‖ ∧
      let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
      let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
      EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b) ∧
      G a ∈ frontier (F '' unitDisk) ∧
      G b ∈ frontier (F '' unitDisk) ∧ p = G a ∧
      G '' Icc a b ⊆ β '' angleInterval ∧
      β '' angleInterval ⊆ G '' Icc a b ∪ frontier (F '' unitDisk) ∧
      (∀ s ∈ angleInterval, ‖β s - p‖ < R) ∧ windingNumber β (F 0) = 0 := by
  let Ω := F '' unitDisk
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  have hF0 : F 0 ∈ Ω := ⟨0, by simp, rfl⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen (F 0) hF0
  let R := min ε ρ / 2
  have hR  := half_pos (lt_min hε hρ)
  have hRε : R < ε := by grind [min_le_left ε ρ]
  have hRρ : R ≤ ρ := by grind [min_le_right ε ρ]
  obtain ⟨η, hη, hshort⟩ := jordanParam_exists_short_arc hK hper hγinj hR
  let ξ := min (η / 2) R
  
  obtain ⟨r, G, τ, H, hr, hrδ, hr1, hGc, _hτc, hHlip, _hi, hL, hLξ,
    hGeq, hGa, hGb, hτm, hτr, _hτl, hH, hH0, hHL, hHim, hHi⟩ :=
    riemannMapping_exists_small_lipschitz_cap F hF hinj hb hζ hδ (lt_min (half_pos hη) hR)
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let L := riemannCapArcLength F ζ r a b
  obtain ⟨hab, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  
  have hLR  := hLξ.trans_le (min_le_right _ _)
  have hLp : R ≤ ‖G a - F 0‖ := by
    have hnot : G a ∉ Ω := by rw [hopen.frontier_eq] at hGa; exact hGa.2
    
    apply hRρ.trans
    by_contra h
    exact hnot (hball (by rw [mem_ball, dist_eq_norm]; exact lt_of_not_ge h))
  have hHsmall : ∀ u ∈ Icc 0 L, ‖H u - G a‖ < R := by
    intro u hu
    have h := hHlip.dist_le_mul u 0
    rw [dist_eq_norm, hH0, Real.dist_eq, sub_zero, abs_of_nonneg hu.1,
      NNReal.coe_one, one_mul] at h
    grind
  have hfinish {Γ : ℝ → ℂ} {T : ℝ} {C : NNReal} (hΓ : LipschitzWith C Γ)
      (hT : 0 < T) (hcl : Γ T = Γ 0) (hΓi : InjOn Γ (Ico 0 T))
      (hcap : G '' Icc a b ⊆ Γ '' Icc 0 T)
      (hsub : Γ '' Icc 0 T ⊆ G '' Icc a b ∪ frontier Ω)
      (hsmall : ∀ u ∈ Icc 0 T, ‖Γ u - G a‖ < R) :
      ∃ (β : ℝ → ℂ) (KB : NNReal), LipschitzWith KB β ∧
        Function.Periodic β anglePeriod ∧ InjOn β angleIco ∧
        G '' Icc a b ⊆ β '' angleInterval ∧
        β '' angleInterval ⊆ G '' Icc a b ∪ frontier Ω ∧
        (∀ s ∈ angleInterval, ‖β s - G a‖ < R) ∧ windingNumber β (F 0) = 0 := by
    obtain ⟨β, ⟨KB, hKB⟩, hp, hii, him⟩ := exists_periodic_of_loop hΓ hT hcl hΓi
    have hβsmall : ∀ s ∈ angleInterval, ‖β s - G a‖ < R := by
      intro s hs
      obtain ⟨u, hu, he⟩ := him ▸ mem_image_of_mem β hs
      exact he ▸ hsmall u hu
    refine ⟨β, KB, hKB, hp, hii, ?_, ?_, hβsmall, ?_⟩
    · rwa [him]
    · rwa [him]
    · exact windingNumber_eq_zero_of_image_ball hKB (by simpa using hp 0) hβsmall hLp
  by_cases hend : G a = G b
  · obtain ⟨β, KB, hKB, hp, hii, hcap, hsub, hsmall, hw⟩ := hfinish hHlip hL
      (by grind) hHi
      (by grind) (by rw [hHim]; exact subset_union_left) hHsmall
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
    have hGi := riemannMapping_cap_injOn_Icc F hF hinj hr.ne' (by linarith) harc hGeq hGa hGb hend
    have hHic : InjOn H (Icc 0 L) := by
      intro u hu v hv he
      
      have hru := hτr u hu
      rw [(hGi (hτm u) (hτm v) ((hH u).symm.trans (he.trans (hH v))))] at hru
      exact hru.symm.trans (hτr v hv)
    let P  := fun u => H (L * u)
    have hP0 : P 0 = G a := by simpa only [P, mul_zero] using hH0
    have hP1 : P 1 = G b := by simpa only [P, mul_one] using hHL
    
    
    have hPic : InjOn P (Icc 0 1) := by
      intro u hu v hv he
      
      exact mul_left_cancel₀ hL.ne' (hHic ⟨mul_nonneg hL.le hu.1, mul_le_of_le_one_right hL.le hu.2⟩
        ⟨mul_nonneg hL.le hv.1, mul_le_of_le_one_right hL.le hv.2⟩ he)
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
        · apply lt_of_le_of_ne hθm.2
          intro he
          rw [he] at hθr
          linarith [hLu.2]
      
      have hzf  := hAv ▸ hAf hv
      rw [hopen.frontier_eq] at hzf
      apply hzf.2
      refine ⟨circleMap ζ r (τ (L * u)), harc hθi, ?_⟩
      exact (hGeq hθi).symm.trans ((hH _).symm.trans hPu)
    let Γ := joinCapArc P A
    have hΓlip := joinCapArc_lipschitz (normalized_lipschitz_cap hHlip hL) hA (hA0.trans hP1.symm)
    have hΓcl : Γ 2 = Γ 0 := by
      simp only [Γ, joinCapArc, if_neg (by norm_num : ¬(2 : ℝ) ≤ 1),
        if_pos (by norm_num : (0 : ℝ) ≤ 1), show (2 : ℝ) - 1 = 1 by norm_num, hA1, hP0]
    
    have hΓim : Γ '' Icc 0 2 = G '' Icc a b ∪ A '' Icc 0 1 := by
      rw [joinCapArc_image (hA0.trans hP1.symm), (normalized_lipschitz_cap_image hL), hHim]
    have hΓsmall : ∀ u ∈ Icc 0 2, ‖Γ u - G a‖ < R := by
      intro u hu
      by_cases hu1 : u ≤ 1
      · simp [Γ, joinCapArc, if_pos hu1, P]
        exact hHsmall (L * u) ⟨mul_nonneg hL.le hu.1, mul_le_of_le_one_right hL.le hu1⟩
      · simp [Γ, joinCapArc, if_neg hu1]
        rw [← hA1]
        exact hAd (u - 1) ⟨by linarith, by linarith [hu.2]⟩ 1 (by norm_num)
    obtain ⟨β, KB, hKB, hp, hii, hcap, hsub, hsmall, hw⟩ := hfinish hΓlip
      (by positivity) hΓcl (joinCapArc_injOn hPic (hAi (Ne.symm hend))
        (hA0.trans hP1.symm) (hA1.trans hP0.symm) hdisj)
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
  
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

include hF hinj in
/-- An interior source point whose cap radius differs from `r` cannot
map to the actual cap curve, including its finite frontier endpoints. -/
theorem riemannMapping_notMem_cap_of_source_radius_ne {ζ : ℂ} {r a b : ℝ} (hr : 0 ≤ r)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' unitDisk))
    (hGb : G b ∈ frontier (F '' unitDisk))
    {z : ℂ} (hz : z ∈ unitDisk) (hne : ‖z - ζ‖ ≠ r) :
    F z ∉ G '' Icc a b := by
  have hopen  :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  have hzΩ : F z ∈ F '' unitDisk := ⟨z, hz, rfl⟩
  rintro ⟨θ, hθ, he⟩
  rcases eq_or_lt_of_le hθ.1 with hθa | hθa
  · grind [hGa.2]
  · rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · 
      have hn : ‖circleMap ζ r θ - ζ‖ = r := by
        simpa only [mem_sphere, dist_eq_norm] using circleMap_mem_sphere ζ hr θ
      exact hne ((hinj (harc ⟨hθa, hθb⟩) hz
        ((hGeq ⟨hθa, hθb⟩).symm.trans he)) ▸ hn)
    · grind [hGb.2]

include hF hinj in
/-- The actual conformal image of a proved source radial path avoids
the cap loop. Thus its winding is exactly the winding at the genuine
fixed interior point. This is the non-cap side selection used later. -/
theorem riemannMapping_winding_eq_at_zero_of_radial_side {ζ : ℂ} {r a b : ℝ} (hr : 0 ≤ r)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' unitDisk))
    (hGb : G b ∈ frontier (F '' unitDisk))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hclosed : β anglePeriod = β 0)
    (hsub : β '' angleInterval ⊆
      G '' Icc a b ∪ frontier (F '' unitDisk))
    {z : ℂ} (hz : z ∈ unitDisk) (hfar : r < ‖z - ζ‖)
    (hdot : ‖z‖ ^ 2 ≤ ⟪z, ζ⟫_ℝ) : windingNumber β (F z) = windingNumber β (F 0) := by
  let Ω := F '' unitDisk
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  have hm : MapsTo (fun t : ℝ => t • z) (Icc 0 1) unitDisk := by
    intro t ht
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt (mem_ball_zero_iff.mp hz)
  let P : ℝ → ℂ := fun t => F (t • z)
  
  have hdisj : Disjoint (P '' Icc 0 1) (β '' angleInterval) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨t, ht, htw⟩ hwβ
    
    rcases hsub hwβ with hwcap | hwfront
    · 
      apply riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr harc hGeq hGa hGb
        (hm ht) (hfar.trans_le (norm_sub_le_norm_radial_sub hdot ht.1 ht.2)).ne'
      change P t ∈ G '' Icc a b
      simp [*]
    · rw [hopen.frontier_eq] at hwfront
      exact hwfront.2 (⟨t • z, hm ht, htw⟩)
  apply windingNumber_const_of_isPreconnected hKB hclosed
    (isPreconnected_Icc.image P (hF.continuousOn.comp
      (continuous_id.smul continuous_const).continuousOn hm)) hdisj
  · exact ⟨1, by norm_num, by simp [P]⟩
  · exact ⟨0, by norm_num, by simp [P]⟩

include hF hinj in
/-- The entire actual source cap has a single winding value, because
its true conformal image is connected and avoids the constructed loop.
This proves the propagation step without any region separation premise. -/
theorem riemannMapping_winding_const_on_source_cap {ζ : ℂ} {r a b : ℝ} (hr : 0 ≤ r)
    (harc : MapsTo (circleMap ζ r) (Ioo a b) unitDisk)
    {G : ℝ → ℂ} (hGeq : EqOn G (fun θ => F (circleMap ζ r θ)) (Ioo a b))
    (hGa : G a ∈ frontier (F '' unitDisk))
    (hGb : G b ∈ frontier (F '' unitDisk))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hclosed : β anglePeriod = β 0)
    (hsub : β '' angleInterval ⊆
      G '' Icc a b ∪ frontier (F '' unitDisk))
    {z w : ℂ} (hz : z ∈ unitDisk ∩ ball ζ r)
    (hw : w ∈ unitDisk ∩ ball ζ r) :
    windingNumber β (F z) = windingNumber β (F w) := by
  
  let S := F '' (unitDisk ∩ ball ζ r)
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  have hSc  :=
    ((convex_ball 0 1).inter (convex_ball ζ r)).isPreconnected.image F
      (hF.continuousOn.mono inter_subset_left)
  
  refine windingNumber_const_of_isPreconnected hKB hclosed hSc ?_
    ⟨z, hz, rfl⟩ ⟨w, hw, rfl⟩
  apply Set.disjoint_left.mpr
  rintro v ⟨x, hx, hFx⟩ hvβ
  rcases hsub hvβ with hvcap | hvfront
  · apply riemannMapping_notMem_cap_of_source_radius_ne F hF hinj hr harc hGeq hGa hGb
      hx.1 (ne_of_lt (by simpa only [mem_ball, dist_eq_norm] using hx.2))
    simp [*]
  · rw [hopen.frontier_eq] at hvfront
    exact hvfront.2 ⟨x, hx.1, hFx⟩

include r ζ in
/-- The actual source midpoint of the circular cap. -/
def riemannCapMidpoint : ℂ := (1 - r) • ζ

include F r ζ in
/-- The inward physical normal obtained from the actual conformal
derivative, before choosing any boundary extension of the conformal map. -/
def riemannCapNormal : ℂ :=
  (r : ℂ) * deriv F (riemannCapMidpoint ζ r) * ζ

theorem riemannCapMidpoint_mem_disk {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) : riemannCapMidpoint ζ r ∈ unitDisk := by
  rw [mem_ball_zero_iff, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith), hζ, mul_one]
  linarith

theorem riemannCap_circle_midpoint {ζ : ℂ} (hζ : ‖ζ‖ = 1) (r : ℝ) :
    circleMap ζ r (riemannCapCenterAngle ζ) = riemannCapMidpoint ζ r := by
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  simp only [circleMap, he, riemannCapMidpoint, Complex.real_smul, Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

/-- The midpoint normal is exactly `I` times the actual oriented cap
tangent. Its sign is fixed by the source circle and conformal orientation. -/
theorem riemannCapNormal_eq_I_mul_tangent {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    riemannCapNormal F ζ r = Complex.I *
      riemannCapDerivative F ζ r (riemannCapCenterAngle ζ) := by
  
  have he : Complex.exp ((riemannCapCenterAngle ζ : ℂ) * Complex.I) = -ζ := by
    simpa only [riemannCapCenterAngle, norm_neg, hζ, Complex.ofReal_one, one_mul]
      using Complex.norm_mul_exp_arg_mul_I (-ζ)
  unfold riemannCapDerivative
  rw [riemannCap_circle_midpoint hζ r]
  unfold riemannInteriorDerivative
  rw [indicator_of_mem (riemannCapMidpoint_mem_disk hζ hr hr1)]
  simp only [circleMap, zero_add, he, riemannCapNormal]
  calc
    _ = -(Complex.I * Complex.I) * (r * deriv F (riemannCapMidpoint ζ r) * ζ) := by
      simp
    _ = _ := by ring

private theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hdneg : d < 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f s < f 0 := by
  
  filter_upwards [(hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hdneg)), self_mem_nhdsWithin] with s hs hspos
  simp at hs
  have hspos'  := hspos
  
  exact sub_neg.mp ((mul_lt_mul_iff_right₀ (inv_pos.mpr hspos')).mp (by simpa only [mul_zero] using hs))

private theorem eventually_gt_of_hasDerivAt_pos {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hdpos : 0 < d) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), f 0 < f s := by
  
  filter_upwards [(hd.tendsto_slope_zero_right.eventually (eventually_gt_nhds hdpos)), self_mem_nhdsWithin] with s hs hspos
  simp at hs
  have hspos'  := hspos
  
  exact sub_pos.mp ((mul_lt_mul_iff_right₀ (inv_pos.mpr hspos')).mp (by simpa only [mul_zero] using hs))

include hF hinj in
/-- Genuine local normal crossing of the actual circular source cap.
The inverse is constructed on the open image; both crossing inequalities
follow from its proved derivative, rather than a separation premise. -/
theorem riemannMapping_exists_inverse_normal_crossing {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ J : ℂ → ℂ, DifferentiableOn ℂ J (F '' unitDisk) ∧
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
  let Ω := F '' unitDisk
  let z₀ := riemannCapMidpoint ζ r
  let q := F z₀
  let N := riemannCapNormal F ζ r
  have hz₀  := riemannCapMidpoint_mem_disk hζ hr hr1
  have hq : q ∈ Ω := ⟨z₀, hz₀, rfl⟩
  have hopen  := RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  obtain ⟨J, hJ, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse
    isOpen_ball hF hinj
  have hJq  := hJF z₀ hz₀
  have hDF : deriv F z₀ ≠ 0 :=
    RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball hF hinj hz₀
  have hζne : ζ ≠ 0 := by
    intro h
    have hn : ‖ζ‖ = 0 := norm_eq_zero.mpr h
    linarith
  
  have hJc  := (hJ.differentiableAt (hopen.mem_nhds hq)).continuousAt
  have hdF : HasDerivAt F (deriv F z₀) (J q) := by
    rw [hJq]
    exact (hF.differentiableAt (isOpen_ball.mem_nhds hz₀)).hasDerivAt
  
  have hdJ  :=
    hdF.of_local_left_inverse hJc hDF (by
      filter_upwards [hopen.mem_nhds hq] with w hw using hFJ w hw)
  have hdP : HasDerivAt (fun s : ℝ => q + s • N) N 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const N).const_add q
    simp only [one_smul, id] at h
    exact h
  have hinvN : (deriv F z₀)⁻¹ * N = r • ζ := by
    change (deriv F z₀)⁻¹ * ((r : ℂ) * deriv F z₀ * ζ) = (r : ℂ) * ζ
    field_simp [hDF]
  have hdJP : HasDerivAt (fun s : ℝ => J (q + s • N)) (r • ζ) 0 := by
    simpa only [Function.comp_def, hinvN] using hdJ.comp_of_eq 0 hdP (by simp)
  have hJP0 : J (q + (0 : ℝ) • N) = z₀ := by simpa using hJq
  have hzsub : z₀ - ζ = (-r) • ζ := by
    change (1 - r) • ζ - ζ = (-r) • ζ
    simp [sub_smul]
  have hsqD : HasDerivAt (fun s : ℝ => ‖J (q + s • N) - ζ‖ ^ 2) (-2 * r ^ 2) 0 := by
    have h := (hdJP.sub_const ζ).norm_sq
    rw [hJP0, hzsub, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hζ] at h
    convert h using 1
    ring
  have hsq0 : ‖J (q + (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by
    rw [hJP0, hzsub, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hr, hζ, mul_one]
  have hplus : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖J (q + s • N) - ζ‖ ^ 2 < r ^ 2 := by
    simpa only [hsq0] using eventually_lt_of_hasDerivAt_neg hsqD (by nlinarith [sq_pos_of_pos hr])
  have hsqMinusD : HasDerivAt (fun s : ℝ => ‖J (q - s • N) - ζ‖ ^ 2)
      (2 * r ^ 2) 0 := by
    have h := hsqD.comp_of_eq 0 (hasDerivAt_neg 0) (by simp)
    convert h using 1
    · simp [Function.comp_def, neg_smul, sub_eq_add_neg]
    · ring
  have hsqMinus0 : ‖J (q - (0 : ℝ) • N) - ζ‖ ^ 2 = r ^ 2 := by
    simpa only [zero_smul, add_zero, sub_zero] using hsq0
  have hminus : ∀ᶠ s in 𝓝[>] (0 : ℝ), r ^ 2 < ‖J (q - s • N) - ζ‖ ^ 2 := by
    have he := eventually_gt_of_hasDerivAt_pos hsqMinusD (by positivity)
    simpa only [hsqMinus0] using he
  have hdot₀ : ‖J q‖ ^ 2 < ⟪J q, ζ⟫_ℝ := by
    rw [hJq]
    simp only [z₀, riemannCapMidpoint, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - r), hζ, mul_one, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    nlinarith
  have hminusC : ContinuousAt (fun s : ℝ => J (q - s • N)) 0 :=
    hJc.comp_of_eq (by fun_prop) (by simp)
  
  have hdotE : ∀ᶠ s in 𝓝 (0 : ℝ),
      ‖J (q - s • N)‖ ^ 2 < ⟪J (q - s • N), ζ⟫_ℝ := by
    have hdot0 : (0 : ℝ) <
        ⟪J (q - (0 : ℝ) • N), ζ⟫_ℝ - ‖J (q - (0 : ℝ) • N)‖ ^ 2 := by
      simpa only [zero_smul, sub_zero] using sub_pos.mpr hdot₀
    have he := ((hminusC.inner continuousAt_const).sub (hminusC.norm.pow 2)).tendsto.eventually (eventually_gt_nhds hdot0)
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
  refine ⟨J, hJ, hJm, hJF, hFJ, (mul_ne_zero (mul_ne_zero (by exact_mod_cast hr.ne') hDF) hζne), hdJP, ?_⟩
  filter_upwards [hplus, hminus, hdotE.filter_mono nhdsWithin_le_nhds,
    hΩplus.filter_mono nhdsWithin_le_nhds, hΩminus.filter_mono nhdsWithin_le_nhds]
    with s hsplus hsminus hsdot hsΩplus hsΩminus
  refine ⟨⟨hJm hsΩplus, ?_⟩, hJm hsΩminus, ?_, hsdot, hFJ _ hsΩplus, hFJ _ hsΩminus⟩
  · rw [mem_ball, dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsplus
  · exact (sq_lt_sq₀ hr.le (norm_nonneg _)).mp hsminus

include hF hinj in
/-- Along the two genuine physical normals, winding is already constant:
the inward value is the winding on the entire source cap, and the outward
value equals the proved winding at `F 0`. No winding jump is assumed here. -/
theorem riemannMapping_winding_normal_values {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {G : ℝ → ℂ}
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hclosed : β anglePeriod = β 0)
    (hsub : β '' angleInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk))
    {z : ℂ} (hz : z ∈ unitDisk ∩ ball ζ r) :
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
    rw [hs.2.2.2.2.1] at hwind
    exact hwind
  · have hwind := riemannMapping_winding_eq_at_zero_of_radial_side F hF hinj hr.le
      harc hGeq hGa hGb hKB hclosed hsub hs.2.1 hs.2.2.1 hs.2.2.2.1.le
    rw [hs.2.2.2.2.2] at hwind
    exact hwind

private theorem exists_graph_of_local_regular_arc {G V : ℝ → ℂ}
    (hGc : Continuous G) {a t b : ℝ} (ht : t ∈ Ioo a b)
    (hd : ∀ θ ∈ Ioo a b, HasDerivAt G (V θ) θ)
    (hVc : ContinuousAt V t) (hV : V t ≠ 0)
    (havoid : ∀ θ ∈ Icc a b, θ ≠ t → G θ ≠ G t) :
    ∃ d : ℝ, 0 < d ∧ ∃ f : ℝ → ℝ, ∀ θ ∈ Icc a b,
      ‖G θ - G t‖ < d →
        ((V t)⁻¹ * (G θ - G t)).im = f ((V t)⁻¹ * (G θ - G t)).re := by
  classical
  let c := (V t)⁻¹
  let x  := fun θ => (c * (G θ - G t)).re
  let xd  := fun θ => (c * V θ).re
  have hxd : ContinuousAt xd t :=
    (by fun_prop)
  have hxd0 : xd t = 1 := by simp only [xd, c, inv_mul_cancel₀ hV, Complex.one_re]
  
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp
    ((hxd.tendsto.eventually (eventually_gt_nhds (by positivity))).and (isOpen_Ioo.mem_nhds ht))
  let η := ρ / 2
  have hη : 0 < η := half_pos hρ
  have hnear (θ : ℝ) (hθ : θ ∈ Icc (t - η) (t + η)) :
      0 < xd θ ∧ θ ∈ Ioo a b := by
    apply hρsub
    rw [mem_ball, Real.dist_eq]
    have habs : |θ - t| ≤ η := abs_le.mpr (by grind)
    grind [habs.trans_lt]
  have hdx (θ : ℝ) (hθ : θ ∈ Ioo a b) : HasDerivAt x (xd θ) θ := by
    simpa only [x, xd, Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ (((hd θ hθ).sub_const (G t)).const_mul c)
  have hxc : Continuous x :=
    (by fun_prop)
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
    grind [hxmono.injOn hp.1 hθ hp.2]
  have hleft : ∀ θ ∈ Icc a (t - η), G θ ≠ G t := by
    intro θ hθ
    exact havoid θ ⟨hθ.1, by linarith [hθ.2, ht.2]⟩ (by linarith [hθ.2])
  have hright : ∀ θ ∈ Icc (t + η) b, G θ ≠ G t := by
    intro θ hθ
    exact havoid θ ⟨by linarith [hθ.1, ht.1], hθ.2⟩ (by linarith [hθ.1])
  obtain ⟨d₁, hd₁, hfar₁⟩ := exists_pos_le_norm_sub hGc hleft
  obtain ⟨d₂, hd₂, hfar₂⟩ := exists_pos_le_norm_sub hGc hright
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, f, ?_⟩
  intro θ hθ hsmall
  apply hgraph
  constructor
  · by_contra hn
    
    exact not_lt_of_ge (hfar₁ θ (⟨hθ.1, (lt_of_not_ge hn).le⟩)) (hsmall.trans_le (min_le_left _ _))
  · by_contra hn
    
    exact not_lt_of_ge (hfar₂ θ (⟨(lt_of_not_ge hn).le, hθ.2⟩)) (hsmall.trans_le (min_le_right _ _))

include hF hinj in
/-- The actual cap loop is a local graph at its genuine physical
midpoint. The closing boundary arc stays away from this interior point;
all other cap parameters stay away by compactness and actual injectivity. -/
theorem riemannMapping_cap_loop_local_graph {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    {β : ℝ → ℂ}
    (hsub : β '' angleInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk)) :
    let q := F (riemannCapMidpoint ζ r)
    let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
    T ≠ 0 ∧ ∃ d : ℝ, 0 < d ∧ ∃ f : ℝ → ℝ, ∀ w ∈ β '' angleInterval,
      ‖w - q‖ < d → (T⁻¹ * (w - q)).im = f (T⁻¹ * (w - q)).re := by
  let a := riemannCapCenterAngle ζ - riemannCapHalfAngle r
  let b := riemannCapCenterAngle ζ + riemannCapHalfAngle r
  let t := riemannCapCenterAngle ζ
  let q := F (riemannCapMidpoint ζ r)
  
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : t ∈ Ioo a b := (by grind)
  obtain ⟨_, hwidth, harc, _, _⟩ := riemannCap_geometry hζ hr hr1
  have htm  := harc ht
  have hT  := riemannCapDerivative_ne_zero_interior F hF hinj ζ hr t htm
  have hGq  := (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  have hopen  :=
    RiemannInterior.isOpen_image_of_injOn isOpen_ball hF hinj
  have hq : q ∈ F '' unitDisk :=
    (by grind)
  
  have havoid : ∀ θ ∈ Icc a b, θ ≠ t → G θ ≠ G t := by
    intro θ hθ hθt he
    rcases lt_or_eq_of_le hθ.2 with hθb | hθb
    · exact hθt ((riemannMapping_cap_injOn_Ico F hF hinj hr.ne'
      (by linarith) harc hGeq hGa) (by grind) (by grind) he)
    · rw [hopen.frontier_eq] at hGb
      apply hGb.2
      have hbe : G b = q := by simpa only [hθb, hGq] using he
      exact hbe.symm ▸ hq
  
  obtain ⟨d₁, hd₁, f, hgraph⟩ := exists_graph_of_local_regular_arc hGc ht (by
    intro θ hθ
    apply (riemannCapDerivative_hasDerivAt F hF ζ r θ (harc hθ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with u hu using hGeq hu)
    (riemannCapDerivative_continuousAt F hF ζ r t htm) hT havoid
  obtain ⟨d₂, hd₂, hball⟩ := Metric.isOpen_iff.mp hopen q hq
  refine ⟨hT, min d₁ d₂, lt_min hd₁ hd₂, f, ?_⟩
  intro w hw hsmall
  rcases hsub hw with ⟨θ, hθ, he⟩ | hwfront
  · grind
  · 
    rw [hopen.frontier_eq] at hwfront
    exact False.elim (hwfront.2 (hball (by
      rw [mem_ball, dist_eq_norm]
      exact hsmall.trans_le (min_le_right _ _))))

private theorem windingNumber_shift {β : ℝ → ℂ}
    (hper : Function.Periodic β anglePeriod) (t : ℝ) (w : ℂ) :
    windingNumber (fun θ => β (θ + t)) w = windingNumber β w := by
  have hdper  := deriv_periodic hper
  have hp : Function.Periodic (fun θ => deriv β θ / (β θ - w)) anglePeriod := by
    aesop
  have hd : deriv (fun θ => β (θ + t)) = fun θ => deriv β (θ + t) := by
    funext θ
    exact deriv_comp_add_const β t θ
  unfold windingNumber
  congr 1
  rw [hd]
  
  rw [intervalIntegral.integral_comp_add_right (fun θ => deriv β θ / (β θ - w)) t]
  simpa [add_comm] using hp.intervalIntegral_add_eq t 0

private theorem windingNumber_jump_of_local_image_graph {β : ℝ → ℂ} {KB : NNReal}
    (hKB : LipschitzWith KB β) (hper : Function.Periodic β anglePeriod)
    (hinj : InjOn β angleIco) {t : ℝ} {q T : ℂ}
    (ht : β t = q) (hT : T ≠ 0) {d : ℝ} (hd : 0 < d) {f : ℝ → ℝ}
    (hgraph : ∀ w ∈ β '' angleInterval, ‖w - q‖ < d →
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
      _ ≤ _ :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
  
  
  have hβc : Continuous β := hKB.continuous
  have hn : ContinuousAt (fun θ : ℝ => ‖β (θ + t) - q‖) 0 := by
    fun_prop
  have hn0 : ‖β ((0 : ℝ) + t) - q‖ = 0 := by simp [ht, sub_self, norm_zero]
  have he  :=
    hn.tendsto.eventually (eventually_lt_nhds (by rw [hn0]; exact hd))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp he
  let η := min (δ / 2) (Real.pi / 2)
  have hη  := lt_min (half_pos hδ) (half_pos Real.pi_pos)
  have hηδ : η < δ := (min_le_left _ _).trans_lt (by linarith)
  have hηπ : η < Real.pi := (by bound)
  have hg : ∀ θ ∈ Icc (-η) η, (ρ θ).im = f (ρ θ).re := by
    intro θ hθ
    apply hgraph _ (mem_image_Icc_of_periodic hper (θ + t))
    apply hδsub
    rw [mem_ball, Real.dist_eq, sub_zero]
    grind
  have hρinj : InjOn ρ (Icc (-η) η) := by
    intro x hx y hy heq
    
    have habs : |(x + t) - (y + t)| < anglePeriod := by
      rw [add_sub_add_right_eq_sub]
      apply (abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩).trans_lt
        (show 2 * η < anglePeriod by linarith)
    have hh := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (by
      have hh  :=
        mul_left_cancel₀ (inv_ne_zero hT) heq
      linear_combination hh) habs
    linarith
  have hfar : ∀ θ ∈ Icc η (anglePeriod - η), ρ θ ≠ 0 := by
    intro θ hθ heq
    have hh  := sub_eq_zero.mp
      ((mul_eq_zero.mp heq).resolve_left (inv_ne_zero hT))
    have hθpos  := hη.trans_le hθ.1
    have habs : |(θ + t) - t| < anglePeriod := by
      rw [add_sub_cancel_right, abs_of_pos hθpos]
      linarith [hθ.2]
    have hh' := jordanParam_eq_of_eq_of_abs_sub_lt hper hinj (hh.trans ht.symm) habs
    linarith
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump hρK (by
    intro θ
    dsimp [ρ]
    rw [show (θ + anglePeriod) + t = (θ + t) + anglePeriod by ring, hper]) hη hηπ (by simp [ρ, ht, sub_self]) hg hρinj hfar
  have hw (s : ℝ) : windingNumber ρ (s * Complex.I) =
      windingNumber β (q + s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1
    simp only [Complex.real_smul]
    ring
  have hw' (s : ℝ) : windingNumber ρ (-(s * Complex.I)) =
      windingNumber β (q - s • (Complex.I * T)) := by
    rw [windingNumber_affine _ (inv_ne_zero hT), windingNumber_shift hper, inv_inv]
    congr 1
    simp only [Complex.real_smul]
    ring
  refine ⟨σ, hσ, ?_⟩
  simpa [hw, hw'] using hlim

include hF hinj in
/-- The winding on the actual conformal cap is `±1`. The sign is
deduced from the genuine graph jump and inverse normal crossing, while
the other side is selected by its proved radial path to `F 0`. -/
theorem riemannMapping_cap_winding_pm_one {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hper : Function.Periodic β anglePeriod)
    (hβinj : InjOn β angleIco)
    (hcap : G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ⊆ β '' angleInterval)
    (hsub : β '' angleInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk))
    (hzero : windingNumber β (F 0) = 0)
    {z : ℂ} (hz : z ∈ unitDisk ∩ ball ζ r) :
    windingNumber β (F z) = 1 ∨ windingNumber β (F z) = -1 := by
  let q := F (riemannCapMidpoint ζ r)
  let T := riemannCapDerivative F ζ r (riemannCapCenterAngle ζ)
  have hα : 0 < riemannCapHalfAngle r := Real.arccos_pos.mpr (by linarith)
  have ht : riemannCapCenterAngle ζ ∈
      Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) := (by grind)
  have hGq  :=
    (hGeq ht).trans (congrArg F (riemannCap_circle_midpoint hζ r))
  have hqβ  :=
    hcap ⟨riemannCapCenterAngle ζ, Ioo_subset_Icc_self ht, hGq⟩
  obtain ⟨t, _ht, hβt⟩ := hqβ
  obtain ⟨hT, d, hd, f, hg⟩ :=
    riemannMapping_cap_loop_local_graph F hF hinj hζ hr hr1 hGc hGeq hGa hGb hsub
  obtain ⟨σ, hσ, hlim⟩ := windingNumber_jump_of_local_image_graph hKB hper hβinj hβt hT hd hg
  have hclosed : β anglePeriod = β 0 := by simpa only [zero_add] using hper 0
  have he := riemannMapping_winding_normal_values F hF hinj hζ hr hr1
    hGeq hGa hGb hKB hclosed hsub hz
  
  rw [riemannCapNormal_eq_I_mul_tangent F hζ hr hr1] at he
  have heq : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      windingNumber β (q + s • (Complex.I * T)) -
        windingNumber β (q - s • (Complex.I * T)) = windingNumber β (F z) := by
    filter_upwards [he] with s hs
    grind
  
  have hvalue  := tendsto_nhds_unique (by
    apply tendsto_const_nhds.congr'
    filter_upwards [heq] with s hs using hs.symm) hlim
  simp [*]

include hF hinj in
/-- A genuine cap loop contained in a physical ball confines the
entire conformal cap to that ball. A point outside the ball has winding
zero by the proved logarithm formula, contradicting the actual jump. -/
theorem riemannMapping_cap_image_subset_ball {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {G : ℝ → ℂ} (hGc : Continuous G)
    (hGeq : EqOn G (fun θ => F (circleMap ζ r θ))
      (Ioo (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r)))
    (hGa : G (riemannCapCenterAngle ζ - riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    (hGb : G (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∈
      frontier (F '' unitDisk))
    {β : ℝ → ℂ} {KB : NNReal} (hKB : LipschitzWith KB β)
    (hper : Function.Periodic β anglePeriod)
    (hβinj : InjOn β angleIco)
    (hcap : G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
      (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ⊆ β '' angleInterval)
    (hsub : β '' angleInterval ⊆
      G '' Icc (riemannCapCenterAngle ζ - riemannCapHalfAngle r)
        (riemannCapCenterAngle ζ + riemannCapHalfAngle r) ∪
          frontier (F '' unitDisk))
    (hzero : windingNumber β (F 0) = 0) {p : ℂ} {R : ℝ}
    (hball : ∀ θ ∈ angleInterval, ‖β θ - p‖ < R) :
    F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  rintro w ⟨z, hz, rfl⟩
  rw [mem_ball, dist_eq_norm]
  by_contra hn
  have hwind := windingNumber_eq_zero_of_image_ball hKB
    (by simpa only [zero_add] using hper 0) hball
    (by simpa only [norm_sub_rev] using le_of_not_gt hn)
  rcases riemannMapping_cap_winding_pm_one F hF hinj hζ hr hr1 hGc hGeq hGa hGb
      hKB hper hβinj hcap hsub hzero hz with h | h
  · rw [hwind] at h
    norm_num at h
  · rw [hwind] at h
    norm_num at h

include hF hb hinj in
/-- Genuine Courant–Lebesgue region oscillation. Arbitrarily small
source caps have their entire conformal images in arbitrarily small
physical balls centered on the actual frontier. No closed-disk extension
or endpoint injectivity of the conformal map is a premise. -/
theorem riemannMapping_exists_small_cap_region
    {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hper : Function.Periodic γ anglePeriod)
    (hγinj : InjOn γ angleIco)
    (himage : γ '' angleInterval = frontier (F '' unitDisk))
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r R : ℝ) (p : ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ 0 < R ∧ R < ε ∧
      p ∈ frontier (F '' unitDisk) ∧
      F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  obtain ⟨r, G, β, KB, p, R, hr, hrδ, hr1, hGc, hKB, hβper, hβinj,
    hR, hRε, _hRfar, hGeq, hGa, hGb, hp, hcap, hsub, hball, hzero⟩ :=
    riemannMapping_exists_small_lipschitz_cap_loop F hF hinj hb hK hper hγinj himage hζ hδ hε
  refine ⟨r, R, p, hr, hrδ, hr1, hR, hRε, hp.symm ▸ hGa, ?_⟩
  exact riemannMapping_cap_image_subset_ball F hF hinj hζ hr hr1 hGc hGeq hGa hGb
    hKB hβper hβinj hcap hsub hzero hball

end

/-- An interior holomorphic parametrization by the unit disk. -/
structure IsDiskUniformization (Ω : Set ℂ) (F : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ F unitDisk
  injective : InjOn F unitDisk
  image : F '' unitDisk = Ω

/-- Simple connectivity is automatic once an interior uniformization is given. -/
theorem IsDiskUniformization.simplyConnected {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : IsDiskUniformization Ω F) :
    SimplyConnectedSpace Ω := by
  obtain ⟨g, hg, hm, hl, hr⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball hΦ.holomorphic hΦ.injective
  rw [hΦ.image] at hg hm hr
  let e : unitDisk ≃ₜ Ω := {
    toFun := fun z => ⟨F z, hΦ.image ▸ mem_image_of_mem F z.2⟩
    invFun := fun w => ⟨g w, hm w.2⟩
    left_inv := fun z => Subtype.ext (hl z z.2)
    right_inv := fun w => Subtype.ext (hr w w.2)
    continuous_toFun := hΦ.holomorphic.continuousOn.restrict.subtype_mk _
    continuous_invFun := hg.continuousOn.restrict.subtype_mk _ }
  letI := (convex_ball (0 : ℂ) 1).contractibleSpace (nonempty_ball.mpr zero_lt_one)
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- A bounded Lipschitz image with its given disk uniformization. -/
structure LipschitzUniformization (Ω : Set ℂ) (F : ℂ → ℂ) : Prop extends IsDiskUniformization Ω F where
  bounded : Bornology.IsBounded Ω
  lipschitz : IsLipschitzDomain Ω

/-- The region estimate for an actual bounded simply connected
Lipschitz domain. Its physical Jordan boundary is constructed by the
proved domain topology; no additional curve is an assumption. -/
theorem riemannMapping_exists_small_cap_region_of_simplyConnected
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ (r R : ℝ) (p : ℂ), 0 < r ∧ r < δ ∧ r < 1 ∧ 0 < R ∧ R < ε ∧
      p ∈ frontier Ω ∧ F '' (unitDisk ∩ ball ζ r) ⊆ ball p R := by
  obtain ⟨γ, ⟨K, hK⟩, hper, hγinj, hγimage⟩ :=
    exists_jordanParam_of_isPreconnected_frontier hΦ.bounded hΦ.lipschitz
      (isPreconnected_frontier_of_simplyConnected hΦ.bounded hΦ.lipschitz hΦ.simplyConnected)
  have hbF  := hΦ.image.symm ▸ hΦ.bounded
  have hγF : γ '' angleInterval = frontier (F '' unitDisk) := by
    simpa only [hΦ.image] using hγimage
  simpa only [hΦ.image] using riemannMapping_exists_small_cap_region F hΦ.holomorphic hΦ.injective hbF
    hK hper hγinj hγF hζ hδ hε

/-- Every actual boundary source point has a unique finite physical
frontier limit. Small-cap region confinement makes the full interior
approach filter Cauchy; no radial-only or normal-only limit is used. -/
theorem riemannMapping_exists_unique_boundary_limit
    {Ω : Set ℂ} {F : ℂ → ℂ} (hΦ : LipschitzUniformization Ω F)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃! p : ℂ, p ∈ frontier Ω ∧ Tendsto F (𝓝[unitDisk] ζ) (𝓝 p) := by
  have hζcl : ζ ∈ closure unitDisk := by
    rw [closure_ball (0 : ℂ) (one_ne_zero : (1 : ℝ) ≠ 0), mem_closedBall_zero_iff, hζ]
  letI  := mem_closure_iff_nhdsWithin_neBot.mp hζcl
  have hC : Cauchy (Filter.map F (𝓝[unitDisk] ζ)) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    obtain ⟨r, R, p, hr, _hrδ, _hr1, _hR, hRε, _hp, hcap⟩ :=
      riemannMapping_exists_small_cap_region_of_simplyConnected hΦ hζ (zero_lt_one : (0 : ℝ) < 1) (half_pos hε)
    have hmem : ball p R ∈ Filter.map F (𝓝[unitDisk] ζ) := by
      change F ⁻¹' ball p R ∈ 𝓝[unitDisk] ζ
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds ζ hr)] with z hz hzcap
      exact hcap ⟨z, ⟨hz, hzcap⟩, rfl⟩
    refine ⟨ball p R, hmem, ?_⟩
    intro x hx y hy
    have hxp : dist x p < R := hx
    have hyp : dist y p < R := hy
    have hpy : dist p y < R := by simpa only [dist_comm] using hyp
    have ht := dist_triangle x p y
    linarith
  obtain ⟨p, hp⟩ := cauchy_map_iff_exists_tendsto.mp hC
  have hpf : p ∈ frontier Ω := by
    rw [← hΦ.image]
    exact riemannMapping_limit_mem_frontier (l := 𝓝[unitDisk] ζ)
       F hΦ.holomorphic hΦ.injective hζ self_mem_nhdsWithin
      ((tendsto_id : Tendsto (fun z : ℂ => z) (𝓝 ζ) (𝓝 ζ)).mono_left nhdsWithin_le_nhds) hp
  refine ⟨p, ⟨hpf, hp⟩, ?_⟩
  intro q hq
  exact tendsto_nhds_unique hq.2 hp

end PolyaNeumann

end
