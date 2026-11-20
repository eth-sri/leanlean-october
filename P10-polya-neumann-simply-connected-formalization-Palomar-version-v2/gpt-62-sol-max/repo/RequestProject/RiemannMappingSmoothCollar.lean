module

public import Mathlib.Topology.ExtendFrom
public import RequestProject.AnalyticBoundaryChart
public import RequestProject.CircleReflection
public import RequestProject.ConformalDiskCoordinates
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Filter Metric Complex Classical
open scoped Topology ContDiff

private lemma ball_inter_ball_inter_disk_nonempty {z w x : ℂ} {r s : ℝ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (hw : w ∈ closedBall (0 : ℂ) 1)
    (hx : x ∈ ball z r ∩ ball w s) : ((ball z r ∩ ball w s) ∩ ball (0 : ℂ) 1).Nonempty := by
  have hr := nonempty_ball.mp ⟨x, hx.1⟩
  have hs := nonempty_ball.mp ⟨x, hx.2⟩
  have hd := (dist_triangle_left z w x).trans_lt
    (add_lt_add (mem_ball.mp hx.1) (mem_ball.mp hx.2))
  have ht : r / (r + s) ∈ Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩
  let y := AffineMap.lineMap z w (r / (r + s))
  have hy : y ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact Convex.lineMap_mem (convex_closedBall 0 1) hz hw ht
  have hmem : y ∈ ball z r ∩ ball w s := by
    constructor
    · rw [mem_ball, dist_lineMap_left, Real.norm_of_nonneg ht.1]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      gcongr
    · rw [mem_ball, dist_lineMap_right, Real.norm_of_nonneg (sub_nonneg.mpr ht.2),
        show 1 - r / (r + s) = s / (r + s) by field_simp; ring]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      gcongr
  exact mem_closure_iff_nhds.mp hy _ ((isOpen_ball.inter isOpen_ball).mem_nhds hmem)

/-- Local holomorphic extensions on balls centred in the closed disk agree
on overlaps by the identity theorem, and so extend to one larger disk. -/
private theorem extend_closedDisk {H : ℂ → ℂ}
    (hloc : ∀ z : closedBall (0 : ℂ) 1, ∃ (r : ℝ) (f : ℂ → ℂ), 0 < r ∧
      DifferentiableOn ℂ f (ball z r) ∧ InjOn f (ball z r) ∧
      EqOn f H (ball z r ∩ ball (0 : ℂ) 1)) :
    ∃ (R : ℝ) (G : ℂ → ℂ), 1 < R ∧ DifferentiableOn ℂ G (ball 0 R) ∧
      EqOn G H (ball (0 : ℂ) 1) ∧ ∀ z ∈ closedBall (0 : ℂ) 1, deriv G z ≠ 0 := by
  classical
  choose r f hr hf hi he using hloc
  let U := ⋃ z : closedBall (0 : ℂ) 1, ball (z : ℂ) (r z)
  have ho : IsOpen U := isOpen_iUnion fun _ => isOpen_ball
  have hsub : closedBall (0 : ℂ) 1 ⊆ U := fun z hz =>
    mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
  have hagree (z w : closedBall (0 : ℂ) 1) {x : ℂ}
      (hx : x ∈ ball (z : ℂ) (r z)) (hy : x ∈ ball (w : ℂ) (r w)) : f z x = f w x := by
    let V := ball (z : ℂ) (r z) ∩ ball (w : ℂ) (r w)
    have hv : IsOpen V := isOpen_ball.inter isOpen_ball
    obtain ⟨q, hq, hqd⟩ := ball_inter_ball_inter_disk_nonempty z.2 w.2 ⟨hx, hy⟩
    exact ((hf z).mono inter_subset_left |>.analyticOnNhd hv).eqOn_of_preconnected_of_eventuallyEq
      ((hf w).mono inter_subset_right |>.analyticOnNhd hv)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected hq
      (eventually_of_mem ((hv.inter isOpen_ball).mem_nhds ⟨hq, hqd⟩) fun _ hp =>
        (he z ⟨hp.1.1, hp.2⟩).trans
          (he w ⟨hp.1.2, hp.2⟩).symm) ⟨hx, hy⟩
  let G (x : ℂ) := if hx : x ∈ U then f (mem_iUnion.mp hx).choose x else 0
  have hG (z : closedBall (0 : ℂ) 1) : EqOn G (f z) (ball (z : ℂ) (r z)) := by
    intro x hx
    have hu : x ∈ U := mem_iUnion.mpr ⟨z, hx⟩
    change G x = f z x
    simp  [G, dif_pos hu]
    exact hagree _ _ (mem_iUnion.mp hu).choose_spec hx
  obtain ⟨ε, hε, hεU⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open ho hsub
  rw [thickening_closedBall hε zero_le_one] at hεU
  refine ⟨1 + ε, G, by linarith, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hεU (by simpa [add_comm] using hx))
    exact ((hf z).differentiableAt (isOpen_ball.mem_nhds hz)).congr_of_eventuallyEq
      ((hG z).eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)) |>.differentiableWithinAt
  · intro z hz
    let w : closedBall (0 : ℂ) 1 := ⟨z, ball_subset_closedBall hz⟩
    have hh : z ∈ ball (w : ℂ) (r w) := mem_ball_self (hr w)
    exact (hG w hh).trans (he w ⟨hh, hz⟩)
  · intro z hz
    let w : closedBall (0 : ℂ) 1 := ⟨z, hz⟩
    have hw : z ∈ ball (w : ℂ) (r w) := mem_ball_self (hr w)
    rw [((hG w).eventuallyEq_of_mem (isOpen_ball.mem_nhds hw)).deriv_eq]
    exact RiemannInterior.deriv_ne_zero_of_injOn isOpen_ball (hf w) (hi w) hw

/-- Properness of the conformal bijection gives continuity of the modulus of
its inverse with the boundary value one. -/
private theorem continuous_inverse_norm {Ω : Set ℂ} (ho : IsOpen Ω) {F J : ℂ → ℂ}
    (hf : ContinuousOn F (ball (0 : ℂ) 1)) (hFm : MapsTo F (ball (0 : ℂ) 1) Ω)
    (hj : ContinuousOn J Ω) (hJm : MapsTo J Ω (ball (0 : ℂ) 1)) (hFJ : RightInvOn J F Ω) :
    Continuous (Ω.piecewise (fun z => ‖J z‖) (fun _ => (1 : ℝ))) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p ∈ Ω
  · apply (hj.continuousAt (ho.mem_nhds hp)).norm.congr_of_eventuallyEq
    exact eventually_of_mem (ho.mem_nhds hp) fun z hz => piecewise_eq_of_mem Ω _ _ hz
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    let K := closedBall (0 : ℂ) (1 - ε)
    have hKD : K ⊆ ball (0 : ℂ) 1 := closedBall_subset_ball (by linarith)
    have hK := (isCompact_closedBall (0 : ℂ) (1 - ε)).image_of_continuousOn (hf.mono hKD)
    have hpK := fun h => hp (hFm.image_subset (image_mono hKD h))
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hpK] with w hw
    rw [piecewise_eq_of_notMem Ω _ _ hp]
    by_cases hwΩ : w ∈ Ω
    · have hn := fun h => hw ⟨J w, h, hFJ hwΩ⟩
      have ht := mem_ball_zero_iff.mp (hJm hwΩ)
      simp  [K, mem_closedBall_zero_iff, not_le] at hn
      rw [piecewise_eq_of_mem Ω _ _ hwΩ, Real.dist_eq, abs_of_neg (sub_neg.mpr ht)]
      linarith
    · simpa only [piecewise_eq_of_notMem Ω _ _ hwΩ, dist_self] using hε

/-- The inverse Riemann map in an analytic graph coordinate reflects in the
unit circle. Inverting the reflection gives local extensions of the forward
map. No boundary continuity of the Riemann map is assumed. -/
private theorem analytic_extension_of_riemannMap {Ω : Set ℂ}
    (hb : Bornology.IsBounded Ω) (hA : IsAnalyticDomain Ω)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball (0 : ℂ) 1))
    (hinj : InjOn F (ball (0 : ℂ) 1)) (himage : F '' ball (0 : ℂ) 1 = Ω) :
    ∃ (R : ℝ) (G : ℂ → ℂ), 1 < R ∧ DifferentiableOn ℂ G (ball 0 R) ∧
      EqOn G F (ball (0 : ℂ) 1) ∧ InjOn G (closedBall (0 : ℂ) 1) ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, deriv G z ≠ 0 := by
  classical
  let D := ball (0 : ℂ) 1
  have ho := hA.1.1
  have hFm := himage ▸ mapsTo_image F D
  obtain ⟨J, hJd, hJm, hJF, hFJ⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball hF hinj
  rw [himage] at hJd hJm hFJ
  have hj := (show RightInvOn J F Ω from fun _ => hFJ _).injOn
  let N := Ω.piecewise (fun z => ‖J z‖) (fun _ => (1 : ℝ))
  have hNc := continuous_inverse_norm ho hF.continuousOn hFm hJd.continuousOn hJm (fun _ => hFJ _)
  have hbdy (p : ℂ) (hp : p ∈ frontier Ω) : ∃ ζ : ℂ,
      Tendsto J (𝓝[Ω] p) (𝓝 ζ) ∧ ∃ (t : ℝ) (H : ℂ → ℂ), 0 < t ∧
        DifferentiableOn ℂ H (ball ζ t) ∧ InjOn H (ball ζ t) ∧ EqOn H F (ball ζ t ∩ D) := by
    obtain ⟨B, r, hr, hB0, hBd, hBi, hBin, hBfront⟩ := exists_analytic_boundary_chart hA hp
    have hNs : (N ∘ B) 0 = 1 := by
      rw [ho.frontier_eq] at hp
      rw [Function.comp_apply, hB0]
      aesop
    have hball : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) r := ball_mem_nhds 0 hr
    have hev : ∀ᶠ z in 𝓝 (0 : ℂ), 1 / 2 < (N ∘ B) z :=
      (hNc.continuousAt.comp (hBd.continuousOn.continuousAt hball)).eventually
        (lt_mem_nhds (by linarith))
    obtain ⟨s, hs, hsub⟩ := eventually_nhds_iff_ball.mp (hball.and hev)
    have hsr : ball (0 : ℂ) s ⊆ ball (0 : ℂ) r := fun _ h => (hsub _ h).1
    have hBu : MapsTo B (ball (0 : ℂ) s ∩ {z | 0 < z.im}) Ω :=
      fun _ h => (hBin _ (hsr h.1)).mpr h.2
    obtain ⟨v, hvd, hvi, hve, _, hvchar⟩ := exists_circle_reflection_of_continuous_norm (u := J ∘ B) hs
      (hNc.comp_continuousOn (hBd.continuousOn.mono hsr))
      (fun z hz hz₀ => by
        have hh := (ho.frontier_eq ▸ hBfront z (hsr hz) hz₀).2
        simp [N, hh])
      (fun z hz hz₀ => by simp [N, hBu ⟨hz, hz₀⟩])
      (fun z hz hz₀ => by simpa [N, hBu ⟨hz, hz₀⟩] using (hsub z hz).2.le)
      (fun z hz hz₀ => mem_ball_zero_iff.mp (hJm (hBu ⟨hz, hz₀⟩)))
      (hJd.comp (hBd.mono (inter_subset_left.trans hsr)) hBu)
      (hj.comp (hBi.mono (inter_subset_left.trans hsr)) hBu)
    refine ⟨v 0, ?_, ?_⟩
    · obtain ⟨b, hbd, hbm, hbl, hbr⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball
        (hBd.mono hsr) (hBi.mono hsr)
      have hBo := RiemannInterior.isOpen_image_of_injOn isOpen_ball (hBd.mono hsr)
        (hBi.mono hsr) subset_rfl isOpen_ball
      have hpB : p ∈ B '' ball (0 : ℂ) s := ⟨0, mem_ball_self hs, hB0⟩
      have hb0 := hB0 ▸ hbl 0 (mem_ball_self hs)
      have hct := (hvd.continuousOn.continuousAt (isOpen_ball.mem_nhds (hbm hpB))).comp
        (hbd.continuousOn.continuousAt (hBo.mem_nhds hpB))
      have ht : Tendsto (v ∘ b) (𝓝[Ω] p) (𝓝 (v 0)) := by
        have hct' : ContinuousWithinAt (v ∘ b) Ω p := hct.continuousWithinAt
        simpa only [Function.comp_apply, hb0, ContinuousWithinAt] using hct'
      refine ht.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (hBo.mem_nhds hpB), self_mem_nhdsWithin] with w hw hwo
      have hbi := hbm hw
      have hrw := hbr w hw
      have hwi := (hBin _ (hsr hbi)).mp (by simp_all)
      exact (hve ⟨hbi, hwi⟩).trans (congrArg J hrw)
    · obtain ⟨g, hgd, hgm, _, hvg⟩ := RiemannInterior.exists_holomorphic_inverse isOpen_ball hvd hvi
      have hgi := (show RightInvOn g v _ from fun _ => hvg _).injOn
      have hvo := RiemannInterior.isOpen_image_of_injOn isOpen_ball hvd hvi subset_rfl isOpen_ball
      obtain ⟨t, ht, hts⟩ := Metric.isOpen_iff.mp hvo _ (mem_image_of_mem v (mem_ball_self hs))
      refine ⟨t, B ∘ g, ht, (hBd.comp hgd (hgm.mono_right hsr)).mono hts,
        (hBi.comp hgi (hgm.mono_right hsr)).mono hts, ?_⟩
      intro w hw
      have hgw := hgm (hts hw.1)
      have hvgw := hvg w (hts hw.1)
      have hwi := (hvchar _ hgw).mp (by rw [hvgw]; exact mem_ball_zero_iff.mp hw.2)
      have hJw := (hve ⟨hgw, hwi⟩).symm.trans hvgw
      grind
  let L := extendFrom Ω J
  have hLc := continuousOn_extendFrom subset_rfl (by
    intro p hp
    by_cases h : p ∈ Ω
    · exact ⟨J p, hJd.continuousOn p h⟩
    · obtain ⟨ζ, hζ, _⟩ := hbdy p (ho.frontier_eq.symm ▸ ⟨hp, h⟩)
      exact ⟨ζ, hζ⟩)
  have hLJ : EqOn L J Ω := extendFrom_extends hJd.continuousOn
  have hJimg : J '' Ω = D := hJm.image_subset.antisymm (fun z hz => ⟨F z, hFm hz, hJF _ hz⟩)
  have hLsurj : SurjOn L (closure Ω) (closedBall (0 : ℂ) 1) := by
    have hcomp : IsCompact (closure Ω) := hb.isCompact_closure
    change closedBall (0 : ℂ) 1 ⊆ L '' closure Ω
    rw [← closure_ball _ one_ne_zero, show ball (0 : ℂ) 1 = D from rfl, ← hJimg, ← hLJ.image_eq]
    exact closure_minimal (image_mono subset_closure) (hcomp.image_of_continuousOn hLc).isClosed
  obtain ⟨R, G, hR, hGd, hGF, hn⟩ := extend_closedDisk (H := F) (by
    intro z
    by_cases hz : (z : ℂ) ∈ D
    · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_ball _ hz
      exact ⟨r, F, hr, hF.mono hsub, hinj.mono hsub, fun _ _ => rfl⟩
    · obtain ⟨p, hp, hpz⟩ := hLsurj z.2
      have h : p ∉ Ω := fun h => hz (hpz ▸ hLJ h ▸ hJm h)
      obtain ⟨ζ, ht, hloc⟩ := hbdy p (ho.frontier_eq.symm ▸ ⟨hp, h⟩)
      rwa [← hpz, show L p = ζ from extendFrom_eq hp ht])
  have hGc := hGd.continuousOn.mono (closedBall_subset_ball hR)
  have hGm : MapsTo G (closedBall (0 : ℂ) 1) (closure Ω) := by
    have hh : MapsTo G D Ω := fun _ h => hGF h ▸ hFm h
    have hcl : closure D = closedBall (0 : ℂ) 1 := closure_ball _ one_ne_zero
    rw [← hcl] at hGc ⊢
    exact hh.closure_of_continuousOn hGc
  have hleft : LeftInvOn L G (closedBall (0 : ℂ) 1) := by
    have he : EqOn (L ∘ G) id D := fun _ hz => by grind
    exact he.of_subset_closure (hLc.comp hGc hGm) continuousOn_id ball_subset_closedBall
      (closure_ball _ one_ne_zero).symm.subset
  exact ⟨R, G, hR, hGd, hGF, hleft.injOn, hn⟩

/-- Analytic domains admit a holomorphic collar of the genuine conformal map.
Compactness supplies upper and positive lower differential bounds. -/
theorem exists_analyticConformal_coordinates (Ω : Set ℂ)
    (hb : Bornology.IsBounded Ω) (hA : IsAnalyticDomain Ω) (hsc : SimplyConnectedSpace Ω) :
    ∃ (G : ℂ → ℂ), Nonempty (ConformalDiskCoordinates G) ∧ G '' ball 0 1 = Ω := by
  obtain ⟨F, hF, hi, him⟩ := exists_interior_conformal_map Ω hA.1.1 hb hsc
  obtain ⟨R, G, hR, hG, heq, hinj, hn⟩ := analytic_extension_of_riemannMap hb hA hF hi him
  have hD := closedBall_subset_ball (x := (0 : ℂ)) hR
  have hc (z) (hz : z ∈ closedBall (0 : ℂ) 1) :=
    hG.differentiableAt (isOpen_ball.mem_nhds (hD hz))
  have hloc (z) (hz : z ∈ closedBall (0 : ℂ) 1) : ∃ V ∈ 𝓝 z, InjOn G V := by
    have hd := (hG.analyticOnNhd isOpen_ball z (hD hz)).hasStrictDerivAt
    let J := hd.localInverse G (deriv G z) z (hn z hz)
    have hl : LeftInvOn J G {x | J (G x) = x} := fun _ h => h
    exact ⟨_, hd.eventually_left_inverse (hn z hz), hl.injOn⟩
  have hcompact := isCompact_closedBall (0 : ℂ) 1
  obtain ⟨W, hW, hDW, hWi⟩ := hinj.exists_isOpen_superset hcompact
    (fun z hz => (hc z hz).continuousAt) hloc
  obtain ⟨ε, hε, hεW⟩ := hcompact.exists_thickening_subset_open (hW.inter isOpen_ball)
    (subset_inter hDW hD)
  rw [thickening_closedBall hε zero_le_one, add_comm] at hεW
  have hc' := ((hG.deriv isOpen_ball).continuousOn.mono hD).norm
  obtain ⟨w, hw, hmin⟩ := hcompact.exists_isMinOn ⟨0, by simp⟩ hc'
  obtain ⟨K, hK⟩ := hcompact.exists_bound_of_continuousOn hc'
  have himage := heq.image_eq.trans him
  refine ⟨G, ⟨1 + ε, (‖deriv G w‖ ^ 2)⁻¹, K, by linarith, himage.symm ▸ hb,
    himage.symm ▸ hA.isLipschitzDomain, hG.mono (hεW.trans inter_subset_right),
    hWi.mono (hεW.trans inter_subset_left), ?_, ?_⟩, himage⟩
  · intro z hz
    rw [inv_mul_eq_div, le_div_iff₀ (pow_pos (norm_pos_iff.mpr (hn w hw)) _), one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin (ball_subset_closedBall hz)) _
  · intro z hz
    simpa only [norm_norm] using hK z (ball_subset_closedBall hz)

end PolyaNeumann

end
