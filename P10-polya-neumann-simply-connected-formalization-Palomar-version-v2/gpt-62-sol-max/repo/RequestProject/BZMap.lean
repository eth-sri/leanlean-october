module

public import RequestProject.BZConstruct
public import RequestProject.SmoothDomain

/-!
# The collar homeomorphism (towards External theorem BZ)

For level data `D` (parameter `T`), the collar map `f = collarMap Φ C a b T` is a homeomorphism of
the plane (`BZLevelData.homeo`) with uniformly controlled bi-Lipschitz constants, which maps `Ω`
into itself, onto the smooth domain `f(Ω)` (`BZLevelData.isAnalyticDomain_image`), is the identity
off `{|d_Ω| ≤ 2 M T}` and moves points by at most `M T / 2`.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal ContDiff

noncomputable section

namespace PolyaNeumann

namespace BZSetting

variable {Ω : Set ℂ} (S : BZSetting Ω)

/-- Uniform Lipschitz constant of the collar maps. -/
def K₁ : ℝ := S.M * (S.Lb + S.La / 2) + 1 / 2 + Real.exp S.LX

/-- Uniform Lipschitz constant of the inverse collar maps. -/
def K₂ : ℝ := S.M * (3 * S.La + 2 * S.Lb) + 1 / 2 + Real.exp S.LX

lemma K₁_nonneg : 0 ≤ S.K₁ := by
  have := S.M_pos; have := S.La_nonneg; have := S.Lb_nonneg; unfold K₁; positivity

lemma K₂_nonneg : 0 ≤ S.K₂ := by
  have := S.M_pos; have := S.La_nonneg; have := S.Lb_nonneg; unfold K₂; positivity

end BZSetting

namespace BZLevelData

variable {Ω : Set ℂ} {S : BZSetting Ω} (D : BZLevelData S)

lemma C_sub_U₁ {x : ℂ} (hx : x ∈ D.C) : x ∈ S.U₁ := by
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have := D.path_bound
  have := S.M_pos; have := D.T₁_pos
  show |signedDist Ω x| < S.r₀ / 2
  nlinarith

/-- Points of the collar lie above the level `ρ = ε` exactly when the crossing time is negative. -/
lemma lt_ρ_iff_s_neg {x : ℂ} (hx : x ∈ D.C) : D.ε < D.ρ x ↔ D.s x < 0 := by
  obtain ⟨hu, h₀⟩ := D.cross_ρ_spec hx
  have hT := D.T₁_le
  have hm : StrictMonoOn (fun t => D.ρ (S.Φ t x)) (Icc (-D.T₁) D.T₁) := by
    intro s hs t ht hst
    exact S.hΦ.lt_of_transversal S.hX S.hM D.lip S.hτ₀ (half_pos S.hκ₀) D.trans x
      (by grind) hst (by grind) fun u hu => D.flow_mem_U₁ hx (abs_le.mpr (by grind))
  simpa only [h₀, S.hΦ.zero] using hm.lt_iff_lt hu (show 0 ∈ Icc (-D.T₁) D.T₁ by grind [D.T₁_pos])

/-- The collar map. -/
def f : ℂ → ℂ := collarMap S.Φ D.C D.a D.b D.T

/-- The inverse collar map. -/
def g : ℂ → ℂ := collarMapInv S.Φ D.C D.a D.b D.T

lemma g_f (x : ℂ) : D.g (D.f x) = x :=
  IsFlowCollar.collarMapInv_collarMap S.hΦ S.hX D.isFlowCollar x

lemma f_g (y : ℂ) : D.f (D.g y) = y :=
  IsFlowCollar.collarMap_collarMapInv S.hΦ S.hX D.isFlowCollar y

lemma dist_f_le (x y : ℂ) : dist (D.f x) (D.f y) ≤ S.K₁ * dist x y := by
  have h := IsFlowCollar.collarMap_lipschitz S.hΦ S.hX S.hM D.isFlowCollar x y
  have e : S.M * ((S.Lb + S.La / 2) + (D.T / 2) / (S.M * D.T)) + Real.exp S.LX = S.K₁ := by
    have := S.M_pos.ne'; have := D.T_pos.ne'
    unfold BZSetting.K₁; field_simp
  aesop

lemma dist_g_le (x y : ℂ) : dist (D.g x) (D.g y) ≤ S.K₂ * dist x y := by
  have h := IsFlowCollar.collarMapInv_lipschitz S.hΦ S.hX S.hM D.isFlowCollar x y
  have e : S.M * ((3 * S.La + 2 * S.Lb) + (D.T / 2) / (S.M * D.T)) + Real.exp S.LX = S.K₂ := by
    have := S.M_pos.ne'; have := D.T_pos.ne'
    unfold BZSetting.K₂; field_simp
  aesop

lemma lipschitzWith_f : LipschitzWith (Real.toNNReal S.K₁) D.f :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ S.K₁_nonneg]; exact D.dist_f_le x y

lemma lipschitzWith_g : LipschitzWith (Real.toNNReal S.K₂) D.g :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.coe_toNNReal _ S.K₂_nonneg]; exact D.dist_g_le x y

/-- The collar homeomorphism. -/
def homeo : ℂ ≃ₜ ℂ where
  toFun := D.f
  invFun := D.g
  left_inv := D.g_f
  right_inv := D.f_g
  continuous_toFun := D.lipschitzWith_f.continuous
  continuous_invFun := D.lipschitzWith_g.continuous

lemma coe_homeo : (D.homeo : ℂ → ℂ) = D.f := rfl

lemma f_eq_self {x : ℂ} (hx : 2 * S.M * D.T < |signedDist Ω x|) : D.f x = x := by
  have h0 : collarShift D.C D.a D.b D.T x = 0 := by
    refine D.isFlowCollar.collarShift_eq_zero ?_
    by_cases hC : x ∈ D.C
    · right
      have h1 := D.abs_d_le hC
      have hM := S.M_pos
      by_contra hlt
      push_neg at hlt
      have := mul_le_mul_of_nonneg_left hlt.le hM.le
      linarith
    tauto
  simp_all [f, collarMap, S.hΦ.zero]

lemma norm_f_sub_le (x : ℂ) : ‖D.f x - x‖ ≤ S.M * (D.T / 2) := by
  have hu := D.isFlowCollar.abs_collarShift_le x
  have hT := D.T_lt
  have := S.hΦ.norm_sub_self_le S.hM x (t := collarShift D.C D.a D.b D.T x)
    ⟨by grind, by grind⟩
  exact this.trans (mul_le_mul_of_nonneg_left hu S.M_pos.le)

lemma f_mem (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ Ω) : D.f x ∈ Ω := by
  have hc := D.isFlowCollar
  by_cases h : x ∈ D.C ∧ |D.a x| < D.T
  · obtain ⟨hxC, hax⟩ := h
    have hT := D.T_pos
    set u := collarShift D.C D.a D.b D.T x
    have hu := hc.abs_collarShift_le x
    have hueq : u = D.b x * tentθ D.T (D.a x) := by simp [u, collarShift, hxC]
    obtain ⟨hyC, hya, -⟩ := hc.flow x hxC hax u (by linarith)
    have hpos := (D.mem_iff_a_pos hΩo hΩu hxC).mp hx
    have hb := D.b_mem hxC
    have hσ :=
      sigmaMap_pos hT (hc.b_le x hxC) hb.1 hpos
    show S.Φ u x ∈ Ω
    rw [D.mem_iff_a_pos hΩo hΩu hyC, hya, hueq]
    exact hσ
  · have h0 : collarShift D.C D.a D.b D.T x = 0 := hc.collarShift_eq_zero (by grind)
    simp_all [f, collarMap, S.hΦ.zero]

lemma mem_image_iff (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {w : ℂ} (hw : w ∈ D.C)
    (haw : |D.a w| < D.T) : w ∈ D.f '' Ω ↔ D.ε < D.ρ w := by
  have hc := D.isFlowCollar
  have h1 : w ∈ D.f '' Ω ↔ D.g w ∈ Ω := by
    constructor
    grind [D.g_f]
    · intro h; exact ⟨D.g w, h, D.f_g w⟩
  obtain ⟨hgC, hga⟩ := hc.a_collarMapInv hw haw
  rw [h1, show D.g w = collarMapInv S.Φ D.C D.a D.b D.T w from rfl,
    D.mem_iff_a_pos hΩo hΩu hgC, hga, sigmaInv_pos_iff D.T_pos (hc.b_le w hw),
    D.lt_ρ_iff_s_neg hw]
  simp only [b]
  simp

/-- The collar map takes the frontier to the regular level within the active collar. -/
private lemma f_frontier_spec (hΩo : IsOpen Ω) {q : ℂ} (hq : q ∈ frontier Ω) :
    D.f q ∈ D.C ∧ |D.a (D.f q)| < D.T ∧ D.ρ (D.f q) = D.ε := by
  have hT := D.T_pos
  have hM := S.M_pos
  have hd := signedDist_eq_zero_of_frontier hΩo hq
  have hqC : q ∈ D.C := by simp [C, hd]; positivity
  have haq := D.a_eq hqC (u := 0) (by grind [D.T₁_pos]) (by simpa only [S.hΦ.zero] using hd)
  simp only [neg_zero] at haq
  have hbq := D.b_mem hqC
  have hbs : D.b q = D.s q := by simp [b, haq]
  have hfq : D.f q = S.Φ (D.s q) q := by simp [f, collarMap, collarShift, hqC, haq, hbs, tentθ_zero]
  obtain ⟨hpC, hpa, -⟩ := D.isFlowCollar.flow q hqC (by simp [haq, hT]) (D.s q) (by grind)
  rw [hfq]
  exact ⟨hpC, by rw [hpa, haq, zero_add, ← hbs, abs_of_nonneg hbq.1]; linarith [hbq.2],
    (D.cross_ρ_spec hqC).2⟩

/-- The collar map sends boundary points into `Ω` (onto the level `ρ = ε`). -/
lemma f_mem_of_frontier (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {q : ℂ} (hq : q ∈ frontier Ω) :
    D.f q ∈ Ω := by
  have h := D.close (D.f q)
  rw [(D.f_frontier_spec hΩo hq).2.2, show D.ε = S.κ₀ * D.T / 24 from rfl] at h
  exact (signedDist_pos_iff hΩo hΩu).mp (by linarith [(abs_le.mp h).2, mul_pos S.hκ₀ D.T_pos])

/-- The collar map sends `Ω̄` into `Ω`. -/
lemma f_mem_of_mem_closure (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ closure Ω) :
    D.f x ∈ Ω := by
  by_cases h : x ∈ Ω
  · exact D.f_mem hΩo hΩu h
  · exact D.f_mem_of_frontier hΩo hΩu ⟨hx, by rwa [hΩo.interior_eq]⟩

/-- The image `f(Ω)` is a smooth domain. -/
theorem isAnalyticDomain_image (hΩ : IsDomain Ω) (hΩu : Ωᶜ.Nonempty) :
    IsAnalyticDomain (D.f '' Ω) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  exact D.homeo.isOpenMap _ hΩ.1
  exact hΩ.2.image _ D.lipschitzWith_f.continuous.continuousOn
  intro p hp
  rw [← D.coe_homeo, ← Homeomorph.image_frontier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  rw [D.coe_homeo]
  obtain ⟨hpC, hpa, hρp⟩ := D.f_frontier_spec hΩ.1 hq
  have hC : IsOpen D.C := isOpen_lt (lipschitzWith_signedDist Ω).continuous.abs continuous_const
  have ha : LipschitzOnWith (Real.toNNReal S.La) D.a D.C :=
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
      simpa [Real.coe_toNNReal _ S.La_nonneg, Real.dist_eq, dist_eq_norm] using
        D.isFlowCollar.a_lip x hx y hy
  have hn : ∀ᶠ z in 𝓝 (D.f q), z ∈ D.C := hC.mem_nhds hpC
  have hlt := (ha.continuousOn.continuousAt hn).abs.eventually_lt continuousAt_const hpa
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hn.and hlt)
  exact analyticChart_of_level D.smooth D.lip S.hX S.hτ₀ (half_pos S.hκ₀) D.trans D.analytic hR
    (fun w hw => D.C_sub_U₁ (hball hw).1) hρp
    (fun w hw => D.mem_image_iff hΩ.1 hΩu (hball hw).1 (hball hw).2)

end BZLevelData

end PolyaNeumann

end
