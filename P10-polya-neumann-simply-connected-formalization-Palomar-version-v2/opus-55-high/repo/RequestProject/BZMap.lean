module

public import RequestProject.BZConstruct
public import RequestProject.SmoothDomain

/-!
# The collar homeomorphism (towards External theorem BZ)

For level data `D` (parameter `T`), the collar map `f = collarMap Φ C a b T` is a homeomorphism of
the plane (`BZLevelData.homeo`) with uniformly controlled bi-Lipschitz constants, which maps `Ω`
into itself, onto the smooth domain `f(Ω)` (`BZLevelData.isSmoothDomain_image`), is the identity
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

variable {x : ℂ}

lemma C_sub_U₁ (hx : x ∈ D.C) : x ∈ S.U₁ := by
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have := D.path_bound
  have := S.M_pos; have := D.T₁_pos
  show |signedDist Ω x| < S.r₀ / 2
  nlinarith

/-- Points of the collar lie above the level `ρ = ε` exactly when the crossing time is negative. -/
lemma lt_ρ_iff_s_neg (hx : x ∈ D.C) : D.ε < D.ρ x ↔ D.s x < 0 := by
  obtain ⟨hu, h0⟩ := D.cross_ρ_spec hx
  have hT1 := D.T₁_le
  have hκ  := half_pos S.hκ₀
  have hpath : ∀ v, |v| ≤ D.T₁ → S.Φ v x ∈ S.U₁ := fun v hv =>
    D.flow_mem_U₁ hx (by grind)
  rcases lt_trichotomy (D.s x) 0 with hneg | hzero | hpos
  · have := S.hΦ.lt_of_transversal S.hX S.hM D.lip S.hτ₀ hκ D.trans x
        (by grind) hneg (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
    simp_all [S.hΦ.zero]
  · simp_all [S.hΦ.zero]
  · have := S.hΦ.lt_of_transversal S.hX S.hM D.lip S.hτ₀ hκ D.trans x
        (by norm_num) hpos (by grind)
      (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
    rw [S.hΦ.zero] at this
    grind

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
  rw [e] at h; assumption

lemma dist_g_le (x y : ℂ) : dist (D.g x) (D.g y) ≤ S.K₂ * dist x y := by
  have h := IsFlowCollar.collarMapInv_lipschitz S.hΦ S.hX S.hM D.isFlowCollar x y
  have e : S.M * ((3 * S.La + 2 * S.Lb) + (D.T / 2) / (S.M * D.T)) + Real.exp S.LX = S.K₂ := by
    have := S.M_pos.ne'; have := D.T_pos.ne'
    unfold BZSetting.K₂; field_simp
  rw [e] at h; assumption

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

lemma coe_homeo : D.homeo = D.f := rfl

lemma f_eq_self {x : ℂ} (hx : 2 * S.M * D.T < |signedDist Ω x|) : D.f x = x := by
  have h0 : collarShift D.C D.a D.b D.T x = 0 := by
    refine D.isFlowCollar.collarShift_eq_zero ?_
    by_cases hC : x ∈ D.C
    · right
      have h1 := D.abs_d_le hC
      by_contra hlt
      push_neg at hlt
      have  := mul_le_mul_of_nonneg_left hlt.le S.M_pos.le
      linarith
    simp_all
  simp [f, collarMap, h0, S.hΦ.zero]

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
    have hu  := hc.abs_collarShift_le x
    have hueq : u = D.b x * tentθ D.T (D.a x) := by simp [u, collarShift, hxC]
    obtain ⟨hyC, hya, -⟩ := hc.flow x hxC hax u (by linarith)
    have hσ  :=
      sigmaMap_pos hT (hc.b_le x hxC) (D.b_mem hxC).1 ((D.mem_iff_a_pos hΩo hΩu hxC).mp hx)
    show S.Φ u x ∈ Ω
    rwa [D.mem_iff_a_pos hΩo hΩu hyC, hya, hueq]
  · simp only [f, collarMap, hc.collarShift_eq_zero (by
      by_cases h' : x ∈ D.C
      · exact Or.inr (by push_neg at h; exact h h')
      simp_all), S.hΦ.zero]; assumption

lemma mem_image_iff (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {w : ℂ} (hw : w ∈ D.C)
    (haw : |D.a w| < D.T) : w ∈ D.f '' Ω ↔ D.ε < D.ρ w := by
  have hc := D.isFlowCollar
  have h1 : w ∈ D.f '' Ω ↔ D.g w ∈ Ω := by
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [D.g_f]
    · intro h; exact ⟨D.g w, h, D.f_g w⟩
  obtain ⟨hgC, hga⟩ := hc.a_collarMapInv hw haw
  rw [h1, show D.g w = collarMapInv S.Φ D.C D.a D.b D.T w from rfl,
    D.mem_iff_a_pos hΩo hΩu hgC, hga, sigmaInv_pos_iff D.T_pos (hc.b_le w hw),
    D.lt_ρ_iff_s_neg hw]
  simp [b]

/-- The collar map sends boundary points into `Ω` (onto the level `ρ = ε`). -/
lemma f_mem_of_frontier (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {q : ℂ} (hq : q ∈ frontier Ω) :
    D.f q ∈ Ω := by
  have hT := D.T_pos
  have hM := S.M_pos
  have hd  := signedDist_eq_zero_of_frontier hΩo hq
  have hqC : q ∈ D.C := by
    show |signedDist Ω q| < 4 * S.M * D.T
    simp_all
  have haq : D.a q = 0 := by
    have := D.a_eq hqC  ⟨by linarith [D.T₁_pos], D.T₁_pos.le⟩ (by simp_all [S.hΦ.zero])
    linarith
  have hshift : collarShift D.C D.a D.b D.T q = D.s q := by
    simp [collarShift, if_pos hqC, haq, tentθ_zero, b]
  have hfq : D.f q = S.Φ (D.s q) q := by simp [f, collarMap, hshift]
  have hρp : D.ρ (D.f q) = D.ε := by rw [hfq]; exact (D.cross_ρ_spec hqC).2
  have hε : D.ε = S.κ₀ * D.T / 24 := rfl
  rw [← signedDist_pos_iff hΩo hΩu]
  have := (abs_le.mp (D.close (D.f q))).2
  have  := mul_pos S.hκ₀ hT
  linarith

/-- The collar map sends `Ω̄` into `Ω`. -/
lemma f_mem_of_mem_closure (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ closure Ω) :
    D.f x ∈ Ω := by
  by_cases h : x ∈ Ω
  · exact D.f_mem hΩo hΩu h
  · exact D.f_mem_of_frontier hΩo hΩu ⟨hx, by grind⟩

/-- The image `f(Ω)` is a smooth domain. -/
theorem isSmoothDomain_image (hΩ : IsDomain Ω) (hΩu : Ωᶜ.Nonempty) :
    IsSmoothDomain (D.f '' Ω) := by
  have hc := D.isFlowCollar
  have hT := D.T_pos
  have hM := S.M_pos
  have hLa := S.La_nonneg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact D.homeo.isOpenMap _ hΩ.1
  · exact hΩ.2.image _ D.lipschitzWith_f.continuous.continuousOn
  intro p hp
  rw [← D.coe_homeo, ← Homeomorph.image_frontier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hd  := signedDist_eq_zero_of_frontier hΩ.1 hq
  have hqC : q ∈ D.C := by
    show |signedDist Ω q| < 4 * S.M * D.T
    simp_all
  have haq : D.a q = 0 := by
    have := D.a_eq hqC  ⟨by linarith [D.T₁_pos], D.T₁_pos.le⟩ (by simp_all [S.hΦ.zero])
    linarith
  have hshift : collarShift D.C D.a D.b D.T q = D.s q := by
    simp [collarShift, if_pos hqC, haq, tentθ_zero, b]
  have hfq : D.f q = S.Φ (D.s q) q := by simp [f, collarMap, hshift]
  have hρp : D.ρ (D.f q) = D.ε := by rw [hfq]; exact (D.cross_ρ_spec hqC).2
  have hbq := D.b_mem hqC
  have hbs : D.b q = D.s q := by simp [b, haq]
  obtain ⟨hpC, hpa, -⟩ := hc.flow q hqC (by simp_all) (D.s q)
    (by grind )
  rw [← hfq] at hpC hpa
  rw [haq, zero_add, ← hbs] at hpa
  set R : ℝ := min (S.M * D.T) (D.T / (2 * S.La + 1))
  have hball : ∀ w ∈ ball (D.f q) R, w ∈ D.C ∧ |D.a w| < D.T := by
    intro w hw
    have hw' : ‖w - D.f q‖ < R := by simp_all [dist_eq_norm]
    have hR1 : R ≤ S.M * D.T := min_le_left _ _
    have hR2 : R ≤ D.T / (2 * S.La + 1) := min_le_right _ _
    have hdp := D.abs_d_le hpC
    rw [hpa, abs_of_nonneg hbq.1] at hdp
    have hwC : w ∈ D.C := by
      have h2 := (lipschitzWith_signedDist Ω).dist_le_mul w (D.f q)
      rw [Real.dist_eq, dist_eq_norm] at h2
      push_cast at h2
      have h3 := abs_sub_abs_le_abs_sub (signedDist Ω w) (signedDist Ω (D.f q))
      show |signedDist Ω w| < 4 * S.M * D.T
      nlinarith
    have h4 := hc.a_lip w hwC (D.f q) hpC
    have h5  := mul_le_mul_of_nonneg_left hw'.le hLa
    have h6 : S.La * (D.T / (2 * S.La + 1)) ≤ D.T / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have h7  := mul_le_mul_of_nonneg_left hR2 hLa
    grind 
  exact smoothChart_of_level D.smooth D.lip S.hX S.hτ₀ (half_pos S.hκ₀) D.trans (lt_min (by positivity) (by positivity))
    (fun w hw => D.C_sub_U₁ (hball w hw).1) hρp
    (fun w hw => D.mem_image_iff hΩ.1 hΩu (hball w hw).1 (hball w hw).2)

end BZLevelData

end PolyaNeumann

end
