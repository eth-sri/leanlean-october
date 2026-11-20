module

public import RequestProject.BZField
public import RequestProject.BZMono
public import RequestProject.BZLevel
public import RequestProject.BZCollar
public import RequestProject.PolynomialSmoothing

/-!
# The flow collar of a Lipschitz domain (towards External theorem BZ)

We fix a bounded Lipschitz domain with a transversal field `X` (`exists_transversalField`) and its
short-time flow `Φ` (`BZSetting`). For a small parameter `T > 0` and a smooth function `ρ` close
to the signed distance and transversal to `X` (`BZLevelData`), the flow time `a` from the boundary
and the flow time `b` from the boundary to the level `ρ = ε` (`ε = κ₀ T / 24`) form a flow collar
in the sense of `IsFlowCollar` on `C = {|d_Ω| < 4 M T}` (`BZLevelData.isFlowCollar`).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal ContDiff

noncomputable section

namespace PolyaNeumann

lemma IsTransversalOn.mono {φ : ℂ → ℝ} {X : ℂ → ℂ} {U V : Set ℂ} {τ κ κ' : ℝ}
    (h : IsTransversalOn φ X U τ κ) (hVU : V ⊆ U) (hκ : κ' ≤ κ) :
    IsTransversalOn φ X V τ κ' := fun z hz t ht0 htτ => by
  have := h z (hVU hz) t ht0 htτ
  nlinarith

/-- The fixed data of the construction: a transversal field for the signed distance and its
short-time flow. -/
structure BZSetting (Ω : Set ℂ) where
  X : ℂ → ℂ
  LX : ℝ≥0
  M : ℝ
  r₀ : ℝ
  τ₀ : ℝ
  κ₀ : ℝ
  Φ : ℝ → ℂ → ℂ
  hX : LipschitzWith LX X
  hM : ∀ z, ‖X z‖ ≤ M
  hκ₀ : 0 < κ₀
  hκM : κ₀ ≤ M
  hr₀ : 0 < r₀
  hτ₀ : 0 < τ₀
  hQ : IsTransversalOn (signedDist Ω) X {z | |signedDist Ω z| < r₀} τ₀ κ₀
  hΦ : IsShortFlow X Φ

theorem exists_bzSetting {Ω : Set ℂ} (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hΩne : Ω.Nonempty) (hΩu : Ωᶜ.Nonempty) : Nonempty (BZSetting Ω) := by
  obtain ⟨X, LX, M, r₀, τ, κ, hX, hM, hr₀, hτ, hκ, hQ⟩ :=
    exists_transversalField hb hL hΩne hΩu
  have hM0 := (norm_nonneg _).trans (hM 0)
  obtain ⟨Φ, hΦ⟩ := exists_isShortFlow hX hM
  exact ⟨⟨X, LX, M + κ, r₀, τ, κ, Φ, hX, fun z => (hM z).trans (by linarith), hκ,
    by linarith, hr₀, hτ, fun z hz t ht0 htτ => hQ z hz t ht0 htτ, hΦ⟩⟩

namespace BZSetting

variable {Ω : Set ℂ} (S : BZSetting Ω)

lemma M_pos : 0 < S.M := lt_of_lt_of_le S.hκ₀ S.hκM

/-- The ratio `A₁ = 64 M / κ₀ ≥ 64`. -/
def A₁ : ℝ := 64 * S.M / S.κ₀

lemma A₁_ge : 64 ≤ S.A₁ := by
  unfold A₁; rw [le_div_iff₀ S.hκ₀]; nlinarith [S.hκM]

/-- The admissible range of the parameter `T`. -/
def T₀ : ℝ := min (1 / (8 * S.A₁)) (S.r₀ / (16 * S.M * (1 + S.A₁)))

lemma T₀_pos : 0 < S.T₀ := by
  have := S.A₁_ge; have := S.M_pos; have := S.hr₀
  exact lt_min (by positivity) (by positivity)

/-- The region `{|d| < r₀/2}` where both transversality statements hold. -/
def U₁ : Set ℂ := {z | |signedDist Ω z| < S.r₀ / 2}

lemma abs_signedDist_flow_sub_le (x : ℂ) {u : ℝ} (hu : u ∈ Ioo (-3 : ℝ) 3) :
    |signedDist Ω (S.Φ u x) - signedDist Ω x| ≤ 2 * (S.M * |u|) := by
  have h1 := (lipschitzWith_signedDist Ω).dist_le_mul (S.Φ u x) x
  rw [Real.dist_eq, dist_eq_norm] at h1
  have h2 := S.hΦ.norm_sub_self_le S.hM x hu
  push_cast at h1
  linarith

lemma hQ₁ : IsTransversalOn (signedDist Ω) S.X S.U₁ S.τ₀ S.κ₀ :=
  S.hQ.mono (fun z (hz : |signedDist Ω z| < S.r₀ / 2) => by grind) le_rfl

/-- Lipschitz constant of the flow time from the boundary. -/
def La : ℝ := 4 * Real.exp S.LX / S.κ₀

/-- Lipschitz constant of the flow time to the level. -/
def Lb : ℝ := 12 * Real.exp S.LX / S.κ₀

lemma La_nonneg : 0 ≤ S.La := by unfold La; have := S.hκ₀; positivity
lemma Lb_nonneg : 0 ≤ S.Lb := by unfold Lb; have := S.hκ₀; positivity

end BZSetting

section

variable {Ω : Set ℂ} (S : BZSetting Ω)
include Ω S

/-- The level data for the parameter `T`: a smooth function `ρ`, `ε/2`-close to the signed
distance (`ε = κ₀ T / 24`) and transversal to `X` on `{|d| < r₀/2}`. -/
structure BZLevelData  where
  T : ℝ
  ρ : ℂ → ℝ
  T_pos : 0 < T
  T_le : T ≤ S.T₀
  smooth : ContDiff ℝ ∞ ρ
  analytic : ∀ p ∈ S.U₁, AnalyticAt ℝ ρ p
  lip : LipschitzWith 2 ρ
  close : ∀ x, |ρ x - signedDist Ω x| ≤ S.κ₀ * T / 48
  trans : IsTransversalOn ρ S.X S.U₁ S.τ₀ (S.κ₀ / 2)

theorem exists_bzLevelData (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {T : ℝ} (hT : 0 < T) (hT₀ : T ≤ S.T₀) : ∃ D : BZLevelData S, D.T = T := by
  have hκ := S.hκ₀
  have hr := S.hr₀
  let δ := min (S.κ₀ * T / 96) (min (S.r₀ / 4) (S.κ₀ / (4 * S.LX + 4)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ S.κ₀ * T / 96 := min_le_left _ _
  have hδ2 : δ ≤ S.r₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ S.κ₀ / (4 * S.LX + 4) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨f, hfs, hfl, hfc, hft⟩ := exists_smooth_transversal (signedDist_lipschitz Ω) S.hX S.hQ hδ
  simp  [NNReal.coe_one, one_mul] at hfc hft
  have hft' : IsTransversalOn f S.X S.U₁ S.τ₀ (3 * S.κ₀ / 4) := by
    refine hft.mono (fun z hz t ht => ?_) ?_
    · have h1 := (signedDist_lipschitz Ω).dist_le_mul (z - t) z
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg, NNReal.coe_one, one_mul] at h1
      have hz' : |signedDist Ω z| < S.r₀ / 2 := hz
      show |signedDist Ω (z - t)| < S.r₀
      linarith [abs_sub_abs_le_abs_sub (signedDist Ω (z - t)) (signedDist Ω z)]
    · have hLX := S.LX.2
      have h₁ : (S.LX : ℝ) * (S.κ₀ / (4 * S.LX + 4)) ≤ S.κ₀ / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hδ3 hLX]
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hU : S.U₁ ⊆ closedBall 0 (R + S.r₀ / 2) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_cases hzΩ : z ∈ Ω
    · linarith [mem_closedBall_zero_iff.mp (hR hzΩ)]
    · have h : |signedDist Ω z| < S.r₀ / 2 := hz
      rw [signedDist_of_notMem hzΩ, abs_neg, abs_of_nonneg infDist_nonneg] at h
      obtain ⟨x, hx, hzx⟩ := (infDist_lt_iff hne).mp h
      rw [dist_eq_norm] at hzx
      linarith [norm_le_norm_sub_add z x, mem_closedBall_zero_iff.mp (hR hx)]
  let e := min 1 (min (S.κ₀ * T / 96) (S.κ₀ / (4 * (S.M + 1))))
  have he : 0 < e := lt_min one_pos (lt_min (by positivity) (by have := S.M_pos; positivity))
  obtain ⟨ρ, hρs, hρa, hρc, hρl⟩ := exists_analytic_perturbation hfs (isCompact_closedBall _ _) he
  have hρeq : ρ = (ρ - f) + f := by abel
  refine ⟨⟨T, ρ, hT, hT₀, hρs, fun z hz => hρa z (hU hz), ?_, ?_, ?_⟩, rfl⟩
  · rw [hρeq]
    apply (hρl.add hfl).weaken
    have h : e ≤ 1 := min_le_left _ _
    exact_mod_cast (show (e.toNNReal : ℝ) + 1 ≤ 2 by rw [Real.coe_toNNReal _ he.le]; linarith)
  · intro z
    have h : e ≤ S.κ₀ * T / 96 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [abs_sub_le (ρ z) (f z) (signedDist Ω z), hρc z, hfc z]
  · intro z hz t ht0 htτ
    have h := hρl.dist_le_mul (z + t * S.X z) z
    rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ht0, Real.coe_toNNReal _ he.le] at h
    have h₁ : e * S.M ≤ S.κ₀ / 4 := by
      have heM : e ≤ S.κ₀ / (4 * (S.M + 1)) := (min_le_right _ _).trans (min_le_right _ _)
      rw [le_div_iff₀ (by have := S.M_pos; positivity)] at heM
      nlinarith
    have h₂ : e * (t * ‖S.X z‖) ≤ S.κ₀ / 4 * t := by
      rw [mul_left_comm, mul_comm (_ / 4) t]
      gcongr
      exact (mul_le_mul_of_nonneg_left (S.hM z) he.le).trans h₁
    have h₃ := hft' z hz t ht0 htτ
    simp  [Pi.sub_apply] at h
    linarith [(abs_le.mp (h.trans h₂)).1]

end

open Classical in
/-- The crossing time of the level `l` of `φ` along the flow line of `x`, within `[-T₁, T₁]`
(`0` if there is none). -/
def crossTime (Φ : ℝ → ℂ → ℂ) (T₁ : ℝ) (φ : ℂ → ℝ) (l : ℝ) (x : ℂ) : ℝ :=
  if h : ∃ u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l then h.choose else 0

section

variable {Φ : ℝ → ℂ → ℂ} {T₁ : ℝ} {φ : ℂ → ℝ} {l : ℝ} {x : ℂ}
include Φ T₁ φ l x

lemma crossTime_spec 
    (h : ∃ u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) :
    crossTime Φ T₁ φ l x ∈ Icc (-T₁) T₁ ∧ φ (Φ (crossTime Φ T₁ φ l x) x) = l := by grind [crossTime]

lemma crossTime_eq 
    (h : ∃! u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) {u : ℝ}
    (hu : u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) : crossTime Φ T₁ φ l x = u :=
  h.unique (crossTime_spec h.exists) hu

end

namespace BZLevelData

variable {Ω : Set ℂ} {S : BZSetting Ω} (D : BZLevelData S)

/-- The window `T₁ = A₁ D.T` of crossing times. -/
def T₁ : ℝ := S.A₁ * D.T

/-- The level `ε = κ₀ D.T / 24`. -/
def ε : ℝ := S.κ₀ * D.T / 24

/-- The collar `C = {|d| < 4 M D.T}`. -/
def C : Set ℂ := {x | |signedDist Ω x| < 4 * S.M * D.T}

section

variable (x : ℂ)
include x

/-- The flow time from the boundary. -/
def a  : ℝ := -crossTime S.Φ D.T₁ (signedDist Ω) 0 x

/-- The flow time to the level `ρ = ε`. -/
def s  : ℝ := crossTime S.Φ D.T₁ D.ρ D.ε x

/-- The flow time from the boundary to the level `ρ = ε`. -/
def b  : ℝ := D.a x + D.s x

end

lemma T₁_pos : 0 < D.T₁ := by
  have := S.A₁_ge; have := D.T_pos; unfold T₁; positivity

lemma T₁_le : D.T₁ ≤ 1 / 8 := by
  have hA := S.A₁_ge
  have h1 := D.T_le.trans (min_le_left _ _)
  unfold T₁
  rw [le_div_iff₀ (by positivity)] at h1
  nlinarith

lemma T_le_T₁ : 64 * D.T ≤ D.T₁ := by
  have := S.A₁_ge; have := D.T_pos; unfold T₁; nlinarith

lemma κT₁ : S.κ₀ * D.T₁ = 64 * S.M * D.T := by
  unfold T₁ BZSetting.A₁; field_simp [S.hκ₀.ne']

lemma path_bound : 4 * S.M * D.T + 2 * (S.M * (2 * D.T₁)) < S.r₀ / 2 := by
  have hA := S.A₁_ge
  have hMp := S.M_pos
  have h1 := D.T_le.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h1
  unfold T₁
  have e : 4 * S.M * D.T + 2 * (S.M * (2 * (S.A₁ * D.T))) =
      D.T * (16 * S.M * (1 + S.A₁)) / 4 := by ring
  rw [e]
  linarith [S.hr₀]

/-- Flow lines from the collar stay in the region of transversality for times `|u| ≤ 2 T₁`. -/
lemma flow_mem_U₁ {x : ℂ} (hx : |signedDist Ω x| < 4 * S.M * D.T) {u : ℝ}
    (hu : |u| ≤ 2 * D.T₁) : S.Φ u x ∈ S.U₁ := by
  have h1 := D.T₁_le
  have h2 := S.abs_signedDist_flow_sub_le x (u := u)
    ⟨by grind, by grind⟩
  have h3 := D.path_bound
  have hM := S.M_pos
  show |signedDist Ω (S.Φ u x)| < S.r₀ / 2
  have := abs_sub_abs_le_abs_sub (signedDist Ω (S.Φ u x)) (signedDist Ω x)
  nlinarith

lemma existsUnique_cross_d {x : ℂ} (hx : x ∈ D.C) :
    ∃! u, u ∈ Icc (-D.T₁) D.T₁ ∧ signedDist Ω (S.Φ u x) = 0 := by
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have hκT := D.κT₁
  have hM := S.M_pos
  have hT := D.T_pos
  refine S.hΦ.existsUnique_crossing S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁
    D.T₁_pos (by linarith [D.T₁_le]) x
    (fun u hu => D.flow_mem_U₁ hx' (abs_le.mpr ⟨by grind,
      by grind⟩)) ?_ ?_
  all_goals grind

lemma abs_ρ_sub_ε_le (x : ℂ) : |D.ρ x - D.ε| ≤ |signedDist Ω x| + S.κ₀ * D.T / 16 := by
  have h1 := D.close x
  unfold ε
  grind

section

variable {x : ℂ} (hx : x ∈ D.C)
include x hx

lemma existsUnique_cross_ρ  :
    ∃! u, u ∈ Icc (-D.T₁) D.T₁ ∧ D.ρ (S.Φ u x) = D.ε := by
  have hx' : |signedDist Ω x| < 4 * S.M * D.T := hx
  have hκT := D.κT₁
  have hM := S.M_pos
  have hT := D.T_pos
  have hκM := S.hκM
  have h1 := D.abs_ρ_sub_ε_le x
  refine S.hΦ.existsUnique_crossing S.hX S.hM D.lip S.hτ₀ (by linarith [S.hκ₀]) D.trans
    D.T₁_pos (by linarith [D.T₁_le]) x
    (fun u hu => D.flow_mem_U₁ hx' (abs_le.mpr ⟨by grind,
      by grind⟩)) ?_ ?_
  · have := (abs_le.mp h1).1; nlinarith
  · have := (abs_le.mp h1).2; nlinarith

lemma cross_d_spec  :
    -D.a x ∈ Icc (-D.T₁) D.T₁ ∧ signedDist Ω (S.Φ (-D.a x) x) = 0 := by simpa [a, neg_neg] using crossTime_spec (D.existsUnique_cross_d hx).exists

lemma cross_ρ_spec  :
    D.s x ∈ Icc (-D.T₁) D.T₁ ∧ D.ρ (S.Φ (D.s x) x) = D.ε :=
  crossTime_spec (D.existsUnique_cross_ρ hx).exists

lemma a_eq  {u : ℝ} (hu : u ∈ Icc (-D.T₁) D.T₁)
    (hdu : signedDist Ω (S.Φ u x) = 0) : D.a x = -u := by
  simp  [a, crossTime_eq (D.existsUnique_cross_d hx) ⟨hu, hdu⟩]

lemma s_eq  {u : ℝ} (hu : u ∈ Icc (-D.T₁) D.T₁)
    (hdu : D.ρ (S.Φ u x) = D.ε) : D.s x = u :=
  crossTime_eq (D.existsUnique_cross_ρ hx) ⟨hu, hdu⟩

/-- `|d(x)| ≤ 2 M |a(x)|`. -/
lemma abs_d_le  : |signedDist Ω x| ≤ 2 * (S.M * |D.a x|) := by
  obtain ⟨hu, h0⟩ := D.cross_d_spec hx
  have h1 := D.T₁_le
  have := S.abs_signedDist_flow_sub_le x (u := -D.a x)
    ⟨by grind, by grind⟩
  simp_all

end

/-- Points of the collar are in `Ω` exactly when their flow time from the boundary is positive. -/
lemma mem_iff_a_pos (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty) {x : ℂ} (hx : x ∈ D.C) :
    x ∈ Ω ↔ 0 < D.a x := by
  obtain ⟨hu, h0⟩ := D.cross_d_spec hx
  have hx' := hx
  have hT1 := D.T₁_le
  have hpath : ∀ v, |v| ≤ D.T₁ → S.Φ v x ∈ S.U₁ := fun v hv =>
    D.flow_mem_U₁ hx' (by grind)
  rw [← signedDist_pos_iff hΩo hΩu]
  rcases lt_trichotomy (D.a x) 0 with hneg | hzero | hpos
  · -- the crossing time `-a x` is positive: `d x < 0`
    have := S.hΦ.lt_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ x
      (s := 0) (t := -D.a x) (by norm_num) (by linarith) (by grind)
      (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
    rw [S.hΦ.zero, h0] at this
    grind
  · have : -D.a x = 0 := by simp_all
    rw [this, S.hΦ.zero] at h0
    simp_all
  · have := S.hΦ.lt_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ x
      (s := -D.a x) (t := 0) (by grind) (by linarith) (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
    simp_all [S.hΦ.zero]

lemma T_lt : D.T < 1 / 2 := by
  have := D.T_le_T₁; have := D.T₁_le; linarith

/-- Group law within the window. -/
lemma flow_add (x : ℂ) {u v : ℝ} (hu : |u| ≤ 4 * D.T₁) (hv : |v| ≤ 2 * D.T₁) :
    S.Φ u (S.Φ v x) = S.Φ (u + v) x := by
  have h := D.T₁_le
  exact S.hΦ.add S.hX x ⟨by grind, by grind⟩
    ⟨by grind, by grind⟩

section

variable {x : ℂ} (hx : x ∈ D.C)
include x hx

/-- The flow time from the boundary to the level `ρ = ε` lies in `[0, T/8]`. -/
lemma b_mem  : 0 ≤ D.b x ∧ D.b x ≤ D.T / 8 := by
  obtain ⟨ht, hd⟩ := D.cross_d_spec hx
  obtain ⟨hs, hρ⟩ := D.cross_ρ_spec hx
  have hT1 := D.T₁_le
  have hT1p := D.T₁_pos
  set t₀ := -D.a x
  set p := S.Φ t₀ x
  have hq : S.Φ (D.b x) p = S.Φ (D.s x) x := by
    simp  [p]
    rw [D.flow_add x (abs_le.mpr ⟨by grind [b],
      by grind [b]⟩) (abs_le.mpr ⟨by grind, by grind⟩)]
    simp [b, t₀]
  have hbq : |D.b x| ≤ 2 * D.T₁ := abs_le.mpr ⟨by grind [b],
    by grind [b]⟩
  have hdq : D.ε / 2 ≤ signedDist Ω (S.Φ (D.b x) p) ∧
      signedDist Ω (S.Φ (D.b x) p) ≤ 3 * D.ε / 2 := by
    rw [hq]
    have := D.close (S.Φ (D.s x) x)
    rw [hρ] at this
    have h1 := abs_le.mp this
    unfold ε at *
    grind
  have hp0 : |signedDist Ω p| < 4 * S.M * D.T := by
    rw [hd, abs_zero]; have := S.M_pos; have := D.T_pos; positivity
  have hpath : ∀ v, |v| ≤ 2 * D.T₁ → S.Φ v p ∈ S.U₁ := fun v hv => D.flow_mem_U₁ hp0 hv
  have hε : 0 < D.ε := by unfold ε; have := S.hκ₀; have := D.T_pos; positivity
  have hb0 : 0 < D.b x := by
    by_contra hle
    push_neg at hle
    have := S.hΦ.le_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ p
      (s := D.b x) (t := 0) (by grind) hle (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
    rw [S.hΦ.zero, hd] at this
    have := S.hκ₀
    nlinarith [hdq.1]
  have := S.hΦ.le_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ p
    (s := 0) (t := D.b x) (by norm_num) hb0.le (by grind)
    (fun v hv => hpath v (abs_le.mpr ⟨by grind, by grind⟩))
  rw [S.hΦ.zero, hd] at this
  refine ⟨hb0.le, ?_⟩
  have h2 := hdq.2
  unfold ε at h2
  have hκ := S.hκ₀
  have : S.κ₀ / 2 * D.b x ≤ S.κ₀ * (D.T / 16) := by nlinarith
  nlinarith

/-- Flow invariance of the collar coordinates. -/
lemma flow_collar  (hax : |D.a x| < D.T) {u : ℝ} (hu : |u| ≤ D.T) :
    S.Φ u x ∈ D.C ∧ D.a (S.Φ u x) = D.a x + u ∧ D.b (S.Φ u x) = D.b x := by
  obtain ⟨ht, hd⟩ := D.cross_d_spec hx
  obtain ⟨hs, hρ⟩ := D.cross_ρ_spec hx
  have hT := D.T_pos
  have h64 := D.T_le_T₁
  have hT1 := D.T₁_le
  obtain ⟨hb0, hb8⟩ := D.b_mem hx
  have hax' := abs_lt.mp hax
  have hu' := abs_le.mp hu
  -- `Φ_u x = Φ_{a + u} p` with `p` on the boundary level
  have hyp : S.Φ (D.a x + u) (S.Φ (-D.a x) x) = S.Φ u x := by
    rw [D.flow_add x (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩)]
    simp
  have hyC : S.Φ u x ∈ D.C := by
    have := S.abs_signedDist_flow_sub_le (S.Φ (-D.a x) x) (u := D.a x + u)
      ⟨by linarith, by linarith⟩
    rw [hyp, hd, sub_zero] at this
    show |signedDist Ω (S.Φ u x)| < 4 * S.M * D.T
    have hM := S.M_pos
    have : S.M * |D.a x + u| < S.M * (2 * D.T) := by
      apply mul_lt_mul_of_pos_left _ hM
      grind
    linarith
  have ha : D.a (S.Φ u x) = D.a x + u := by
    have h1 : S.Φ (-(D.a x + u)) (S.Φ u x) = S.Φ (-D.a x) x := by
      rw [D.flow_add x (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)]
      simp
    rw [D.a_eq hyC (u := -(D.a x + u)) ⟨by linarith, by linarith⟩ (by simp_all), neg_neg]
  have hsu : D.s (S.Φ u x) = D.s x - u := by
    have hsx : D.s x = D.b x - D.a x := by simp [b]
    have h1 : S.Φ (D.s x - u) (S.Φ u x) = S.Φ (D.s x) x := by
      rw [D.flow_add x (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)]
      simp
    exact D.s_eq hyC ⟨by linarith, by linarith⟩ (by simp_all)
  refine ⟨hyC, ha, ?_⟩
  simp_all [b]

end

section

variable {x : ℂ} (hx : x ∈ D.C) {y : ℂ} (hy : y ∈ D.C)
include x hx y hy

lemma a_lip  :
    |D.a x - D.a y| ≤ S.La * ‖x - y‖ := by
  have hy' := hy
  have := S.hΦ.abs_crossing_sub_le S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁
    (by linarith [D.T₁_le]) (x := x) (y := y)
    (fun v hv => D.flow_mem_U₁ hy' (abs_le.mpr ⟨by grind,
      by grind⟩))
    (D.cross_d_spec hx).1 (D.cross_d_spec hy).1 (D.cross_d_spec hx).2 (D.cross_d_spec hy).2
  rw [show -D.a x - -D.a y = -(D.a x - D.a y) by ring, abs_neg] at this
  unfold BZSetting.La
  have hκ := S.hκ₀
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  push_cast at this
  nlinarith

lemma s_lip  :
    |D.s x - D.s y| ≤ 8 * Real.exp S.LX / S.κ₀ * ‖x - y‖ := by
  have hy' := hy
  have := S.hΦ.abs_crossing_sub_le S.hX S.hM D.lip S.hτ₀ (by linarith [S.hκ₀]) D.trans
    (by linarith [D.T₁_le]) (x := x) (y := y)
    (fun v hv => D.flow_mem_U₁ hy' (abs_le.mpr ⟨by grind,
      by grind⟩))
    (D.cross_ρ_spec hx).1 (D.cross_ρ_spec hy).1 (D.cross_ρ_spec hx).2 (D.cross_ρ_spec hy).2
  have hκ := S.hκ₀
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  push_cast at this
  nlinarith

lemma b_lip  :
    |D.b x - D.b y| ≤ S.Lb * ‖x - y‖ := by
  have h1 := D.a_lip hx hy
  have h2 := D.s_lip hx hy
  have : |D.b x - D.b y| ≤ |D.a x - D.a y| + |D.s x - D.s y| := by
    grind [b]
  have e : S.Lb = S.La + 8 * Real.exp S.LX / S.κ₀ := by unfold BZSetting.Lb BZSetting.La; ring
  rw [e, add_mul]
  linarith

end

lemma gap {x : ℂ} (hx : x ∈ D.C) (hax : |D.a x| < D.T) {y : ℂ} (hy : y ∉ D.C) :
    S.M * D.T ≤ ‖x - y‖ := by
  have h1 := D.abs_d_le hx
  have hy' : 4 * S.M * D.T ≤ |signedDist Ω y| := not_lt.mp hy
  have h2 := (lipschitzWith_signedDist Ω).dist_le_mul y x
  rw [Real.dist_eq, dist_eq_norm, norm_sub_rev] at h2
  have h3 := abs_sub_abs_le_abs_sub (signedDist Ω y) (signedDist Ω x)
  have hM := S.M_pos
  have := mul_le_mul_of_nonneg_left hax.le hM.le
  push_cast at h2
  linarith


theorem isFlowCollar : IsFlowCollar S.Φ D.C D.a D.b D.T S.La S.Lb (S.M * D.T) where
  T_pos := D.T_pos
  T_lt := D.T_lt
  γ_pos := mul_pos S.M_pos D.T_pos
  La_nonneg := S.La_nonneg
  Lb_nonneg := S.Lb_nonneg
  flow := fun x hx hax u hu => D.flow_collar hx hax hu
  b_le := fun x hx => by
    obtain ⟨h0, h8⟩ := D.b_mem hx
    grind
  a_lip := fun x hx y hy => D.a_lip hx hy
  b_lip := fun x hx y hy => D.b_lip hx hy
  gap := fun x hx hax y hy => D.gap hx hax hy

end BZLevelData

end PolyaNeumann

end
