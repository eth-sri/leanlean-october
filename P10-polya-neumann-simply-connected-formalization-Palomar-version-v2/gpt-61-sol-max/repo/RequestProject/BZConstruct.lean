module

public import RequestProject.PlanarTypes

public import RequestProject.BZField
public import RequestProject.BZMono
public import RequestProject.BZLevel
public import RequestProject.BZCollar

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

lemma IsTransversalOn.mono    
    (h : IsTransversalOn φ X U τ κ) (hVU : V ⊆ U) (hκ : κ' ≤ κ) :
    IsTransversalOn φ X V τ κ' := fun z hz t ht0 htτ => by
  have := h z (hVU hz) t ht0 htτ
  nlinarith

/-- The fixed data of the construction: a transversal field for the signed distance and its
short-time flow. -/
structure BZSetting (Ω : PlanarSet) where
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

theorem exists_bzSetting  (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
    (hΩne : Ω.Nonempty) (hΩu : Ωᶜ.Nonempty) : Nonempty (BZSetting Ω) := by
  obtain ⟨X, LX, M, r₀, τ, κ, hX, hM, hr₀, hτ, hκ, hQ⟩ :=
    exists_transversalField hb hL hΩne hΩu
  have hM0  := (norm_nonneg _).trans (hM 0)
  obtain ⟨Φ, hΦ⟩ := exists_isShortFlow hX hM
  exact ⟨⟨X, LX, M + κ, r₀, τ, κ, Φ, hX, fun z => (hM z).trans (by linarith), hκ,
    by linarith, hr₀, hτ, hQ, hΦ⟩⟩

namespace BZSetting

variable {Ω } (S : BZSetting Ω)

lemma M_pos : 0 < S.M := lt_of_lt_of_le S.hκ₀ S.hκM

/-- The ratio `A₁ = 64 M / κ₀ ≥ 64`. -/
def A₁  := 64 * S.M / S.κ₀

lemma A₁_ge : 64 ≤ S.A₁ := by
  unfold A₁; rw [le_div_iff₀ S.hκ₀]; nlinarith [S.hκM]

/-- The admissible range of the parameter `T`. -/
def T₀  := min (1 / (8 * S.A₁)) (S.r₀ / (16 * S.M * (1 + S.A₁)))

lemma T₀_pos : 0 < S.T₀ := by
  have := S.A₁_ge; have := S.M_pos; have := S.hr₀
  exact lt_min (by positivity) (by positivity)

/-- The region `{|d| < r₀/2}` where both transversality statements hold. -/
def U₁  := {z | |signedDist Ω z| < S.r₀ / 2}

lemma abs_signedDist_flow_sub_le x  (hu : u ∈ Ioo (-3 : ℝ) 3) :
    |signedDist Ω (S.Φ u x) - signedDist Ω x| ≤ 2 * (S.M * |u|) := by
  have h1 := (lipschitzWith_signedDist Ω).dist_le_mul (S.Φ u x) x
  rw [Real.dist_eq, dist_eq_norm] at h1
  have h2 := S.hΦ.norm_sub_self_le S.hM x hu
  push_cast at h1
  linarith

lemma hQ₁ : IsTransversalOn (signedDist Ω) S.X S.U₁ S.τ₀ S.κ₀ :=
  S.hQ.mono (fun z (hz : |signedDist Ω z| < S.r₀ / 2) => by
    grind) le_rfl

/-- Lipschitz constant of the flow time from the boundary. -/
def La  := 4 * Real.exp S.LX / S.κ₀

/-- Lipschitz constant of the flow time to the level. -/
def Lb  := 12 * Real.exp S.LX / S.κ₀

lemma La_nonneg : 0 ≤ S.La := by unfold La; have := S.hκ₀; positivity
lemma Lb_nonneg : 0 ≤ S.Lb := by unfold Lb; have := S.hκ₀; positivity

end BZSetting

/-- The level data for the parameter `T`: a smooth function `ρ`, `ε/2`-close to the signed
distance (`ε = κ₀ T / 24`) and transversal to `X` on `{|d| < r₀/2}`. -/
structure BZLevelData {Ω : PlanarSet} (S : BZSetting Ω) where
  T : ℝ
  ρ : ℂ → ℝ
  T_pos : 0 < T
  T_le : T ≤ S.T₀
  smooth : RealSmooth ρ
  lip : LipschitzWith 2 ρ
  close : ∀ x, |ρ x - signedDist Ω x| ≤ S.κ₀ * T / 48
  trans : IsTransversalOn ρ S.X S.U₁ S.τ₀ (S.κ₀ / 2)

theorem exists_bzLevelData  (S : BZSetting Ω)  (hT : 0 < T)
    (hT₀ : T ≤ S.T₀) : ∃ D : BZLevelData S, D.T = T := by
  have hκ := S.hκ₀
  have hr := S.hr₀
  set δ : ℝ := min (S.κ₀ * T / 96) (min (S.r₀ / 4) (S.κ₀ / (8 * S.LX + 8)))
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ S.κ₀ * T / 96 := min_le_left _ _
  have hδ2 : δ ≤ S.r₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ S.κ₀ / (8 * S.LX + 8) := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨ρ, hρs, hρl, hρc, hρt⟩ :=
    exists_smooth_transversal (lipschitzWith_signedDist Ω) S.hX S.hQ hδ
  refine ⟨⟨T, ρ, hT, hT₀, hρs, hρl, fun x => (hρc x).trans (by linarith), ?_⟩, rfl⟩
  refine hρt.mono (fun z hz t ht => ?_) ?_
  · have h1 := (lipschitzWith_signedDist Ω).dist_le_mul (z - t) z
    rw [Real.dist_eq, dist_eq_norm, show z - t - z = -t by ring, norm_neg] at h1
    have hz' : |signedDist Ω z| < S.r₀ / 2 := hz
    show |signedDist Ω (z - t)| < S.r₀
    have := abs_sub_abs_le_abs_sub (signedDist Ω (z - t)) (signedDist Ω z)
    push_cast at h1
    linarith
  · have : 2 * S.LX * δ ≤ S.κ₀ / 4 := by
      have h1 : (S.LX : ℝ) * (S.κ₀ / (8 * S.LX + 8)) ≤ S.κ₀ / 8 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      nlinarith
    linarith

open Classical in
/-- The crossing time of the level `l` of `φ` along the flow line of `x`, within `[-T₁, T₁]`
(`0` if there is none). -/
def crossTime (Φ : ℝ → PlaneMap) (T₁ : ℝ) (φ : ℂ → ℝ) (l : ℝ) (x : ℂ) : ℝ :=
  if h : ∃ u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l then h.choose else 0

section
variable {Φ : ℝ → PlaneMap} {T₁ : ℝ} {φ : ℂ → ℝ} {l : ℝ} {x : ℂ}
include Φ T₁ φ l x

lemma crossTime_spec
    (h : ∃ u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) :
    crossTime Φ T₁ φ l x ∈ Icc (-T₁) T₁ ∧ φ (Φ (crossTime Φ T₁ φ l x) x) = l := by
  grind [crossTime]

lemma crossTime_eq
    (h : ∃! u, u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) 
    (hu : u ∈ Icc (-T₁) T₁ ∧ φ (Φ u x) = l) : crossTime Φ T₁ φ l x = u :=
  h.unique (crossTime_spec h.exists) hu

end


namespace BZLevelData

variable {Ω : PlanarSet} {S : BZSetting Ω} (D : BZLevelData S)
local notation "signedDistFixed" => signedDist Ω


/-- The window `T₁ = A₁ D.T` of crossing times. -/
def T₁  := S.A₁ * D.T

/-- The level `ε = κ₀ D.T / 24`. -/
def ε  := S.κ₀ * D.T / 24

/-- The collar `C = {|d| < 4 M D.T}`. -/
def C  := {x | |signedDistFixed x| < 4 * S.M * D.T}

/-- The flow time from the boundary. -/
def a x  := -crossTime S.Φ D.T₁ (signedDistFixed) 0 x

/-- The flow time to the level `ρ = ε`. -/
def s x  := crossTime S.Φ D.T₁ D.ρ D.ε x

/-- The flow time from the boundary to the level `ρ = ε`. -/
def b x  := D.a x + D.s x

lemma T₁_pos : 0 < D.T₁ := by
  have := S.A₁_ge; have := D.T_pos; unfold T₁; positivity

lemma T₁_le : D.T₁ ≤ 1 / 8 := by
  have hA := S.A₁_ge
  have h1  := D.T_le.trans (min_le_left _ _)
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
  have h1  := D.T_le.trans (min_le_right _ _)
  rw [le_div_iff₀ (by positivity)] at h1
  unfold T₁
  have e : 4 * S.M * D.T + 2 * (S.M * (2 * (S.A₁ * D.T))) =
      D.T * (16 * S.M * (1 + S.A₁)) / 4 := by ring
  linarith [S.hr₀]

/-- Flow lines from the collar stay in the region of transversality for times `|u| ≤ 2 T₁`. -/
lemma flow_mem_U₁  (hx : |signedDistFixed x| < 4 * S.M * D.T) 
    (hu : |u| ≤ 2 * D.T₁) : S.Φ u x ∈ S.U₁ := by
  have h1 := D.T₁_le
  have h2 := S.abs_signedDist_flow_sub_le x (u := u)
    ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩
  have h3 := D.path_bound
  have hM := S.M_pos
  show |signedDistFixed (S.Φ u x)| < S.r₀ / 2
  have := abs_sub_abs_le_abs_sub (signedDistFixed (S.Φ u x)) (signedDistFixed x)
  nlinarith

lemma existsUnique_cross_d  (hx : x ∈ D.C) :
    ∃! u, u ∈ Icc (-D.T₁) D.T₁ ∧ signedDistFixed (S.Φ u x) = 0 := by
  have hx' : |signedDistFixed x| < 4 * S.M * D.T := hx
  have hκT := D.κT₁
  have hM := S.M_pos
  have hT := D.T_pos
  refine S.hΦ.existsUnique_crossing S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁
    D.T₁_pos (by linarith [D.T₁_le]) x
    (fun u hu => D.flow_mem_U₁ hx' (abs_le.mpr ⟨by linarith [hu.1, D.T₁_pos],
      by linarith [hu.2, D.T₁_pos]⟩)) ?_ ?_
  · have := (abs_lt.mp hx').1; nlinarith
  · have := (abs_lt.mp hx').2; nlinarith

lemma abs_ρ_sub_ε_le x : |D.ρ x - D.ε| ≤ |signedDistFixed x| + S.κ₀ * D.T / 16 := by
  have h1 := D.close x
  unfold ε
  grind

section
variable {x } (hx : x ∈ D.C)
include x hx

lemma existsUnique_cross_ρ :
    ∃! u, u ∈ Icc (-D.T₁) D.T₁ ∧ D.ρ (S.Φ u x) = D.ε := by
  have hx' : |signedDistFixed x| < 4 * S.M * D.T := hx
  have hκT := D.κT₁
  have hM := S.M_pos
  have hT := D.T_pos
  have hκM := S.hκM
  have h1 := D.abs_ρ_sub_ε_le x
  refine S.hΦ.existsUnique_crossing S.hX S.hM D.lip S.hτ₀ (by linarith [S.hκ₀]) D.trans
    D.T₁_pos (by linarith [D.T₁_le]) x
    (fun u hu => D.flow_mem_U₁ hx' (abs_le.mpr ⟨by linarith [hu.1, D.T₁_pos],
      by linarith [hu.2, D.T₁_pos]⟩)) ?_ ?_
  · have := (abs_le.mp h1).1; nlinarith
  · have := (abs_le.mp h1).2; nlinarith

lemma cross_d_spec :
    -D.a x ∈ Icc (-D.T₁) D.T₁ ∧ signedDistFixed (S.Φ (-D.a x) x) = 0 := by
  simp  [a]; exact crossTime_spec (D.existsUnique_cross_d hx).exists

lemma cross_ρ_spec :
    D.s x ∈ Icc (-D.T₁) D.T₁ ∧ D.ρ (S.Φ (D.s x) x) = D.ε :=
  crossTime_spec (D.existsUnique_cross_ρ hx).exists

section
variable {u } (hu : u ∈ Icc (-D.T₁) D.T₁)
include u hu

lemma a_eq
    (hdu : signedDistFixed (S.Φ u x) = 0) : D.a x = -u := by
  simp  [a, crossTime_eq (D.existsUnique_cross_d hx) ⟨hu, hdu⟩]

lemma s_eq
    (hdu : D.ρ (S.Φ u x) = D.ε) : D.s x = u :=
  crossTime_eq (D.existsUnique_cross_ρ hx) ⟨hu, hdu⟩

end


/-- `|d(x)| ≤ 2 M |a(x)|`. -/
lemma abs_d_le : |signedDistFixed x| ≤ 2 * (S.M * |D.a x|) := by
  obtain ⟨hu, h0⟩ := D.cross_d_spec hx
  have h1 := D.T₁_le
  have := S.abs_signedDist_flow_sub_le x (u := -D.a x)
    ⟨by linarith [hu.1, D.T₁_pos], by linarith [hu.2]⟩
  simp_all

end


/-- Points of the collar are in `Ω` exactly when their flow time from the boundary is positive. -/
lemma mem_iff_a_pos (hΩo : IsOpen Ω) (hΩu : Ωᶜ.Nonempty)  (hx : x ∈ D.C) :
    x ∈ Ω ↔ 0 < D.a x := by
  obtain ⟨hu, h0⟩ := D.cross_d_spec hx
  have hx'  := hx
  have hT1 := D.T₁_le
  have hpath : ∀ v, |v| ≤ D.T₁ → S.Φ v x ∈ S.U₁ := fun v hv =>
    D.flow_mem_U₁ hx' (by linarith [D.T₁_pos])
  rw [← signedDist_pos_iff hΩo hΩu]
  rcases lt_trichotomy (D.a x) 0 with hneg | hzero | hpos
  · -- the crossing time `-a x` is positive: `d x < 0`
    have := S.hΦ.lt_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ x
      (s := 0) (t := -D.a x) (by norm_num) (by linarith) (by linarith [hu.2])
      (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1, D.T₁_pos], by linarith [hv.2, hu.2]⟩))
    rw [S.hΦ.zero, h0] at this
    constructor <;> intro h <;> linarith
  · have : -D.a x = 0 := by rw [hzero, neg_zero]
    rw [this, S.hΦ.zero] at h0
    rw [h0, hzero]
  · have := S.hΦ.lt_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ x
      (s := -D.a x) (t := 0) (by linarith [hu.1]) (by linarith) (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1, hu.1], by linarith [hv.2, D.T₁_pos]⟩))
    rw [S.hΦ.zero, h0] at this
    constructor <;> intro _ <;> linarith

lemma T_lt : D.T < 1 / 2 := by
  have := D.T_le_T₁; have := D.T₁_le; linarith

/-- Group law within the window. -/
lemma flow_add x  (hu : |u| ≤ 4 * D.T₁) (hv : |v| ≤ 2 * D.T₁) :
    S.Φ u (S.Φ v x) = S.Φ (u + v) x := by
  have h := D.T₁_le
  exact S.hΦ.add S.hX x ⟨by linarith [(abs_le.mp hu).1], by linarith [(abs_le.mp hu).2]⟩
    ⟨by linarith [(abs_le.mp hv).1], by linarith [(abs_le.mp hv).2]⟩

section
variable {x } (hx : x ∈ D.C)
include x hx

/-- The flow time from the boundary to the level `ρ = ε` lies in `[0, T/8]`. -/
lemma b_mem : 0 ≤ D.b x ∧ D.b x ≤ D.T / 8 := by
  obtain ⟨ht, hd⟩ := D.cross_d_spec hx
  obtain ⟨hs, hρ⟩ := D.cross_ρ_spec hx
  have hT1 := D.T₁_le
  have hT1p := D.T₁_pos
  set t₀ := -D.a x
  set p := S.Φ t₀ x
  have hq : S.Φ (D.b x) p = S.Φ (D.s x) x := by
    rw [D.flow_add x (abs_le.mpr ⟨by simp  [b]; linarith [hs.1, ht.2],
      by simp only [b]; linarith [hs.2, ht.1]⟩) (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
    simp only [b, t₀]; ring
  have hbq : |D.b x| ≤ 2 * D.T₁ := abs_le.mpr ⟨by simp only [b]; linarith [hs.1, ht.2],
    by simp only [b]; linarith [hs.2, ht.1]⟩
  have hdq : D.ε / 2 ≤ signedDistFixed (S.Φ (D.b x) p) ∧
      signedDistFixed (S.Φ (D.b x) p) ≤ 3 * D.ε / 2 := by
    rw [hq]
    have := D.close (S.Φ (D.s x) x)
    rw [hρ] at this
    have h1 := abs_le.mp this
    grind only [ε]
  have hp0 : |signedDistFixed p| < 4 * S.M * D.T := by
    rw [hd, abs_zero]; have := S.M_pos; have := D.T_pos; positivity
  have hpath : ∀ v, |v| ≤ 2 * D.T₁ → S.Φ v p ∈ S.U₁ := fun v hv => D.flow_mem_U₁ hp0 hv
  have hε : 0 < D.ε := by unfold ε; have := S.hκ₀; have := D.T_pos; positivity
  have hb0 : 0 < D.b x := by
    by_contra hle
    push_neg at hle
    have := S.hΦ.le_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ p
      (s := D.b x) (t := 0) (by linarith [(abs_le.mp hbq).1]) hle (by norm_num)
      (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1, (abs_le.mp hbq).1], by
        linarith [hv.2]⟩))
    rw [S.hΦ.zero, hd] at this
    have := S.hκ₀
    nlinarith [hdq.1]
  have := S.hΦ.le_of_transversal S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁ p
    (s := 0) (t := D.b x) (by norm_num) hb0.le (by linarith [(abs_le.mp hbq).2])
    (fun v hv => hpath v (abs_le.mpr ⟨by linarith [hv.1], by linarith [hv.2, (abs_le.mp hbq).2]⟩))
  rw [S.hΦ.zero, hd] at this
  refine ⟨hb0.le, ?_⟩
  have h2 := hdq.2
  unfold ε at h2
  have hκ := S.hκ₀
  nlinarith

/-- Flow invariance of the collar coordinates. -/
lemma flow_collar (hax : |D.a x| < D.T)  (hu : |u| ≤ D.T) :
    S.Φ u x ∈ D.C ∧ D.a (S.Φ u x) = D.a x + u ∧ D.b (S.Φ u x) = D.b x := by
  obtain ⟨ht, hd⟩ := D.cross_d_spec hx
  obtain ⟨hs, hρ⟩ := D.cross_ρ_spec hx
  have h64 := D.T_le_T₁
  have hT1 := D.T₁_le
  obtain ⟨hb0, hb8⟩ := D.b_mem hx
  have hax' := abs_lt.mp hax
  have hu' := abs_le.mp hu
  -- `Φ_u x = Φ_{a + u} p` with `p` on the boundary level
  have hyp : S.Φ (D.a x + u) (S.Φ (-D.a x) x) = S.Φ u x := by
    rw [D.flow_add x (abs_le.mpr ⟨by linarith, by linarith⟩)
      (abs_le.mpr ⟨by linarith, by linarith⟩)]
    ring
  have hyC : S.Φ u x ∈ D.C := by
    have := S.abs_signedDist_flow_sub_le (S.Φ (-D.a x) x) (u := D.a x + u)
      ⟨by linarith, by linarith⟩
    rw [hyp, hd, sub_zero] at this
    show |signedDistFixed (S.Φ u x)| < 4 * S.M * D.T
    have hM := S.M_pos
    have : S.M * |D.a x + u| < S.M * (2 * D.T) := by
      apply mul_lt_mul_of_pos_left _ hM
      rw [abs_lt]; constructor <;> linarith
    linarith
  have ha : D.a (S.Φ u x) = D.a x + u := by
    have h1 : S.Φ (-(D.a x + u)) (S.Φ u x) = S.Φ (-D.a x) x := by
      rw [D.flow_add x (abs_le.mpr ⟨by linarith, by linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)]
      congr 1; ring
    rw [D.a_eq hyC (u := -(D.a x + u)) ⟨by linarith, by linarith⟩ (by rw [h1, hd]), neg_neg]
  have hsu : D.s (S.Φ u x) = D.s x - u := by
    have hsx : D.s x = D.b x - D.a x := by simp only [b]; ring
    have h1 : S.Φ (D.s x - u) (S.Φ u x) = S.Φ (D.s x) x := by
      rw [D.flow_add x (abs_le.mpr ⟨by rw [hsx]; linarith, by rw [hsx]; linarith⟩)
        (abs_le.mpr ⟨by linarith, by linarith⟩)]
      congr 1; ring
    exact D.s_eq hyC ⟨by rw [hsx]; linarith, by rw [hsx]; linarith⟩ (by rw [h1, hρ])
  simp_all [b, PolyaNeumann.BZLevelData.C,  PolyaNeumann.BZLevelData.a, PolyaNeumann.BZLevelData.b]

section
variable {y } (hy : y ∈ D.C)
include y hy

lemma a_lip :
    |D.a x - D.a y| ≤ S.La * ‖x - y‖ := by
  have hy'  := hy
  have := S.hΦ.abs_crossing_sub_le S.hX S.hM (lipschitzWith_signedDist Ω) S.hτ₀ S.hκ₀ S.hQ₁
    (by linarith [D.T₁_le]) (x := x) (y := y)
    (fun v hv => D.flow_mem_U₁ hy' (abs_le.mpr ⟨by linarith [hv.1, D.T₁_pos],
      by linarith [hv.2, D.T₁_pos]⟩))
    (D.cross_d_spec hx).1 (D.cross_d_spec hy).1 (D.cross_d_spec hx).2 (D.cross_d_spec hy).2
  rw [show -D.a x - -D.a y = -(D.a x - D.a y) by ring, abs_neg] at this
  unfold BZSetting.La
  have hκ := S.hκ₀
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  push_cast at this
  nlinarith

lemma s_lip :
    |D.s x - D.s y| ≤ 8 * Real.exp S.LX / S.κ₀ * ‖x - y‖ := by
  have hy'  := hy
  have := S.hΦ.abs_crossing_sub_le S.hX S.hM D.lip S.hτ₀ (by linarith [S.hκ₀]) D.trans
    (by linarith [D.T₁_le]) (x := x) (y := y)
    (fun v hv => D.flow_mem_U₁ hy' (abs_le.mpr ⟨by linarith [hv.1, D.T₁_pos],
      by linarith [hv.2, D.T₁_pos]⟩))
    (D.cross_ρ_spec hx).1 (D.cross_ρ_spec hy).1 (D.cross_ρ_spec hx).2 (D.cross_ρ_spec hy).2
  have hκ := S.hκ₀
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
  push_cast at this
  nlinarith

lemma b_lip :
    |D.b x - D.b y| ≤ S.Lb * ‖x - y‖ := by
  have h1 := D.a_lip hx hy
  have h2 := D.s_lip hx hy
  have : |D.b x - D.b y| ≤ |D.a x - D.a y| + |D.s x - D.s y| := by
    simp  [b]
    grind
  have e : S.Lb = S.La + 8 * Real.exp S.LX / S.κ₀ := by unfold BZSetting.Lb BZSetting.La; ring
  rw [e, add_mul]
  linarith

end


lemma gap (hax : |D.a x| < D.T)  (hy : y ∉ D.C) :
    S.M * D.T ≤ ‖x - y‖ := by
  have h1 := D.abs_d_le hx
  have hy' : 4 * S.M * D.T ≤ |signedDistFixed y| := not_lt.mp hy
  have h2 := (lipschitzWith_signedDist Ω).dist_le_mul y x
  rw [Real.dist_eq, dist_eq_norm, norm_sub_rev] at h2
  have h3 := abs_sub_abs_le_abs_sub (signedDistFixed y) (signedDistFixed x)
  have hM := S.M_pos
  have  := mul_le_mul_of_nonneg_left hax.le hM.le
  push_cast at h2
  linarith

end



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
