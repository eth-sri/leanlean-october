module

public import Chazelle.Core.ShootCutSeg

/-!
# WP-G, part 6: origins and hit points as symbolic points

On a regular host (`HostRegular`), every non-horizontal edge of the host polygon lies on the line
of an edge of `Q` (`HostEdgeOK`).  So a walk position of the chain model at the height of a
vertex `h` of `Q` on such a host edge is the symbolic point `onEdge e h` (`pos_eq_onEdge`); this is
how the ray-shooter turns walk-position origins into query origins of the Lemma 3.6 structure and
how it names hit points.

* `xAt_eq_of_line`: two points on a non-horizontal line define the same line;
* `edgeOf`: the edge of `Q` carrying a host edge;
* `pos_eq_onEdge`: the walk position at height code `h + 1` on a non-horizontal host edge.
* `firstHit_shift`: moving the origin along the ray line, behind every point of the set on that
  line, shifts the first-hit parameter.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd xAt xAt_left xAt_right xAt_lerp edgeX)

namespace ShootCut

theorem goodEnv_distinct {P : Polygon} (hG : GoodEnv P) : DistinctHeights (Qof P) :=
  (goodShear_epsOf hG.2).2.1

/-- A point lies on the line through `u` and `w` (as a graph over the height). -/
def OnLine (u w a : Point) : Prop := a.1 = xAt u w a.2

/-- **Two points of a line define it.** -/
theorem xAt_eq_of_line {u w a b : Point} (huw : u.2 ≠ w.2) (hab : a.2 ≠ b.2) (ha : OnLine u w a)
    (hb : OnLine u w b) (y : ℝ) : xAt a b y = xAt u w y := by
  unfold OnLine at ha hb
  unfold xAt at ha hb ⊢
  have h1 : w.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm huw)
  have h2 : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  rw [ha, hb]
  field_simp
  ring

/-- **The edge of `Q` carrying a host edge** (for `HostEdgeOK` pairs). -/
def edgeOf (n : ℕ) : SymPt → SymPt → ℕ
  | .vtx i, .vtx j => if j = (i + 1) % n then i else j
  | .vtx _, .onEdge e _ => e
  | .onEdge e _, _ => e

variable {Q : Polygon}

theorem vtx_onLine (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    OnLine (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) (Q.vtx e) ∧
      OnLine (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) (Q.vtx ((e + 1) % Q.n)) := by
  have hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2 :=
    hD _ _ he (Nat.mod_lt _ (by omega)) (by
      intro h
      rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · rw [h', Nat.mod_self] at h; omega)
  exact ⟨(xAt_left _ _).symm, (xAt_right hne).symm⟩

/-- The edges of `Q` are not horizontal. -/
theorem edge_nh (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2 :=
  hD _ _ he (Nat.mod_lt _ (by omega)) (by
      intro h
      rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h' | h'
      · rw [Nat.mod_eq_of_lt h'] at h; omega
      · rw [h', Nat.mod_self] at h; omega)

/-- **The symbolic points of a regular host edge lie on the line of its edge of `Q`.** -/
theorem hostEdge_onLine (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {sp₁ sp₂ : SymPt}
    (hl₁ : sp₁.Lt Q.n) (hl₂ : sp₂.Lt Q.n) (hok : HostEdgeOK Q.n sp₁ sp₂)
    (hnh : (sp₁.eval Q).2 ≠ (sp₂.eval Q).2) :
    edgeOf Q.n sp₁ sp₂ < Q.n ∧
      OnLine (Q.vtx (edgeOf Q.n sp₁ sp₂)) (Q.vtx ((edgeOf Q.n sp₁ sp₂ + 1) % Q.n)) (sp₁.eval Q) ∧
      OnLine (Q.vtx (edgeOf Q.n sp₁ sp₂)) (Q.vtx ((edgeOf Q.n sp₁ sp₂ + 1) % Q.n)) (sp₂.eval Q) := by
  have onE : ∀ e h, e < Q.n → OnLine (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) ((SymPt.onEdge e h).eval Q) :=
    fun e h _ => rfl
  cases sp₁ with
  | vtx i =>
    cases sp₂ with
    | vtx j =>
      simp only [HostEdgeOK] at hok
      simp only [SymPt.Lt] at hl₁ hl₂
      by_cases hj : j = (i + 1) % Q.n
      · have e : edgeOf Q.n (.vtx i) (.vtx j) = i := by simp [edgeOf, hj]
        rw [e]
        subst hj
        exact ⟨hl₁, (vtx_onLine hD hn hl₁).1, (vtx_onLine hD hn hl₁).2⟩
      · have e : edgeOf Q.n (.vtx i) (.vtx j) = j := by simp [edgeOf, hj]
        rw [e]
        have hi : i = (j + 1) % Q.n := hok.resolve_left hj
        subst hi
        exact ⟨hl₂, (vtx_onLine hD hn hl₂).2, (vtx_onLine hD hn hl₂).1⟩
    | onEdge e h =>
      simp only [HostEdgeOK] at hok
      simp only [SymPt.Lt] at hl₁ hl₂
      refine ⟨hl₂.1, ?_, onE e h hl₂.1⟩
      rcases hok with rfl | rfl
      · exact (vtx_onLine hD hn hl₂.1).1
      · exact (vtx_onLine hD hn hl₂.1).2
  | onEdge e h =>
    simp only [SymPt.Lt] at hl₁
    refine ⟨hl₁.1, onE e h hl₁.1, ?_⟩
    cases sp₂ with
    | vtx j =>
      simp only [HostEdgeOK] at hok
      rcases hok with rfl | rfl
      · exact (vtx_onLine hD hn hl₁.1).1
      · exact (vtx_onLine hD hn hl₁.1).2
    | onEdge e' h' =>
      simp only [HostEdgeOK] at hok
      rcases hok with rfl | rfl
      · exact absurd rfl hnh
      · exact onE e h' hl₁.1

/-- **A walk position at a vertex height on a non-horizontal regular host edge** is the symbolic
point `onEdge e h`, `e` the edge of `Q` carrying the host edge. -/
theorem pos_eq_onEdge (M : Model) (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {p h : ℕ}
    {sp₁ sp₂ : SymPt} (ha : M.wa p = sp₁.eval Q) (hb : M.wb p = sp₂.eval Q) (hl₁ : sp₁.Lt Q.n)
    (hl₂ : sp₂.Lt Q.n) (hok : HostEdgeOK Q.n sp₁ sp₂) (hnh : (M.wa p).2 ≠ (M.wb p).2) :
    M.pos Q ⟨p, h + 1⟩ = (SymPt.onEdge (edgeOf Q.n sp₁ sp₂) h).eval Q := by
  rw [ha, hb] at hnh
  obtain ⟨he, h1, h2⟩ := hostEdge_onLine hD hn hl₁ hl₂ hok hnh
  have hQnh := edge_nh hD hn he
  unfold Model.pos Model.param
  simp only
  rw [ite_eq_right (by rw [ha, hb]; exact hnh), ha, hb]
  have hy : (lerp (sp₁.eval Q) (sp₂.eval Q)
      (((Q.vtx h).2 - (sp₁.eval Q).2) / ((sp₂.eval Q).2 - (sp₁.eval Q).2))).2 = (Q.vtx h).2 :=
    hpar_snd hnh _
  have hx := xAt_lerp hnh (((Q.vtx h).2 - (sp₁.eval Q).2) / ((sp₂.eval Q).2 - (sp₁.eval Q).2))
  rw [hy, xAt_eq_of_line hQnh hnh h1 h2] at hx
  ext
  · rw [← hx]; rfl
  · rw [hy]; rfl

/-! ## Shifting the origin along the ray line -/

/-- **Shifting the origin**: if every point of `S` on the ray line is strictly ahead of both `z`
and `z'` (same height), the first hits from `z` and `z'` correspond. -/
theorem firstHit_shift {S : Set Point} {z z' : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hy : z.2 = z'.2) (hahead : ∀ x ∈ S, x.2 = z.2 → 0 < σ * (x.1 - z.1) ∧ 0 < σ * (x.1 - z'.1)) :
    (∀ t', FirstHit S z' σ t' → FirstHit S z σ (t' + σ * (z'.1 - z.1))) ∧
      (NoHit S z' σ → NoHit S z σ) := by
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have key : ∀ t, rayPt z σ t = rayPt z' σ (t - σ * (z'.1 - z.1)) := by
    intro t
    ext
    · simp only [rayPt_fst]; rw [mul_sub, ← mul_assoc, hσ2, one_mul]; ring
    · simp only [rayPt_snd]; exact hy
  -- parameters of points of `S` on the line
  have ahead_z : ∀ t, rayPt z σ t ∈ S → 0 < t := by
    intro t ht
    have := (hahead _ ht rfl).1
    simp only [rayPt_fst] at this
    have : σ * (σ * t) = t := by rw [← mul_assoc, hσ2, one_mul]
    nlinarith
  refine ⟨fun t' ht' => ⟨?_, ?_, fun s hs1 hs2 hsS => ?_⟩, fun hN t ht hS => ?_⟩
  · apply ahead_z
    rw [key]; simp only [add_sub_cancel_right]; exact ht'.2.1
  · rw [key]; simp only [add_sub_cancel_right]; exact ht'.2.1
  · rw [key] at hsS
    have hpos : 0 < s - σ * (z'.1 - z.1) := by
      have := (hahead _ hsS (by simp [rayPt_snd, hy])).2
      simp only [rayPt_fst] at this
      have e : σ * (σ * (s - σ * (z'.1 - z.1))) = s - σ * (z'.1 - z.1) := by
        rw [← mul_assoc, hσ2, one_mul]
      nlinarith
    exact ht'.2.2 _ hpos (by linarith) hsS
  · rw [key] at hS
    have hpos : 0 < t - σ * (z'.1 - z.1) := by
      have := (hahead _ hS (by simp [rayPt_snd, hy])).2
      simp only [rayPt_fst] at this
      have e : σ * (σ * (t - σ * (z'.1 - z.1))) = t - σ * (z'.1 - z.1) := by
        rw [← mul_assoc, hσ2, one_mul]
      nlinarith
    exact hN _ hpos hS

end ShootCut

end

end Chazelle.Core
