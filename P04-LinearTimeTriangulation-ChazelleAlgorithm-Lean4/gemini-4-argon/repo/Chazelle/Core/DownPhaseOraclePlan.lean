module

public import Chazelle.Core.DownPhaseOracleHit

/-!
# WP-M (E7-B, part 5): the plan of an interior query

A query of the interior oracles (a subarc of the interior walk from `s = ⟨e₁, h₁⟩` to
`e = ⟨e₂, h₂⟩`) is served by one or two subarcs of at most `n - 1` edges, each by one or two arcs
of the chain model of its chain (`DownPhaseOracleArc`).

* `nh`: the end is normalized (a height code at the height of the start vertex of its edge
  becomes the vertex code `0`, `param_nh`), so that a nonzero code has a positive parameter
  (`param_pos_nh`);
* `plan_arc`: with `ee` the offset of the end edge (`dOf`, or `0`/`n` on one edge) and
  `L = ee + [h₂ ≠ 0]` the number of walk edges met, the point set is `oset e₁ x (ee + t₂)` and the
  weight is `L` (`n` if `L = n + 1`);
* `CArc`: the facts the chain shooter and cutter need for one chain arc (proper ends on the walk,
  inner points, weight, point set); `chainArcs_one`, `chainArcs_two`: the chain arcs of a subarc;
* `oset_sub_set`: the points of a subarc lie on its chain.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_fst lerp_snd)

variable {Q : Polygon}

/-! ## Point sets -/

theorem oset_mod (W : Polygon) (g : ℕ) (x y : ℝ) : oset W (g % W.n) x y = oset W g x y := by
  ext z; constructor
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    exact ⟨d, t, h0, h1, h2, h3, by simp only [Nat.add_assoc, Nat.mod_add_mod]⟩
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    exact ⟨d, t, h0, h1, h2, h3, by simp only [Nat.add_assoc, Nat.mod_add_mod]⟩

/-- **The points of a subarc lie on its chain.** -/
theorem oset_sub_set {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) {x y : ℝ}
    (hy : y ≤ L) : oset (interiorWalk Q) u x y ⊆ (ch Q u L h1 h2).set := by
  rintro _ ⟨d, t, ht0, ht1, hx, hdy, rfl⟩
  have hQ1 : 1 ≤ Q.n := by omega
  have hd : d ≤ L := by
    have : (d : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have tv : ∀ k, k ≤ L → (interiorWalk Q).vtx ((u + k) % (interiorWalk Q).n) =
      WalkEmbed.tourV (ch Q u L h1 h2) (jStart Q L) k := fun k hk => by
    have e1 := iw_tour (a := cStart Q u L) (m := L) (hm1 := h1) (hm := h2) hQ1 (d := k) hk
    rwa [uStart_cStart hu (by omega)] at e1
  rcases ht0.lt_or_eq with htp | rfl
  · have hd1 : d + 1 ≤ L := by
      have : (d : ℝ) < L := by linarith
      have : d < L := by exact_mod_cast this
      omega
    rw [tv d hd, show u + d + 1 = u + (d + 1) by ring, tv (d + 1) hd1]
    unfold jStart
    split_ifs
    · rw [ShootCut.tourV_up _ hd, ShootCut.tourV_up _ hd1]
      exact ShootCut.segment_mem_set _ (show d < (ch Q u L h1 h2).m by rw [ch_m]; omega)
        (ShootCut.lerp_mem_segment ht0 ht1)
    · have e1 : WalkEmbed.tourV (ch Q u L h1 h2) L d = (ch Q u L h1 h2).vertex (L - d) :=
        ShootCut.tourV_down (ch Q u L h1 h2) hd
      have e2 : WalkEmbed.tourV (ch Q u L h1 h2) L (d + 1) =
          (ch Q u L h1 h2).vertex (L - (d + 1)) := ShootCut.tourV_down (ch Q u L h1 h2) hd1
      rw [e1, e2]
      refine ShootCut.segment_mem_set _ (k := L - (d + 1)) (by rw [ch_m]; omega) ?_
      rw [show L - (d + 1) + 1 = L - d by omega, Chazelle.Geometry.segment_comm]
      exact ShootCut.lerp_mem_segment ht0 ht1
  · rw [lerp_zero, tv d hd]
    unfold WalkEmbed.tourV
    exact Chain.vertex_mem_set _ (Chazelle.Chain.sideE_le (Nat.mod_lt _ (Chain.two_m_pos _)).le)

/-! ## Points of the interior walk are within the coordinate bound -/

theorem abs_lerp_le {a b : ℝ} {B t : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |a + t * (b - a)| ≤ B := by
  rw [abs_le] at *
  constructor <;> nlinarith

/-- A proper position of the interior walk lies within the coordinate bound of `Q`. -/
theorem mi_pos_bound {p h : ℕ} (hp : p < Q.n) (hpp : ProperPos (interiorModel Q) Q Q.n ⟨p, h⟩) :
    |((interiorModel Q).pos Q ⟨p, h⟩).1| ≤ Jordan.coordBound Q ∧
      |((interiorModel Q).pos Q ⟨p, h⟩).2| ≤ Jordan.coordBound Q := by
  have hn : 0 < Q.n := by omega
  have ha := mi_wa hp
  have hb := mi_wb hp
  have i1 := iv_lt hp
  have i2 := iv_lt (Q := Q) (p := (p + 1) % Q.n) (Nat.mod_lt _ hn)
  unfold Model.pos
  simp only
  rw [ha, hb, lerp_fst, lerp_snd]
  exact ⟨abs_lerp_le (Jordan.abs_fst_vtx_le_coordBound Q i1)
      (Jordan.abs_fst_vtx_le_coordBound Q i2) hpp.1 hpp.2.1.le,
    abs_lerp_le (Jordan.abs_snd_vtx_le_coordBound Q i1)
      (Jordan.abs_snd_vtx_le_coordBound Q i2) hpp.1 hpp.2.1.le⟩

/-! ## The normalized end -/

/-- **The normalized height code**: a code at the height of the start vertex of the edge becomes
the vertex code `0` (same key, same point). -/
noncomputable def nh (Q : Polygon) (e h : ℕ) : ℕ := by
  classical
  exact if h ≠ 0 ∧ h - 1 = iv Q e then 0 else h

theorem param_nh {e h : ℕ} (he : e < Q.n) :
    (interiorModel Q).param Q ⟨e, nh Q e h⟩ = (interiorModel Q).param Q ⟨e, h⟩ := by
  unfold nh
  split_ifs with hc
  · obtain ⟨h0, h1⟩ := hc
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1
    show (0 : ℝ) = _
    unfold Model.param
    simp only
    rw [mi_wa he, ← h1]
    split_ifs <;> simp
  · rfl

theorem nh_le {e h : ℕ} : nh Q e h ≤ h := by
  unfold nh; split_ifs <;> omega

theorem nh_zero_or {e h : ℕ} : nh Q e h = 0 ∨ nh Q e h = h := by
  unfold nh; split_ifs <;> simp

/-- A nonzero normalized code has a positive parameter. -/
theorem param_pos_nh (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e h : ℕ} (he : e < Q.n)
    (hh : h ≤ Q.n) (hp0 : 0 ≤ (interiorModel Q).param Q ⟨e, h⟩) (h0 : nh Q e h ≠ 0) :
    0 < (interiorModel Q).param Q ⟨e, nh Q e h⟩ := by
  have hnh : nh Q e h = h := nh_zero_or.resolve_left h0
  rw [hnh] at h0 ⊢
  have hc : ¬ (h ≠ 0 ∧ h - 1 = iv Q e) := by
    intro hc; unfold nh at hnh; rw [ite_eq_left hc] at hnh; exact h0 hnh.symm
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hne : h' ≠ iv Q e := fun hc' => hc ⟨h0, by simpa using hc'⟩
  rcases hp0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    unfold Model.param at heq
    simp only at heq
    have hwa := mi_wa (Q := Q) he
    have hwb := mi_wb (Q := Q) he
    have hnh' : ((interiorModel Q).wa e).2 ≠ ((interiorModel Q).wb e).2 := by
      rw [hwa, hwb]
      have h1 := iv_lt (Q := Q) he
      have h2 := iv_lt (Q := Q) (p := (e + 1) % Q.n) (Nat.mod_lt _ (by omega))
      refine hD _ _ h1 h2 ?_
      unfold iv
      split_ifs
      · intro hc2
        rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at hc2; omega
        · rw [h3, Nat.mod_self] at hc2; omega
      · intro hc2
        rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
        · rw [Nat.mod_eq_of_lt h3] at hc2; omega
        · rw [h3, Nat.mod_self] at hc2; omega
    rw [ite_eq_right hnh', eq_comm, div_eq_zero_iff] at heq
    rcases heq with heq | heq
    · rw [hwa] at heq
      exact hD _ _ (by omega) (iv_lt he) hne (by linarith)
    · exact hnh' (by linarith)

/-! ## The plan of a query -/

/-- **The offset of the end edge** of an interior query from its start edge: `dOf`, or on one
edge `0` (the end after the start) or `n` (the query goes once around). -/
noncomputable def eeOf (Q : Polygon) (e₁ h₁ e₂ h₂ : ℕ) : ℕ := by
  classical
  exact if WalkEmbed.dOf Q.n e₁ e₂ = 0 then
    (if (interiorModel Q).param Q ⟨e₁, h₁⟩ < (interiorModel Q).param Q ⟨e₂, h₂⟩ then 0 else Q.n)
  else WalkEmbed.dOf Q.n e₁ e₂

/-- The number of walk edges met by a query whose end edge is at offset `ee`. -/
def spanL (ee h₂ : ℕ) : ℕ := ee + (if h₂ = 0 then 0 else 1)

theorem param_hgt_zero (M : Model) (e : ℕ) : M.param Q ⟨e, 0⟩ = 0 := rfl

/-- The weight of a query going once around past its start. -/
theorem arcWt_around {e₁ : ℕ} (he₁ : e₁ < Q.n) {x t₂ : ℝ} (hx : x < 1) (ht0 : 0 < t₂)
    (htx : t₂ ≤ x) : (interiorModel Q).arcWt ((e₁ : ℝ) + x) ((e₁ : ℝ) + t₂) = Q.n := by
  have hc : ∀ p, p < (interiorModel Q).W.n →
      ((interiorModel Q).counted p ↔ 0 ≤ p ∧ p < (interiorModel Q).W.n) := fun p hp => by
    rw [mi_n] at hp ⊢; exact interiorModel_counted_iff Q p (by rwa [mi_n])
  rw [(interiorModel Q).arcWt_closed hc le_rfl ⟨by linarith, hx⟩ ⟨ht0.le, by linarith⟩, mi_n]
  unfold arcWtNat keyCeil
  rw [ite_eq_right (by linarith), ite_eq_right ht0.ne']
  simp only [min_eq_left he₁.le]
  omega

/-- **The plan of an interior query** (with the normalized end). -/
theorem plan_arc (hn : 3 ≤ Q.n) {e₁ h₁ e₂ h₂ : ℕ} (he₁ : e₁ < Q.n) (he₂ : e₂ < Q.n)
    (hx : 0 ≤ (interiorModel Q).param Q ⟨e₁, h₁⟩ ∧ (interiorModel Q).param Q ⟨e₁, h₁⟩ < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ⟨e₂, h₂⟩ ∧ (interiorModel Q).param Q ⟨e₂, h₂⟩ < 1)
    (hnz : h₂ = 0 ∨ 0 < (interiorModel Q).param Q ⟨e₂, h₂⟩) :
    (interiorModel Q).arcSet ((interiorModel Q).key Q ⟨e₁, h₁⟩)
        ((interiorModel Q).key Q ⟨e₂, h₂⟩) =
      oset (interiorWalk Q) e₁ ((interiorModel Q).param Q ⟨e₁, h₁⟩)
        (eeOf Q e₁ h₁ e₂ h₂ + (interiorModel Q).param Q ⟨e₂, h₂⟩) ∧
    (interiorModel Q).param Q ⟨e₁, h₁⟩ < eeOf Q e₁ h₁ e₂ h₂ + (interiorModel Q).param Q ⟨e₂, h₂⟩ ∧
    (e₁ + eeOf Q e₁ h₁ e₂ h₂) % Q.n = e₂ ∧ eeOf Q e₁ h₁ e₂ h₂ ≤ Q.n ∧
    ((h₂ = 0 ∧ eeOf Q e₁ h₁ e₂ h₂ = spanL (eeOf Q e₁ h₁ e₂ h₂) h₂) ∨
      (h₂ ≠ 0 ∧ eeOf Q e₁ h₁ e₂ h₂ + 1 = spanL (eeOf Q e₁ h₁ e₂ h₂) h₂ ∧
        0 < (interiorModel Q).param Q ⟨e₂, h₂⟩)) ∧
    1 ≤ spanL (eeOf Q e₁ h₁ e₂ h₂) h₂ ∧
    (spanL (eeOf Q e₁ h₁ e₂ h₂) h₂ ≤ Q.n → (interiorModel Q).arcWt
      ((interiorModel Q).key Q ⟨e₁, h₁⟩) ((interiorModel Q).key Q ⟨e₂, h₂⟩) =
        spanL (eeOf Q e₁ h₁ e₂ h₂) h₂) ∧
    (Q.n < spanL (eeOf Q e₁ h₁ e₂ h₂) h₂ → (interiorModel Q).arcWt
      ((interiorModel Q).key Q ⟨e₁, h₁⟩) ((interiorModel Q).key Q ⟨e₂, h₂⟩) = Q.n) := by
  set x := (interiorModel Q).param Q ⟨e₁, h₁⟩
  set t₂ := (interiorModel Q).param Q ⟨e₂, h₂⟩ with ht₂
  set ee := eeOf Q e₁ h₁ e₂ h₂ with heed
  have hn0 : 0 < Q.n := by omega
  have hd := WalkEmbed.add_dOf he₁ he₂
  have hdl := WalkEmbed.dOf_lt hn0 e₁ e₂
  -- the offset and its properties
  have hE : (x < ee + t₂ ∧ (ee : ℝ) + t₂ ≤ x + Q.n) ∧ (e₁ + ee) % Q.n = e₂ ∧ ee ≤ Q.n ∧
      (ee = 0 → h₂ ≠ 0) := by
    rw [heed]
    unfold eeOf
    by_cases h0 : WalkEmbed.dOf Q.n e₁ e₂ = 0
    · rw [ite_eq_left h0]
      rw [h0, Nat.add_zero, Nat.mod_eq_of_lt he₁] at hd
      by_cases hlt : x < t₂
      · rw [ite_eq_left hlt]
        have h3 : (3 : ℝ) ≤ Q.n := by exact_mod_cast hn
        refine ⟨⟨by push_cast; linarith, by push_cast; linarith [hy.2, hx.1]⟩, by
          rw [Nat.add_zero, Nat.mod_eq_of_lt he₁, hd], by omega, fun _ hz => ?_⟩
        rw [hz] at ht₂
        have : t₂ = 0 := by rw [ht₂]; rfl
        linarith [hx.1]
      · rw [ite_eq_right hlt]
        push Not at hlt
        refine ⟨⟨by linarith [hy.1, hx.2, (show (1 : ℝ) ≤ Q.n by exact_mod_cast (show 1 ≤ Q.n by
          omega))], by linarith⟩, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt he₁, hd], le_rfl,
          fun h => by omega⟩
    · rw [ite_eq_right h0]
      have h1 : (1 : ℝ) ≤ WalkEmbed.dOf Q.n e₁ e₂ := by exact_mod_cast (show 1 ≤ _ by omega)
      have h2 : ((WalkEmbed.dOf Q.n e₁ e₂ : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast hdl
      exact ⟨⟨by linarith [hx.2, hy.1], by linarith [hx.1, hy.2]⟩, hd, hdl.le, fun h => absurd h h0⟩
  obtain ⟨⟨hxy, hlap⟩, hmod, heen, hee0⟩ := hE
  have hsp : ((h₂ = 0 ∧ ee = spanL ee h₂) ∨ (h₂ ≠ 0 ∧ ee + 1 = spanL ee h₂ ∧ 0 < t₂)) := by
    unfold spanL
    by_cases h0 : h₂ = 0
    · left; exact ⟨h0, by rw [ite_eq_left h0]; rfl⟩
    · right; exact ⟨h0, by rw [ite_eq_right h0], hnz.resolve_left h0⟩
  have hkc : keyCeil ee t₂ = spanL ee h₂ := by
    unfold keyCeil
    rcases hsp with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · have : t₂ = 0 := by rw [ht₂, h0]; rfl
      rwa [ite_eq_left this]
    · rwa [ite_eq_right h2.ne']
  have hb : (interiorModel Q).key Q ⟨e₂, h₂⟩ = (((e₁ + ee) % Q.n : ℕ) : ℝ) + t₂ := by
    rw [hmod]; rfl
  have hu' : e₁ < (interiorModel Q).W.n := by rwa [mi_n]
  refine ⟨?_, hxy, hmod, heen, hsp, ?_, fun hle => ?_, fun hlt => ?_⟩
  · rw [key_eq, hb]
    have hb0 : (0 : ℝ) ≤ (((e₁ + ee) % Q.n : ℕ) : ℝ) + t₂ := by have := hy.1; positivity
    have hbn : (((e₁ + ee) % Q.n : ℕ) : ℝ) + t₂ < (interiorModel Q).W.n := by
      rw [mi_n]
      have : ((e₁ + ee) % Q.n : ℕ) + 1 ≤ Q.n := Nat.mod_lt _ hn0
      have : (((e₁ + ee) % Q.n : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast this
      linarith [hy.2]
    rw [arcSet_eq_oset _ hu' hx.1 hx.2 hb0 hbn, mi_n, len_key he₁ hx.2 hy.1 hxy hlap]
    congr 1; ring
  · rcases hsp with ⟨h0, h1⟩ | ⟨h0, h1, -⟩
    · rw [← h1]; by_contra hc; exact hee0 (by omega) h0
    · omega
  · have hc : ∀ p, p < (interiorModel Q).W.n →
        ((interiorModel Q).counted p ↔ 0 ≤ p ∧ p < (interiorModel Q).W.n) := fun p hp => by
      rw [mi_n] at hp ⊢; exact interiorModel_counted_iff Q p (by rwa [mi_n])
    rw [key_eq, hb, ← hkc]
    have := arcWt_off (interiorModel Q) hc le_rfl hu' (Nat.zero_le _) hx.1 hx.2 hy.1 hy.2 hxy
      (Or.inl ⟨rfl, rfl, by rwa [hkc, mi_n]⟩)
    rwa [mi_n] at this
  · -- once around: `ee = n`, the end on the start edge, before the start
    rcases hsp with ⟨h0, h1⟩ | ⟨h0, h1, ht0⟩
    · omega
    · have hen : ee = Q.n := by omega
      rw [hen, Nat.add_mod_right, Nat.mod_eq_of_lt he₁] at hmod
      have htx : t₂ ≤ x := by
        rw [hen] at hlap; linarith
      rw [key_eq, key_eq]
      show (interiorModel Q).arcWt ((e₁ : ℝ) + x) ((e₂ : ℝ) + t₂) = Q.n
      rw [← hmod]
      exact arcWt_around he₁ hx.2 ht0 htx

end

end IOrc

end Chazelle.Core
