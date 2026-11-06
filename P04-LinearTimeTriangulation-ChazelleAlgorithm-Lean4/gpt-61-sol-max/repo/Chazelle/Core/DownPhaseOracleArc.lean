module

public import Chazelle.Core.DownPhaseOracleSet

/-!
# WP-M (E7-B, part 3): an interior subarc as one or two chain arcs (O3)

A subarc of the interior walk of `Q` spanning `L ≤ n - 1` walk edges from the walk vertex `u`
is served through the chain `ch Q u L` of `Q` (start `cStart Q u L`, `L` edges), whose chain
model walk agrees with the interior walk from `u` (`agree_pre`), up to the top of the chain if
the tour passes the box there (then from the walk vertex `6` on, `agree_post`).

For the subarc from `⟨u, h₁⟩` (parameter `x`) to `⟨(u + e) mod n, h₂⟩` (offset `y = e + t₂`):

* `sub_arcSet`: its point set is `oset (interiorWalk Q) u x y`;
* `chain_arcSet_one` (no split, `τ ≤ L`): the chain arc from `⟨g', h₁⟩` to `⟨g' + e, h₂⟩`
  (`g' = 6 + τ`, `τ` the tour offset) has the same point set;
* `chain_arcSet_two` (split at the top, `τ > L`, `L₁ = 2L - τ`): the chain arcs from `⟨g', h₁⟩`
  to the top `⟨2L + 6, 0⟩` and from `⟨6, 0⟩` to `⟨6 + e - L₁, h₂⟩` have the union;
* parameters agree (`param_start`, `param_end_one`, `param_end_two`), and the weights of the
  chain arcs are at most `L` (`wt_one`, `wt_two₁`, `wt_two₂`).
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

variable {Q : Polygon}

/-! ## Vertices of the interior walk -/

/-- The vertex of `Q` at vertex `p` of the interior walk. -/
noncomputable def iv (Q : Polygon) (p : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then p else Q.n - 1 - p

section
variable {p : ℕ} (hp : p < Q.n)
include hp
theorem iv_lt : iv Q p < Q.n := by
  grind [iv]

theorem iw_vtx : (interiorWalk Q).vtx p = Q.vtx (iv Q p) := by
  unfold iv
  by_cases hL : Mountain.LeftInside Q
  · simp only [hL, ↓reduceIte]; exact Trans.iw_vtx_left hL p
  · simp only [hL, ↓reduceIte]; exact Trans.iw_vtx_right hL hp


end

theorem mi_n : (interiorModel Q).W.n = Q.n := interiorModel_n Q

/-! ## The chain of a stretch of the interior walk -/

/-- The first vertex (in `Q`) of the chain read along the interior walk from `u` for `L`
steps. -/
noncomputable def cStart (Q : Polygon) (u L : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then u else (Q.n - 1 - u + (Q.n - L)) % Q.n

section
variable {u L : ℕ} (hu : u < Q.n)
include hu
theorem cStart_lt : cStart Q u L < Q.n := by
  unfold cStart; split_ifs
  · exact hu
  · exact Nat.mod_lt _ (by omega)

theorem uStart_cStart (hL : L < Q.n) : uStart Q (cStart Q u L) L = u := by
  unfold uStart cStart
  by_cases hl : Mountain.LeftInside Q
  · simp only [hl, ↓reduceIte]; exact Nat.mod_eq_of_lt hu
  · simp only [hl, ↓reduceIte]
    have e : ((Q.n - 1 - u + (Q.n - L)) % Q.n + L) % Q.n = Q.n - 1 - u := by
      rw [Nat.mod_add_mod, show Q.n - 1 - u + (Q.n - L) + L = (Q.n - 1 - u) + Q.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega


end

/-- **The chain of the stretch** of `L` edges of the interior walk from `u`. -/
noncomputable def ch (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : Chain :=
  subChain Q (cStart Q u L) L h1 h2

section
variable {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n}
theorem ch_m : (ch Q u L h1 h2).m = L := rfl

theorem ch_P : (ch Q u L h1 h2).P = Q := rfl


end

/-- The tour offset of the chain read along the interior walk. -/
noncomputable def tau (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : ℕ :=
  WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L)

section
variable {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n}
theorem tau_lt : tau Q u L h1 h2 < 2 * L :=
  WalkEmbed.tpos_lt _ _

theorem cm_n' :
    (chainModel (ch Q u L h1 h2)).W.n = 2 * L + 7 := WalkEmbed.cm_n _


end

section
variable {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)
include hu
/-- **The interior walk agrees with the chain model walk** from `u`, resp. `6 + τ`, up to the top
of the chain or the end of the stretch. -/
theorem agree_pre :
    WalkEmbed.Agree (interiorWalk Q) (chainModel (ch Q u L h1 h2)).W u
      (6 + tau Q u L h1 h2) (min L (2 * L - tau Q u L h1 h2)) := by
  intro d hd
  have hQ1 : 1 ≤ Q.n := by omega
  have e1 := iw_tour (a := cStart Q u L) (m := L) (hm1 := h1) (hm := h2) hQ1 (d := d)
    (by omega)
  rw [uStart_cStart hu (by omega)] at e1
  rw [e1]
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  exact (WalkEmbed.walk_tour (ch Q u L h1 h2) (jStart Q L) d (by
    show tau Q u L h1 h2 + d ≤ 2 * L; omega)).symm

/-- **After the top** (when the tour passes the box inside the stretch): the interior walk from
`u + L₁` agrees with the chain model walk from its vertex `6`. -/
theorem agree_post
    (hs : L < tau Q u L h1 h2) :
    WalkEmbed.Agree (interiorWalk Q) (chainModel (ch Q u L h1 h2)).W
      (u + (2 * L - tau Q u L h1 h2)) 6 (L - (2 * L - tau Q u L h1 h2)) := by
  intro d hd
  have hQ1 : 1 ≤ Q.n := by omega
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  have e1 := iw_tour (a := cStart Q u L) (m := L) (hm1 := h1) (hm := h2) hQ1
    (d := 2 * L - tau Q u L h1 h2 + d) (by omega)
  rw [uStart_cStart hu (by omega)] at e1
  rw [show u + (2 * L - tau Q u L h1 h2) + d = u + (2 * L - tau Q u L h1 h2 + d) by ring, e1]
  have e2 := WalkEmbed.walk_after (ch Q u L h1 h2) (jStart Q L) d (by
    show d ≤ 2 * L; omega)
  have e3 : (6 + WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L) +
      (2 * (ch Q u L h1 h2).m - WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L)) + 7 + d) %
      (chainModel (ch Q u L h1 h2)).W.n = (6 + d) % (chainModel (ch Q u L h1 h2)).W.n := by
    rw [cm_n', ch_m]
    have : WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L) < 2 * L := tau_lt
    rw [show 6 + WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L) +
      (2 * L - WalkEmbed.tpos (ch Q u L h1 h2) (jStart Q L)) + 7 + d = (6 + d) + (2 * L + 7) by
      omega, Nat.add_mod_right]
  rw [e3] at e2
  rw [e2]
  rfl

/-! ## The point set of the interior subarc -/


end

theorem key_eq (M : Model) (Q : Polygon) (x : WPos) : M.key Q x = x.edge + M.param Q x := rfl

/-! ## Chain arcs -/

section chainArc

variable {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)

/-- The chain model of the stretch. -/
noncomputable abbrev MC (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : Model :=
  chainModel (ch Q u L h1 h2)

include hu in
/-- The start parameter is the same in both models. -/
theorem param_start (h₁ : ℕ) :
    (MC Q u L h1 h2).param Q ⟨6 + tau Q u L h1 h2, h₁⟩ = (interiorModel Q).param Q ⟨u, h₁⟩ := by
  have hA := agree_pre hu h1 h2
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  have h0 : 0 < min L (2 * L - tau Q u L h1 h2) := by omega
  have := param_agree (M := interiorModel Q) (M' := MC Q u L h1 h2) hA Q h0 h₁
  rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, cm_n',
    Nat.mod_eq_of_lt (by omega)] at this
  simp_all

include hu in
/-- The end parameter is the same in both models (no split). -/
theorem param_end_one {e h₂ : ℕ} (hs : tau Q u L h1 h2 ≤ L) (he : e < L ∨ (e = L ∧ h₂ = 0)) :
    (MC Q u L h1 h2).param Q ⟨6 + tau Q u L h1 h2 + e, h₂⟩ =
      (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ := by
  rcases he with he | ⟨-, rfl⟩
  · have hA := agree_pre hu h1 h2
    have := param_agree (M := interiorModel Q) (M' := MC Q u L h1 h2) hA Q
      (d := e) (by omega) h₂
    rw [mi_n, cm_n', Nat.mod_eq_of_lt (show 6 + tau Q u L h1 h2 + e < 2 * L + 7 by omega)]
      at this
    simp_all
  · rfl

include hu in
/-- The end parameter is the same in both models (after the top). -/
theorem param_end_two {e h₂ : ℕ} (hs : L < tau Q u L h1 h2)
    (hle : 2 * L - tau Q u L h1 h2 ≤ e) (he : e < L ∨ (e = L ∧ h₂ = 0)) :
    (MC Q u L h1 h2).param Q ⟨6 + (e - (2 * L - tau Q u L h1 h2)), h₂⟩ =
      (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ := by
  rcases he with he | ⟨-, rfl⟩
  · have hA := agree_post hu h1 h2 hs
    have := param_agree (M := interiorModel Q) (M' := MC Q u L h1 h2) hA Q
      (d := e - (2 * L - tau Q u L h1 h2)) (by omega) h₂
    
    rw [mi_n, cm_n', Nat.mod_eq_of_lt (show 6 + (e - (2 * L - tau Q u L h1 h2)) < 2 * L + 7 by
      omega), show u + (2 * L - tau Q u L h1 h2) + (e - (2 * L - tau Q u L h1 h2)) = u + e by
      omega] at this
    simp_all
  · rfl

include hu in
/-- **The chain arc, no split**: the same point set as the interior subarc. -/
theorem chain_arcSet_one {e h₁ h₂ : ℕ} (hs : tau Q u L h1 h2 ≤ L)
    (hx : 0 ≤ (interiorModel Q).param Q ⟨u, h₁⟩ ∧ (interiorModel Q).param Q ⟨u, h₁⟩ < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ ∧
      (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ < 1)
    (he : e < L ∨ (e = L ∧ h₂ = 0))
    (hxy : (interiorModel Q).param Q ⟨u, h₁⟩ < e + (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩) :
    (MC Q u L h1 h2).arcSet ((MC Q u L h1 h2).key Q ⟨6 + tau Q u L h1 h2, h₁⟩)
      ((MC Q u L h1 h2).key Q ⟨6 + tau Q u L h1 h2 + e, h₂⟩) =
      oset (interiorWalk Q) u ((interiorModel Q).param Q ⟨u, h₁⟩)
        (e + (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩) := by
  set x := (interiorModel Q).param Q ⟨u, h₁⟩ with hxd
  set t₂ := (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ with ht₂
  set g := 6 + tau Q u L h1 h2 with hg
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  have hn : (MC Q u L h1 h2).W.n = 2 * L + 7 := cm_n'
  have hge : e ≤ L := by omega
  rw [key_eq, key_eq, param_start hu h1 h2, param_end_one hu h1 h2 hs he]
  have hg' : g < (MC Q u L h1 h2).W.n := by omega
  have hb0 : (0 : ℝ) ≤ ((g + e : ℕ) : ℝ) + t₂ := by grind
  have hbn : ((g + e : ℕ) : ℝ) + t₂ < (MC Q u L h1 h2).W.n := by
    have : ((g + e : ℕ) : ℝ) + 1 ≤ (MC Q u L h1 h2).W.n := by
      rw [hn]; exact_mod_cast (show g + e + 1 ≤ 2 * L + 7 by omega)
    linarith
  show (MC Q u L h1 h2).arcSet ((g : ℝ) + x) (((g + e : ℕ) : ℝ) + t₂) = _
  rw [arcSet_eq_oset _ hg' hx.1 hx.2 hb0 hbn]
  have hmod : (g + e) % (MC Q u L h1 h2).W.n = g + e := Nat.mod_eq_of_lt (by omega)
  have hlap : (e : ℝ) + t₂ ≤ x + (MC Q u L h1 h2).W.n := by
    grind
  have hl := len_key (n := (MC Q u L h1 h2).W.n) hg' hx.2 hy.1 hxy hlap
  rw [hmod] at hl
  rw [hl, show x + (e + t₂ - x) = e + t₂ by ring]
  have hyL : (e : ℝ) + t₂ ≤ ((min L (2 * L - tau Q u L h1 h2) : ℕ) : ℝ) := by
    rw [min_eq_left (by omega)]
    rcases he with he | ⟨he, h0⟩
    · have : (e : ℝ) + 1 ≤ L := by exact_mod_cast he
      linarith
    · have : t₂ = 0 := by rw [ht₂, h0]; rfl
      grind
  exact (oset_congr (agree_pre hu h1 h2) hyL).symm

include hu in
/-- **The chain arcs, split at the top**: the union has the point set of the interior subarc. -/
theorem chain_arcSet_two {e h₁ h₂ : ℕ} (hs : L < tau Q u L h1 h2)
    (hle : 2 * L - tau Q u L h1 h2 ≤ e)
    (hx : 0 ≤ (interiorModel Q).param Q ⟨u, h₁⟩ ∧ (interiorModel Q).param Q ⟨u, h₁⟩ < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ ∧
      (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ < 1)
    (he : e < L ∨ (e = L ∧ h₂ = 0))
    (hxy : (2 * L - tau Q u L h1 h2 : ℕ) <
      e + (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩) :
    (MC Q u L h1 h2).arcSet ((MC Q u L h1 h2).key Q ⟨6 + tau Q u L h1 h2, h₁⟩)
      ((MC Q u L h1 h2).key Q ⟨2 * L + 6, 0⟩) =
      oset (interiorWalk Q) u ((interiorModel Q).param Q ⟨u, h₁⟩)
        ((2 * L - tau Q u L h1 h2 : ℕ) : ℝ) ∧
    (MC Q u L h1 h2).arcSet ((MC Q u L h1 h2).key Q ⟨6, 0⟩)
      ((MC Q u L h1 h2).key Q ⟨6 + (e - (2 * L - tau Q u L h1 h2)), h₂⟩) =
      oset (interiorWalk Q) u ((2 * L - tau Q u L h1 h2 : ℕ) : ℝ)
        (e + (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩) := by
  set x := (interiorModel Q).param Q ⟨u, h₁⟩ with hxd
  set t₂ := (interiorModel Q).param Q ⟨(u + e) % Q.n, h₂⟩ with ht₂
  set g := 6 + tau Q u L h1 h2 with hg
  set L₁ := 2 * L - tau Q u L h1 h2 with hL₁
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  have hn : (MC Q u L h1 h2).W.n = 2 * L + 7 := cm_n'
  have hge : e ≤ L := by omega
  have hL₁0 : 0 < L₁ := by omega
  have hL₁L : L₁ < L := by omega
  constructor
  · rw [key_eq, key_eq, param_start hu h1 h2, param_zero, add_zero]
    have hg' : g < (MC Q u L h1 h2).W.n := by omega
    have hb0 : (0 : ℝ) ≤ ((2 * L + 6 : ℕ) : ℝ) := by positivity
    have hbn : ((2 * L + 6 : ℕ) : ℝ) < (MC Q u L h1 h2).W.n := by
      rw [hn]; grind
    have hb' : ((2 * L + 6 : ℕ) : ℝ) = (((g + L₁) % (MC Q u L h1 h2).W.n : ℕ) : ℝ) + 0 := by
      rw [add_zero, Nat.mod_eq_of_lt (by omega)]
      congr 1; omega
    show (MC Q u L h1 h2).arcSet ((g : ℝ) + x) ((2 * L + 6 : ℕ) : ℝ) = _
    rw [arcSet_eq_oset _ hg' hx.1 hx.2 hb0 hbn, hb']
    have hL₁r : (1 : ℝ) ≤ L₁ := by exact_mod_cast hL₁0
    have hlap : (L₁ : ℝ) + 0 ≤ x + (MC Q u L h1 h2).W.n := by
      rw [hn]
      have : (L₁ : ℝ) ≤ ((2 * L + 7 : ℕ) : ℝ) := by exact_mod_cast (show L₁ ≤ 2 * L + 7 by omega)
      grind
    rw [len_key (n := (MC Q u L h1 h2).W.n) hg' hx.2 le_rfl (by grind) hlap,
      show x + (L₁ + 0 - x) = L₁ by ring]
    exact (oset_congr (agree_pre hu h1 h2) (by rw [min_eq_right (by omega)])).symm
  · have hA := agree_post hu h1 h2 hs
    rw [key_eq, key_eq, param_zero, param_end_two hu h1 h2 hs hle he, add_zero]
    have h6 : (6 : ℕ) < (MC Q u L h1 h2).W.n := by omega
    have hb0 : (0 : ℝ) ≤ ((6 + (e - L₁) : ℕ) : ℝ) + t₂ := by grind
    have hbn : ((6 + (e - L₁) : ℕ) : ℝ) + t₂ < (MC Q u L h1 h2).W.n := by
      have : ((6 + (e - L₁) : ℕ) : ℝ) + 1 ≤ (MC Q u L h1 h2).W.n := by
        rw [hn]; exact_mod_cast (show 6 + (e - L₁) + 1 ≤ 2 * L + 7 by omega)
      grind
    have ha : (((6 : ℕ) : ℝ)) = ((6 : ℕ) : ℝ) + 0 := by ring
    show (MC Q u L h1 h2).arcSet ((6 : ℕ) : ℝ) (((6 + (e - L₁) : ℕ) : ℝ) + t₂) = _
    rw [ha, arcSet_eq_oset _ h6 le_rfl zero_lt_one hb0 hbn]
    have hmod : (6 + (e - L₁)) % (MC Q u L h1 h2).W.n = 6 + (e - L₁) :=
      Nat.mod_eq_of_lt (by omega)
    have hpos : (0 : ℝ) < (e - L₁ : ℕ) + t₂ := by
      have e1 : ((e - L₁ : ℕ) : ℝ) = e - L₁ := Nat.cast_sub hle
      grind
    have hlap : ((e - L₁ : ℕ) : ℝ) + t₂ ≤ 0 + (MC Q u L h1 h2).W.n := by
      grind
    have hl := len_key (n := (MC Q u L h1 h2).W.n) (u := 6) (e := e - L₁) h6 zero_lt_one hy.1
      hpos hlap
    rw [hmod] at hl
    rw [hl, show (0 : ℝ) + (((e - L₁ : ℕ) : ℝ) + t₂ - 0) = ((e - L₁ : ℕ) : ℝ) + t₂ by ring]
    have hy' : ((e - L₁ : ℕ) : ℝ) + t₂ ≤ ((L - L₁ : ℕ) : ℝ) := by
      rcases he with he | ⟨he, h0⟩
      · have : ((e - L₁ : ℕ) : ℝ) + 1 ≤ ((L - L₁ : ℕ) : ℝ) := by
          exact_mod_cast (show e - L₁ + 1 ≤ L - L₁ by omega)
        grind
      · have : t₂ = 0 := by rw [ht₂, h0]; rfl
        grind
    rw [← oset_congr hA hy', ← oset_shift _ _ L₁ le_rfl]
    congr 1
    · ring
    · have e1 : ((e - L₁ : ℕ) : ℝ) = e - L₁ := Nat.cast_sub hle
      grind

end chainArc

end

end IOrc

end Chazelle.Core
