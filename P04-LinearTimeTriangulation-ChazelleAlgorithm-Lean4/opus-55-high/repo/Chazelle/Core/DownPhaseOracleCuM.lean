module

public import Chazelle.Core.DownPhaseOracleQPlan

/-!
# WP-M (E7-B, part 13): translating chain-model positions along a stretch

The interior cutter calls the chain cutter on a chain arc of the chain `C = ch Q u L` of a
subarc.  The arc lies in a **stretch** (`Stretch`) where the interior walk of `Q`, read from its
vertex `u₀`, agrees with the walk of `chainModel C`, read from its vertex `g₀` (`ℓ` steps, inside
the double boundary).  A position `x` of the chain walk with key in `[g₀, g₀ + ℓ]` is translated to
the interior position `trP x = ⟨(u₀ + (x.edge - g₀)) mod n, x.hgt⟩` (`trP_spec`): it is proper, has
the same parameter and the same point.  Arcs between two such positions have the same point set
and the same weight in both models (`trP_arc`).

* `cm_nh`: the walk edges `6 … 2m + 6` of a chain model are not horizontal.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

/-! ## The double boundary is not horizontal -/

/-- **The walk edges `6 … 2m + 6` of a chain model are not horizontal.** -/
theorem cm_nh {C : Chain} (hD : DistinctHeights C.P) {e : ℕ} (h6 : 6 ≤ e)
    (he : e ≤ 2 * C.m + 6) : ((chainModel C).wa e).2 ≠ ((chainModel C).wb e).2 := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hm := C.one_le
  rcases he.lt_or_eq with he | rfl
  · have hwa : (chainModel C).wa e = C.P.vtx (cVtx C e) := cm_vtx_tour C h6 he.le
    have hwb : (chainModel C).wb e = C.P.vtx (cVtx C (e + 1)) := by
      unfold Model.wb; rw [hn, Nat.mod_eq_of_lt (by omega)]
      exact cm_vtx_tour C (by omega) (by omega)
    have hstep := C.sideTour_step C.sideBeta (e - 6)
    have hk1 := C.sideIdx_le C.sideBeta (e - 6)
    have hk2 := C.sideIdx_le C.sideBeta (e - 6 + 1)
    have e7 : e + 1 - 6 = e - 6 + 1 := by omega
    have hne : cVtx C e ≠ cVtx C (e + 1) := by
      unfold cVtx
      rw [e7]
      intro hc
      have := C.sideEdgeIdx_inj (j := C.sideIdx C.sideBeta (e - 6))
        (k := C.sideIdx C.sideBeta (e - 6 + 1)) hk1 hk2 hc
      rcases hstep with h1 | h1 <;> omega
    rw [hwa, hwb]
    exact hD _ _ (cVtx_lt C e) (cVtx_lt C (e + 1)) hne
  · have hwa : (chainModel C).wa (2 * C.m + 6) = C.top := by
      unfold Model.wa
      rw [cm_vtx_tour C (by omega) le_rfl]
      unfold cVtx
      rw [show 2 * C.m + 6 - 6 = 2 * C.m by omega, C.sideIdx_two_m]; rfl
    have hwb : (chainModel C).wb (2 * C.m + 6) = C.slitTop := by
      unfold Model.wb; rw [hn, show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]; rfl
    rw [hwa, hwb]
    have := C.top_snd_lt_radius
    simp only [Chain.slitTop]
    exact this.ne

/-! ## Stretches -/

/-- **A stretch** of the interior walk of `Q` from its vertex `u₀` agreeing with the walk of the
chain model of `C` from its vertex `g₀`, for `ℓ` steps inside the double boundary. -/
structure Stretch (Q : Polygon) (C : Chain) (u₀ g₀ ℓ : ℕ) : Prop where
  hu : u₀ < Q.n
  h6 : 6 ≤ g₀
  hend : g₀ + ℓ ≤ 2 * C.m + 6
  hCP : C.P = Q
  hD : DistinctHeights Q
  hn : 3 ≤ Q.n
  hℓ : ℓ < Q.n
  agree : WalkEmbed.Agree (interiorWalk Q) (chainModel C).W u₀ g₀ ℓ

/-- **The translation** of a chain-model position. -/
def trP (n u₀ g₀ : ℕ) (x : WPos) : WPos := ⟨(u₀ + (x.edge - g₀)) % n, x.hgt⟩

section

variable {Q : Polygon} {C : Chain} {u₀ g₀ ℓ : ℕ} (S : Stretch Q C u₀ g₀ ℓ)

include S in
omit S in
theorem str_cmn (_S : Stretch Q C u₀ g₀ ℓ) : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C

include S in
omit S in
/-- The edge of a proper position with key in the stretch. -/
theorem str_edge (_S : Stretch Q C u₀ g₀ ℓ) {x : WPos} (hx : ProperPos (chainModel C) Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    g₀ ≤ x.edge ∧ x.edge ≤ g₀ + ℓ ∧ (x.edge < g₀ + ℓ ∨ (chainModel C).param Q x = 0) := by
  have hp0 := hx.1
  have hp1 := hx.2.1
  rw [key_eq] at hk0 hk1
  have a1 : (g₀ : ℝ) < x.edge + 1 := by linarith
  have a2 : (x.edge : ℝ) ≤ g₀ + ℓ := by linarith
  have b1 : g₀ < x.edge + 1 := by exact_mod_cast a1
  have b2 : x.edge ≤ g₀ + ℓ := by exact_mod_cast a2
  refine ⟨by omega, b2, ?_⟩
  rcases b2.lt_or_eq with h | h
  · exact Or.inl h
  · right
    have : (x.edge : ℝ) = g₀ + ℓ := by exact_mod_cast h
    linarith

include S in
/-- **The translated position** has the same parameter, is proper, and has the same point. -/
theorem trP_spec {x : WPos} (hx : ProperPos (chainModel C) Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    (interiorModel Q).param Q (trP Q.n u₀ g₀ x) = (chainModel C).param Q x ∧
      ProperPos (interiorModel Q) Q Q.n (trP Q.n u₀ g₀ x) ∧ (trP Q.n u₀ g₀ x).edge < Q.n ∧
      (interiorModel Q).pos Q (trP Q.n u₀ g₀ x) = (chainModel C).pos Q x := by
  obtain ⟨hg1, hg2, hlt⟩ := str_edge S hx hk0 hk1
  have hcm := str_cmn S
  have hmi : (interiorModel Q).W.n = Q.n := mi_n
  have hend := S.hend
  have h6 := S.h6
  set d := x.edge - g₀ with hd
  have hxe : x.edge = g₀ + d := by omega
  have hxe' : x.edge = (g₀ + d) % (chainModel C).W.n := by
    rw [hcm, Nat.mod_eq_of_lt (by omega)]; omega
  have htr : trP Q.n u₀ g₀ x = ⟨(u₀ + d) % (interiorModel Q).W.n, x.hgt⟩ := by
    unfold trP; rw [hmi]
  have hedge : (trP Q.n u₀ g₀ x).edge < Q.n := by
    unfold trP; exact Nat.mod_lt _ (by have := S.hn; omega)
  -- the parameter
  have hpar : (interiorModel Q).param Q (trP Q.n u₀ g₀ x) = (chainModel C).param Q x := by
    rcases hlt with hlt | hpz
    · have := param_agree (M := interiorModel Q) (M' := chainModel C) S.agree Q (d := d)
        (by omega) x.hgt
      rw [htr, this, ← hxe']
    · rw [hpz]
      -- the end of the stretch: both parameters vanish
      rcases Nat.eq_zero_or_pos x.hgt with h0 | h0
      · rw [htr]; show (interiorModel Q).param Q ⟨_, x.hgt⟩ = 0; rw [h0]; rfl
      obtain ⟨h', hh⟩ : ∃ h', x.hgt = h' + 1 := ⟨x.hgt - 1, by omega⟩
      have hDC : DistinctHeights C.P := by rw [S.hCP]; exact S.hD
      have hnh := cm_nh hDC (e := x.edge) (by omega) (by omega)
      have hy : (Q.vtx h').2 = ((chainModel C).wa x.edge).2 := by
        have hp := hpz
        unfold Model.param at hp
        rw [hh] at hp
        simp only at hp
        rw [ite_eq_right hnh, div_eq_zero_iff] at hp
        rcases hp with hp | hp
        · linarith
        · exact absurd (by linarith) hnh
      have hva : (interiorModel Q).wa ((u₀ + d) % (interiorModel Q).W.n) =
          (chainModel C).wa x.edge := by
        unfold Model.wa
        exact (S.agree d (by omega)).trans (congrArg _ hxe'.symm)
      rw [htr]
      unfold Model.param
      simp only [hh]
      split_ifs with hz
      · rfl
      · rw [hva, ← hy, sub_self, zero_div]
  refine ⟨hpar, ⟨by rw [hpar]; exact hx.1, by rw [hpar]; exact hx.2.1, hx.2.2⟩, hedge, ?_⟩
  -- the point
  rcases hlt with hlt | hpz
  · have := pos_agree (M := interiorModel Q) (M' := chainModel C) S.agree Q (d := d)
      (by omega) x.hgt
    rw [htr, this, ← hxe']
  · unfold Model.pos
    rw [hpar, hpz, lerp_zero, lerp_zero, htr]
    unfold Model.wa
    exact (S.agree d (by omega)).trans (congrArg _ hxe'.symm)

include S in
/-- The interior key of a translated position. -/
theorem trP_key {x : WPos} (hx : ProperPos (chainModel C) Q Q.n x)
    (hk0 : (g₀ : ℝ) ≤ (chainModel C).key Q x) (hk1 : (chainModel C).key Q x ≤ g₀ + ℓ) :
    (interiorModel Q).key Q (trP Q.n u₀ g₀ x) =
      (((u₀ + (x.edge - g₀)) % Q.n : ℕ) : ℝ) + (chainModel C).param Q x := by
  rw [key_eq, (trP_spec S hx hk0 hk1).1]; rfl

include S in
/-- **Arcs between translated positions** have the same point set and weight. -/
theorem trP_arc {x y : WPos} (hx : ProperPos (chainModel C) Q Q.n x)
    (hy : ProperPos (chainModel C) Q Q.n y) (hx0 : (g₀ : ℝ) ≤ (chainModel C).key Q x)
    (hy1 : (chainModel C).key Q y ≤ g₀ + ℓ)
    (hxy : (chainModel C).key Q x < (chainModel C).key Q y) :
    (interiorModel Q).arcSet ((interiorModel Q).key Q (trP Q.n u₀ g₀ x))
        ((interiorModel Q).key Q (trP Q.n u₀ g₀ y)) =
      (chainModel C).arcSet ((chainModel C).key Q x) ((chainModel C).key Q y) ∧
    (interiorModel Q).arcWt ((interiorModel Q).key Q (trP Q.n u₀ g₀ x))
        ((interiorModel Q).key Q (trP Q.n u₀ g₀ y)) =
      (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) := by
  have hx1 : (chainModel C).key Q x ≤ g₀ + ℓ := hxy.le.trans hy1
  have hy0 : (g₀ : ℝ) ≤ (chainModel C).key Q y := hx0.trans hxy.le
  obtain ⟨gx1, gx2, -⟩ := str_edge S hx hx0 hx1
  obtain ⟨gy1, gy2, gy3⟩ := str_edge S hy hy0 hy1
  have hcm := str_cmn S
  have hmi : (interiorModel Q).W.n = Q.n := mi_n
  have hiw : (interiorWalk Q).n = Q.n := Trans.iw_n
  have hend := S.hend
  have h6 := S.h6
  have hℓ := S.hℓ
  have hn := S.hn
  have hu := S.hu
  rw [trP_key S hx hx0 hx1, trP_key S hy hy0 hy1]
  set tx := (chainModel C).param Q x with htx
  set ty := (chainModel C).param Q y with hty
  have tx0 := hx.1
  have tx1 := hx.2.1
  have ty0 := hy.1
  have ty1 := hy.2.1
  simp only [key_eq] at hxy hx0 hy1 ⊢
  set dx := x.edge - g₀ with hdx
  set dy := y.edge - g₀ with hdy
  have hxe : x.edge = g₀ + dx := by omega
  have hye : y.edge = g₀ + dy := by omega
  have hdxy : dx ≤ dy := by
    have : (x.edge : ℝ) < y.edge + 1 := by linarith
    have : x.edge < y.edge + 1 := by exact_mod_cast this
    omega
  set e := dy - dx with he
  have hye' : y.edge = x.edge + e := by omega
  have hxyr : tx < (e : ℝ) + ty := by
    have : (e : ℝ) = (y.edge : ℝ) - x.edge := by rw [hye']; push_cast; ring
    rw [this]; linarith
  have hey : (e : ℝ) + ty ≤ ℓ - dx := by
    have h1 : (y.edge : ℝ) + ty ≤ g₀ + ℓ := hy1
    have : (e : ℝ) = (y.edge : ℝ) - x.edge := by rw [hye']; push_cast; ring
    have : (x.edge : ℝ) = g₀ + dx := by exact_mod_cast hxe
    linarith
  have hdyℓ : dy ≤ ℓ := by omega
  have hmod : ((u₀ + dx) % Q.n + e) % Q.n = (u₀ + dy) % Q.n := by
    rw [Nat.mod_add_mod, show u₀ + dx + e = u₀ + dy by omega]
  have hmodc : (x.edge + e) % (chainModel C).W.n = y.edge := by
    rw [← hye', hcm, Nat.mod_eq_of_lt (by omega)]
  have hen : (e : ℝ) + ty ≤ tx + Q.n := by
    have : (ℓ : ℝ) < Q.n := by exact_mod_cast hℓ
    have : (0 : ℝ) ≤ dx := Nat.cast_nonneg _
    linarith
  have hu' : (u₀ + dx) % Q.n < (interiorModel Q).W.n := by rw [hmi]; exact Nat.mod_lt _ (by omega)
  have hxe2 : x.edge < (chainModel C).W.n := by rw [hcm]; omega
  constructor
  · -- the point sets
    have hb0 : (0 : ℝ) ≤ (((u₀ + dy) % Q.n : ℕ) : ℝ) + ty := by positivity
    have hbn : (((u₀ + dy) % Q.n : ℕ) : ℝ) + ty < (interiorModel Q).W.n := by
      have : (u₀ + dy) % Q.n + 1 ≤ Q.n := Nat.mod_lt _ (by omega)
      have : (((u₀ + dy) % Q.n : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast this
      rw [hmi]; linarith
    rw [arcSet_eq_oset _ hu' tx0 tx1 hb0 hbn, hmi, ← hmod,
      len_key (Nat.mod_lt _ (by omega)) tx1 ty0 hxyr hen]
    have hb0' : (0 : ℝ) ≤ (y.edge : ℝ) + ty := by positivity
    have hbn' : (y.edge : ℝ) + ty < (chainModel C).W.n := by
      have : (y.edge : ℝ) + 1 ≤ (chainModel C).W.n := by
        rw [hcm]; exact_mod_cast (show y.edge + 1 ≤ 2 * C.m + 7 by omega)
      linarith
    rw [arcSet_eq_oset _ hxe2 tx0 tx1 hb0' hbn']
    have hlap' : (e : ℝ) + ty ≤ tx + (chainModel C).W.n := by
      rw [hcm]; push_cast
      have : (ℓ : ℝ) < Q.n := by exact_mod_cast hℓ
      have : (e : ℝ) ≤ ℓ := by exact_mod_cast (show e ≤ ℓ by omega)
      have : (1 : ℝ) ≤ 2 * C.m + 7 - ℓ := by
        have : ℓ + 1 ≤ 2 * C.m + 7 := by omega
        have : ((ℓ + 1 : ℕ) : ℝ) ≤ ((2 * C.m + 7 : ℕ) : ℝ) := by exact_mod_cast this
        push_cast at this; linarith
      linarith
    have hl2 := len_key (n := (chainModel C).W.n) hxe2 tx1 ty0 hxyr hlap'
    rw [hmodc] at hl2
    rw [hl2]
    have e1 : oset (interiorModel Q).W ((u₀ + dx) % Q.n) = oset (interiorWalk Q) (u₀ + dx) := by
      funext a b
      show oset (interiorWalk Q) ((u₀ + dx) % Q.n) a b = _
      rw [← hiw]; exact oset_mod _ _ _ _
    rw [e1, hxe, ← oset_shift _ _ _ tx0, ← oset_shift _ _ _ tx0]
    exact oset_congr S.agree (by
      have : (dx : ℝ) + (tx + (e + ty - tx)) = dy + ty := by
        rw [he, Nat.cast_sub hdxy]; ring
      rw [this]
      have : (y.edge : ℝ) = g₀ + dy := by exact_mod_cast hye
      linarith)
  · -- the weights
    have hci : ∀ p, p < (interiorModel Q).W.n →
        ((interiorModel Q).counted p ↔ 0 ≤ p ∧ p < (interiorModel Q).W.n) := fun p hp => by
      rw [hmi] at hp ⊢; exact interiorModel_counted_iff Q p (by rw [hmi]; exact hp)
    have hkc : keyCeil e ty ≤ e + 1 := keyCeil_le_succ
    have hkc' : keyCeil e ty = e ∨ (keyCeil e ty = e + 1 ∧ 0 < ty) := by
      unfold keyCeil; split_ifs with h
      · left; rfl
      · right; exact ⟨rfl, lt_of_le_of_ne ty0 (Ne.symm h)⟩
    have w1 := arcWt_off (interiorModel Q) (lo := 0) (hi := (interiorModel Q).W.n) hci le_rfl
      hu' (Nat.zero_le _) tx0 tx1 ty0 ty1 hxyr (Or.inl ⟨rfl, rfl, by
        rw [hmi]; exact le_trans hkc (by omega)⟩)
    rw [hmi, hmod] at w1
    have hcc : ∀ p, p < (chainModel C).W.n →
        ((chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) := chain_counted C
    have w2 := arcWt_off (chainModel C) (lo := 6) (hi := 2 * C.m + 6) hcc (by rw [hcm]; omega)
      hxe2 (by omega) tx0 tx1 ty0 ty1 hxyr (Or.inr ⟨by
        show x.edge + keyCeil e ty ≤ 2 * C.m + 6
        rcases hkc' with h | ⟨h, hpos⟩
        · omega
        · rcases gy3 with g | g
          · omega
          · exact absurd g hpos.ne', by rw [hcm]; omega⟩)
    rw [hmodc] at w2
    rw [w1, w2]


include S in
/-- **The interior walk agrees with the chain walk** at the translated position. -/
theorem trP_agree {x : WPos} (hx : g₀ ≤ x.edge) {a L' : ℕ} (h : x.edge - g₀ + a + L' ≤ ℓ) :
    WalkAgree (interiorModel Q).W (chainModel C).W (((trP Q.n u₀ g₀ x).edge + a) % Q.n)
      ((x.edge + a) % (chainModel C).W.n) L' := by
  intro d hd
  have hmi : (interiorModel Q).W.n = Q.n := mi_n
  have hcm := str_cmn S
  have hend := S.hend
  have := S.agree (x.edge - g₀ + a + d) (by omega)
  have e1 : (((trP Q.n u₀ g₀ x).edge + a) % Q.n + d) % Q.n =
      (u₀ + (x.edge - g₀ + a + d)) % Q.n := by
    unfold trP; simp only
    rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod]; congr 1; omega
  have e2 : ((x.edge + a) % (chainModel C).W.n + d) % (chainModel C).W.n =
      (g₀ + (x.edge - g₀ + a + d)) % (chainModel C).W.n := by
    rw [Nat.mod_add_mod]; congr 1; omega
  have hiw : (interiorWalk Q).n = Q.n := Trans.iw_n
  rw [hiw] at this
  rw [hmi, e1, e2]
  exact this

theorem walkAgree_trans {A B C' : Polygon} {a b c L : ℕ} (h₁ : WalkAgree A B a b L)
    (h₂ : WalkAgree B C' (b % B.n) c L) : WalkAgree A C' a c L := fun d hd => by
  rw [h₁ d hd, ← h₂ d hd, Nat.mod_add_mod]

include S in
/-- **The chain weight of an arc in the stretch** between two vertex positions. -/
theorem str_wt0 {x y : WPos} (hx : x.hgt = 0) (hy : y.hgt = 0) (hxy : x.edge < y.edge)
    (hx0 : g₀ ≤ x.edge) (hy1 : y.edge ≤ g₀ + ℓ) :
    (chainModel C).arcWt ((chainModel C).key Q x) ((chainModel C).key Q y) = y.edge - x.edge := by
  have hcm := str_cmn S
  have hend := S.hend
  have h6 := S.h6
  have hcc : ∀ p, p < (chainModel C).W.n →
      ((chainModel C).counted p ↔ 6 ≤ p ∧ p < 2 * C.m + 6) := chain_counted C
  have hxe2 : x.edge < (chainModel C).W.n := by rw [hcm]; omega
  have kx : (chainModel C).key Q x = (x.edge : ℝ) + 0 := by
    rw [key_eq]; congr 1; show (chainModel C).param Q ⟨x.edge, x.hgt⟩ = 0; rw [hx]; rfl
  have ky : (chainModel C).key Q y = (((x.edge + (y.edge - x.edge)) % (chainModel C).W.n : ℕ) : ℝ) + 0 := by
    rw [key_eq, show x.edge + (y.edge - x.edge) = y.edge by omega,
      Nat.mod_eq_of_lt (by rw [hcm]; omega)]
    congr 1; show (chainModel C).param Q ⟨y.edge, y.hgt⟩ = 0; rw [hy]; rfl
  rw [kx, ky]
  have hk : keyCeil (y.edge - x.edge) (0 : ℝ) = y.edge - x.edge := by unfold keyCeil; rw [ite_eq_left rfl]
  rw [arcWt_off (chainModel C) (lo := 6) (hi := 2 * C.m + 6) hcc (by rw [hcm]; omega) hxe2
    (by omega) le_rfl zero_lt_one le_rfl zero_lt_one
    (by have : (1 : ℝ) ≤ ((y.edge - x.edge : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ y.edge - x.edge by omega)
        linarith) (Or.inr ⟨by rw [hk]; omega, by rw [hcm]; omega⟩), hk]

include S in
/-- **`PieceWalk` along the stretch**: a kind-1 piece of the chain cutter inside the stretch is a
piece of the interior walk, its chain visited along the same vertices. -/
theorem trP_pieceWalk {s e : WPos} {Cα : Chain} (hpw : PieceWalk (chainModel C) Cα s e)
    (hwt : (chainModel C).arcWt ((chainModel C).key Q s) ((chainModel C).key Q e) = Cα.m)
    (hse : (chainModel C).key Q s < (chainModel C).key Q e)
    (hs0 : (g₀ : ℝ) ≤ (chainModel C).key Q s) (he1 : (chainModel C).key Q e ≤ g₀ + ℓ)
    (hvl : (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ((s.edge + d) % (chainModel C).W.n) =
        Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → (chainModel C).W.vtx ((s.edge + d) % (chainModel C).W.n) =
        Cα.vertex (Cα.m - d))) :
    PieceWalk (interiorModel Q) Cα (trP Q.n u₀ g₀ s) (trP Q.n u₀ g₀ e) ∧
      ((∀ d, d ≤ Cα.m → (interiorModel Q).W.vtx (((trP Q.n u₀ g₀ s).edge + d) %
          (interiorModel Q).W.n) = Cα.vertex d) ∨
        (∀ d, d ≤ Cα.m → (interiorModel Q).W.vtx (((trP Q.n u₀ g₀ s).edge + d) %
          (interiorModel Q).W.n) = Cα.vertex (Cα.m - d))) := by
  obtain ⟨hs, he, hsn, hee, g', hg', hw⟩ := hpw
  have hcm := str_cmn S
  have hmi : (interiorModel Q).W.n = Q.n := mi_n
  have hend := S.hend
  have hn := S.hn
  have ks : (chainModel C).key Q s = s.edge := by
    rw [key_eq, show (chainModel C).param Q s = 0 by
      show (chainModel C).param Q ⟨s.edge, s.hgt⟩ = 0; rw [hs]; rfl, add_zero]
  have ke : (chainModel C).key Q e = e.edge := by
    rw [key_eq, show (chainModel C).param Q e = 0 by
      show (chainModel C).param Q ⟨e.edge, e.hgt⟩ = 0; rw [he]; rfl, add_zero]
  rw [ks, ke] at hse
  rw [ks] at hs0
  rw [ke] at he1
  have hs0' : g₀ ≤ s.edge := by exact_mod_cast hs0
  have he1' : e.edge ≤ g₀ + ℓ := by exact_mod_cast he1
  have hse' : s.edge < e.edge := by exact_mod_cast hse
  have hm : Cα.m = e.edge - s.edge := by rw [← hwt, str_wt0 S hs he hse' hs0' he1']
  have hdiff : s.edge + Cα.m = e.edge := by omega
  have hA := trP_agree S hs0' (a := 0) (L' := Cα.m) (by omega)
  simp only [Nat.add_zero] at hA
  have hsl : s.edge % (chainModel C).W.n = s.edge := Nat.mod_eq_of_lt hsn
  have hts : (trP Q.n u₀ g₀ s).edge < Q.n := by unfold trP; exact Nat.mod_lt _ (by omega)
  have htsmod : (trP Q.n u₀ g₀ s).edge % Q.n = (trP Q.n u₀ g₀ s).edge := Nat.mod_eq_of_lt hts
  rw [htsmod, hsl] at hA
  have hte : (trP Q.n u₀ g₀ e).edge = ((trP Q.n u₀ g₀ s).edge + Cα.m) % (interiorModel Q).W.n := by
    unfold trP; simp only
    rw [hmi, Nat.mod_add_mod, ← hdiff, show u₀ + (s.edge - g₀) + Cα.m = u₀ + (s.edge + Cα.m - g₀) by
      omega]
  refine ⟨⟨hs, he, by rw [hmi]; exact hts, hte, g', hg', ?_⟩, ?_⟩
  · rcases hw with hw | ⟨L₁, h1, h2, h3, hw1, hw2⟩
    · exact Or.inl (walkAgree_trans hA (by rw [hsl]; exact hw))
    · refine Or.inr ⟨L₁, h1, h2, h3, walkAgree_trans (L := L₁)
        (fun d hd => hA d (by omega)) (by rw [hsl]; exact hw1), ?_⟩
      have hB := trP_agree S hs0' (a := L₁) (L' := Cα.m - L₁) (by omega)
      rw [hmi]
      refine walkAgree_trans hB ?_
      rw [Nat.mod_mod]
      exact hw2
  · rcases hvl with hv | hv
    · left; intro d hd; rw [hA d hd]; exact hv d hd
    · right; intro d hd; rw [hA d hd]; exact hv d hd

end

end

end IOrc

end Chazelle.Core
