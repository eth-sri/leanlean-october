module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.OracleMono

/-!
# Lemma 3.6 (WP-H), part 18: the walk positions of a stopping point

The main phase of the query stops the ray at a point `X` of a chain edge `c` (at the height of
the ray) and locates the walk positions of `X`: `wAOf c` on the tour edge running along `c`
forwards, `wBOf c` on the tour edge running backwards, and at the top vertex also the two ends
`6`, `2 m + 6` of the tour (`posOf`).  This file shows that these are proper walk positions with
point `X` (`fwd_pos`, `bwd_pos`), and that every walk key whose point is `X` is one of their
keys (`keys_of_stop`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ
open Chazelle.Visibility (rayPt hseg)
open Chazelle.Chain (sidePt sideE)

@[expose] public section

variable {P : Polygon} {C : Chain} {V : QV}

theorem mod_shift {a b M : ℕ} (hb : b ≤ M) : (b + (a + M - b) % M) % M = a % M := by
  rw [Nat.add_mod_mod, show b + (a + M - b) = a + M by omega, Nat.add_mod_right]

/-- The walk edge `i + 6` runs from the chain vertex `sideE (tj i)` to `sideE (tj i + 1)`. -/
theorem tour_ends {i : ℕ} (hi : i < 2 * C.m) :
    (chainModel C).W.vtx (i + 6) = C.vertex (sideE C.m (tj C i)) ∧
      (chainModel C).W.vtx ((i + 6 + 1) % (chainModel C).W.n) =
        C.vertex (sideE C.m (tj C i + 1)) := by
  refine ⟨?_, ?_⟩
  · show (C.sideWalk C.sideBeta).vtx (i + 6) = _
    rw [C.sideWalk_vtx_tour _ hi.le]; rfl
  · show (C.sideWalk C.sideBeta).vtx ((i + 6 + 1) % (C.sideWalk C.sideBeta).n) = _
    rw [C.sideWalk_next_tour _ hi, C.sideWalk_vtx_tour _ (by omega)]
    unfold Chain.sideTour; rw [C.sideIdx_succ]; rfl

theorem sideE_lo {m j : ℕ} (hj : j ≤ m) : sideE m j = j := by core_grind
theorem sideE_hi {m j : ℕ} (hj : m ≤ j) : sideE m j = 2 * m - j := by
  aesop (add simp [sideE, le_refl, reduceIte]) (add safe (by omega))

/-- The chain vertex `k` is the vertex `(s + k) mod n` of `Q`. -/
theorem vertex_eq (hv : QVOK P C V) (k : ℕ) : C.vertex k = (Qof P).vtx ((V.s + k) % P.n) := by
  unfold Chain.vertex Chain.edgeIdx
  rw [hv.CQ, hv.s, show (Qof P).n = P.n from shear_n _ _]

/-- The walk position facts. -/
def PosFacts (P : Polygon) (C : Chain) (hz w : ℕ) (X : Point) (κ : ℝ) : Prop :=
  w < 2 * C.m + 7 ∧ ProperPos (chainModel C) (Qof P) P.n ⟨w, hz + 1⟩ ∧
    (chainModel C).pos (Qof P) ⟨w, hz + 1⟩ = X ∧ (chainModel C).key (Qof P) ⟨w, hz + 1⟩ = κ

/-- A walk position inside a non-horizontal walk edge. -/
theorem edge_pos {w hz : ℕ} {a b : Point} (ha : (chainModel C).W.vtx w = a)
    (hb : (chainModel C).W.vtx ((w + 1) % (chainModel C).W.n) = b) (hne : a.2 ≠ b.2)
    (ht0 : 0 ≤ (((Qof P).vtx hz).2 - a.2) / (b.2 - a.2))
    (ht1 : (((Qof P).vtx hz).2 - a.2) / (b.2 - a.2) < 1) (hh : hz < P.n) :
    ProperPos (chainModel C) (Qof P) P.n ⟨w, hz + 1⟩ ∧
      (chainModel C).pos (Qof P) ⟨w, hz + 1⟩ =
        Geometry.lerp a b ((((Qof P).vtx hz).2 - a.2) / (b.2 - a.2)) ∧
      (chainModel C).key (Qof P) ⟨w, hz + 1⟩ = w + (((Qof P).vtx hz).2 - a.2) / (b.2 - a.2) := by
  have hp : (chainModel C).param (Qof P) ⟨w, hz + 1⟩ =
      (((Qof P).vtx hz).2 - a.2) / (b.2 - a.2) := by
    unfold Model.param Model.wa Model.wb
    simp only
    rw [ha, hb, ite_eq_right hne]
  refine ⟨⟨by simp_all, by simp_all, by simp_all⟩, ?_, ?_⟩
  · grind [Model.pos, Model.wa, Model.wb]
  grind [Model.key]

/-- A walk position at the start vertex of its walk edge. -/
theorem vertex_pos {w hz : ℕ} {a : Point} (ha : (chainModel C).W.vtx w = a)
    (hy : a.2 = ((Qof P).vtx hz).2) (hh : hz < P.n) :
    ProperPos (chainModel C) (Qof P) P.n ⟨w, hz + 1⟩ ∧
      (chainModel C).pos (Qof P) ⟨w, hz + 1⟩ = a ∧
      (chainModel C).key (Qof P) ⟨w, hz + 1⟩ = w := by
  have hp : (chainModel C).param (Qof P) ⟨w, hz + 1⟩ = 0 := by
    unfold Model.param Model.wa
    simp only
    rw [ha, hy, sub_self, zero_div]; split_ifs <;> rfl
  refine ⟨⟨by rw [hp], by simp_all, by simp_all⟩, ?_, ?_⟩
  all_goals (grind [Model.pos, Model.wa, Geometry.lerp_zero, Model.key])

section
variable (hT : TopOK P C V)
include hT
theorem heights_ne {i j : ℕ} (hi : i < P.n) (hj : j < P.n) :
    ((Qof P).vtx i).2 = ((Qof P).vtx j).2 ↔ i = j := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  constructor
  · intro h; by_contra hne; exact hT.hD i j (by omega) (by omega) hne h
  simp_all

/-- **The walk positions of a point of a chain edge.** -/
theorem fwd_bwd_pos {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 1 ∧
      PosFacts P C V.hz (wAOf V P.n c) X
        (6 + ((c + 2 * C.m - C.sideS C.sideBeta) % (2 * C.m) : ℕ) + τ) ∧
      PosFacts P C V.hz (wBOf V P.n c) X
        (6 + ((2 * C.m - 1 - c + 2 * C.m - C.sideS C.sideBeta) % (2 * C.m) : ℕ) + (1 - τ)) := by
  have hv := hT.hv
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hm1 := C.one_le
  have hmn : C.m < P.n := by have := C.m_lt; rw [hv.CQ, hQn] at this; exact this
  have hn2 : 2 ≤ P.n := by omega
  have hS := C.sideS_lt C.sideBeta
  have hzn := hv.hz_lt
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  set S := C.sideS C.sideBeta with hSdef
  set e := (V.s + c) % P.n with he
  set e1 := (V.s + c + 1) % P.n with he1
  have hen : e < P.n := Nat.mod_lt _ (by omega)
  have he1n : e1 < P.n := Nat.mod_lt _ (by omega)
  have hvc : C.vertex c = (Qof P).vtx e := vertex_eq hv c
  have hvc1 : C.vertex (c + 1) = (Qof P).vtx e1 := by rw [vertex_eq hv]; rfl
  have hee1 : e ≠ e1 := by
    intro h
    have hx := Nat.add_mod (V.s + c) 1 P.n
    rw [Nat.mod_eq_of_lt (show 1 < P.n by omega)] at hx
    
    rw [he, he1, hx] at h
    rcases Nat.lt_or_ge ((V.s + c) % P.n + 1) P.n with h' | h'
    · rw [Nat.mod_eq_of_lt h'] at h; omega
    grind [Nat.mod_self]
  have hne : ((Qof P).vtx e).2 ≠ ((Qof P).vtx e1).2 := fun h =>
    hee1 ((heights_ne hT hen he1n).1 h)
  -- the parameter on the chain edge
  rw [C.chainEdge_eq] at hX
  obtain ⟨τ, hτ0, hτ1, hXe⟩ := hX
  rw [hvc, hvc1] at hXe
  have hXl : X = Geometry.lerp ((Qof P).vtx e) ((Qof P).vtx e1) τ := hXe
  set y := ((Qof P).vtx V.hz).2 with hydef
  have hyτ : y = ((Qof P).vtx e).2 + τ * (((Qof P).vtx e1).2 - ((Qof P).vtx e).2) := by
    simp_all
  have hd : ((Qof P).vtx e1).2 - ((Qof P).vtx e).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hτ : τ = (y - ((Qof P).vtx e).2) / (((Qof P).vtx e1).2 - ((Qof P).vtx e).2) := by
    grind
  have hτ' : 1 - τ = (y - ((Qof P).vtx e1).2) / (((Qof P).vtx e).2 - ((Qof P).vtx e1).2) := by
    grind
  have hy1 : V.hz = e1 ↔ τ = 1 := by
    rw [← heights_ne hT hzn he1n, ← hydef, hyτ]
    constructor
    all_goals grind
  have hy0 : V.hz = e ↔ τ = 0 := by
    rw [← heights_ne hT hzn hen, ← hydef, hyτ]
    constructor
    all_goals grind
  refine ⟨τ, hτ0, hτ1, ?_, ?_⟩
  · -- forwards
    set i := (c + 2 * C.m - S) % (2 * C.m) with hi
    have hi2 : i < 2 * C.m := Nat.mod_lt _ (by omega)
    have htj : tj C i = c := by
      unfold tj; rw [hi, mod_shift hS, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨ea, eb⟩ := tour_ends (C := C) hi2
    simp only [htj, sideE_lo hc.le, sideE_lo (by omega : c + 1 ≤ C.m), hvc, hvc1, hnW,
      Nat.mod_eq_of_lt (by omega : i + 6 + 1 < 2 * C.m + 7)] at ea eb
    have hw : wAOf V P.n c = i + 6 + (if V.hz = e1 then 1 else 0) := by
      unfold wAOf; rw [hv.m, hv.sS]
    by_cases h1 : V.hz = e1
    · 
      rw [hw, ite_eq_left h1]
      obtain ⟨p1, p2, p3⟩ := vertex_pos (C := C) (P := P) (w := i + 6 + 1) (hz := V.hz) eb
        (by rw [h1]) hzn
      refine ⟨by omega, p1, by grind, by grind⟩
    · have ht : τ < 1 := lt_of_le_of_ne hτ1 (fun h => h1 (hy1.2 h))
      rw [hw, ite_eq_right h1, Nat.add_zero]
      obtain ⟨p1, p2, p3⟩ := edge_pos (C := C) (P := P) (w := i + 6) (hz := V.hz) ea
        (by rw [hnW, Nat.mod_eq_of_lt (by omega)]; exact eb) hne (by grind)
        (by grind) hzn
      rw [← hτ] at p2 p3
      refine ⟨by omega, p1, by rw [p2, hXl], by grind⟩
  · -- backwards
    set i := (2 * C.m - 1 - c + 2 * C.m - S) % (2 * C.m) with hi
    have hi2 : i < 2 * C.m := Nat.mod_lt _ (by omega)
    have htj : tj C i = 2 * C.m - 1 - c := by
      unfold tj; rw [hi, mod_shift hS, Nat.mod_eq_of_lt (by omega)]
    obtain ⟨ea, eb⟩ := tour_ends (C := C) hi2
    simp only [htj, sideE_hi (by omega : C.m ≤ 2 * C.m - 1 - c),
      sideE_hi (by omega : C.m ≤ 2 * C.m - 1 - c + 1),
      show 2 * C.m - (2 * C.m - 1 - c) = c + 1 by omega,
      show 2 * C.m - (2 * C.m - 1 - c + 1) = c by omega, hvc, hvc1, hnW,
      Nat.mod_eq_of_lt (by omega : i + 6 + 1 < 2 * C.m + 7)] at ea eb
    have hw : wBOf V P.n c = i + 6 + (if V.hz = e then 1 else 0) := by
      unfold wBOf; rw [hv.m, hv.sS]
    by_cases h0 : V.hz = e
    · 
      rw [hw, ite_eq_left h0]
      obtain ⟨p1, p2, p3⟩ := vertex_pos (C := C) (P := P) (w := i + 6 + 1) (hz := V.hz) eb
        (by rw [h0]) hzn
      refine ⟨by omega, p1, by grind, by grind⟩
    · have ht : 0 < τ := lt_of_le_of_ne hτ0 (fun h => h0 (hy0.2 h.symm))
      rw [hw, ite_eq_right h0, Nat.add_zero]
      obtain ⟨p1, p2, p3⟩ := edge_pos (C := C) (P := P) (w := i + 6) (hz := V.hz) ea
        (by rw [hnW, Nat.mod_eq_of_lt (by omega)]; exact eb) (Ne.symm hne)
        (by grind) (by grind) hzn
      rw [← hτ'] at p2 p3
      refine ⟨by omega, p1, ?_, by grind⟩
      rw [p2, hXl]
      ext <;> simp [Geometry.lerp] <;> ring


end

theorem nat_add_frac_eq {p k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (h : (p : ℝ) + t = k) :
    p = k ∧ t = 0 := by
  have h1 : (p : ℝ) ≤ k := by linarith
  have h2 : (k : ℝ) < p + 1 := by linarith
  have h1' : p ≤ k := by simp_all
  have h2' : k < p + 1 := by exact_mod_cast h2
  grind

/-- The key of a walk position whose point is on the chain is in `[6, 2 m + 6]`. -/
theorem key_range_chain {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt (C.sideWalk C.sideBeta) p t ∈ C.set) :
    (6 : ℝ) ≤ p + t ∧ (p : ℝ) + t ≤ 2 * C.m + 6 := by
  rcases pos_on_chain C hp ht0 ht1 hx with ⟨h1, h2⟩ | ⟨rfl, rfl⟩
  · have a : (6 : ℝ) ≤ p := by simp_all
    have b : (p : ℝ) + 1 ≤ 2 * C.m + 6 := by exact_mod_cast h2
    grind
  simp_all

/-- A walk position with key `6` or `2 m + 6` is the top. -/
theorem top_of_key {p : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h : (p : ℝ) + t = 6 ∨ (p : ℝ) + t = 2 * C.m + 6) :
    sidePt (C.sideWalk C.sideBeta) p t = C.top := by
  rcases h with h | h
  · obtain ⟨rfl, rfl⟩ := nat_add_frac_eq (k := 6) ht0 ht1 (by omega)
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_six]
  · obtain ⟨rfl, rfl⟩ := nat_add_frac_eq (k := 2 * C.m + 6) ht0 ht1 (by rw [h]; simp_all)
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]

section
variable (hT : TopOK P C V)
include hT
/-- **Every walk key of a point of a chain edge** is the key of its forward or backward
position, or (at the top) one of the two ends `6`, `2 m + 6` of the tour. -/
theorem keys_of_stop (hP : C.P.Simple) {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) {p : ℕ} (hp : p < 2 * C.m + 7)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpt : Geometry.lerp ((chainModel C).W.vtx p) ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n))
      t = X) :
    (p : ℝ) + t = (chainModel C).key (Qof P) ⟨wAOf V P.n c, V.hz + 1⟩ ∨
      (p : ℝ) + t = (chainModel C).key (Qof P) ⟨wBOf V P.n c, V.hz + 1⟩ ∨
      (V.hz = V.tv ∧ ((p : ℝ) + t = 6 ∨ (p : ℝ) + t = 2 * C.m + 6)) := by
  have hXs : X ∈ C.set := ⟨c, hc, hX⟩
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  have hS := C.sideS_lt C.sideBeta
  
  have hsp : ∀ q u, sidePt (C.sideWalk C.sideBeta) q u = Geometry.lerp ((chainModel C).W.vtx q)
      ((chainModel C).W.vtx ((q + 1) % (chainModel C).W.n)) u := fun _ _ => rfl
  -- normalise `t = 1`
  obtain ⟨p', t', hp', ht0', ht1', hk, hpt'⟩ : ∃ p' : ℕ, ∃ t' : ℝ, p' < 2 * C.m + 7 ∧ 0 ≤ t' ∧
      t' < 1 ∧ (p' : ℝ) + t' = p + t ∧ sidePt (C.sideWalk C.sideBeta) p' t' = X := by
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · subst h1
      have hv : (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) = X := by
        simp_all
      rw [hnW] at hv
      rcases Nat.lt_or_ge (p + 1) (2 * C.m + 7) with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at hv
        refine ⟨p + 1, 0, h2, le_rfl, one_pos, by simp_all, ?_⟩
        simp_all
      · exfalso
        rw [show p + 1 = 2 * C.m + 7 by omega, Nat.mod_self] at hv
        have := (C.sideWalk_box_pt C.sideBeta (p := 0) (t := 0) (Or.inl (by omega)) le_rfl
          one_pos).1
        simp_all
    · exact ⟨p, t, hp, ht0, h1, rfl, by simp_all⟩
  rw [← hk]
  obtain ⟨τ, hτ0, hτ1, ⟨wa, ⟨pa0, pa1, -⟩, pax, pak⟩, ⟨wb, ⟨pb0, pb1, -⟩, pbx, pbk⟩⟩ :=
    fwd_bwd_pos hT hc hX hy
  set κA := (chainModel C).key (Qof P) ⟨wAOf V P.n c, V.hz + 1⟩
  set κB := (chainModel C).key (Qof P) ⟨wBOf V P.n c, V.hz + 1⟩
  set τA := (chainModel C).param (Qof P) ⟨wAOf V P.n c, V.hz + 1⟩
  set τB := (chainModel C).param (Qof P) ⟨wBOf V P.n c, V.hz + 1⟩
  have hκA : κA = (wAOf V P.n c : ℝ) + τA := rfl
  have hκB : κB = (wBOf V P.n c : ℝ) + τB := rfl
  have hA : sidePt (C.sideWalk C.sideBeta) (wAOf V P.n c) τA = X := pax
  have hB : sidePt (C.sideWalk C.sideBeta) (wBOf V P.n c) τB = X := pbx
  -- the top
  have htop : ∀ q : ℕ, ∀ u : ℝ, 0 ≤ u → u < 1 → sidePt (C.sideWalk C.sideBeta) q u = X →
      ((q : ℝ) + u = 6 ∨ (q : ℝ) + u = 2 * C.m + 6) → V.hz = V.tv := by
    intro q u hu0 hu1 hq hk6
    have e := top_of_key hu0 hu1 hk6
    rw [hq] at e
    rw [← hT.top] at e
    have := congrArg Prod.snd e
    rw [hy] at this
    exact (heights_ne hT hT.hv.hz_lt hT.tv_lt).1 this
  by_cases hA' : (p' : ℝ) + t' = κA
  · grind
  by_cases hB' : (p' : ℝ) + t' = κB
  · grind
  right; right
  have hXA : sidePt (C.sideWalk C.sideBeta) (wAOf V P.n c) τA ∈ C.set := by grind
  rcases mirror_sum C hP wa hp' pa0 pa1 ht0' ht1' hXA (hA.trans hpt'.symm)
      (by grind) with ⟨n1, hn1⟩ | ⟨h6, h26⟩ | ⟨h26, h6⟩
  · -- the mirror of `κA` is `κB`, up to `2 m`
    have hAB : ∃ n2 : ℤ, κA + κB = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * n2 := by
      rw [pak, pbk]
      set iA := (c + 2 * C.m - C.sideS C.sideBeta) % (2 * C.m)
      set iB := (2 * C.m - 1 - c + 2 * C.m - C.sideS C.sideBeta) % (2 * C.m)
      have e1 := Nat.mod_add_div (c + 2 * C.m - C.sideS C.sideBeta) (2 * C.m)
      have e2 := Nat.mod_add_div (2 * C.m - 1 - c + 2 * C.m - C.sideS C.sideBeta) (2 * C.m)
      set qa := (c + 2 * C.m - C.sideS C.sideBeta) / (2 * C.m)
      set qb := (2 * C.m - 1 - c + 2 * C.m - C.sideS C.sideBeta) / (2 * C.m)
      have e1' : iA + 2 * C.m * qa + C.sideS C.sideBeta = c + 2 * C.m := by
        omega
      have e2' : iB + 2 * C.m * qb + C.sideS C.sideBeta + c + 1 = 4 * C.m := by
        omega
      have e1r : (iA : ℝ) + 2 * C.m * qa + C.sideS C.sideBeta = c + 2 * C.m := by
        exact_mod_cast e1'
      have e2r : (iB : ℝ) + 2 * C.m * qb + C.sideS C.sideBeta + c + 1 = 4 * C.m := by
        exact_mod_cast e2'
      refine ⟨3 - qa - qb, ?_⟩
      push_cast; linarith
    obtain ⟨n2, hn2⟩ := hAB
    have hdiff : (p' : ℝ) + t' - κB = 2 * C.m * ((n1 : ℝ) - n2) := by
      grind
    have r1 := key_range_chain hp' ht0' ht1' (by grind)
    have r2 := key_range_chain wb pb0 pb1 (by grind)
    rw [← hκB] at r2
    have hm0 : (0 : ℝ) < C.m := by grind
    have hlt : (n1 : ℝ) - n2 < 2 := by nlinarith
    have hgt : -2 < (n1 : ℝ) - n2 := by nlinarith
    have hne0 : (n1 : ℝ) - n2 ≠ 0 := fun h0 => hB' (by grind)
    have hz1 : (n1 : ℤ) - n2 < 2 := by exact_mod_cast hlt
    have hz2 : -2 < (n1 : ℤ) - n2 := by exact_mod_cast hgt
    have hz3 : (n1 : ℤ) - n2 ≠ 0 := fun h => hne0 (by grind)
    have hk6 : (p' : ℝ) + t' = 6 ∨ (p' : ℝ) + t' = 2 * C.m + 6 := by
      rcases (by omega : (n1 : ℤ) - n2 = 1 ∨ (n1 : ℤ) - n2 = -1) with h | h
      · have h' : (n1 : ℝ) - n2 = 1 := by exact_mod_cast h
        right; rw [h'] at hdiff; linarith
      · have h' : (n1 : ℝ) - n2 = -1 := by exact_mod_cast h
        left; rw [h'] at hdiff; linarith
    exact ⟨htop p' t' ht0' ht1' hpt' hk6, hk6⟩
  · exact ⟨htop p' t' ht0' ht1' hpt' (Or.inr h26), Or.inr h26⟩
  · exact ⟨htop p' t' ht0' ht1' hpt' (Or.inl h6), Or.inl h6⟩

/-- **The walk keys of a point of a side of the box** at a vertex height. -/
theorem keys_of_box {hz : ℕ} (hh : hz < P.n) {X : Point}
    (hy : X.2 = ((Qof P).vtx hz).2) (hX : |X.1| = C.radius) {p : ℕ} (hp : p < 2 * C.m + 7)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hpt : Geometry.lerp ((chainModel C).W.vtx p) ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n))
      t = X) :
    (X.1 = C.radius → (p : ℝ) + t = (chainModel C).key (Qof P) ⟨3, hz + 1⟩) ∧
      (X.1 = -C.radius → (p : ℝ) + t = (chainModel C).key (Qof P) ⟨1, hz + 1⟩) := by
  have hR := C.radius_pos
  have hyR := abs_lt.1 (vtx_snd_lt_radius hT.hv.CQ hh)
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  
  
  have hsp : ∀ q u, sidePt (C.sideWalk C.sideBeta) q u = Geometry.lerp ((chainModel C).W.vtx q)
      ((chainModel C).W.vtx ((q + 1) % (chainModel C).W.n)) u := fun _ _ => rfl
  -- normalise `t = 1`
  obtain ⟨p', t', hp', ht0', ht1', hk, hpt'⟩ : ∃ p' : ℕ, ∃ t' : ℝ, p' < 2 * C.m + 7 ∧ 0 ≤ t' ∧
      t' < 1 ∧ (p' : ℝ) + t' = p + t ∧ sidePt (C.sideWalk C.sideBeta) p' t' = X := by
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · subst h1
      have hv : (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) = X := by
        simp_all
      rw [hnW] at hv
      rcases Nat.lt_or_ge (p + 1) (2 * C.m + 7) with h2 | h2
      · rw [Nat.mod_eq_of_lt h2] at hv
        refine ⟨p + 1, 0, h2, le_rfl, one_pos, by simp_all, ?_⟩
        simp_all
      · exfalso
        rw [show p + 1 = 2 * C.m + 7 by omega, Nat.mod_self] at hv
        have h0 := (C.sidePt_box C.sideBeta 0).1
        simp_all
    · exact ⟨p, t, hp, ht0, h1, rfl, by simp_all⟩
  rw [← hk]
  -- the edge is a side of the box
  have hp3 : p' = 3 ∨ p' = 1 := by
    by_cases hb : p' ≤ 5 ∨ (p' = 2 * C.m + 6 ∧ 0 < t')
    · have := (C.sideWalk_box_pt C.sideBeta hb ht0' ht1').2 (by simp_all)
        (by rw [hpt', hy]; exact abs_lt.2 hyR)
      omega
    · exfalso
      push Not at hb
      have hmem : X ∈ C.set := by
        rcases (by omega : (6 ≤ p' ∧ p' < 2 * C.m + 6) ∨ p' = 2 * C.m + 6) with ⟨h6, h6'⟩ | h6
        · obtain ⟨i, rfl⟩ : ∃ i, p' = i + 6 := ⟨p' - 6, by omega⟩
          rw [← hpt', C.sidePt_tour C.sideBeta (by omega)]
          refine ⟨tci C i, tci_lt C i, ?_⟩
          rw [← tour_seg C i]; exact ⟨t', ht0', ht1'.le, rfl⟩
        · have ht0'' : t' = 0 := by grind
          subst h6 ht0''
          rw [← hpt', Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ le_rfl,
            Chain.sideTour_two_m]
          exact C.top_mem_set
      have := abs_fst_lt_radius_of_mem hmem
      simp_all
  constructor
  · intro hx
    rcases hp3 with rfl | rfl
    · rw [(C.sidePt_box C.sideBeta t').2.2.2.1] at hpt'
      have h2 := congrArg Prod.snd hpt'
      simp only at h2
      rw [key_box_right, hy] at *
      push_cast
      rw [← h2]; field_simp; ring
    · rw [(C.sidePt_box C.sideBeta t').2.1] at hpt'
      grind
  · intro hx
    rcases hp3 with rfl | rfl
    · rw [(C.sidePt_box C.sideBeta t').2.2.2.1] at hpt'
      grind
    · rw [(C.sidePt_box C.sideBeta t').2.1] at hpt'
      grind [key_box_left]


end

/-- The positions of a stopping point are proper, and cover its keys. -/
def StopOK (P : Polygon) (C : Chain) (V : QV) (q : ℕ × ℕ × ℕ × ℕ) (X : Point) : Prop :=
  (∀ k, k < 4 → posK q k < 2 * C.m + 7 ∧ ProperPos (chainModel C) (Qof P) P.n ⟨posK q k, V.hz + 1⟩) ∧
  ∀ p : ℕ, ∀ t : ℝ, p < 2 * C.m + 7 → 0 ≤ t → t ≤ 1 →
    Geometry.lerp ((chainModel C).W.vtx p) ((chainModel C).W.vtx ((p + 1) % (chainModel C).W.n)) t = X →
      ∃ k, k < 4 ∧ (p : ℝ) + t = (chainModel C).key (Qof P) ⟨posK q k, V.hz + 1⟩

section
variable (hT : TopOK P C V)
include hT
/-- **The stopping point on a chain edge.** -/
theorem stop_chain (hP : C.P.Simple) {c : ℕ} (hc : c < C.m) {X : Point}
    (hX : X ∈ C.chainEdge c) (hy : X.2 = ((Qof P).vtx V.hz).2) :
    StopOK P C V (posOf V P.n (0, c)) X := by
  have hv := hT.hv
  obtain ⟨τ, -, -, ⟨wa, pa, -, -⟩, ⟨wb, pb, -, -⟩⟩ := fwd_bwd_pos hT hc hX hy
  have htop : ((Qof P).vtx V.tv).2 = C.top.2 := by rw [hT.top]
  have hW6 : (chainModel C).W.vtx 6 = C.top := C.sideWalk_vtx_six _
  have hWl : (chainModel C).W.vtx (2 * C.m + 6) = C.top := by
    show (C.sideWalk C.sideBeta).vtx (2 * C.m + 6) = _
    rw [C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]
  have v6 : ∀ hz, hz = V.tv → hz < P.n → ProperPos (chainModel C) (Qof P) P.n ⟨6, hz + 1⟩ ∧
      (chainModel C).key (Qof P) ⟨6, hz + 1⟩ = 6 := fun hz e hh => by
    obtain ⟨a, -, b⟩ := vertex_pos (C := C) (P := P) (w := 6) (hz := hz) hW6
      (by rw [e, htop]) hh
    simp_all
  have vl : ∀ hz, hz = V.tv → hz < P.n →
      ProperPos (chainModel C) (Qof P) P.n ⟨2 * C.m + 6, hz + 1⟩ ∧
      (chainModel C).key (Qof P) ⟨2 * C.m + 6, hz + 1⟩ = 2 * C.m + 6 := fun hz e hh => by
    obtain ⟨a, -, b⟩ := vertex_pos (C := C) (P := P) (w := 2 * C.m + 6) (hz := hz) hWl
      (by rw [e, htop]) hh
    simp_all
  have hzn := hv.hz_lt
  refine ⟨fun k hk => ?_, fun p t hp ht0 ht1 hpt => ?_⟩
  · unfold posOf
    simp only [ite_true]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl
    · exact ⟨wa, pa⟩
    · exact ⟨wb, pb⟩
    · grind [posK]
    · show posK (_, _, _, _) 3 < _ ∧ _
      simp only [posK]
      split_ifs with h
      · rw [hv.m]; simp_all
      simp_all
  · rcases keys_of_stop hT hP hc hX hy hp ht0 ht1 hpt with h | h | ⟨he, h | h⟩
    · exact ⟨0, by omega, by unfold posOf; grind [posK]⟩
    · exact ⟨1, by omega, by unfold posOf; grind [posK]⟩
    · refine ⟨2, by omega, ?_⟩
      unfold posOf; simp only [ite_true, posK, ite_eq_left he]
      simp_all
    · refine ⟨3, by omega, ?_⟩
      unfold posOf; simp only [ite_true, posK, ite_eq_left he]
      rw [hv.m, (vl _ he hzn).2]; exact h

/-- **The stopping point on a side of the box.** -/
theorem stop_box {w : ℕ} (hw : w = 1 ∨ w = 3) {X : Point}
    (hX : X = (if w = 3 then C.radius else -C.radius, ((Qof P).vtx V.hz).2)) :
    StopOK P C V (posOf V P.n (1, w)) X := by
  have hv := hT.hv
  have hzn := hv.hz_lt
  have hR := C.radius_pos
  have hyR := abs_lt.1 (vtx_snd_lt_radius hv.CQ hzn)
  have hm1 := C.one_le
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  have hq : ∀ k, posK (posOf V P.n (1, w)) k = w := fun k => by
    unfold posOf; simp only [show ¬ (1 : ℕ) = 0 by omega, ite_false]
    rcases k with _ | _ | _ | _ <;> rfl
  refine ⟨fun k hk => ?_, fun p t hp ht0 ht1 hpt => ?_⟩
  · rw [hq]
    refine ⟨by omega, ?_⟩
    rcases hw with rfl | rfl
    · refine (edge_pos (C := C) (P := P) (w := 1) (hz := V.hz) (a := (-C.radius, C.radius))
        (b := (-C.radius, -C.radius)) (C.sideWalk_vtx_one _)
        (by aesop)
        (by linarith) ?_ ?_ hzn).1
      · simp only; apply div_nonneg_of_nonpos <;> linarith
      · simp only; rw [div_lt_one_of_neg (by linarith)]; linarith
    · refine (edge_pos (C := C) (P := P) (w := 3) (hz := V.hz) (a := (C.radius, -C.radius))
        (b := (C.radius, C.radius)) (C.sideWalk_vtx_three _)
        (by aesop)
        (by linarith) ?_ ?_ hzn).1
      · simp only; apply div_nonneg <;> linarith
      · simp only; rw [div_lt_one (by linarith)]; linarith
  · have hy : X.2 = ((Qof P).vtx V.hz).2 := by rw [hX]
    have hx : |X.1| = C.radius := by
      grind [abs_neg]
    obtain ⟨k3, k1⟩ := keys_of_box hT hzn hy hx hp ht0 ht1 hpt
    refine ⟨0, by omega, ?_⟩
    rw [hq]
    rcases hw with rfl | rfl
    all_goals grind


end

/-- **The near end of a chord on the chain** gives a chain edge through its point. -/
theorem near_stop (hv : QVOK P C V) {w h : ℕ} (hE : EndFacts P C V w h) (h1 : xpClass w = 1) :
    ∃ c, c < C.m ∧ chordSel C V w = (0, c) ∧ (chainModel C).pos (Qof P) ⟨w, h + 1⟩ ∈ C.chainEdge c := by
  obtain ⟨-, hc, -, hw, hp0, hp1⟩ := hE
  have hmem := (hc h1).1
  have hm1 := C.one_le
  have hpos : (chainModel C).pos (Qof P) ⟨w, h + 1⟩ =
      sidePt (C.sideWalk C.sideBeta) w ((chainModel C).param (Qof P) ⟨w, h + 1⟩) := rfl
  rw [hpos] at hmem ⊢
  rcases pos_on_chain C hw hp0 hp1 hmem with ⟨h6, h6'⟩ | ⟨rfl, h0⟩
  · refine ⟨tci C (w - 6), tci_lt C _, ?_, ?_⟩
    · unfold chordSel; rw [ite_eq_left (by rw [hv.m]; omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, w = i + 6 := ⟨w - 6, by omega⟩
      rw [C.sidePt_tour C.sideBeta (by omega), show i + 6 - 6 = i by omega, ← tour_seg C i]
      exact ⟨_, hp0, hp1.le, rfl⟩
  · refine ⟨tci C (2 * C.m - 1), tci_lt C _, ?_, ?_⟩
    · unfold chordSel; rw [ite_eq_right (by rw [hv.m]; omega), ite_eq_left (by rw [hv.m]), hv.m]
    · rw [h0, Chazelle.Chain.sidePt_zero, ← tour_seg C (2 * C.m - 1),
        C.sideWalk_vtx_tour _ le_rfl, show 2 * C.m - 1 + 1 = 2 * C.m by omega]
      exact ⟨1, zero_le_one, le_rfl, by simp⟩

end

end OracleR

end Chazelle.Core
