module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoHoleChain
public import Chazelle.Core.RestoreTNear

/-!
# The sweep RAM (WP-D), answers: the holes of a walk position (copied from WP-E, renumbered)

`chainH_exec`: the holes computed by `chainH` (registers `241309 … 241315`, the hole registers of
the shot block `R = 241300`) are pairs of distinct walk vertices that cover the point of the
position (`Restore.Cover`) and are near it (`Restore.Near`).
-/

namespace Chazelle.Core

namespace SweepIo

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE sidePt)
open Restore (Cover Near eHole vHole prevV cover_chain_vertex cover_chain_edge near_eHole
  near_vHole key_hole eHole_mem vHole_mem)

variable {P : Polygon} {W : ℕ}

/-- **Where the candidate of a chain model lies**: at a tour vertex, or inside a tour edge. -/
theorem chain_x_cases {C : Chain} {Q : Polygon} {n : ℕ} {x : WPos}
    (hx : ProperPos (chainModel C) Q n x) (he : x.edge < (chainModel C).W.n)
    (hxc : x.hgt = 0 ∨ 0 < (chainModel C).param Q x) (hz : (chainModel C).pos Q x ∈ C.set) :
    6 ≤ x.edge ∧
      (x.hgt = 0 → x.edge - 6 ≤ 2 * C.m ∧
        (chainModel C).pos Q x = C.vertex (C.sideIdx C.sideBeta (x.edge - 6))) ∧
      (0 < x.hgt → x.edge - 6 < 2 * C.m ∧ 0 < (chainModel C).param Q x ∧
        (chainModel C).param Q x < 1) := by
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  have hpos : (chainModel C).pos Q x = sidePt (C.sideWalk C.sideBeta) x.edge
      ((chainModel C).param Q x) := rfl
  rw [hpos] at hz
  rw [hW] at he
  rcases C.sideWalk_pos_cases C.sideBeta he hx.1 with hbox | ⟨i, hi, hie, hit⟩
  · exact absurd hz (C.sideWalk_box_pt C.sideBeta hbox hx.1 hx.2.1).1
  refine ⟨by omega, fun h0 => ⟨by omega, ?_⟩, fun hh => ⟨?_, ?_, hx.2.1⟩⟩
  · have hp0 : (chainModel C).param Q x = 0 := by
      obtain ⟨e, h⟩ := x; aesop
    rw [hpos, hp0, Chazelle.Chain.sidePt_zero, hie, C.sideWalk_vtx_tour _ hi]
    aesop
  all_goals grind

/-! ## The holes as a list -/

theorem holeList_one (c : Config) (h : c.nreg 241309 = 1) :
    ShotList.holeList c 241300 = [ShotList.holeAt c 241300 0] := by
  core_grind

/-! ## The contract -/

/-- **The holes in the registers** `241309 … 241315` are proper and cover the point `z`. -/
def HoleOut (M : Model) (Q : Polygon) (c : Config) (z : Point) : Prop :=
  c.nreg 241309 ≤ 3 ∧
    (∀ j < c.nreg 241309, c.nreg (241300 + 10 + 2 * j) < M.W.n ∧
      c.nreg (241300 + 11 + 2 * j) < M.W.n ∧ c.nreg (241300 + 10 + 2 * j) ≠ c.nreg (241300 + 11 + 2 * j)) ∧
    Cover M Q (ShotList.holeList c 241300) z ∧ Near M Q (ShotList.holeList c 241300) z

/-- The scratch registers of `holeS`. -/
def holeL : List ℕ := chainHL ++ [243092, 243093]

theorem holeAt_eq (c : Config) (j : ℕ) :
    ShotList.holeAt c 241300 j = (⟨c.nreg (241300 + 10 + 2 * j), 0⟩, ⟨c.nreg (241300 + 11 + 2 * j), 0⟩) :=
  rfl

/-! ## Hole arithmetic -/

theorem hole_mem {c : Config} {j : ℕ} (hj : j < c.nreg 241309) (h3 : c.nreg 241309 ≤ 3) :
    ShotList.holeAt c 241300 j ∈ ShotList.holeList c 241300 :=
  List.mem_map.2 ⟨j, List.mem_range.2 (by simp_all), rfl⟩

theorem vHole_six {n c : ℕ} (h : c + 6 < n) : vHole n (c + 6) = (⟨c + 5, 0⟩, ⟨(c + 7) % n, 0⟩) := by
  unfold vHole prevV
  rw [show c + 6 + n - 1 = (c + 5) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem vtx_hole_ne {m c : ℕ} (hc : c ≤ 2 * m) : c + 5 ≠ (c + 7) % (2 * m + 7) := by
  rcases Nat.lt_or_ge (c + 7) (2 * m + 7) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  grind [Nat.mod_self]

theorem sOf_sideS {C : Chain} {b : ℕ} (hb : b = 1 ↔ C.sideBeta = true) :
    sOf C.m C.topIdx b = C.sideS C.sideBeta := by
  simp_all [sOf, Chain.sideS] 

set_option maxHeartbeats 1600000 in
/-- **The holes of a position in a chain model** (`chainH`): pairs of distinct walk vertices
covering its point, near it; only the scratch registers `holeL` change.  The position
`x = (243005, 243006)` is normalised (height code `0` exactly at a walk vertex) and its point lies
on the chain; `243020` holds the address of the chain descriptor, `243022 = 0`, `243023 = 1`. -/
theorem chainH_exec {c : Config} (hw : WordsBounded W c) {H : Host} {C : Chain}
    (hC : ChainDescAt c.nmem (c.nreg 243020) (Qof P) H C)
    (hwf : c.nreg 243020 + 5 ≤ c.nreg ALLOC) (hsimp : C.P.Simple) (hWm : 2 * C.m + 7 ≤ W)
    (h22 : c.nreg 243022 = 0) (h23 : c.nreg 243023 = 1)
    (hxp : ProperPos (chainModel C) (Qof P) P.n ⟨c.nreg 243005, c.nreg 243006⟩)
    (hxe : c.nreg 243005 < (chainModel C).W.n)
    (hxc : c.nreg 243006 = 0 ∨ 0 < (chainModel C).param (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩)
    (hxC : (chainModel C).pos (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩ ∈ C.set) :
    ∃ c' k, Exec P W chainH c c' k ∧ k ≤ 100 ∧ HoleOut (chainModel C) (Qof P) c'
      ((chainModel C).pos (Qof P) ⟨c.nreg 243005, c.nreg 243006⟩) ∧ Out c c' holeL := by
  set c₀ := c with hc₀
  have h05 : c.nreg 243005 = c₀.nreg 243005 := rfl
  have h06 : c.nreg 243006 = c₀.nreg 243006 := rfl
  have hm1 := C.one_le
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  -- the candidate
  set x : WPos := ⟨c₀.nreg 243005, c₀.nreg 243006⟩ with hxdef
  obtain ⟨he6, hvtx, hedge⟩ := chain_x_cases hxp hxe hxc hxC
  
  -- the descriptor words
  set B := c.nreg 243020 with hBdef
  obtain ⟨-, -, hs1, hs2, hs3, hs4⟩ := hC
  have hBW : B + 4 ≤ W := by
    have := hw.1 ALLOC; omega
  obtain ⟨c₁, k₁, hk₁, e₁, v97, v98, v99, v100, v101, v90, v96, v103, v104, o₁⟩ :=
    chainPre_exec (P := P) hw (B := B) rfl h23 hs2 hs3 rfl hBW hWm
  obtain ⟨c₂, k₂, hk₂, e₂, v102, o₂⟩ := sS_exec (P := P) e₁.wb_right v99 v100 v98
    (by rw [o₁.1 _ (by decide)]; exact h23)
  have hS : sOf C.m C.topIdx (c.nmem (B + 4)) = C.sideS C.sideBeta := sOf_sideS hs4
  rw [hS] at v102
  have hSle := C.sideS_lt C.sideBeta
  set S := C.sideS C.sideBeta with hSdef
  have hi : c₀.nreg 243005 - 6 ≤ 2 * C.m := by omega
  obtain ⟨c₃, k₃, hk₃, e₃, v106, o₃⟩ := jS_exec (P := P) e₂.wb_right (m := C.m) (i := c₀.nreg 243005 - 6) (by omega) v102
    (by ram_grind) (by ram_grind) hSle hi
    (by omega)
  set j := (S + (c₀.nreg 243005 - 6)) % (2 * C.m) with hjdef
  have hj : j < 2 * C.m := Nat.mod_lt _ (by omega)
  -- registers carried to the branch
  have o₁₃ := (o₁.trans o₂).trans o₃
  have r05 : c₃.nreg 243005 = c₀.nreg 243005 := by rw [o₁₃.1 _ (by decide), h05]
  have r06 : c₃.nreg 243006 = c₀.nreg 243006 := by rw [o₁₃.1 _ (by decide), h06]
  have r22 : c₃.nreg 243022 = 0 := by rw [o₁₃.1 _ (by decide), h22]
  have r23 : c₃.nreg 243023 = 1 := by rw [o₁₃.1 _ (by decide), h23]
  have r100 : c₃.nreg 243100 = 2 * C.m := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v100]
  have r102 : c₃.nreg 243102 = S := by rw [o₃.1 _ (by decide), v102]
  have r103 : c₃.nreg 243103 = 6 := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v103]
  have r97 : c₃.nreg 243097 = C.m := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v97]
  have r98 : c₃.nreg 243098 = C.topIdx := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v98]
  have r101 : c₃.nreg 243101 = 7 := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v101]
  have r96 : c₃.nreg 243096 = 2 := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v96]
  have r90 : c₃.nreg 243090 = 2 * C.m + 7 := by rw [o₃.1 _ (by decide), o₂.1 _ (by decide), v90]
  
  have hpos : (chainModel C).pos (Qof P) x =
      Chazelle.Chain.sidePt (chainModel C).W x.edge ((chainModel C).param (Qof P) x) := rfl
  by_cases hh : c₀.nreg 243006 = 0
  · -- a tour vertex
    have g06 : ¬ c₃.nreg 243022 < c₃.nreg 243006 := by omega
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, wtop, o₄⟩ := vtxH_exec (P := P)
      e₃.wb_right r97 r98 r100 r101 r96 r90 r103 r102 (by rw [v106]) r23 hSle hj hWm
    have ex : Exec P W chainH c c₄ (k₁ + (k₂ + (k₃ + (k₄ + 2)))) :=
      .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g06 e₄)))
    have ho : Out c c₄ holeL := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine ⟨c₄, _, ex, by omega, ?_, ho⟩
    set k := Chazelle.Chain.sideE C.m j with hkdef
    have hk : k ≤ C.m := Chazelle.Chain.sideE_le hj.le
    have ha := candIdx_le (m := C.m) (j := k) hSle (by omega)
    have hb := candIdx_le (m := C.m) (j := 2 * C.m - k) hSle (by omega)
    have h9 : c₄.nreg 241309 = 2 ∨ c₄.nreg 241309 = 3 := by rw [w9]; split_ifs <;> simp
    have m0 : (⟨c₄.nreg 241310, 0⟩, ⟨c₄.nreg 241311, 0⟩) ∈ ShotList.holeList c₄ 241300 :=
      hole_mem (c := c₄) (j := 0) (by omega) (by omega)
    have m1 : (⟨c₄.nreg 241312, 0⟩, ⟨c₄.nreg 241313, 0⟩) ∈ ShotList.holeList c₄ 241300 :=
      hole_mem (c := c₄) (j := 1) (by omega) (by omega)
    have va : vHole (chainModel C).W.n (candIdx C.m S k + 6) =
        (⟨c₄.nreg 241310, 0⟩, ⟨c₄.nreg 241311, 0⟩) := by
      rw [hn, vHole_six (by omega), w10, w11]
    have vb : vHole (chainModel C).W.n (candIdx C.m S (2 * C.m - k) + 6) =
        (⟨c₄.nreg 241312, 0⟩, ⟨c₄.nreg 241313, 0⟩) := by
      rw [hn, vHole_six (by omega), w12, w13]
    refine ⟨by omega, fun q hq => ?_, ?_, ?_⟩
    · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · show c₄.nreg 241310 < _ ∧ c₄.nreg 241311 < _ ∧ c₄.nreg 241310 ≠ c₄.nreg 241311
        rw [hn, w10, w11]
        exact ⟨by omega, Nat.mod_lt _ (by omega), vtx_hole_ne ha⟩
      · show c₄.nreg 241312 < _ ∧ c₄.nreg 241313 < _ ∧ c₄.nreg 241312 ≠ c₄.nreg 241313
        rw [hn, w12, w13]
        exact ⟨by omega, Nat.mod_lt _ (by omega), vtx_hole_ne hb⟩
      · have ht : k = C.topIdx := by
          grind
        obtain ⟨t14, t15⟩ := wtop ht
        show c₄.nreg 241314 < _ ∧ c₄.nreg 241315 < _ ∧ c₄.nreg 241314 ≠ c₄.nreg 241315
        omega
    · have hv := (hvtx hh).2
      have hsi : C.sideIdx C.sideBeta (x.edge - 6) = k := by rw [C.sideIdx_eq]
      rw [hsi] at hv
      rw [hv]
      refine cover_chain_vertex hsimp hk (by grind) (by grind)
        (fun ht => ?_) (Qof P)
      obtain ⟨t14, t15⟩ := wtop ht
      have h93 : c₄.nreg 241309 = 3 := by grind
      have m2 : (⟨c₄.nreg 241314, 0⟩, ⟨c₄.nreg 241315, 0⟩) ∈ ShotList.holeList c₄ 241300 :=
        hole_mem (c := c₄) (j := 2) (by omega) (by omega)
      rw [hn, show 2 * C.m + 6 = 2 * C.m + 6 from rfl, vHole_six (by omega), t14, t15,
        Nat.mod_self] at *
      omega
    · intro g hg p' τ hp' h0 h1 hkk
      have hn3 : 3 ≤ (chainModel C).W.n := by omega
      have hv := (hvtx hh).2
      have hsi : C.sideIdx C.sideBeta (x.edge - 6) = k := by rw [C.sideIdx_eq]
      rw [hsi] at hv
      rw [hv]
      have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
      have cv := cand_vertex C C.sideBeta hk
      have za : (chainModel C).W.vtx (candIdx C.m S k + 6) = C.vertex k := by
        rw [hW, C.sideWalk_vtx_tour _ cv.1.1, Chain.sideTour, cv.1.2]
      have zb : (chainModel C).W.vtx (candIdx C.m S (2 * C.m - k) + 6) = C.vertex k := by
        rw [hW, C.sideWalk_vtx_tour _ cv.2.1, Chain.sideTour, cv.2.2]
      simp only [ShotList.holeList, List.mem_map, List.mem_range] at hg
      obtain ⟨q, hq, rfl⟩ := hg
      have hq' : q < min (c₄.nreg 241309) 3 := hq
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · have e : ShotList.holeAt c₄ 241300 0 =
            vHole (chainModel C).W.n (candIdx C.m S k + 6) := by rw [va]; rfl
        rw [e] at hkk
        exact near_vHole _ _ hn3 (by omega) za hp' h0 h1 hkk
      · have e : ShotList.holeAt c₄ 241300 1 =
            vHole (chainModel C).W.n (candIdx C.m S (2 * C.m - k) + 6) := by rw [vb]; rfl
        rw [e] at hkk
        exact near_vHole _ _ hn3 (by omega) zb hp' h0 h1 hkk
      · have ht : k = C.topIdx := by
          by_contra hne; rw [w9, ite_eq_right hne] at hq'; omega
        obtain ⟨t14, t15⟩ := wtop ht
        have e : ShotList.holeAt c₄ 241300 2 = vHole (chainModel C).W.n (2 * C.m + 6) := by
          rw [hn, vHole_six (by omega), Nat.mod_self]
          show ((⟨c₄.nreg 241314, 0⟩, ⟨c₄.nreg 241315, 0⟩) : WPos × WPos) = _
          grind
        rw [e] at hkk
        have e2m : C.sideIdx C.sideBeta (2 * C.m) = C.sideIdx C.sideBeta 0 := by
          rw [C.sideIdx_eq, C.sideIdx_eq, Nat.add_mod_right, Nat.add_zero]
        have h6 : (C.sideWalk C.sideBeta).vtx (0 + 6) = C.top := C.sideWalk_vtx_six _
        rw [C.sideWalk_vtx_tour _ (Nat.zero_le _), Chain.sideTour] at h6
        have ztop : (chainModel C).W.vtx (2 * C.m + 6) = C.vertex k := by
          rw [hW, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour, e2m, h6, ht]; rfl
        exact near_vHole _ _ hn3 (by omega) ztop hp' h0 h1 hkk
  · -- inside a tour edge
    have hh0 : 0 < c₀.nreg 243006 := Nat.pos_of_ne_zero hh
    have g06 : c₃.nreg 243022 < c₃.nreg 243006 := by omega
    obtain ⟨hi2, hτ, hτ1⟩ := hedge hh0
    have hi2' : c₀.nreg 243005 - 6 < 2 * C.m := hi2
    have he6' : 6 ≤ c₀.nreg 243005 := he6
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, o₄⟩ := edgeH_exec (P := P)
      e₃.wb_right r100 v106 r102 r103 r23 r05 hj hSle (by omega) hWm
    have ex : Exec P W chainH c c₄ (k₁ + (k₂ + (k₃ + (k₄ + 1)))) :=
      .seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_true g06 e₄)))
    have ho : Out c c₄ holeL := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine ⟨c₄, _, ex, by omega, ?_, ho⟩
    have htw := (tour_twin C hi2).1
    have htt : tourTwin C (c₀.nreg 243005 - 6) = candIdx C.m S (2 * C.m - 1 - j) := rfl
    rw [htt] at htw
    have m0 : (⟨c₄.nreg 241310, 0⟩, ⟨c₄.nreg 241311, 0⟩) ∈ ShotList.holeList c₄ 241300 :=
      hole_mem (c := c₄) (j := 0) (by omega) (by omega)
    have m1 : (⟨c₄.nreg 241312, 0⟩, ⟨c₄.nreg 241313, 0⟩) ∈ ShotList.holeList c₄ 241300 :=
      hole_mem (c := c₄) (j := 1) (by omega) (by omega)
    refine ⟨by omega, fun q hq => ?_, ?_, ?_⟩
    · rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · grind
      grind
    · have e1 : eHole (chainModel C).W.n (c₀.nreg 243005 - 6 + 6) =
          (⟨c₄.nreg 241310, 0⟩, ⟨c₄.nreg 241311, 0⟩) := by
        unfold eHole
        rw [hn, w10, w11, Nat.mod_eq_of_lt (by omega), show c₀.nreg 243005 - 6 + 6 =
          c₀.nreg 243005 by omega]
      have e2 : eHole (chainModel C).W.n (tourTwin C (c₀.nreg 243005 - 6) + 6) =
          (⟨c₄.nreg 241312, 0⟩, ⟨c₄.nreg 241313, 0⟩) := by
        unfold eHole
        rw [htt, hn, w12, w13, Nat.mod_eq_of_lt (by omega)]
      have hcov := cover_chain_edge hsimp hi2 hτ hτ1 (by rw [e1]; exact m0)
        (by grind) (Qof P)
      grind
    · intro g hg p' τ' hp' h0 h1 hkk
      simp only [ShotList.holeList, List.mem_map, List.mem_range] at hg
      obtain ⟨q, hq, rfl⟩ := hg
      have hq' : q < min (c₄.nreg 241309) 3 := hq
      
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · have e : ShotList.holeAt c₄ 241300 0 = eHole (chainModel C).W.n (c₀.nreg 243005) := by
          rw [holeAt_eq]; unfold eHole
          show ((⟨c₄.nreg 241310, 0⟩, ⟨c₄.nreg 241311, 0⟩) : WPos × WPos) = _
          rw [hn, w10, w11, Nat.mod_eq_of_lt (by omega)]
        rw [e] at hkk
        exact near_eHole _ _ (by omega) ⟨_, hτ.le, hτ1.le, rfl⟩ hp' h0 h1 hkk
      · have e2 : eHole (chainModel C).W.n (tourTwin C (c₀.nreg 243005 - 6) + 6) =
            (⟨c₄.nreg 241312, 0⟩, ⟨c₄.nreg 241313, 0⟩) := by
          unfold eHole
          rw [htt, hn, w12, w13, Nat.mod_eq_of_lt (by omega)]
        have e : ShotList.holeAt c₄ 241300 1 =
            eHole (chainModel C).W.n (tourTwin C (c₀.nreg 243005 - 6) + 6) := by
          grind [holeAt_eq]
        rw [e] at hkk
        obtain ⟨-, a1, a2⟩ := tour_twin C hi2'
        rw [show c₀.nreg 243005 - 6 + 6 = c₀.nreg 243005 by omega] at a1 a2
        have zt : Chazelle.Chain.sidePt (chainModel C).W (tourTwin C (c₀.nreg 243005 - 6) + 6)
            (1 - (chainModel C).param (Qof P) x) = (chainModel C).pos (Qof P) x := by
          show Geometry.lerp ((chainModel C).wa (tourTwin C (c₀.nreg 243005 - 6) + 6))
            ((chainModel C).wb (tourTwin C (c₀.nreg 243005 - 6) + 6)) _ =
            Geometry.lerp ((chainModel C).wa (c₀.nreg 243005)) ((chainModel C).wb (c₀.nreg 243005))
              ((chainModel C).param (Qof P) x)
          rw [a1, a2]
          ext <;> simp [Geometry.lerp] <;> ring
        exact near_eHole _ _ (by omega) ⟨_, by linarith, by linarith, zt⟩ hp' h0 h1 hkk

end

end SweepIo

end Chazelle.Core
