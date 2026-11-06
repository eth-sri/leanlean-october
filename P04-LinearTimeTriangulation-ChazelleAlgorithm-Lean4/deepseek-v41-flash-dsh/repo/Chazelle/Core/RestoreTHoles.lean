module

public import Chazelle.Core.RestoreTHoleChain
public import Chazelle.Core.RestoreTNear

/-!
# WP-E, the candidate test on the RAM: the holes of the candidate

`holeS` writes the holes of the candidate `x` into the registers `84009 … 84015` of the shot
block `RS0 = 84000` (the wrapper's hole registers `R + 9 … R + 15`): `intH` in the interior model,
`chainH` in a chain model.  `holeS_rs`: the holes are pairs of distinct walk vertices and cover
the candidate point (`Cover`), and every walk point with a key in a closed hole lies on a walk
edge through the candidate point (`Near`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK
open Chazelle.Chain (sideE sidePt)

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **The holes of the candidate.** -/
def holeS : Stmt := .ifLtN 83021 83023 chainH intH

/-! ## The candidate on the chain -/

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
  Ξ' hpos at hz
  Ξ' hW at he
  rcases C.sideWalk_pos_cases C.sideBeta he hx.1 with hbox | ⟨i, hi, hie, hit⟩
  · exact absurd hz (C.sideWalk_box_pt C.sideBeta hbox hx.1 hx.2.1).1
  refine ⟨⋄, fun h0 => ⟨⋄, ?_⟩, fun hh => ⟨?_, ?_, hx.2.1⟩⟩
  · have hp0 : (chainModel C).param Q x = 0 := by
      obtain ⟨e, h⟩ := x; simp only at h0; subst h0; rfl
    Ξ hpos, hp0, Chazelle.Chain.sidePt_zero, hie, C.sideWalk_vtx_tour _ hi
    rw [show i + 6 - 6 = i by omega]; rfl
  · have hp : 0 < (chainModel C).param Q x := by
      rcases hxc with h | h
      · omega
      · exact h
    rcases hi.lt_or_eq with h | h
    · omega
    · exact absurd (hit h) hp.ne'
  · rcases hxc with h | h
    · omega
    · exact h

/-! ## The holes as a list -/

/-! ## The descriptor chain of a run -/

/-- **The chain of the descriptor of a run**, with its host regular and its polygon simple. -/
theorem TInv.chainS (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C : Chain}
    (hM : M = chainModel C) :
    ∃ H C', ChainDescAt c.nmem (c.nreg 83020) (Qof P) H C' ∧ M = chainModel C' ∧
      ChainWF P (c.nreg ALLOC) c.nmem (c.nreg 83020) ∧ C'.P.Simple ∧
      HostRegular (Qof P).n H := by
  obtain ⟨h0, H₀, C₀, hC₀, hM₀⟩ := chainDesc_of hE.hMD hM
  obtain ⟨H, C', hC, hM', hwf⟩ := hI.chain hE hM
  have hcw := hE.hwfMD.2 h0
  obtain ⟨-, -, hEb, -⟩ := hcw.2 H₀ C₀ hC₀
  have hC₀' : ChainDescAt c.nmem (c.nreg 83020) (Qof P) H₀ C₀ := by
    rw [hI.h20]; exact chainDesc_agree hC₀ hcw.1 hEb (fun a ha => hI.hm a ha)
  have e1 : C₀ = C' := NFLoc.chain_eq_of_desc hC₀' hC
  have e2 : H₀ = H := NFLoc.hostAt_unique hC₀'.1 hC.1
  subst e1 e2
  exact ⟨H₀, C₀, hC, hM', hwf, hE.hsimp h0 H₀ C₀ hC₀, hE.hreg h0 H₀ C₀ hC₀⟩

/-! ## The contract -/

/-- **The holes in the registers** `84009 … 84015` are proper and cover the point `z`. -/
def HoleOut (M : Model) (Q : Polygon) (c : Config) (z : Point) : Prop :=
  c.nreg 84009 ≤ 3 ∧
    (∀ j < c.nreg 84009, c.nreg (84000 + 10 + 2 * j) < M.W.n ∧
      c.nreg (84000 + 11 + 2 * j) < M.W.n ∧ c.nreg (84000 + 10 + 2 * j) ≠ c.nreg (84000 + 11 + 2 * j)) ∧
    Cover M Q (ShotList.holeList c 84000) z ∧ Near M Q (ShotList.holeList c 84000) z

/-- The scratch registers of `holeS`. -/
def holeL : List ℕ := chainHL ++ [83092, 83093]

theorem holeAt_eq (c : Config) (j : ℕ) :
    ShotList.holeAt c 84000 j = (⟨c.nreg (84000 + 10 + 2 * j), 0⟩, ⟨c.nreg (84000 + 11 + 2 * j), 0⟩) :=
  rfl

/-! ## Hole arithmetic -/

theorem hole_mem {c : Config} {j : ℕ} (hj : j < c.nreg 84009) (h3 : c.nreg 84009 ≤ 3) :
    ShotList.holeAt c 84000 j ∈ ShotList.holeList c 84000 :=
  List.mem_map.2 ⟨j, List.mem_range.2 (by show j < min (c.nreg 84009) 3; omega), rfl⟩

theorem prevV_lt {n q : ℕ} (hn : 0 < n) : prevV n q < n := Nat.mod_lt _ hn

theorem prevV_ne {n q : ℕ} (hn : 3 ≤ n) (hq : q < n) : prevV n q ≠ (q + 1) % n := by
  unfold prevV
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · Ξ show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (⋄), Nat.mod_eq_of_lt (⋄)
    omega
  · Ξ show q + n - 1 = (q - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (⋄)
    rcases Nat.lt_or_ge (q + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show q + 1 = n by omega, Nat.mod_self]; omega

theorem succ_ne {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : q ≠ (q + 1) % n := by
  rcases Nat.lt_or_ge (q + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show q + 1 = n by omega, Nat.mod_self]; omega

theorem vHole_six {n c : ℕ} (h : c + 6 < n) : vHole n (c + 6) = (⟨c + 5, 0⟩, ⟨(c + 7) % n, 0⟩) := by
  unfold vHole prevV
  Ξ show c + 6 + n - 1 = (c + 5) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (⋄)

theorem vtx_hole_ne {m c : ℕ} (hc : c ≤ 2 * m) : c + 5 ≠ (c + 7) % (2 * m + 7) := by
  rcases Nat.lt_or_ge (c + 7) (2 * m + 7) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · rw [show c + 7 = 2 * m + 7 by omega, Nat.mod_self]; omega

/-! ## The holes on the RAM -/

theorem holeS_int (hE : TGood P W (interiorModel (Qof P)) N c₀) (hI : TInv W c₀ c)
    (h1 : c₀.nmem (c₀.nreg 83000) = 1) :
    RS P W c₀ holeS c 40 (fun c' => HoleOut (interiorModel (Qof P)) (Qof P) c'
      ((interiorModel (Qof P)).pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩) ∧ Out c c' holeL) := by
  have h05 : c.nreg 83005 = c₀.nreg 83005 := hI.hin _ (⊛) (⊛)
  have h06 : c.nreg 83006 = c₀.nreg 83006 := hI.hin _ (⊛) (⊛)
  have hn : (interiorModel (Qof P)).W.n = P.n := interior_n
  have hn3 : 3 ≤ P.n := hE.hG.1.1
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hE.hG.1
  have hWs : (interiorModel (Qof P)).W.Simple := (FactsInterior.interiorWalk_spec hQ).1
  have g21 : ¬ c.nreg 83021 < c.nreg 83023 := by rw [hI.h21, hI.h23, h1]; omega
  have he : c.nreg 83005 < P.n := by rw [h05, ← hn]; exact hE.hxe
  obtain ⟨c', k, hk, ex, v9, v10, v11, ho⟩ := intH_exec hI.hw
    (by have := hE.hW; unfold hostWords at this; omega) hI.h22 hI.h23 he
  have hL : ∀ r ∈ [83090, 83092, 83093, 84009, 84010, 84011], r ∈ holeL := by
    intro r hr; simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢; omega
  refine RS.out hI (fun r hr => ?_) (.ifLtN_false g21 ex) (⋄) (ho.mono hL) ⟨?_, ho.mono hL⟩
  · ϴ' holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false at hr
    unfold Scr; omega
  Ξ' h05, h06 at v10
  Ξ' h05 at v11
  Ξ' h05 at he
  set e := c₀.nreg 83005
  have a0 : ShotList.holeAt c' 84000 0 = (⟨c'.nreg 84010, 0⟩, ⟨c'.nreg 84011, 0⟩) := holeAt_eq c' 0
  have hp := hE.hxp
  refine ⟨⋄, fun j hj => ?_, ?_, ?_⟩
  · obtain rfl : j = 0 := ⋄
    show c'.nreg 84010 < _ ∧ c'.nreg 84011 < _ ∧ c'.nreg 84010 ≠ c'.nreg 84011
    Ξ hn, v10, v11
    refine ⟨?_, Nat.mod_lt _ (⋄), ?_⟩
    · split_ifs
      · exact prevV_lt (⋄)
      · exact he
    · split_ifs
      · exact prevV_ne hn3 he
      · exact succ_ne (⋄) he
  · have hmem := hole_mem (c := c') (j := 0) (⋄) (⋄)
    Ξ' a0 at hmem
    exact cover_unique hWs (by rw [hn]; exact he) hp.1 hp.2.1 (by rw [hn]; exact hn3)
      (fun h0 => by
        have hg : c₀.nreg 83006 = 0 := by
          rcases hE.hxc with h | h
          · exact h
          · exact absurd h0 h.ne'
        Ξ' v10, v11, ite_eq_left hg at hmem; rw [hn]; exact hmem)
      (fun hpos => by
        have hg : c₀.nreg 83006 ≠ 0 := fun hg => by
          have : (interiorModel (Qof P)).param (Qof P) ⟨e, c₀.nreg 83006⟩ = 0 := by
            rw [hg]; rfl
          exact absurd this hpos.ne'
        Ξ' v10, v11, ite_eq_right hg at hmem; rw [hn]; exact hmem) (Qof P)
  · intro g hg p' τ hp' h0 h1 hkk
    ϴ' ShotList.holeList, List.mem_map, List.mem_range at hg
    obtain ⟨q, hq, rfl⟩ := hg
    obtain rfl : q = 0 := by have : q < min (c'.nreg 84009) 3 := hq; omega
    Ξ' a0, v10, v11 at hkk
    by_cases hg0 : c₀.nreg 83006 = 0
    · Ξ' ite_eq_left hg0 at hkk
      have hv : vHole (interiorModel (Qof P)).W.n e = (⟨prevV P.n e, 0⟩, ⟨(e + 1) % P.n, 0⟩) := by
        rw [hn]; rfl
      refine near_vHole _ (Qof P) (by rw [hn]; exact hn3) (by rw [hn]; exact he) ?_ hp' h0 h1
        (by rw [hv]; exact hkk)
      rw [hg0, ← Chazelle.Chain.sidePt_zero]; rfl
    · Ξ' ite_eq_right hg0 at hkk
      have hv : eHole (interiorModel (Qof P)).W.n e = (⟨e, 0⟩, ⟨(e + 1) % P.n, 0⟩) := by
        rw [hn]; rfl
      exact near_eHole _ (Qof P) (by rw [hn]; exact he) ⟨_, hp.1, hp.2.1.le, rfl⟩ hp' h0 h1
        (by rw [hv]; exact hkk)

theorem sOf_sideS {C : Chain} {b : ℕ} (hb : b = 1 ↔ C.sideBeta = true) :
    sOf C.m C.topIdx b = C.sideS C.sideBeta := by
  unfold sOf Chain.sideS
  by_cases h : b = 1
  · Ξ ite_eq_left h, ite_eq_left (hb.1 h)
  · Ξ ite_eq_right h, ite_eq_right (fun h' => h (hb.2 h'))

theorem holeL_scr : ∀ r ∈ holeL, Scr r := by
  intro r hr
  ϴ' holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil, or_false at hr
  unfold Scr; omega

set_option maxHeartbeats 1600000 in
/-- **The holes of the candidate in a chain model** (`chainH`): pairs of distinct walk vertices
covering the candidate point. -/
theorem holeS_chain (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {C₀ : Chain}
    (hM₀ : M = chainModel C₀) :
    RS P W c₀ holeS c 100 (fun c' => HoleOut M (Qof P) c'
      (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩) ∧ Out c c' holeL) := by
  obtain ⟨H, C, hC, hM, hwf, hsimp, -⟩ := hI.chainS hE hM₀
  subst hM
  have h05 : c.nreg 83005 = c₀.nreg 83005 := hI.hin _ (⊛) (⊛)
  have h06 : c.nreg 83006 = c₀.nreg 83006 := hI.hin _ (⊛) (⊛)
  have hm1 := C.one_le
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have hWm : 2 * C.m + 7 ≤ W := hE.hWm C rfl
  have hz0 : c₀.nmem (c₀.nreg 83000) = 0 := (chainDesc_of hE.hMD rfl).1
  have g21 : c.nreg 83021 < c.nreg 83023 := by rw [hI.h21, hI.h23, hz0]; omega
  -- the candidate
  set x : WPos := ⟨c₀.nreg 83005, c₀.nreg 83006⟩ with hxdef
  obtain ⟨he6, hvtx, hedge⟩ := chain_x_cases hE.hxp hE.hxe hE.hxc (hE.hxC C rfl)
  have hxe : c₀.nreg 83005 < 2 * C.m + 7 := by rw [← hn]; exact hE.hxe
  -- the descriptor words
  set B := c.nreg 83020 with hBdef
  obtain ⟨-, -, hs1, hs2, hs3, hs4⟩ := hC
  have hBW : B + 4 ≤ W := by
    have := hwf.1; have := hI.hw.1 ALLOC; omega
  obtain ⟨c₁, k₁, hk₁, e₁, v97, v98, v99, v100, v101, v90, v96, v103, v104, o₁⟩ :=
    chainPre_exec (P := P) hI.hw (B := B) rfl hI.h23 hs2 hs3 rfl hBW hWm
  obtain ⟨c₂, k₂, hk₂, e₂, v102, o₂⟩ := sS_exec (P := P) e₁.wb_right v99 v100 v98
    (by rw [o₁.1 _ (⌖)]; exact hI.h23)
  have hS : sOf C.m C.topIdx (c.nmem (B + 4)) = C.sideS C.sideBeta := sOf_sideS hs4
  Ξ' hS at v102
  have hSle := C.sideS_lt C.sideBeta
  set S := C.sideS C.sideBeta with hSdef
  have hi : c₀.nreg 83005 - 6 ≤ 2 * C.m := ⋄
  obtain ⟨c₃, k₃, hk₃, e₃, v106, o₃⟩ := jS_exec (P := P) e₂.wb_right (m := C.m) (i := c₀.nreg 83005 - 6) (⋄) v102
    (Ρ o₂.1 _ (⌖), v104, h05) (Ρ o₂.1 _ (⌖), v100) hSle hi
    (⋄)
  set j := (S + (c₀.nreg 83005 - 6)) % (2 * C.m) with hjdef
  have hj : j < 2 * C.m := Nat.mod_lt _ (⋄)
  -- registers carried to the branch
  have o₁₃ := (o₁.trans o₂).trans o₃
  have r05 : c₃.nreg 83005 = c₀.nreg 83005 := Ρ o₁₃.1 _ (⌖), h05
  have r06 : c₃.nreg 83006 = c₀.nreg 83006 := Ρ o₁₃.1 _ (⌖), h06
  have r22 : c₃.nreg 83022 = 0 := Ρ o₁₃.1 _ (⌖), hI.h22
  have r23 : c₃.nreg 83023 = 1 := Ρ o₁₃.1 _ (⌖), hI.h23
  have r100 : c₃.nreg 83100 = 2 * C.m := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v100
  have r102 : c₃.nreg 83102 = S := Ρ o₃.1 _ (⌖), v102
  have r103 : c₃.nreg 83103 = 6 := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v103
  have r97 : c₃.nreg 83097 = C.m := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v97
  have r98 : c₃.nreg 83098 = C.topIdx := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v98
  have r101 : c₃.nreg 83101 = 7 := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v101
  have r96 : c₃.nreg 83096 = 2 := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v96
  have r90 : c₃.nreg 83090 = 2 * C.m + 7 := Ρ o₃.1 _ (⌖), o₂.1 _ (⌖), v90
  have hL₁₃ : ∀ r ∈ chainHL ++ [83102] ++ [83105, 83106], r ∈ holeL := by
    intro r hr; simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢; omega
  have hpos : (chainModel C).pos (Qof P) x =
      Chazelle.Chain.sidePt (chainModel C).W x.edge ((chainModel C).param (Qof P) x) := rfl
  by_cases hh : c₀.nreg 83006 = 0
  · -- a tour vertex
    have g06 : ¬ c₃.nreg 83022 < c₃.nreg 83006 := by rw [r22, r06, hh]; omega
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, wtop, o₄⟩ := vtxH_exec (P := P)
      e₃.wb_right r97 r98 r100 r101 r96 r90 r103 r102 (Ρ v106) r23 hSle hj hWm
    have ex : Exec P W holeS c c₄ (k₁ + (k₂ + (k₃ + (k₄ + 2))) + 1) :=
      .ifLtN_true g21 (.seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_false g06 e₄))))
    have ho : Out c c₄ holeL := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine RS.out hI holeL_scr ex (⋄) ho ⟨?_, ho⟩
    set k := Chazelle.Chain.sideE C.m j with hkdef
    have hk : k ≤ C.m := Chazelle.Chain.sideE_le hj.le
    have ha := candIdx_le (m := C.m) (j := k) hSle (⋄)
    have hb := candIdx_le (m := C.m) (j := 2 * C.m - k) hSle (⋄)
    have h9 : c₄.nreg 84009 = 2 ∨ c₄.nreg 84009 = 3 := by rw [w9]; split_ifs <;> simp
    have m0 : (⟨c₄.nreg 84010, 0⟩, ⟨c₄.nreg 84011, 0⟩) ∈ ShotList.holeList c₄ 84000 :=
      hole_mem (c := c₄) (j := 0) (⋄) (⋄)
    have m1 : (⟨c₄.nreg 84012, 0⟩, ⟨c₄.nreg 84013, 0⟩) ∈ ShotList.holeList c₄ 84000 :=
      hole_mem (c := c₄) (j := 1) (⋄) (⋄)
    have va : vHole (chainModel C).W.n (candIdx C.m S k + 6) =
        (⟨c₄.nreg 84010, 0⟩, ⟨c₄.nreg 84011, 0⟩) := by
      Ξ hn, vHole_six (⋄), w10, w11
    have vb : vHole (chainModel C).W.n (candIdx C.m S (2 * C.m - k) + 6) =
        (⟨c₄.nreg 84012, 0⟩, ⟨c₄.nreg 84013, 0⟩) := by
      Ξ hn, vHole_six (⋄), w12, w13
    refine ⟨⋄, fun q hq => ?_, ?_, ?_⟩
    · rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · show c₄.nreg 84010 < _ ∧ c₄.nreg 84011 < _ ∧ c₄.nreg 84010 ≠ c₄.nreg 84011
        Ξ hn, w10, w11
        exact ⟨⋄, Nat.mod_lt _ (⋄), vtx_hole_ne ha⟩
      · show c₄.nreg 84012 < _ ∧ c₄.nreg 84013 < _ ∧ c₄.nreg 84012 ≠ c₄.nreg 84013
        Ξ hn, w12, w13
        exact ⟨⋄, Nat.mod_lt _ (⋄), vtx_hole_ne hb⟩
      · have ht : k = C.topIdx := by
          by_contra hne; Ξ' w9, ite_eq_right hne at hq; omega
        obtain ⟨t14, t15⟩ := wtop ht
        show c₄.nreg 84014 < _ ∧ c₄.nreg 84015 < _ ∧ c₄.nreg 84014 ≠ c₄.nreg 84015
        Ξ hn, t14, t15
        omega
    · have hv := (hvtx hh).2
      have hsi : C.sideIdx C.sideBeta (x.edge - 6) = k := Ρ C.sideIdx_eq
      Ξ' hsi at hv
      Ξ hv
      refine cover_chain_vertex hsimp hk (by rw [va]; exact m0) (by rw [vb]; exact m1)
        (fun ht => ?_) (Qof P)
      obtain ⟨t14, t15⟩ := wtop ht
      have h93 : c₄.nreg 84009 = 3 := Ρ w9, ite_eq_left ht
      have m2 : (⟨c₄.nreg 84014, 0⟩, ⟨c₄.nreg 84015, 0⟩) ∈ ShotList.holeList c₄ 84000 :=
        hole_mem (c := c₄) (j := 2) (⋄) (⋄)
      rw [hn, show 2 * C.m + 6 = 2 * C.m + 6 from rfl, vHole_six (⋄), t14, t15,
        Nat.mod_self] at *
      Ξ ← t14, ← t15
      exact m2
    · intro g hg p' τ hp' h0 h1 hkk
      have hn3 : 3 ≤ (chainModel C).W.n := by rw [hn]; omega
      have hv := (hvtx hh).2
      have hsi : C.sideIdx C.sideBeta (x.edge - 6) = k := Ρ C.sideIdx_eq
      Ξ' hsi at hv
      Ξ hv
      have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
      have cv := cand_vertex C C.sideBeta hk
      have za : (chainModel C).W.vtx (candIdx C.m S k + 6) = C.vertex k := by
        Ξ hW, C.sideWalk_vtx_tour _ cv.1.1, Chain.sideTour, cv.1.2
      have zb : (chainModel C).W.vtx (candIdx C.m S (2 * C.m - k) + 6) = C.vertex k := by
        Ξ hW, C.sideWalk_vtx_tour _ cv.2.1, Chain.sideTour, cv.2.2
      ϴ' ShotList.holeList, List.mem_map, List.mem_range at hg
      obtain ⟨q, hq, rfl⟩ := hg
      have hq' : q < min (c₄.nreg 84009) 3 := hq
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
      · have e : ShotList.holeAt c₄ 84000 0 =
            vHole (chainModel C).W.n (candIdx C.m S k + 6) := by rw [va]; rfl
        Ξ' e at hkk
        exact near_vHole _ _ hn3 (by rw [hn]; omega) za hp' h0 h1 hkk
      · have e : ShotList.holeAt c₄ 84000 1 =
            vHole (chainModel C).W.n (candIdx C.m S (2 * C.m - k) + 6) := by rw [vb]; rfl
        Ξ' e at hkk
        exact near_vHole _ _ hn3 (by rw [hn]; omega) zb hp' h0 h1 hkk
      · have ht : k = C.topIdx := by
          by_contra hne; Ξ' w9, ite_eq_right hne at hq'; omega
        obtain ⟨t14, t15⟩ := wtop ht
        have e : ShotList.holeAt c₄ 84000 2 = vHole (chainModel C).W.n (2 * C.m + 6) := by
          Ξ hn, vHole_six (⋄), Nat.mod_self
          show ((⟨c₄.nreg 84014, 0⟩, ⟨c₄.nreg 84015, 0⟩) : WPos × WPos) = _
          Ξ t14, t15
        Ξ' e at hkk
        have e2m : C.sideIdx C.sideBeta (2 * C.m) = C.sideIdx C.sideBeta 0 := by
          Ξ C.sideIdx_eq, C.sideIdx_eq, Nat.add_mod_right, Nat.add_zero
        have h6 : (C.sideWalk C.sideBeta).vtx (0 + 6) = C.top := C.sideWalk_vtx_six _
        Ξ' C.sideWalk_vtx_tour _ (Nat.zero_le _), Chain.sideTour at h6
        have ztop : (chainModel C).W.vtx (2 * C.m + 6) = C.vertex k := by
          rw [hW, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour, e2m, h6, ht]; rfl
        exact near_vHole _ _ hn3 (by rw [hn]; omega) ztop hp' h0 h1 hkk
  · -- inside a tour edge
    have hh0 : 0 < c₀.nreg 83006 := Nat.pos_of_ne_zero hh
    have g06 : c₃.nreg 83022 < c₃.nreg 83006 := by rw [r22, r06]; exact hh0
    obtain ⟨hi2, hτ, hτ1⟩ := hedge hh0
    have hi2' : c₀.nreg 83005 - 6 < 2 * C.m := hi2
    have he6' : 6 ≤ c₀.nreg 83005 := he6
    obtain ⟨c₄, k₄, hk₄, e₄, w9, w10, w11, w12, w13, o₄⟩ := edgeH_exec (P := P)
      e₃.wb_right r100 v106 r102 r103 r23 r05 hj hSle (⋄) hWm
    have ex : Exec P W holeS c c₄ (k₁ + (k₂ + (k₃ + (k₄ + 1))) + 1) :=
      .ifLtN_true g21 (.seq e₁ (.seq e₂ (.seq e₃ (.ifLtN_true g06 e₄))))
    have ho : Out c c₄ holeL := (o₁₃.trans o₄).mono (fun r hr => by
      simp only [holeL, chainHL, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr ⊢; omega)
    refine RS.out hI holeL_scr ex (⋄) ho ⟨?_, ho⟩
    have htw := (tour_twin C hi2).1
    have htt : tourTwin C (c₀.nreg 83005 - 6) = candIdx C.m S (2 * C.m - 1 - j) := rfl
    Ξ' htt at htw
    have m0 : (⟨c₄.nreg 84010, 0⟩, ⟨c₄.nreg 84011, 0⟩) ∈ ShotList.holeList c₄ 84000 :=
      hole_mem (c := c₄) (j := 0) (⋄) (⋄)
    have m1 : (⟨c₄.nreg 84012, 0⟩, ⟨c₄.nreg 84013, 0⟩) ∈ ShotList.holeList c₄ 84000 :=
      hole_mem (c := c₄) (j := 1) (⋄) (⋄)
    refine ⟨⋄, fun q hq => ?_, ?_, ?_⟩
    · rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · show c₄.nreg 84010 < _ ∧ c₄.nreg 84011 < _ ∧ c₄.nreg 84010 ≠ c₄.nreg 84011
        rw [hn, w10, w11]; omega
      · show c₄.nreg 84012 < _ ∧ c₄.nreg 84013 < _ ∧ c₄.nreg 84012 ≠ c₄.nreg 84013
        rw [hn, w12, w13]; omega
    · have e1 : eHole (chainModel C).W.n (c₀.nreg 83005 - 6 + 6) =
          (⟨c₄.nreg 84010, 0⟩, ⟨c₄.nreg 84011, 0⟩) := by
        unfold eHole
        rw [hn, w10, w11, Nat.mod_eq_of_lt (⋄), show c₀.nreg 83005 - 6 + 6 =
          c₀.nreg 83005 by omega]
      have e2 : eHole (chainModel C).W.n (tourTwin C (c₀.nreg 83005 - 6) + 6) =
          (⟨c₄.nreg 84012, 0⟩, ⟨c₄.nreg 84013, 0⟩) := by
        unfold eHole
        Ξ htt, hn, w12, w13, Nat.mod_eq_of_lt (⋄)
      have hcov := cover_chain_edge hsimp hi2 hτ hτ1 (by rw [e1]; exact m0)
        (by rw [e2]; exact m1) (Qof P)
      Ξ' show c₀.nreg 83005 - 6 + 6 = c₀.nreg 83005 by omega at hcov
      Ξ hpos
      exact hcov
    · intro g hg p' τ' hp' h0 h1 hkk
      ϴ' ShotList.holeList, List.mem_map, List.mem_range at hg
      obtain ⟨q, hq, rfl⟩ := hg
      have hq' : q < min (c₄.nreg 84009) 3 := hq
      have htw2 : tourTwin C (c₀.nreg 83005 - 6) < 2 * C.m := (tour_twin C hi2').1
      rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
      · have e : ShotList.holeAt c₄ 84000 0 = eHole (chainModel C).W.n (c₀.nreg 83005) := by
          rw [holeAt_eq]; unfold eHole
          show ((⟨c₄.nreg 84010, 0⟩, ⟨c₄.nreg 84011, 0⟩) : WPos × WPos) = _
          Ξ hn, w10, w11, Nat.mod_eq_of_lt (⋄)
        Ξ' e at hkk
        exact near_eHole _ _ (by rw [hn]; omega) ⟨_, hτ.le, hτ1.le, rfl⟩ hp' h0 h1 hkk
      · have e2 : eHole (chainModel C).W.n (tourTwin C (c₀.nreg 83005 - 6) + 6) =
            (⟨c₄.nreg 84012, 0⟩, ⟨c₄.nreg 84013, 0⟩) := by
          unfold eHole
          Ξ htt, hn, w12, w13, Nat.mod_eq_of_lt (⋄)
        have e : ShotList.holeAt c₄ 84000 1 =
            eHole (chainModel C).W.n (tourTwin C (c₀.nreg 83005 - 6) + 6) := by
          Ξ holeAt_eq, e2
        Ξ' e at hkk
        obtain ⟨-, a1, a2⟩ := tour_twin C hi2'
        Ξ' show c₀.nreg 83005 - 6 + 6 = c₀.nreg 83005 by omega at a1 a2
        have zt : Chazelle.Chain.sidePt (chainModel C).W (tourTwin C (c₀.nreg 83005 - 6) + 6)
            (1 - (chainModel C).param (Qof P) x) = (chainModel C).pos (Qof P) x := by
          show Geometry.lerp ((chainModel C).wa (tourTwin C (c₀.nreg 83005 - 6) + 6))
            ((chainModel C).wb (tourTwin C (c₀.nreg 83005 - 6) + 6)) _ =
            Geometry.lerp ((chainModel C).wa (c₀.nreg 83005)) ((chainModel C).wb (c₀.nreg 83005))
              ((chainModel C).param (Qof P) x)
          Ξ a1, a2
          ext <;> simp [Geometry.lerp] <;> ring
        exact near_eHole _ _ (by rw [hn]; omega) ⟨_, ⟡, ⟡, zt⟩ hp' h0 h1 hkk

/-- **The holes of the candidate** (both models): pairs of distinct walk vertices covering the
candidate point; only the scratch registers `holeL` change. -/
theorem holeS_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ holeS c 100 (fun c' => HoleOut M (Qof P) c'
      (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩) ∧ Out c c' holeL) := by
  rcases hE.kind with ⟨-, C, hM⟩ | ⟨h1, hM, -⟩
  · exact holeS_chain hE hI hM
  · subst hM
    exact (holeS_int hE hI h1).mono (⋄) (fun _ h => h)

end

end Restore

end Chazelle.Core
