module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvWinM2
public import Chazelle.Core.RestoreFPGood

/-!
# The sweep (WP-D), stage 3: the window of the event loop (task C1)

**`winTask : WinTask`** (contract in `SweepEvTasks.lean`, section C).  The program `win`: the key
read in the walk of `C₁` (`wKeyS`), double identification in `N₁` (`locS`), the located arc
(`arcS`), the chord count (`cntS`), the arc after the key and the window end (`bodyS`), and the
gather of the arcs of its region (`gatherS`); cost `κW D · (TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

/-! ## The program -/

def cntS : Stmt := .instr (.loadN wCh (sw 3))

/-- **The window computation.** -/
def win : Stmt := .seq wKeyS (.seq locS (.seq arcS (.seq cntS (.seq bodyS gatherS))))

/-- The cost factor of the window (`D` the degree bound of `N₁`). -/
def κW (D : ℕ) : ℕ := 30000 + 22062 * (D + 1)

theorem DecOut.congr {J : Merge.Junction} {Pw : Prop} {d₀ eE hE : ℕ} {c c' : Config}
    (h : DecOut J Pw d₀ eE hE c) (hX : c'.nreg wX = c.nreg wX) (hE' : c'.nreg wE = c.nreg wE)
    (hH : c'.nreg wH = c.nreg wH) : DecOut J Pw d₀ eE hE c' := by
  grind [DecOut]

theorem gatherK_single_le {M : Model} {Q : Polygon} {N : NF} (hM : WalkAx M) (hNF : IsNF M Q N)
    {D : ℕ} (hD : M.DegLe (N.F M Q) D) {r : ℕ} (hr : r < N.nRegions) :
    gatherK N [r] ≤ 33 + 22062 * (D + 1) := by
  have := Restore.region_arcs_le hM hNF hD hr
  grind [gatherK, regK, arcK, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]



theorem win_cost (T D : ℕ) : 12 + ((5500 * (T + 1) + 9) + (16 + (1 + (22100 +
    ((33 + 22062 * (D + 1)) + 10))))) ≤ κW D * (T + 1) := by
  unfold κW; grind

theorem win_room_body {a a' W K T G : ℕ} (hroom : a + K ≤ W)
    (hc : 12 + ((5500 * (T + 1) + 9) + (16 + (1 + (22100 + G)))) ≤ K) (ha : a' = a) :
    a' + 22100 ≤ W := by omega

theorem wr_of_gathW {q : ℕ} (h : GathW q) : WR q := by
  omega_nf

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
/-- **Task C1: the window.** -/
theorem winTask : WinTask := by
  refine ⟨win, κW, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI hpw hL hroom
  have hP : J.P.Simple := E.hP
  have hP₁ : J.left.P.Simple := E.hP
  have hNF := E.hNF₁
  obtain ⟨hoff, hkdE, hgap0, hψ0, hm0, hv0, hpar, hpt⟩ := key_map hP hpw hL
  
  have hcost0 := win_cost (c₀.nreg TLR) (c₀.nreg (sw 6))
  generalize hKdef : κW (c₀.nreg (sw 6)) * (c₀.nreg TLR + 1) = K at hroom hcost0 ⊢
  have hcost : 12 + ((5500 * (c₀.nreg TLR + 1) + 9) + (16 + (1 + (22100 +
      ((33 + 22062 * (c₀.nreg (sw 6) + 1)) + 10))))) ≤ K := hcost0
  have hn₁ : 0 < (chainModel J.left).W.n := by grind [win_n₁_eq]
  refine IRS.mono (IRS.seq (wKeyS_irs (P := P) hI E.hM hpw.1 hP E.hWn hkdE) ?_) hcost (fun _ h => h)
  rintro c₁ hI₁ - - ⟨v1D, v1E, o1, m1⟩
  have a1 : c₁.nreg ALLOC = c.nreg ALLOC := o1 _ (by rne) (by rne)
  have k1H : c₁.nreg kH = c.nreg kH := o1 _ (by rne) (by rne)
  have hpx1 : ProperPos (chainModel J.left) (Qof P) P.n ⟨c₁.nreg wE1, c₁.nreg kH⟩ := by
    rw [v1E, k1H]
    exact ⟨by rw [hpar]; exact hpw.2.1.1, by rw [hpar]; exact hpw.2.1.2.1, hpw.2.1.2.2⟩
  -- double identification
  refine IRS.seq (locS_irs E hI₁ (by rw [v1E]; exact Nat.mod_lt _ hn₁) hpx1 (by omega)) ?_
  rintro c₂ hI₂ - - ⟨ho2, hl1, hl2, k2, m2⟩
  have e2 : ∀ q, 240000 ≤ q → q < 250000 → q ≠ wO → c₂.nreg q = c₁.nreg q := fun q h1 h2 h3 =>
    k2 q (not_oracle_sw h1 h2) h3
  have a2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [k2 _ (by decide) (by rne), a1]
  -- the located arc
  have hNT := win_nt E hI₂
  have hNA : NFAt c₂.nmem (c₂.nreg (sw 3)) N₁ := hNT.nfAt
  have hA0 := arcs_pos hP₁ hNF
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT hNF hA0
  obtain ⟨-, -, hTB, -⟩ := win_tab E hI₂
  
  have hAc := hI₂.hA
  refine IRS.seq (arcS_irs hI₂ (E.hK.fix hI₂) hNF hNA (by omega) (by omega) (by omega) ho2) ?_
  rintro c₃ hI₃ - - ⟨r1, r2, r3, r4, k3, m3⟩
  have e3 : ∀ q, 240000 ≤ q → q < 250000 → q ≠ wO → q ≠ wT → q ≠ wA → q ≠ wR → q ≠ wEE →
      q ≠ wEH → c₃.nreg q = c₁.nreg q := fun q h1 h2 h3 h4 h5 h6 h7 h8 => by
    ram_grind
  have eO3 : c₃.nreg wO = c₂.nreg wO := k3 _ (by rne) (by rne) (by rne) (by rne) (by rne)
  -- the chord count
  refine IRS.seq (win_irs_load hI₃ (iscr_sw' (i := 3012) (by norm_num) (by norm_num))) ?_
  rintro c₄ hI₄ - - ⟨v4, k4, m4⟩
  have e4 : ∀ q, (q = wE1 ∨ q = kH ∨ q = wD) → c₄.nreg q = c₁.nreg q := by
    intro q hq
    have hq' : 240000 ≤ q ∧ q < 250000 ∧ q ≠ wO ∧ q ≠ wT ∧ q ≠ wA ∧ q ≠ wR ∧ q ≠ wEE ∧
        q ≠ wEH ∧ q ≠ wCh := by
      rcases hq with h | h | h <;> subst h <;>
        omega_nf 
    grind
  have hE4 : c₄.nreg wE1 = ke₁ J (c.nreg kE) := by grind
  have hH4 : c₄.nreg kH = c.nreg kH := by grind
  have hD4 : c₄.nreg wD = kd J (c.nreg kE) := by grind
  have hO4 : c₄.nreg wO = c₂.nreg wO := by rw [k4 _ (by rne), eO3]
  have s3 : c₃.nreg (sw 3) = c₂.nreg (sw 3) :=
    k3 _ (by rne) (by rne) (by rne) (by rne) (by rne)
  have hch : c₄.nreg wCh = N₁.chords.length := by rw [v4, s3, m3]; exact hNA.1
  have a4 : c₄.nreg ALLOC = c.nreg ALLOC := by
    rw [k4 _ (by rne), k3 _ (by rne) (by rne) (by rne) (by rne) (by rne), a2]
  
  -- the body
  have hpx4 : ProperPos (chainModel J.left) (Qof P) P.n ⟨c₄.nreg wE1, c₄.nreg kH⟩ := by
    ram_grind
  have h6x : c₄.nreg kH = 0 → 6 ≤ c₄.nreg wE1 := by
    rw [hE4, hH4]; exact key6 hP hpw hL
  have hkey : (⟨c₄.nreg wE1, c₄.nreg kH⟩ : WPos) = ⟨c₁.nreg wE1, c₁.nreg kH⟩ := by
    ram_grind
  have hl1' := hl1
  have hl2' := hl2
  rw [← hkey, ← hO4] at hl1' hl2'
  have har4 : ArcRegs N₁ c₄ (c₄.nreg wO) := by
    rw [hO4]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [k4 _ (by rne), r1]
    · rw [k4 _ (by rne), r2]
    · rw [k4 _ (by rne), r3]
    · rw [k4 _ (by rne), r4]
  have hnoA : bandOf ALLOC ∉ oracleBands := fun h => alloc_not_io (oracle_sub h)
  have hwA : ¬ WR ALLOC := by omega_nf
  refine IRS.seq (bodyS_irs E hI₄ (by rw [hE4]; exact Nat.mod_lt _ hn₁) hpx4 h6x
    (by omega) har4 hl1' hl2' hch (win_room_body hroom hcost a4)) ?_
  rintro c₅ hI₅ - - ⟨o', ho', ⟨w1, w2, w3, w4⟩, hne5, hemp5, k5, m5⟩
  have hR : c₅.nreg wR < N₁.nRegions := by
    rw [w2]; exact (arc_mem_region hNF (NFLoc.seq_lt hNF ho')).1
  have a5 : c₅.nreg ALLOC = c.nreg ALLOC := by grind
  have hGM : GoodModel (chainModel J.left) := Or.inl ⟨J.left, hP₁, rfl⟩
  have hgk := gatherK_single_le (walkAx_of_goodModel hGM) hNF E.hdeg₁ hR
  refine (gatherS_irs E hI₅ hR (by omega)).mono (by omega) ?_
  rintro c₆ ⟨g1, g2, g3, g4, g5, g6⟩
  have ng : ∀ q, (q = wX ∨ q = wE ∨ q = wH) → ¬ GathW q := by
    intro q hq h'
    unfold GathW GSet at h'
    rcases hq with h | h | h <;> subst h <;>
      simp only [wX, wE, wH, gL, gC, gNF, wGB, wGK, sw] at h' <;> omega
  have kg : ∀ q, (q = wX ∨ q = wE ∨ q = wH) → c₆.nreg q = c₅.nreg q := by
    intro q hq
    have h1 : 240000 ≤ q ∧ q < 250000 ∧ q ≠ ALLOC := by
      rcases hq with h | h | h <;> subst h <;> omega_nf 
    exact g6 q (not_oracle_sw h1.1 h1.2.1) (ng q hq) h1.2.2
  have hx4 : (chainModel J.left).key (Qof P) ⟨c₄.nreg wE1, c₄.nreg kH⟩ =
      (chainModel J.left).key (Qof P) ⟨ke₁ J (c.nreg kE), c.nreg kH⟩ := by ram_grind
  have hu4 : (⟨c₄.nreg wE1, c₄.nreg kH⟩ : WPos) = ⟨ke₁ J (c.nreg kE), c.nreg kH⟩ := by
    ram_grind
  rw [hx4, hu4, hD4] at hne5
  obtain ⟨wm1, wm2, wm3⟩ := win_math E hpw hL ho' (c' := c₆)
    (fun hF => ⟨(hne5 hF).1, (hne5 hF).2.congr (kg _ (by simp)) (kg _ (by simp)) (kg _ (by simp))⟩)
    (fun hF => by rw [kg _ (by simp)]; ram_grind)
    (by ram_grind)
  rw [← w2] at wm3
  refine ⟨[c₅.nreg wR], by simp, fun r hr => by rw [List.mem_singleton.1 hr]; exact hR, g2,
    by omega, g3, g4, wm1, wm2, wm3, fun a ha => ?_, fun r hr hw hra => ?_⟩
  · ram_simp
  · rw [g6 r hr (fun h => hw (wr_of_gathW h)) hra, k5 r hr hw,
      k4 r (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))),
      k3 r (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))) (ne_of_wr hw (wr_sw (by norm_num) (by norm_num)))
        (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))) (ne_of_wr hw (wr_sw (by norm_num) (by norm_num)))
        (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))),
      k2 r hr (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))),
      o1 r (ne_of_wr hw (wr_sw (by norm_num) (by norm_num))) (ne_of_wr hw (wr_sw (by norm_num) (by norm_num)))]


end

end SweepEv

end Chazelle.Core
