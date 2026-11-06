module

public import Chazelle.Golf

public import Chazelle.Core.OracleRamCand

/-!
# Lemma 3.6 (WP-H), RAM part 14: the main phase of the query

`mainS` (the ray does not start along a chord): scan the nodes of `D*`, choose the stopping
point, compute its walk positions, locate them and scan the clusters of the candidates, and
output the best hit (`120005` flag, `120006` edge of `Q`).  Main result: `mainS_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- **The main phase.** -/
def mainS : Stmt :=
  .seq (.instr (.constN 120050 0))
    (.seq dstarS (.seq tchS (.seq posS (.seq (candS 120160) (.seq (candS 120161)
      (.seq (candS 120162) (.seq (candS 120163) (block [.copyN 120005 120050,
        .copyN 120006 120051]))))))))

/-- The `k`-th walk edge of the stopping point. -/
def posK (q : ℕ × ℕ × ℕ × ℕ) : ℕ → ℕ
  | 0 => q.1
  | 1 => q.2.1
  | 2 => q.2.2.1
  | _ => q.2.2.2

/-- The comparison of the chord's near end and the hit on `D*` (in the program's sense). -/
def CBof (P : Polygon) (C : Chain) (V : QV) (bD : Option ℕ) (near : ℕ) : Prop :=
  match bD with
  | some cD => if V.σb = 1 then EndLtD P C V (eIdx P.n V.s cD) near V.hz
      else EndGtD P C V (eIdx P.n V.s cD) near V.hz
  | none => False

/-- **The locate facts** for the walk position `(w, hz + 1)` and the answer `p`. -/
def LocFacts (P : Polygon) (M : Model) (N : NF) (hz w p : ℕ) : Prop :=
  (¬ M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨w, hz + 1⟩) →
    N.F M (Qof P) = ∅ ∨ sideInArc (M.key (Qof P) (N.arc (N.seq.getD p 0)).s)
      (M.key (Qof P) (N.arc (N.seq.getD p 0)).e) (M.key (Qof P) ⟨w, hz + 1⟩)) ∧
  (M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨w, hz + 1⟩) →
    M.key (Qof P) (N.arc (N.seq.getD p 0)).s = M.key (Qof P) ⟨w, hz + 1⟩ ∨
      M.key (Qof P) (N.arc (N.seq.getD p 0)).e = M.key (Qof P) ⟨w, hz + 1⟩)

/-- The registers written by `mainS`. -/
def BMain (r : ℕ) : Bool :=
  BD r || BT r || BPo r || BCa r || decide (r = 120005) || decide (r = 120006) || decide (r = 120050)

open Classical in
/-- The choice of `tchS` with the registers' comparison is the choice with `CBof`. -/
theorem selOf_cb {P : Polygon} {C : Chain} {V : QV} {c : Config} (hb : BestOK P.n V.s V.m c)
    (found : Prop) (near : ℕ) :
    selOf C V (bestOf c) found near
        (if V.σb = 1 then EndLtD P C V (c.nreg 120051) near V.hz
          else EndGtD P C V (c.nreg 120051) near V.hz) =
      selOf C V (bestOf c) found near (CBof P C V (bestOf c) near) := by
  unfold selOf
  by_cases hf : c.nreg 120050 = 1
  · have hbo : bestOf c = some (c.nreg 120052) := by unfold bestOf; rw [ite_eq_left hf]
    have he := (hb.2 hf).1
    Ξ hbo
    unfold CBof
    Ξ he
  · have hbo : bestOf c = none := by unfold bestOf; rw [ite_eq_right hf]
    Ξ hbo
    simp

/-- The cost of one locate-and-clusters step. -/
def candCost (V : QV) (NC CS : ℕ) : ℕ := 5500 * (V.L + 1) + 3 * ((CS + 2) * (NC + 80)) + 30

theorem BCa_main {r : ℕ} (h : BCa r = true) : BMain r = true := ⊚ BMain, h

open Classical in
/-- **The main phase of the query.** -/
theorem mainS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    {N : NF} (hL : LocMemOK P V c.nmem W (chainModel C) N) (hDL : V.DL + V.nD ≤ W)
    (htv : V.tv < P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V (lab c.nmem V u) ≤ CS)
    (hf : c.nreg 120140 ≤ 1)
    (hvalid : ∀ bD : Option ℕ,
      Sweep.FirstHitOpt (dstarPts c.nmem V C V.nD) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD) → (∀ cb, bD = some cb → cb < V.m) →
      ∀ k, k < 4 →
        posK (posOf V P.n (selOf C V bD (c.nreg 120140 = 1) (c.nreg 120141)
          (CBof P C V bD (c.nreg 120141)))) k < (chainModel C).W.n ∧
        ProperPos (chainModel C) (Qof P) P.n ⟨posK (posOf V P.n (selOf C V bD (c.nreg 120140 = 1)
          (c.nreg 120141) (CBof P C V bD (c.nreg 120141)))) k, V.hz + 1⟩) :
    ∃ c' k bD, Exec P W mainS c c' k ∧
      k ≤ dstarCost c.nmem V + 4 * candCost V NC CS + 500 ∧ FrameB BMain c c' ∧
      Sweep.FirstHitOpt (dstarPts c.nmem V C V.nD) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD) ∧ (∀ cb, bD = some cb → cb < V.m) ∧
      ∃ pk : ℕ → ℕ, (∀ k, k < 4 → pk k < V.A ∧ LocFacts P (chainModel C) N V.hz
          (posK (posOf V P.n (selOf C V bD (c.nreg 120140 = 1) (c.nreg 120141)
            (CBof P C V bD (c.nreg 120141)))) k) (pk k)) ∧
        Sweep.FirstHitOpt (dstarPts c.nmem V C V.nD ∪ clusPts3 c.nmem V C (pk 0) ∪
            clusPts3 c.nmem V C (pk 1) ∪ clusPts3 c.nmem V C (pk 2) ∪ clusPts3 c.nmem V C (pk 3))
          z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) ∧
        BestOK P.n V.s V.m c' ∧ c'.nreg 120005 = c'.nreg 120050 ∧
        c'.nreg 120006 = c'.nreg 120051 := by
  have hv := hs.hv
  -- 1. no hit yet
  obtain ⟨c₁, e₁, v₁, r₁⟩ := const_exec (P := P) hw 120050 0 (⋄)
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (⋄)
  have m₁ : c₁.nmem = c.nmem :=
    (exec_frameB e₁ (B := fun r => decide (r = 120050)) (⌖)).2.2.1
  have hbo₁ : bestOf c₁ = none := by unfold bestOf; rw [v₁]; simp
  have hb₁ : BestOK P.n V.s V.m c₁ := ⟨by rw [v₁]; omega, fun h => by rw [v₁] at h; omega⟩
  -- 2. the nodes of `D*`
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hb₂, hit₂⟩ := dstarS_exec (P := P) hG hW hs c₁ e₁.wb_right hq₁ hb₁
    (by rw [m₁]; exact hm) hDL (S := ∅) (by rw [hbo₁]; intro t _ h; exact h)
  rw [m₁, Set.empty_union] at hit₂
  rw [m₁] at hk₂
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ BD_const
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans m₁
  set bD := bestOf c₂ with hbD
  have hbDm : ∀ cb, bD = some cb → cb < V.m := by
    intro cb h
    unfold bestOf at hbD
    by_cases hfl : c₂.nreg 120050 = 1
    · rw [hbD, ite_eq_left hfl] at h; cases h; exact (hb₂.2 hfl).2
    · rw [hbD, ite_eq_right hfl] at h; exact absurd h (✓)
  have x140 : c₂.nreg 120140 = c.nreg 120140 := by
    rw [f₂.1 _ (⌖), r₁ _ (by decide)]
  have x141 : c₂.nreg 120141 = c.nreg 120141 := by
    rw [f₂.1 _ (⌖), r₁ _ (by decide)]
  -- 3. the stopping point
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, s₃⟩ := tchS_exec (P := P) hG hW hv htv c₂ e₂.wb_right hq₂
    (by rw [x140]; exact hf) hb₂
  rw [selOf_cb hb₂, x140, x141, ← hbD] at s₃
  set sel := selOf C V bD (c.nreg 120140 = 1) (c.nreg 120141) (CBof P C V bD (c.nreg 120141))
    with hsel
  have hq₃ : QConst P V c₃ := hq₂.frame f₃ fun r h1 h2 => by
    simp only [BT, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₃ : c₃.nmem = c.nmem := f₃.2.2.1.trans m₂
  have hsel01 : sel.1 = 0 ∨ sel.1 = 1 := by
    rw [hsel]; unfold selOf
    by_cases h : c.nreg 120140 = 1 ∧ (bD = none ∨ CBof P C V bD (c.nreg 120141))
    · rw [ite_eq_left h]; unfold chordSel; split_ifs <;> simp
    · rw [ite_eq_right h]; rcases bD with _ | cD <;> simp [boxSel]
  have hselm : sel.1 = 0 → sel.2 < V.m := by
    rw [hsel]; unfold selOf
    by_cases h : c.nreg 120140 = 1 ∧ (bD = none ∨ CBof P C V bD (c.nreg 120141))
    · rw [ite_eq_left h]; unfold chordSel
      split_ifs <;> simp <;> rw [hv.m] <;> exact tci_lt C _
    · Ξ ite_eq_right h
      rcases hbd : bD with _ | cD
      · Θ boxSel
      · simp only; intro _; exact hbDm cD hbd
  -- 4. the walk positions
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, v₄⟩ := posS_exec (P := P) hW hv c₃ e₃.wb_right hq₃ s₃ hsel01 hselm
  have hq₄ : QConst P V c₄ := hq₃.frame f₄ fun r h1 h2 => by
    simp only [BPo, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₄ : c₄.nmem = c.nmem := f₄.2.2.1.trans m₃
  have hvd := hvalid bD hit₂ hbDm
  rw [← hsel] at hvd
  set q := posOf V P.n sel with hqdef
  have xq : ∀ k, k < 4 → c₄.nreg (120160 + k) = posK q k := by
    intro k hk
    interval_cases k
    · exact congrArg Prod.fst v₄
    · exact congrArg (fun x => x.2.1) v₄
    · exact congrArg (fun x => x.2.2.1) v₄
    · exact congrArg (fun x => x.2.2.2) v₄
  -- the best-hit registers before the candidates
  have hBDbest : ∀ r, BT r = false → BPo r = false → c₄.nreg r = c₂.nreg r := fun r h1 h2 =>
    (f₄.1 r h2).trans (f₃.1 r h1)
  have hb₄ : BestOK P.n V.s V.m c₄ := by
    unfold BestOK
    rw [hBDbest 120050 (⌖) (by decide), hBDbest 120051 (by decide) (by decide),
      hBDbest 120052 (⌖) (by decide)]
    exact hb₂
  have hbo₄ : bestOf c₄ = bD := by
    unfold bestOf; rw [hBDbest 120050 (⌖) (by decide), hBDbest 120052 (by decide) (by decide)]
    rfl
  -- 5 – 8. the candidates
  have candStep : ∀ (k : ℕ), k < 4 → ∀ (d : Config), WordsBounded W d → QConst P V d →
      BestOK P.n V.s V.m d → d.nmem = c.nmem → d.nreg (120160 + k) = posK q k →
      ∀ (S : Set Point), Sweep.FirstHitOpt S z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf d)) →
      ∃ d' k' p, Exec P W (candS (120160 + k)) d d' k' ∧ k' ≤ candCost V NC CS ∧
        FrameB BCa d d' ∧ BestOK P.n V.s V.m d' ∧ p < V.A ∧
        LocFacts P (chainModel C) N V.hz (posK q k) p ∧
        Sweep.FirstHitOpt (S ∪ clusPts3 c.nmem V C p) z (sgnOf V.σb)
          (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf d')) := by
    intro k hk d hd hqd hbd hmd hpos S hS
    obtain ⟨hwn, hx⟩ := hvd k hk
    obtain ⟨d', k', p, ex, hk', fr, hb', hp, hl1, hl2, hit⟩ := candS_exec hcov (P := P) hG hW hs d hd
      hqd hbd (by rw [hmd]; exact hm) (by rw [hmd]; exact hO) (by rw [hmd]; exact hL)
      (NC := NC) (CS := CS) (fun u hu => by rw [hmd]; exact hNC u hu)
      (fun u hu => by rw [hmd]; exact hCS u hu) (rP := 120160 + k) (⋄)
      (by rw [hpos]; exact hwn) (by rw [hpos]; exact hx) hS
    rw [hpos] at hl1 hl2
    rw [hmd] at hit
    exact ⟨d', k', p, ex, hk', fr, hb', hp, ⟨hl1, hl2⟩, hit⟩
  have keepPos : ∀ (d d' : Config), FrameB BCa d d' → ∀ k, k < 4 →
      d'.nreg (120160 + k) = d.nreg (120160 + k) := fun d d' fr k hk =>
    fr.1 _ (by simp only [BCa, BL, BC, BN, BA, BW, BE, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega)
  have hBCac : ∀ r, 120010 ≤ r → r ≤ 120049 → BCa r = false := fun r h1 h2 => by
    simp only [BCa, BL, BC, BN, BA, BW, BE, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]; omega
  obtain ⟨c₅, k₅, p₀, e₅, hk₅, f₅, hb₅, hp₀, hl₀, hit₅⟩ := candStep 0 (⊛) c₄ e₄.wb_right hq₄
    hb₄ m₄ (xq 0 (⊛)) (dstarPts c.nmem V C V.nD) (by rw [hbo₄]; exact hit₂)
  have hq₅ := hq₄.frame f₅ hBCac
  have m₅ : c₅.nmem = c.nmem := f₅.2.2.1.trans m₄
  obtain ⟨c₆, k₆, p₁, e₆, hk₆, f₆, hb₆, hp₁, hl₁, hit₆⟩ := candStep 1 (⊛) c₅ e₅.wb_right hq₅
    hb₅ m₅ (by rw [keepPos c₄ c₅ f₅ 1 (⊛)]; exact xq 1 (by norm_num)) _ hit₅
  have hq₆ := hq₅.frame f₆ hBCac
  have m₆ : c₆.nmem = c.nmem := f₆.2.2.1.trans m₅
  obtain ⟨c₇, k₇, p₂, e₇, hk₇, f₇, hb₇, hp₂, hl₂, hit₇⟩ := candStep 2 (⊛) c₆ e₆.wb_right hq₆
    hb₆ m₆ (by rw [keepPos c₅ c₆ f₆ 2 (⊛), keepPos c₄ c₅ f₅ 2 (by norm_num)]; exact xq 2 (by norm_num)) _ hit₆
  have hq₇ := hq₆.frame f₇ hBCac
  have m₇ : c₇.nmem = c.nmem := f₇.2.2.1.trans m₆
  obtain ⟨c₈, k₈, p₃, e₈, hk₈, f₈, hb₈, hp₃, hl₃, hit₈⟩ := candStep 3 (⊛) c₇ e₇.wb_right hq₇
    hb₇ m₇ (by rw [keepPos c₆ c₇ f₇ 3 (⊛), keepPos c₅ c₆ f₆ 3 (by norm_num),
      keepPos c₄ c₅ f₅ 3 (⊛)]; exact xq 3 (by norm_num)) _ hit₇
  -- 9. the output
  have w₈ := e₈.wb_right
  obtain ⟨c₉, k₉, e₉, hk₉, v₉⟩ : ∃ c₉ k₉, Exec P W (block [.copyN 120005 120050, .copyN 120006 120051])
      c₈ c₉ k₉ ∧ k₉ = 2 ∧ (c₉.nreg 120005 = c₉.nreg 120050 ∧ c₉.nreg 120006 = c₉.nreg 120051 ∧
        ∀ r, r ≠ 120005 → r ≠ 120006 → c₉.nreg r = c₈.nreg r) := by
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => by config_simp; upd_solve⟩
  obtain ⟨o5, o6, r₉⟩ := v₉
  have hbo₉ : bestOf c₉ = bestOf c₈ := by
    unfold bestOf; rw [r₉ 120050 (⌖) (by decide), r₉ 120052 (by decide) (by decide)]
  have hb₉ : BestOK P.n V.s V.m c₉ := by
    unfold BestOK
    rw [r₉ 120050 (⌖) (by decide), r₉ 120051 (by decide) (by decide),
      r₉ 120052 (⌖) (by decide)]
    exact hb₈
  -- frames
  have ex : Exec P W mainS c c₉ (1 + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉)))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉)))))))
  have fr : FrameB BMain c c₉ := by
    have g1 : FrameB BMain c c₁ := FrameB.mono (exec_frameB e₁ (B := fun r => decide (r = 120050))
      (⌖)) fun r hr => by simp only [decide_eq_true_eq] at hr; simp [BMain, hr]
    have g2 : FrameB BMain c₁ c₂ := FrameB.mono f₂ fun r hr => ⊚ BMain, hr
    have g3 : FrameB BMain c₂ c₃ := FrameB.mono f₃ fun r hr => ⊚ BMain, hr
    have g4 : FrameB BMain c₃ c₄ := FrameB.mono f₄ fun r hr => ⊚ BMain, hr
    have g5 : FrameB BMain c₄ c₅ := FrameB.mono f₅ fun r hr => BCa_main hr
    have g6 : FrameB BMain c₅ c₆ := FrameB.mono f₆ fun r hr => BCa_main hr
    have g7 : FrameB BMain c₆ c₇ := FrameB.mono f₇ fun r hr => BCa_main hr
    have g8 : FrameB BMain c₇ c₈ := FrameB.mono f₈ fun r hr => BCa_main hr
    have g9 : FrameB BMain c₈ c₉ := FrameB.mono (exec_frameB e₉ (B := fun r => decide (r = 120005) ||
      decide (r = 120006)) (⌖)) fun r hr => by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with hr | hr <;> simp [BMain, hr]
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans (g8.trans g9)))))))
  refine ⟨c₉, _, bD, ex, ?_, fr, hit₂, hbDm, fun k => if k = 0 then p₀ else if k = 1 then p₁ else
    if k = 2 then p₂ else p₃, fun k hk => ?_, ?_, hb₉, o5, o6⟩
  · omega
  · interval_cases k
    · exact ⟨hp₀, hl₀⟩
    · exact ⟨hp₁, hl₁⟩
    · exact ⟨hp₂, hl₂⟩
    · exact ⟨hp₃, hl₃⟩
  · rw [hbo₉]; simpa using hit₈

end

end OracleR

end Chazelle.Core
