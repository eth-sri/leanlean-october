module

public import Chazelle.Golf

public import Chazelle.Core.OracleRamPos

/-!
# Lemma 3.6 (WP-H), RAM part 13: the candidates and their clusters

`candS rP` locates the walk position `(w, hz + 1)` (`w` in register `rP`) with `myLoc`: a spine
position `p`; then it scans the clusters of the candidate nodes `p`, `succP A p`, `predP A p`
with `clusS`.  Main result: `candS_exec`.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ
open Chazelle.Chain (sideInArc)

@[expose] public section

/-- **Locate the position in `rP` and scan the clusters of its candidates.** -/
def candS (rP : ℕ) : Stmt :=
  .seq (block [.copyN 50000 120040, .copyN 50001 120014, .copyN 50002 rP, .addN 50003 120023 120011])
    (.seq myLoc
      (.seq (.instr (.copyN 120110 120170))
        (.seq clusS
          (.seq (.seq (block [.copyN 120186 120170, .addN 120110 120186 120011])
              (.ifLtN 120110 120030 .skip (.instr (.constN 120110 0))))
            (.seq clusS
              (.seq (.ifLtN 120012 120186 (.instr (.subN 120110 120186 120011))
                  (.instr (.subN 120110 120030 120011)))
                clusS))))))

/-- **The memory facts of double identification.** -/
structure LocMemOK (P : Polygon) (V : QV) (m : ℕ → ℕ) (W : ℕ) (M : Model) (N : NF) : Prop where
  md : ModelDescAt m V.MD (Qof P) M
  good : GoodModel M
  md_le : V.MD + 6 ≤ W
  chwf : LocChainWF P W m V.MD
  nf : NFAt m V.NB N
  isNF : IsNF M (Qof P) N
  A : V.A = N.arcs.length
  st : ∀ j, j < N.arcs.length → ProperPos M (Qof P) P.n (N.arc j).s
  tab : ∀ j, j < V.L → m (V.TB + j) = 2 ^ j
  A_lt : V.A < 2 ^ V.L
  NB_le : V.NB + 7 ≤ V.TB
  AB_le : m (V.NB + 4) + 5 * V.A ≤ V.TB
  SB_le : m (V.NB + 6) + V.A ≤ V.TB
  TB_le : V.TB + V.L ≤ W
  A_le : V.A ≤ V.μ

/-- The registers written by `candS`. -/
def BCa (r : ℕ) : Bool := BL r || BC r || decide (r = 120110) || decide (r = 120186)

/-- The cluster scans of the three candidates of a spine position. -/
def clusPts3 (m : ℕ → ℕ) (V : QV) (C : Chain) (p : ℕ) : Set Point :=
  clusPts m V C (lab m V p) ∪ clusPts m V C (lab m V (succP V.A p)) ∪
    clusPts m V C (lab m V (predP V.A p))

open Classical in
/-- **Locate the position and scan the clusters of its candidates.** -/
theorem candS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hb : BestOK P.n V.s V.m c)
    (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W) {M : Model} {N : NF}
    (hL : LocMemOK P V c.nmem W M N) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V (lab c.nmem V u) ≤ CS) {rP : ℕ}
    (hrP : 120160 ≤ rP ∧ rP ≤ 120163) (hwn : c.nreg rP < M.W.n)
    (hx : ProperPos M (Qof P) P.n ⟨c.nreg rP, V.hz + 1⟩) {S : Set Point}
    (hS : Sweep.FirstHitOpt S z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c))) :
    ∃ c' k p, Exec P W (candS rP) c c' k ∧ k ≤ 5500 * (V.L + 1) + 3 * ((CS + 2) * (NC + 80)) + 30 ∧
      FrameB BCa c c' ∧ BestOK P.n V.s V.m c' ∧ p < V.A ∧
      (¬ M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨c.nreg rP, V.hz + 1⟩) →
        N.F M (Qof P) = ∅ ∨ sideInArc (M.key (Qof P) (N.arc (N.seq.getD p 0)).s)
          (M.key (Qof P) (N.arc (N.seq.getD p 0)).e) (M.key (Qof P) ⟨c.nreg rP, V.hz + 1⟩)) ∧
      (M.IsCut (N.F M (Qof P)) (M.key (Qof P) ⟨c.nreg rP, V.hz + 1⟩) →
        M.key (Qof P) (N.arc (N.seq.getD p 0)).s = M.key (Qof P) ⟨c.nreg rP, V.hz + 1⟩ ∨
          M.key (Qof P) (N.arc (N.seq.getD p 0)).e = M.key (Qof P) ⟨c.nreg rP, V.hz + 1⟩) ∧
      Sweep.FirstHitOpt (S ∪ clusPts3 c.nmem V C p) z (sgnOf V.σb)
        (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) := by
  have hv := hs.hv
  have hn := hv.hz_lt
  -- 1. the inputs of double identification
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 50000 120040, .copyN 50001 120014,
      .copyN 50002 rP, .addN 50003 120023 120011]) c c₁ k₁ ∧ k₁ = 4 ∧
      (c₁.nreg 50000 = V.MD ∧ c₁.nreg 50001 = V.NB ∧ c₁.nreg 50002 = c.nreg rP ∧
        c₁.nreg 50003 = V.hz + 1 ∧ (∀ r, r < 50000 ∨ 50003 < r → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem) := by
    have q40 := hq.MD
    have q14 := hq.NB
    have q23 := hq.hz
    have q11 := hq.one
    exec_block
    · config_simp; rw [hq.hz, hq.one]; omega
    · refine ⟨rfl, by config_simp; exact hq.MD, by config_simp; exact hq.NB, ?_, ?_,
        fun r hr => by config_simp; upd_solve, rfl⟩
      · config_simp; ((try simp only [Machine.upd_apply]); (repeat' split_ifs) <;> first | omega)
      · config_simp; rw [hq.hz, hq.one]
  obtain ⟨x50000, x50001, x50002, x50003, r₁, m₁⟩ := v₁
  have hq₁ : QConst P V c₁ := hq.congr fun r h1 h2 => r₁ r (⋄)
  have hm₁ := m₁
  -- 2. double identification
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hp₂, hloc1, hloc2⟩ := myLoc_exec hcov (P := P) (W := W) (c := c₁)
    e₁.wb_right ⟨hG, ⋄, by rw [x50000]; exact hL.md_le, by rw [x50000, hm₁]; exact hL.chwf,
      M, by rw [x50000, hm₁]; exact hL.md, by rw [x50002]; exact hwn⟩ hG (⋄)
    (by rw [x50000, hm₁]; exact hL.md) hL.good (by rw [x50001, hm₁]; exact hL.nf) hL.isNF
    (by rw [x50002, x50003]; exact hx) hL.st hq₁.TB hq₁.L hq₁.zero hq₁.one
    (fun j hj => by rw [hm₁]; exact hL.tab j hj) (by rw [← hL.A]; exact hL.A_lt)
    (by rw [x50001]; exact hL.NB_le) (by rw [x50001, hm₁, ← hL.A]; exact hL.AB_le)
    (by rw [x50001, hm₁, ← hL.A]; exact hL.SB_le) hL.TB_le
  rw [x50002, x50003] at hloc1 hloc2
  have hBLc : ∀ r, 120010 ≤ r → r ≤ 120049 → BL r = false := fun r h1 h2 => by
    simp only [BL, Bdir, Bloc, Bcmp, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ hBLc
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans hm₁
  obtain ⟨p, hp⟩ : ∃ p, c₂.nreg 120170 = p := ⟨_, rfl⟩
  rw [hp] at hp₂ hloc1 hloc2
  have hpA : p < V.A := by rw [hL.A]; exact hp₂
  have hpμ : p < V.μ := by have := hL.A_le; omega
  have hBL5 : ∀ r, (r = 120050 ∨ r = 120051 ∨ r = 120052) → BL r = false := fun r hr => by
    rcases hr with rfl | rfl | rfl <;> decide
  have hb₂ : BestOK P.n V.s V.m c₂ := by
    unfold BestOK
    rw [f₂.1 _ (hBL5 _ (✓)), f₂.1 _ (hBL5 _ (by simp)), f₂.1 _ (hBL5 _ (by simp)),
      r₁ _ (⋄), r₁ _ (by omega), r₁ _ (by omega)]
    exact hb
  have hbo₂ : bestOf c₂ = bestOf c := by
    unfold bestOf
    rw [f₂.1 _ (hBL5 _ (✓)), f₂.1 _ (hBL5 _ (by simp)), r₁ _ (by omega), r₁ _ (by omega)]
  -- 3. the cluster of `p`
  obtain ⟨c₃, e₃, v₃, r₃⟩ := copy_exec (P := P) e₂.wb_right 120110 120170
  rw [hp] at v₃
  have hq₃ : QConst P V c₃ := hq₂.congr fun r h1 h2 => r₃ r (⋄)
  have hm₃ : c₃.nmem = c.nmem := by
    rw [← m₂]; exact (exec_frameB e₃ (B := fun r => decide (r = 120110)) (⌖)).2.2.1
  have hb₃ : BestOK P.n V.s V.m c₃ := by
    unfold BestOK; rw [r₃ 120050 (⌖), r₃ 120051 (by decide), r₃ 120052 (by decide)]; exact hb₂
  have hbo₃ : bestOf c₃ = bestOf c := by
    unfold bestOf; rw [r₃ 120050 (⌖), r₃ 120052 (by decide)]; exact hbo₂
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hb₄, hit₄⟩ := clusS_exec (P := P) hG hW hs c₃ e₃.wb_right hq₃ hb₃
    (by rw [hm₃]; exact hm) (by rw [hm₃]; exact hO) (by rw [v₃]; exact hpμ) (NC := NC)
    (fun u hu => by rw [hm₃]; exact hNC u hu) (S := S) (by rw [hbo₃]; exact hS)
  rw [v₃, hm₃] at hk₄ hit₄
  have hq₄ : QConst P V c₄ := hq₃.frame f₄ BC_const
  have hm₄ : c₄.nmem = c.nmem := f₄.2.2.1.trans hm₃
  have x170 : c₄.nreg 120170 = p := (f₄.1 _ (⌖)).trans ((r₃ _ (by decide)).trans hp)
  -- 4. the cluster of the successor
  obtain ⟨c₅, k₅, e₅, hk₅, v₅⟩ : ∃ c₅ k₅, Exec P W (.seq (block [.copyN 120186 120170,
      .addN 120110 120186 120011]) (.ifLtN 120110 120030 .skip (.instr (.constN 120110 0)))) c₄ c₅ k₅ ∧
      k₅ ≤ 5 ∧ (c₅.nreg 120110 = succP V.A p ∧ c₅.nreg 120186 = p ∧
        (∀ r, r ≠ 120110 → r ≠ 120186 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
        c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output) := by
    have w₄ := e₄.wb_right
    obtain ⟨d₁, k₁', e₁', hk₁', q⟩ : ∃ d₁ k₁', Exec P W (block [.copyN 120186 120170,
        .addN 120110 120186 120011]) c₄ d₁ k₁' ∧ k₁' = 2 ∧ (d₁.nreg 120110 = p + 1 ∧
          d₁.nreg 120186 = p ∧ (∀ r, r ≠ 120110 → r ≠ 120186 → d₁.nreg r = c₄.nreg r) ∧
          d₁.nmem = c₄.nmem ∧ d₁.rreg = c₄.rreg ∧ d₁.rmem = c₄.rmem ∧ d₁.output = c₄.output) := by
      exec_block
      · config_simp; rw [x170, hq₄.one]; have := hL.A_le; have := hO.μ_le; omega
      · refine ⟨rfl, ?_, ?_, fun r h1 h2 => by config_simp; upd_solve, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [x170, hq₄.one]
        · config_simp; exact x170
    obtain ⟨q110, q186, qr, qm, qrr, qrm, qo⟩ := q
    have hqA : d₁.nreg 120030 = V.A := (qr _ (⌖) (by decide)).trans hq₄.A
    by_cases hs1 : p + 1 < V.A
    · refine ⟨d₁, _, .seq e₁' (.ifLtN_true (by rw [q110, hqA]; exact hs1) (.skip e₁'.wb_right)),
        ⋄, ?_, q186, qr, qm, qrr, qrm, qo⟩
      rw [q110]; unfold succP; rw [ite_eq_left hs1]
    · obtain ⟨d₂, e₂', v₂', r₂'⟩ := const_exec (P := P) e₁'.wb_right 120110 0 (⋄)
      have f₂' := exec_frameB e₂' (B := fun r => decide (r = 120110)) (⌖)
      refine ⟨d₂, _, .seq e₁' (.ifLtN_false (by rw [q110, hqA]; exact hs1) e₂'), ⋄, ?_,
        by rw [r₂' _ (⌖)]; exact q186, fun r h1 h2 => by rw [r₂' r h1]; exact qr r h1 h2,
        f₂'.2.2.1.trans qm, by rw [show d₂.rreg = d₁.rreg from funext fun r =>
          exec_rframe e₂' (B := fun _ => false) (⌖) r rfl]; exact qrr,
        f₂'.2.2.2.1.trans qrm, f₂'.2.2.2.2.trans qo⟩
      rw [v₂']; unfold succP; rw [ite_eq_right hs1]
  obtain ⟨v110, v186, r₅, m₅, rr₅, rm₅, o₅⟩ := v₅
  have hq₅ : QConst P V c₅ := hq₄.congr fun r h1 h2 => r₅ r (⋄) (by omega)
  have hm₅ : c₅.nmem = c.nmem := m₅.trans hm₄
  have hb₅ : BestOK P.n V.s V.m c₅ := by
    unfold BestOK
    rw [r₅ 120050 (⌖) (by decide), r₅ 120051 (by decide) (by decide),
      r₅ 120052 (⌖) (by decide)]
    exact hb₄
  have hbo₅ : bestOf c₅ = bestOf c₄ := by
    unfold bestOf; rw [r₅ 120050 (⌖) (by decide), r₅ 120052 (by decide) (by decide)]
  have hsμ : succP V.A p < V.μ := by have := succP_lt hpA; have := hL.A_le; omega
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, hb₆, hit₆⟩ := clusS_exec (P := P) hG hW hs c₅ e₅.wb_right hq₅ hb₅
    (by rw [hm₅]; exact hm) (by rw [hm₅]; exact hO) (by rw [v110]; exact hsμ) (NC := NC)
    (fun u hu => by rw [hm₅]; exact hNC u hu)
    (S := S ∪ clusPts c.nmem V C (lab c.nmem V p)) (by rw [hbo₅]; exact hit₄)
  rw [v110, hm₅] at hk₆ hit₆
  have hq₆ : QConst P V c₆ := hq₅.frame f₆ BC_const
  have hm₆ : c₆.nmem = c.nmem := f₆.2.2.1.trans hm₅
  have x186 : c₆.nreg 120186 = p := (f₆.1 _ (⌖)).trans v186
  -- 5. the cluster of the predecessor
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, r₇, m₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 120012 120186
      (.instr (.subN 120110 120186 120011)) (.instr (.subN 120110 120030 120011))) c₆ c₇ k₇ ∧
      k₇ ≤ 3 ∧ c₇.nreg 120110 = predP V.A p ∧ (∀ r, r ≠ 120110 → c₇.nreg r = c₆.nreg r) ∧
      c₇.nmem = c₆.nmem := by
    have w₆ := e₆.wb_right
    by_cases h0 : 0 < p
    · refine ⟨_, _, .ifLtN_true (by rw [hq₆.zero, x186]; exact h0) (Exec.subN w₆ _ _ _), ⋄,
        ?_, fun r hr => by config_simp; upd_solve, rfl⟩
      config_simp; rw [x186, hq₆.one]; unfold predP; rw [ite_eq_right (⋄)]
    · refine ⟨_, _, .ifLtN_false (by rw [hq₆.zero, x186]; exact h0) (Exec.subN w₆ _ _ _), ⋄,
        ?_, fun r hr => by config_simp; upd_solve, rfl⟩
      config_simp; rw [hq₆.A, hq₆.one]; unfold predP; rw [ite_eq_left (⋄)]
  have hq₇ : QConst P V c₇ := hq₆.congr fun r h1 h2 => r₇ r (⋄)
  have hm₇ : c₇.nmem = c.nmem := m₇.trans hm₆
  have hb₇ : BestOK P.n V.s V.m c₇ := by
    unfold BestOK
    rw [r₇ 120050 (⌖), r₇ 120051 (by decide), r₇ 120052 (by decide)]
    exact hb₆
  have hbo₇ : bestOf c₇ = bestOf c₆ := by
    unfold bestOf; rw [r₇ 120050 (⌖), r₇ 120052 (by decide)]
  have hpμ' : predP V.A p < V.μ := by have := predP_lt hpA; have := hL.A_le; omega
  obtain ⟨c₈, k₈, e₈, hk₈, f₈, hb₈, hit₈⟩ := clusS_exec (P := P) hG hW hs c₇ e₇.wb_right hq₇ hb₇
    (by rw [hm₇]; exact hm) (by rw [hm₇]; exact hO) (by rw [v₇]; exact hpμ') (NC := NC)
    (fun u hu => by rw [hm₇]; exact hNC u hu)
    (S := S ∪ clusPts c.nmem V C (lab c.nmem V p) ∪ clusPts c.nmem V C (lab c.nmem V (succP V.A p)))
    (by rw [hbo₇]; exact hit₆)
  rw [v₇, hm₇] at hk₈ hit₈
  -- the frame
  have ex : Exec P W (candS rP) c c₈ (k₁ + (k₂ + (1 + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))))))
  have f₁ := exec_frameB e₁ (B := fun r => decide (50000 ≤ r ∧ r ≤ 50003))
    (⊚ block, wr, wrOK)
  have f₃ := exec_frameB e₃ (B := fun r => decide (r = 120110)) (⌖)
  have f₅ := exec_frameB e₅ (B := fun r => decide (r = 120110) || decide (r = 120186)) (⌖)
  have f₇ := exec_frameB e₇ (B := fun r => decide (r = 120110)) (⌖)
  have fr : FrameB BCa c c₈ := by
    have g1 : FrameB BCa c c₁ := FrameB.mono f₁ fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [BCa, BL, Bloc]; omega
    have g2 : FrameB BCa c₁ c₂ := FrameB.mono f₂ fun r hr => ⊚ BCa, hr
    have g3 : FrameB BCa c₂ c₃ := FrameB.mono f₃ fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [BCa, hr]
    have g4 : FrameB BCa c₃ c₄ := FrameB.mono f₄ fun r hr => ⊚ BCa, hr
    have g5 : FrameB BCa c₄ c₅ := FrameB.mono f₅ fun r hr => by
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with hr | hr <;> simp [BCa, hr]
    have g6 : FrameB BCa c₅ c₆ := FrameB.mono f₆ fun r hr => ⊚ BCa, hr
    have g7 : FrameB BCa c₆ c₇ := FrameB.mono f₇ fun r hr => by
      simp only [decide_eq_true_eq] at hr; simp [BCa, hr]
    have g8 : FrameB BCa c₇ c₈ := FrameB.mono f₈ fun r hr => ⊚ BCa, hr
    exact g1.trans (g2.trans (g3.trans (g4.trans (g5.trans (g6.trans (g7.trans g8))))))
  refine ⟨c₈, _, p, ex, ?_, fr, hb₈, hpA, hloc1, hloc2, ?_⟩
  · have a4 := hCS p hpμ
    have a6 := hCS _ hsμ
    have a8 := hCS _ hpμ'
    have b4 : (clusSize c.nmem V (lab c.nmem V p) + 2) * (NC + 80) ≤ (CS + 2) * (NC + 80) :=
      Nat.mul_le_mul_right _ (⋄)
    have b6 : (clusSize c.nmem V (lab c.nmem V (succP V.A p)) + 2) * (NC + 80) ≤
        (CS + 2) * (NC + 80) := Nat.mul_le_mul_right _ (⋄)
    have b8 : (clusSize c.nmem V (lab c.nmem V (predP V.A p)) + 2) * (NC + 80) ≤
        (CS + 2) * (NC + 80) := Nat.mul_le_mul_right _ (⋄)
    omega
  · unfold clusPts3
    Ξ ← Set.union_assoc, ← Set.union_assoc
    exact hit₈

end

end OracleR

end Chazelle.Core
