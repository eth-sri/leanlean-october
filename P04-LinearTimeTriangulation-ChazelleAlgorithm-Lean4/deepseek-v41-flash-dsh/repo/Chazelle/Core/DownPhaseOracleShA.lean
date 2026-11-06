module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleChR3

/-!
# WP-M (E7-B, RAM part 8): the boundary symbolic point of a chain-model hit

The interior shooter shoots at the chain arcs of a subarc with the chain shooter, which answers
with a position `⟨e, h⟩` (registers `140011`, `140012`) of the walk of the chain model.  `hsI`
turns it into the boundary symbolic point `hitSymV n cs L S v e h` of `Q` (`hitSym_ch`), in the
registers `170130 …` (kind, then one or two indices):

* `cvI`: `170136 := cVtxV n cs L S i` for `i` in `170134` (the vertex of `Q` at the walk
  vertex `6 + i`: `mod2` by two conditional subtractions, `sideE`, then `+ cs` modulo `n`);
* `hsI`: the top vertex `v` for the box and the slit, the vertex `a` of the walk vertex `e` if
  the height is its own, else the point of the edge of `Q` from `a` to the next vertex `a'`
  (`edgeOf`) at the height of `h - 1`.

Scratch: `170133 … 170140`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Chain (sideE)

@[expose] public section

/-! ## The programs -/

/-- `170136 := cVtxV n cs L S i` (`i` in `170134`). -/
def cvI : Stmt :=
  .seq (block [.addN 170136 170076 170134])
  (.seq (.ifLtN 170136 170089 .skip (block [.subN 170136 170136 170089]))
  (.seq (.ifLtN 170136 170089 .skip (block [.subN 170136 170136 170089]))
  (.seq (.ifLtN 170037 170136 (block [.subN 170136 170089 170136]) .skip)
  (.seq (block [.addN 170136 170038 170136])
    (.ifLtN 170136 170010 .skip (block [.subN 170136 170136 170010]))))))

/-- The vertex `v` (the top): kind `0`. -/
def vtxV : Stmt := block [.constN 170130 0, .copyN 170131 170079]

/-- The vertex `a` (`170137`): kind `0`. -/
def vtxA : Stmt := block [.constN 170130 0, .copyN 170131 170137]

/-- The edge point: the edge `edgeOf n a a'` and the height vertex `h - 1` (`170139`). -/
def onE : Stmt :=
  .seq (block [.addN 170140 170137 170011])
  (.seq (.ifLtN 170140 170010 .skip (block [.constN 170140 0]))
  (.seq (.ifLtN 170140 170138 (block [.copyN 170131 170138])
      (.ifLtN 170138 170140 (block [.copyN 170131 170138]) (block [.copyN 170131 170137])))
    (block [.constN 170130 1, .copyN 170132 170139])))

/-- The general case `6 ≤ e < 2 L + 6`. -/
def genI : Stmt :=
  .seq (block [.subN 170134 140011 170133]) (.seq cvI
  (.seq (block [.copyN 170137 170136, .addN 170134 170134 170011]) (.seq cvI
  (.seq (block [.copyN 170138 170136])
    (.ifLtN 170012 140012
      (.seq (block [.subN 170139 140012 170011])
        (.ifLtN 170139 170137 onE (.ifLtN 170137 170139 onE vtxA)))
      vtxA)))))

/-- **The boundary symbolic point of the hit** `⟨140011, 140012⟩` into `170130 …`. -/
def hsI : Stmt :=
  .seq (block [.constN 170133 6, .addN 170135 170089 170133])
    (.ifLtN 140011 170133 vtxV (.ifLtN 140011 170135 genI vtxV))

/-- The registers `hsI` writes. -/
def Bhs (r : ℕ) : Bool := decide (170130 ≤ r ∧ r < 170141)

theorem wr_hsI : wr Bhs hsI = true := ⌖

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ}

/-- The register facts `cvI` and `hsI` read. -/
structure HRegs (P : Polygon) (W : ℕ) (c : Config) (cs L S v : ℕ) : Prop where
  r10 : c.nreg 170010 = P.n
  r11 : c.nreg 170011 = 1
  r12 : c.nreg 170012 = 0
  r37 : c.nreg 170037 = L
  r38 : c.nreg 170038 = cs
  r76 : c.nreg 170076 = S
  r79 : c.nreg 170079 = v
  r89 : c.nreg 170089 = 2 * L
  hcs : cs < P.n
  hS : S ≤ 2 * L
  hL : 1 ≤ L
  hLn : L + 1 ≤ P.n
  hW : 256 * P.n + 16 ≤ W

theorem HRegs.keep {c c' : Config} {cs L S v : ℕ} (h : HRegs P W c cs L S v)
    (hk : ∀ r, Bhs r = false → c'.nreg r = c.nreg r) : HRegs P W c' cs L S v :=
  ⟨by rw [hk _ (⌖)]; exact h.r10, by rw [hk _ (by decide)]; exact h.r11,
    by rw [hk _ (⌖)]; exact h.r12, by rw [hk _ (by decide)]; exact h.r37,
    by rw [hk _ (⌖)]; exact h.r38, by rw [hk _ (by decide)]; exact h.r76,
    by rw [hk _ (⌖)]; exact h.r79, by rw [hk _ (by decide)]; exact h.r89, h.hcs, h.hS,
    h.hL, h.hLn, h.hW⟩

/-- A conditional subtraction `r := r - b` if `b ≤ r`. -/
theorem condSub_exec {c : Config} (hw : WordsBounded W c) (r b : ℕ) :
    ∃ k, Exec P W (.ifLtN r b .skip (block [.subN r r b])) c
      { c with nreg := upd c.nreg r (if c.nreg r < c.nreg b then c.nreg r else c.nreg r - c.nreg b) }
      k ∧ k ≤ 3 :=
  exec_ite_upd c (fun _ => ⟨0, exec_skip_upd hw r, ⋄⟩)
    (fun _ => ⟨1, exec_subN_upd hw r r b, le_rfl⟩)

/-- A conditional reflection `r := b - r` if `a < r`. -/
theorem condRef_exec {c : Config} (hw : WordsBounded W c) (r a b : ℕ) :
    ∃ k, Exec P W (.ifLtN a r (block [.subN r b r]) .skip) c
      { c with nreg := upd c.nreg r (if c.nreg a < c.nreg r then c.nreg b - c.nreg r else c.nreg r) }
      k ∧ k ≤ 3 :=
  exec_ite_upd c (fun _ => ⟨1, exec_subN_upd hw r b r, ⋄⟩)
    (fun _ => ⟨0, exec_skip_upd hw r, ⋄⟩)

/-- **The vertex of `Q` at a walk vertex of the double boundary.** -/
theorem cvI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {i : ℕ} (hi : c.nreg 170134 = i) (hi2 : i ≤ 2 * L) :
    ∃ k, Exec P W cvI c { c with nreg := upd c.nreg 170136 (cVtxV P.n cs L S i) } k ∧ k ≤ 18 := by
  have hW := hR.hW
  have hcs := hR.hcs
  have hS := hR.hS
  have hLn := hR.hLn
  have hL1 := hR.hL
  have e₀ := exec_addN_upd (P := P) hw 170136 170076 170134 (by rw [hR.r76, hi]; omega)
  obtain ⟨k₁, e₁, hk₁⟩ := condSub_exec (P := P) e₀.wb_right 170136 170089
  obtain ⟨k₂, e₂, hk₂⟩ := condSub_exec (P := P) e₁.wb_right 170136 170089
  obtain ⟨k₃, e₃, hk₃⟩ := condRef_exec (P := P) e₂.wb_right 170136 170037 170089
  config_simp at e₀
  config_simp at e₁
  config_simp at e₂
  config_simp at e₃
  simp only [hR.r76, hi, hR.r89, hR.r37] at e₀ e₁ e₂ e₃
  set j := if (if S + i < 2 * L then S + i else S + i - 2 * L) < 2 * L then
      (if S + i < 2 * L then S + i else S + i - 2 * L) else
      (if S + i < 2 * L then S + i else S + i - 2 * L) - 2 * L with hj
  have hjm : j = mod2 L (S + i) := by
    unfold mod2; rw [hj]; split_ifs <;> omega
  have hjL : (if L < j then 2 * L - j else j) = sideE L j := by
    unfold sideE; split_ifs <;> omega
  have hj2 : j < 2 * L := by rw [hjm, mod2_eq hR.hL (⋄)]; exact Nat.mod_lt _ (by omega)
  have hjE : sideE L j ≤ L := by unfold sideE; split_ifs <;> omega
  have e₄ := exec_addN_upd (P := P) e₃.wb_right 170136 170038 170136 (by
    config_simp; rw [hR.r38, hjL]; omega)
  config_simp at e₄
  rw [hR.r38, hjL] at e₄
  rw [hjL] at e₃
  obtain ⟨k₅, e₅, hk₅⟩ := condSub_exec (P := P) e₄.wb_right 170136 170010
  config_simp at e₅
  rw [hR.r10] at e₅
  have hval : (if cs + sideE L j < P.n then cs + sideE L j else cs + sideE L j - P.n) =
      cVtxV P.n cs L S i := by
    unfold cVtxV; rw [← hjm]
    split_ifs with h
    · Ξ Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (⋄), Nat.mod_eq_of_lt (by omega)]
  rw [hval] at e₅
  refine ⟨_, .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))), ⋄⟩

/-- The vertex `v`. -/
theorem vtxV_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W vtxV c c' k ∧ k = 2 ∧ SymPtIn c' 170130 (.vtx (c.nreg 170079)) := by
  unfold vtxV
  exec_block
  · omega
  exact ⟨rfl, by config_simp, by config_simp⟩

/-- The vertex `a`. -/
theorem vtxA_exec (c : Config) (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W vtxA c c' k ∧ k = 2 ∧ SymPtIn c' 170130 (.vtx (c.nreg 170137)) := by
  unfold vtxA
  exec_block
  · omega
  exact ⟨rfl, by config_simp, by config_simp⟩

/-- The choice of the edge of the edge point. -/
theorem onETail_exec (c : Config) (hw : WordsBounded W c) {a a' : ℕ} (h37 : c.nreg 170137 = a)
    (h38 : c.nreg 170138 = a') (h40 : c.nreg 170140 = (a + 1) % P.n) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (.seq (.ifLtN 170140 170138 (block [.copyN 170131 170138])
      (.ifLtN 170138 170140 (block [.copyN 170131 170138]) (block [.copyN 170131 170137])))
      (block [.constN 170130 1, .copyN 170132 170139])) c c' k ∧ k ≤ 7 ∧
      SymPtIn c' 170130 (.onEdge (ShootCut.edgeOf P.n (.vtx a) (.vtx a')) (c.nreg 170139)) := by
  refine spec_seq ?_
  set q := (a + 1) % P.n with hq
  by_cases hne : q = a'
  · have h1 : ¬ q < a' := ⋄
    have h2 : ¬ a' < q := ⋄
    refine spec_ifLtN_false (by rw [h38, h40]; exact h1) ?_
    refine spec_ifLtN_false (by rw [h38, h40]; exact h2) ?_
    exec_block
    · omega
    refine ⟨⋄, by config_simp, ?_, ?_⟩
    · config_simp; rw [h37]; simp only [ShootCut.edgeOf]; rw [ite_eq_left hne.symm]
    · config_simp
  · by_cases h1 : q < a'
    · refine spec_ifLtN_true (by rw [h38, h40]; exact h1) ?_
      exec_block
      · omega
      refine ⟨⋄, by config_simp, ?_, ?_⟩
      · config_simp; rw [h38]; simp only [ShootCut.edgeOf]; rw [ite_eq_right (⋄)]
      · config_simp
    · have h2 : a' < q := ⋄
      refine spec_ifLtN_false (by rw [h38, h40]; exact h1) ?_
      refine spec_ifLtN_true (by rw [h38, h40]; exact h2) ?_
      exec_block
      · omega
      refine ⟨⋄, by config_simp, ?_, ?_⟩
      · config_simp; rw [h38]; simp only [ShootCut.edgeOf]; rw [ite_eq_right (⋄)]
      · config_simp

/-- **The edge point.** -/
theorem onE_exec (c : Config) (hw : WordsBounded W c) {a a' : ℕ} (h37 : c.nreg 170137 = a)
    (h38 : c.nreg 170138 = a') (h10 : c.nreg 170010 = P.n) (h11 : c.nreg 170011 = 1)
    (ha : a < P.n) (hW : P.n + 1 ≤ W) :
    ∃ c' k, Exec P W onE c c' k ∧ k ≤ 12 ∧
      SymPtIn c' 170130 (.onEdge (ShootCut.edgeOf P.n (.vtx a) (.vtx a')) (c.nreg 170139)) := by
  unfold onE
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h37, h11]; omega
  refine spec_seq ?_
  by_cases hq1 : a + 1 < P.n
  · refine spec_ifLtN_true (by config_simp; rw [h37, h11, h10]; exact hq1) ?_
    refine spec_skip ‹_› ?_
    obtain ⟨c', k, e, hk, s'⟩ := onETail_exec (P := P) (a := a) (a' := a') _ ‹_›
      (by config_simp; exact h37) (by config_simp; exact h38)
      (by config_simp; rw [h37, h11, Nat.mod_eq_of_lt hq1]) (by omega)
    exact ⟨c', k, e, by omega, by config_simp at s'; exact s'⟩
  · refine spec_ifLtN_false (by config_simp; rw [h37, h11, h10]; exact hq1) ?_
    exec_block
    · omega
    obtain ⟨c', k, e, hk, s'⟩ := onETail_exec (P := P) (a := a) (a' := a') _ ‹_›
      (by config_simp; exact h37) (by config_simp; exact h38)
      (by config_simp; rw [show a + 1 = P.n by omega, Nat.mod_self]) (by omega)
    exact ⟨c', k, e, by omega, by config_simp at s'; exact s'⟩

/-- The general case, without the frame. -/
theorem genI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {e h : ℕ} (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (h33 : c.nreg 170133 = 6)
    (h6 : 6 ≤ e) (he2 : e < 2 * L + 6) :
    ∃ c' k, Exec P W genI c c' k ∧ k ≤ 70 ∧
      SymPtIn c' 170130 (if h = 0 ∨ h - 1 = cVtxV P.n cs L S (e - 6) then
        .vtx (cVtxV P.n cs L S (e - 6))
        else .onEdge (ShootCut.edgeOf P.n (.vtx (cVtxV P.n cs L S (e - 6)))
          (.vtx (cVtxV P.n cs L S (e - 6 + 1)))) (h - 1)) := by
  have hW := hR.hW
  have hL1 := hR.hL
  have hcs := hR.hcs
  have hLn := hR.hLn
  have kR : ∀ {c c' : Config}, HRegs P W c cs L S v →
      (∀ r, (r < 170130 ∨ 170141 ≤ r) → c'.nreg r = c.nreg r) → HRegs P W c' cs L S v :=
    fun h hk => h.keep (fun r hr => hk r (by
      unfold Bhs at hr; simp only [decide_eq_false_iff_not] at hr; omega))
  set a := cVtxV P.n cs L S (e - 6) with had
  set a' := cVtxV P.n cs L S (e - 6 + 1) with had'
  have ha : a < P.n := by rw [had]; unfold cVtxV; exact Nat.mod_lt _ (⋄)
  -- `170134 := e - 6`
  obtain ⟨c₁, k₁, e₁, hk₁, b34, r₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 170134 140011 170133]) c c₁ k₁ ∧
      k₁ = 1 ∧ c₁.nreg 170134 = e - 6 ∧ (∀ r, r ≠ 170134 → c₁.nreg r = c.nreg r) := by
    exec_block
    refine ⟨rfl, by config_simp; rw [he, h33], fun r hr => ?_⟩
    ϴ Config.nreg_mk, upd, ite_eq_right hr
  have R₁ := kR hR (fun r hr => r₁ r (⋄))
  obtain ⟨k₂, e₂, hk₂⟩ := cvI_exec (P := P) c₁ e₁.wb_right R₁ b34 (⋄)
  have w₂ := e₂.wb_right
  -- `170137 := a`, `170134 := e - 6 + 1`
  obtain ⟨c₃, k₃, e₃, hk₃, b37, b34', r₃⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 170137 170136, .addN 170134 170134 170011])
      { c₁ with nreg := upd c₁.nreg 170136 a } c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 170137 = a ∧
      c₃.nreg 170134 = e - 6 + 1 ∧ (∀ r, r ≠ 170137 → r ≠ 170134 → r ≠ 170136 →
        c₃.nreg r = c₁.nreg r) := by
    exec_block
    · config_simp; rw [b34, R₁.r11]; omega
    refine ⟨rfl, by config_simp, by config_simp; rw [b34, R₁.r11], fun r h1 h2 h3 => ?_⟩
    ϴ Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3
  have R₃ := kR R₁ (fun r hr => r₃ r (⋄) (⋄) (⋄))
  obtain ⟨k₄, e₄, hk₄⟩ := cvI_exec (P := P) c₃ e₃.wb_right R₃ b34' (⋄)
  have w₄ := e₄.wb_right
  -- `170138 := a'`
  obtain ⟨c₅, k₅, e₅, hk₅, b38, b37', r₅⟩ : ∃ c₅ k₅, Exec P W (block [.copyN 170138 170136])
      { c₃ with nreg := upd c₃.nreg 170136 a' } c₅ k₅ ∧ k₅ = 1 ∧ c₅.nreg 170138 = a' ∧
      c₅.nreg 170137 = a ∧ (∀ r, r ≠ 170138 → r ≠ 170136 → c₅.nreg r = c₃.nreg r) := by
    exec_block
    refine ⟨rfl, by config_simp, by config_simp; exact b37, fun r h1 h2 => ?_⟩
    ϴ Config.nreg_mk, upd, ite_eq_right h1, ite_eq_right h2
  have R₅ := kR R₃ (fun r hr => r₅ r (⋄) (⋄))
  have w₅ := e₅.wb_right
  have k₅' : ∀ r, (r < 170130 ∨ 170141 ≤ r) → c₅.nreg r = c.nreg r := fun r hr => by
    rw [r₅ r (⋄) (by omega), r₃ r (by omega) (by omega) (by omega), r₁ r (by omega)]
  have h12' : c₅.nreg 170012 = 0 := R₅.r12
  have hh' : c₅.nreg 140012 = h := by rw [k₅' _ (⋄)]; exact hh
  -- the decision
  by_cases hv : h = 0 ∨ h - 1 = a
  · Ξ ite_eq_left hv
    -- `vtxA` (possibly after the two comparisons)
    have hA : ∃ c' k, Exec P W (.ifLtN 170012 140012
        (.seq (block [.subN 170139 140012 170011])
          (.ifLtN 170139 170137 onE (.ifLtN 170137 170139 onE vtxA))) vtxA) c₅ c' k ∧ k ≤ 9 ∧
        SymPtIn c' 170130 (.vtx a) := by
      rcases hv with h0 | h0
      · refine spec_ifLtN_false (by rw [h12', hh', h0]; omega) ?_
        obtain ⟨c', k, e', hk, s'⟩ := vtxA_exec (P := P) c₅ w₅ (⋄)
        exact ⟨c', k, e', ⋄, by rw [b37'] at s'; exact s'⟩
      · by_cases hz : h = 0
        · refine spec_ifLtN_false (by rw [h12', hh', hz]; omega) ?_
          obtain ⟨c', k, e', hk, s'⟩ := vtxA_exec (P := P) c₅ w₅ (⋄)
          exact ⟨c', k, e', ⋄, by rw [b37'] at s'; exact s'⟩
        refine spec_ifLtN_true (by rw [h12', hh']; omega) ?_
        refine spec_seq ?_
        exec_block
        refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        obtain ⟨c', k, e', hk, s'⟩ := vtxA_exec (P := P) _ ‹_› (⋄)
        refine ⟨c', k, e', ⋄, ?_⟩
        config_simp at s'; rw [b37'] at s'; exact s'
    obtain ⟨c', k, e', hk, s'⟩ := hA
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e')))), ⋄, s'⟩
  · Ξ ite_eq_right hv
    push Not at hv
    have hB : ∃ c' k, Exec P W (.ifLtN 170012 140012
        (.seq (block [.subN 170139 140012 170011])
          (.ifLtN 170139 170137 onE (.ifLtN 170137 170139 onE vtxA))) vtxA) c₅ c' k ∧ k ≤ 18 ∧
        SymPtIn c' 170130 (.onEdge (ShootCut.edgeOf P.n (.vtx a) (.vtx a')) (h - 1)) := by
      refine spec_ifLtN_true (by rw [h12', hh']; omega) ?_
      refine spec_seq ?_
      exec_block
      have w := ‹WordsBounded W { c₅ with nreg := upd c₅.nreg 170139 (c₅.nreg 140012 - c₅.nreg 170011) }›
      have o := onE_exec (P := P) { c₅ with nreg := upd c₅.nreg 170139 (c₅.nreg 140012 - c₅.nreg 170011) }
        w (a := a) (a' := a') (by config_simp; exact b37') (by config_simp; exact b38)
        (by config_simp; exact R₅.r10) (by config_simp; exact R₅.r11) ha (⋄)
      obtain ⟨c', k, e', hk, s'⟩ := o
      config_simp at s'
      rw [hh', R₅.r11] at s'
      by_cases hlt : h - 1 < a
      · refine spec_ifLtN_true (by config_simp; rw [hh', R₅.r11, b37']; exact hlt) ?_
        exact ⟨c', k, e', ⋄, s'⟩
      · refine spec_ifLtN_false (by config_simp; rw [hh', R₅.r11, b37']; exact hlt) ?_
        refine spec_ifLtN_true (by config_simp; rw [hh', R₅.r11, b37']; omega) ?_
        exact ⟨c', k, e', ⋄, s'⟩
    obtain ⟨c', k, e', hk, s'⟩ := hB
    exact ⟨c', _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e')))), ⋄, s'⟩

/-- **The boundary symbolic point of a hit.** -/
theorem hsI_exec (c : Config) (hw : WordsBounded W c) {cs L S v : ℕ} (hR : HRegs P W c cs L S v)
    {e h : ℕ} (he : c.nreg 140011 = e) (hh : c.nreg 140012 = h) (he2 : e < 2 * L + 7) :
    ∃ c' k, Exec P W hsI c c' k ∧ k ≤ 90 ∧ SymPtIn c' 170130 (hitSymV P.n cs L S v e h) ∧
      FrameB Bhs c c' := by
  have hW := hR.hW
  have hL1 := hR.hL
  have hLn := hR.hLn
  obtain ⟨c₁, k₁, e₁, hk₁, a33, a35, R₁, f₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 170133 6, .addN 170135 170089 170133]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 170133 = 6 ∧ c₁.nreg 170135 = 2 * L + 6 ∧ HRegs P W c₁ cs L S v ∧
      (∀ r, r ≠ 170133 → r ≠ 170135 → c₁.nreg r = c.nreg r) := by
    exec_block
    · omega
    · config_simp; rw [hR.r89]; omega
    refine ⟨rfl, by config_simp, by config_simp; rw [hR.r89], hR.keep (fun r hr => ?_),
      fun r h1 h2 => ?_⟩
    · unfold Bhs at hr; simp only [decide_eq_false_iff_not] at hr
      simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  have w₁ := e₁.wb_right
  have b11 : c₁.nreg 140011 = e := by rw [f₁ _ (⌖) (by decide)]; exact he
  have b12 : c₁.nreg 140012 = h := by rw [f₁ _ (⌖) (by decide)]; exact hh
  suffices hX : ∃ c' k, Exec P W hsI c c' k ∧ k ≤ 90 ∧
      SymPtIn c' 170130 (hitSymV P.n cs L S v e h) by
    obtain ⟨c', k, ex, hk, s'⟩ := hX
    exact ⟨c', k, ex, hk, s', exec_frameB ex wr_hsI⟩
  unfold hsI hitSymV
  refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
  by_cases h6 : e < 6
  · refine spec_ifLtN_true (by rw [b11, a33]; exact h6) ?_
    obtain ⟨c₂, k₂, e₂, hk₂, s₂⟩ := vtxV_exec (P := P) c₁ w₁ (⋄)
    refine ⟨c₂, k₂, e₂, ⋄, ?_⟩
    Ξ ite_eq_left (Or.inl h6)
    rw [R₁.r79] at s₂
    exact s₂
  refine spec_ifLtN_false (by rw [b11, a33]; exact h6) ?_
  by_cases h7 : e < 2 * L + 6
  · refine spec_ifLtN_true (by rw [b11, a35]; exact h7) ?_
    obtain ⟨c₂, k₂, e₂, hk₂, s₂⟩ := genI_exec (P := P) c₁ w₁ R₁ b11 b12 a33 (⋄) h7
    refine ⟨c₂, k₂, e₂, ⋄, ?_⟩
    rw [ite_eq_right (⋄)]
    exact s₂
  · refine spec_ifLtN_false (by rw [b11, a35]; exact h7) ?_
    obtain ⟨c₂, k₂, e₂, hk₂, s₂⟩ := vtxV_exec (P := P) c₁ w₁ (⋄)
    refine ⟨c₂, k₂, e₂, ⋄, ?_⟩
    rw [ite_eq_left (Or.inr (⋄))]
    rw [R₁.r79] at s₂
    exact s₂

end exec

end

end IOrc

end Chazelle.Core
