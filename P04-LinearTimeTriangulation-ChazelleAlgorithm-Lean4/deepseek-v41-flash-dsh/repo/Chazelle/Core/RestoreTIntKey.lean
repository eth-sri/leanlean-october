module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTDir
public import Chazelle.Core.RestoreTRun

/-!
# WP-E, the candidate test on the RAM, part 15: comparing keys in the interior model

In the interior model of `Q` (vertices of pairwise distinct heights) the key order of two proper
positions is lexicographic: first the walk edge, then, on one edge, the parameter, which compares
like the heights of the positions in the direction of the edge (`param_lt_iff_same_edge`).  The
height of a position is that of a vertex of `Q`: the vertex `h - 1` for the height code `h ≥ 1`,
the start vertex of the edge (`intIdx`) for the code `0`.  Two runs of WP-C's height comparison
`dirTail` (the direction code of the edge, and the comparison of the two heights) decide it.

* `key_lt_lex`: the lexicographic order of keys.
* `iKey a b d e`: the bits `key x < key y`, `key y < key x` into `50210`, `50211`
  (`iKey_exec`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK WalkKey

/-! ## Mathematics -/

/-- **The lexicographic order of keys** of proper positions. -/
theorem key_lt_lex {M : Model} {Q : Polygon} {n : ℕ} {x y : WPos} (hx : ProperPos M Q n x)
    (hy : ProperPos M Q n y) :
    M.key Q x < M.key Q y ↔ x.edge < y.edge ∨ (x.edge = y.edge ∧ M.param Q x < M.param Q y) := by
  unfold Model.key
  obtain ⟨hx0, hx1, -⟩ := hx
  obtain ⟨hy0, hy1, -⟩ := hy
  constructor
  · intro h
    rcases lt_trichotomy x.edge y.edge with h' | h' | h'
    · exact Or.inl h'
    · refine Or.inr ⟨h', ?_⟩
      Ξ' h' at h; linarith
    · exfalso
      have : (y.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h'
      linarith
  · rintro (h | ⟨h, h'⟩)
    · have : (x.edge : ℝ) + 1 ≤ y.edge := by exact_mod_cast h
      linarith
    · rw [h]; linarith

/-- The index in `Q` of vertex `e` of the interior walk, for the orientation bit `bit`. -/
def iIdx (bit n e : ℕ) : ℕ := if bit = 1 then e else n - 1 - e

/-- The index of the vertex of `Q` at the height of a position of the interior walk. -/
def hIdx (bit n : ℕ) (x : WPos) : ℕ := if x.hgt = 0 then iIdx bit n x.edge else x.hgt - 1

variable {P : Polygon}

theorem interior_wa {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P)) {e : ℕ}
    (he : e < P.n) :
    (interiorModel (Qof P)).wa e = (Qof P).vtx (iIdx bit P.n e) := by
  have hn : (Qof P).n = P.n := shear_n _ _
  unfold Model.wa
  ϴ interiorModel
  Ξ interiorWalk_vtx _ (by rw [hn]; exact he), hn
  unfold iIdx
  by_cases h : bit = 1
  · Ξ ite_eq_left (hbit.1 h), ite_eq_left h
  · Ξ ite_eq_right (fun h' => h (hbit.2 h')), ite_eq_right h

theorem interior_hgtY {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P)) {x : WPos}
    (he : x.edge < P.n) :
    (interiorModel (Qof P)).hgtY (Qof P) x = ((Qof P).vtx (hIdx bit P.n x)).2 := by
  rcases x with ⟨e, _ | h⟩
  · ϴ Model.hgtY, hIdx
    Ξ interior_wa hbit he
    simp
  · Θ Model.hgtY, hIdx

theorem iIdx_lt {bit n e : ℕ} (he : e < n) : iIdx bit n e < n := by
  unfold iIdx; split_ifs <;> omega

theorem hIdx_lt {bit n : ℕ} {x : WPos} (he : x.edge < n) (hh : x.hgt ≤ n) : hIdx bit n x < n := by
  unfold hIdx; split_ifs with h
  · exact iIdx_lt he
  · omega


theorem interior_wb {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P)) {e : ℕ}
    (he : e < P.n) :
    (interiorModel (Qof P)).wb e = (Qof P).vtx (iIdx bit P.n ((e + 1) % P.n)) := by
  have hn : (Qof P).n = P.n := shear_n _ _
  have hW : (interiorModel (Qof P)).W.n = P.n := by
    simp only [interiorModel]; Ξ interiorWalk_n, hn
  unfold Model.wb
  Ξ hW
  have := interior_wa (P := P) hbit (e := (e + 1) % P.n) (Nat.mod_lt _ (⋄))
  unfold Model.wa at this
  exact this

theorem dirOf_one {a b : ℝ} : NFLoc.dirOf a b = 1 ↔ a < b := by
  unfold NFLoc.dirOf; split_ifs with h1 h2 <;> simp_all

theorem dirOf_two {a b : ℝ} : NFLoc.dirOf a b = 2 ↔ b < a := by
  unfold NFLoc.dirOf; split_ifs with h1 h2 <;> simp_all; linarith

theorem dirOf_le (a b : ℝ) : NFLoc.dirOf a b ≤ 2 := by
  unfold NFLoc.dirOf; split_ifs <;> omega

/-! ## The machine -/

/-- Set a bit register. -/
def setB (r : ℕ) : Stmt := .instr (.constN r 1)

/-- The height index: `dst := 50121` (the start vertex of the edge) for the code `0`, else
`code - 1`. -/
def hSel (src dst : ℕ) : Stmt :=
  .ifLtN src 50032 (.instr (.copyN dst 50121)) (.instr (.subN dst src 50032))

/-- The bits from the direction code `50120` and the height comparison `10502`. -/
def iDecide : Stmt :=
  .ifLtN 50120 50032 .skip
    (.ifLtN 50032 50120
      (.ifLtN 10502 50032 .skip (.ifLtN 50032 10502 (setB 50210) (setB 50211)))
      (.ifLtN 10502 50032 .skip (.ifLtN 50032 10502 (setB 50211) (setB 50210))))

/-- The start of the comparison on one edge: its direction code into `50120`, the index of its
start vertex into `50121`. -/
def iEdge (a : ℕ) : Stmt :=
  .seq (block [.copyN 50000 83000, .copyN 50002 a]) (.seq intIdx
    (.seq (block [.copyN 50121 50041, .constN 50040 0, .constN 50043 0]) (.seq dirTail
      (block [.copyN 50120 10502, .constN 50032 1]))))

/-- The comparison of two positions on one edge. -/
def iSame (a b _d e : ℕ) : Stmt :=
  .seq (iEdge a) (.seq (hSel b 50122) (.seq (hSel e 50123)
    (.seq (block [.constN 50040 0, .copyN 50041 50122, .constN 50043 0, .copyN 50044 50123])
      (.seq dirTail (.seq (.instr (.constN 50032 1)) iDecide)))))

/-- **The key comparison of the interior model.** -/
def iKey (a b d e : ℕ) : Stmt :=
  .seq (block [.constN 50210 0, .constN 50211 0])
    (.ifLtN a d (setB 50210) (.ifLtN d a (setB 50211) (iSame a b d e)))

/-- The registers `iKey` writes. -/
def Bik (r : ℕ) : Bool :=
  Bdir r || r == 50000 || r == 50002 || (50120 ≤ r && r < 50124) || r == 50210 || r == 50211

theorem wr_intIdx : wr Bdir intIdx = true := ⌖

theorem wr_iKey (a b d e : ℕ) : wr Bik (iKey a b d e) = true := by
  have h1 : wr Bik intIdx = true := wr_mono wr_intIdx (fun r h => ⊚ Bik, h)
  have h2 : wr Bik dirTail = true := wr_mono wr_dirTail (fun r h => ⊚ Bik, h)
  simp only [iKey, iSame, iEdge, hSel, iDecide, setB, wr, block, wrOK, h1, h2, Bool.and_true,
    Bool.true_and]
  decide


variable {W : ℕ}

theorem iEdge_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    (hmd : c.nmem (c.nreg 83000 + 1) = bit) (hD : c.nreg 83000 + 1 ≤ W) (ha : c.nreg a < P.n)
    (ha8 : 80000 ≤ a ∧ a < 90000) :
    ∃ c' k, Exec P W (iEdge a) c c' k ∧ k ≤ 1100 ∧
      c'.nreg 50120 = dirCode (interiorModel (Qof P)) (c.nreg a) ∧
      c'.nreg 50121 = iIdx bit P.n (c.nreg a) ∧ c'.nreg 50032 = 1 := by
  obtain ⟨c₁, k₁, e₁, hk₁, q01, q02, hm₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.copyN 50000 83000, .copyN 50002 a]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = c.nreg a ∧ c₁.nmem = c.nmem := by
    exec_block
    refine ⟨rfl, by config_simp, ?_, rfl⟩
    config_simp
    Ξ upd_ne (⋄)
  obtain ⟨c₂, k₂, e₂, hk₂, r41, r44⟩ := intIdx_exec (P := P) hW c₁ e₁.wb_right
    (by rw [q02]; exact ha) (by rw [q01]; exact hD)
  Ξ' q01, q02, hm₁, hmd at r41 r44
  obtain ⟨c₃, k₃, e₃, hk₃, s40, s41, s43, s44, s121⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 50121 50041, .constN 50040 0, .constN 50043 0]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 50040 = 0 ∧ c₃.nreg 50041 = c₂.nreg 50041 ∧ c₃.nreg 50043 = 0 ∧
      c₃.nreg 50044 = c₂.nreg 50044 ∧ c₃.nreg 50121 = c₂.nreg 50041 := by
    have w₂ := e₂.wb_right
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp⟩
  have hn : 0 < P.n := ⋄
  have hia : iIdx bit P.n (c.nreg a) < P.n := iIdx_lt ha
  have hib : iIdx bit P.n ((c.nreg a + 1) % P.n) < P.n := iIdx_lt (Nat.mod_lt _ hn)
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, d₄⟩ := dirTail_exec (P := P) hG hW c₃ e₃.wb_right
    (sa := .vtx (iIdx bit P.n (c.nreg a))) (sb := .vtx (iIdx bit P.n ((c.nreg a + 1) % P.n)))
    hia hib ⟨s40, by rw [s41, r41]; rfl⟩ ⟨s43, by rw [s44, r44]; rfl⟩
  have g121 : c₄.nreg 50121 = c₃.nreg 50121 := f₄.1 50121 (⌖)
  obtain ⟨c₅, k₅, e₅, hk₅, t120, t121, t32⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 50120 10502, .constN 50032 1]) c₄ c₅ k₅ ∧ k₅ = 2 ∧
      c₅.nreg 50120 = c₄.nreg 10502 ∧ c₅.nreg 50121 = c₄.nreg 50121 ∧ c₅.nreg 50032 = 1 := by
    have w₄ := e₄.wb_right
    exec_block
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp⟩
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ⋄, ?_, ?_, t32⟩
  · Ξ t120, d₄, dirCode_eq
    ϴ SymPt.eval
    Ξ interior_wa hbit ha, interior_wb hbit ha
  · rw [t121, g121, s121, r41]; rfl


/-- The decision on the direction code `dv` and the height comparison `cv`. -/
theorem iDecide_exec {c : Config} (hw : WordsBounded W c) (hW : 1 ≤ W)
    (h32 : c.nreg 50032 = 1) (h10 : c.nreg 50210 = 0) (h11 : c.nreg 50211 = 0)
    (hd : c.nreg 50120 ≤ 2) (hc : c.nreg 10502 ≤ 2) :
    ∃ c' k, Exec P W iDecide c c' k ∧ k ≤ 9 ∧ c'.nreg 50210 ≤ 1 ∧ c'.nreg 50211 ≤ 1 ∧
      (c'.nreg 50210 = 1 ↔ (c.nreg 50120 = 1 ∧ c.nreg 10502 = 1) ∨
        (c.nreg 50120 = 2 ∧ c.nreg 10502 = 2)) ∧
      (c'.nreg 50211 = 1 ↔ (c.nreg 50120 = 1 ∧ c.nreg 10502 = 2) ∨
        (c.nreg 50120 = 2 ∧ c.nreg 10502 = 1)) := by
  unfold iDecide setB
  rcases (show c.nreg 50120 = 0 ∨ c.nreg 50120 = 1 ∨ c.nreg 50120 = 2 by omega) with d | d | d <;>
  rcases (show c.nreg 10502 = 0 ∨ c.nreg 10502 = 1 ∨ c.nreg 10502 = 2 by omega) with v | v | v
  all_goals
    repeat (first
      | (refine spec_ifLtN_true (by omega) ?_)
      | (refine spec_ifLtN_false (by omega) ?_))
  all_goals first
    | exact spec_skip hw ⟨by omega, by omega, by omega, by simp [h10, d, v], by simp [h11, d, v]⟩
    | exact spec_instr (Exec.constN hw _ _ hW) fun _ => ⟨by omega, by simp [upd, h10],
        by simp [upd, h11], by simp [upd, h10, d, v], by simp [upd, h11, d, v]⟩


/-- The registers `iEdge` writes. -/
def BiE (r : ℕ) : Bool := Bdir r || r == 50000 || r == 50002 || r == 50120 || r == 50121

theorem wr_iEdge (a : ℕ) : wr BiE (iEdge a) = true := by
  have h1 : wr BiE intIdx = true := wr_mono wr_intIdx (fun r h => ⊚ BiE, h)
  have h2 : wr BiE dirTail = true := wr_mono wr_dirTail (fun r h => ⊚ BiE, h)
  ϴ iEdge, wr, block, wrOK, h1, h2, Bool.and_true, Bool.true_and
  decide

/-- The height index selection. -/
theorem hSel_exec {c : Config} (hw : WordsBounded W c) {src dst : ℕ} (h32 : c.nreg 50032 = 1)
    (_hdst : dst ≠ src) :
    ∃ c' k, Exec P W (hSel src dst) c c' k ∧ k ≤ 3 ∧
      c'.nreg dst = (if c.nreg src = 0 then c.nreg 50121 else c.nreg src - 1) ∧
      ∀ r, r ≠ dst → c'.nreg r = c.nreg r := by
  unfold hSel
  by_cases h : c.nreg src < c.nreg 50032
  · refine spec_ifLtN_true h (spec_instr (Exec.copyN hw _ _) fun _ => ⟨⋄, ?_, ?_⟩)
    · simp only [upd_eq]; Ξ ite_eq_left (⋄)
    · intro r hr; exact upd_ne hr
  · refine spec_ifLtN_false h (spec_instr (Exec.subN hw _ _ _) fun _ => ⟨⋄, ?_, ?_⟩)
    · simp only [upd_eq]; Ξ ite_eq_right (⋄), h32
    · intro r hr; exact upd_ne hr

/-- **The comparison on one edge** (interior model). -/
theorem iSame_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b d e bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    (hmd : c.nmem (c.nreg 83000 + 1) = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (h8 : ∀ r ∈ [a, b, d, e], 80000 ≤ r ∧ r < 90000)
    (h10 : c.nreg 50210 = 0) (h11 : c.nreg 50211 = 0) (hsame : c.nreg a = c.nreg d)
    (hx : ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c.nreg d, c.nreg e⟩)
    (hxe : c.nreg a < P.n) :
    ∃ c' k, Exec P W (iSame a b d e) c c' k ∧ k ≤ 2200 ∧
      BitIs c' 50210 ((interiorModel (Qof P)).key (Qof P) ⟨c.nreg a, c.nreg b⟩ <
        (interiorModel (Qof P)).key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' 50211 ((interiorModel (Qof P)).key (Qof P) ⟨c.nreg d, c.nreg e⟩ <
        (interiorModel (Qof P)).key (Qof P) ⟨c.nreg a, c.nreg b⟩) := by
  set M := interiorModel (Qof P)
  have ha8 := h8 a (✓)
  have hb8 := h8 b (✓)
  have he8 := h8 e (✓)
  obtain ⟨c₁, k₁, e₁, hk₁, d120, d121, d32⟩ := iEdge_exec hG hW hw hbit hmd hD hxe ha8
  have f₁ : FrameB BiE c c₁ := exec_frameB e₁ (wr_iEdge a)
  have g₁ : ∀ r, 80000 ≤ r → r < 90000 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp [BiE, Bdir]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, v122, o₂⟩ := hSel_exec (P := P) e₁.wb_right (src := b) (dst := 50122)
    d32 (⋄)
  obtain ⟨c₃, k₃, e₃, hk₃, v123, o₃⟩ := hSel_exec (P := P) e₂.wb_right (src := e) (dst := 50123)
    (by rw [o₂ _ (⌖)]; exact d32) (⋄)
  -- the height indices
  have hIx : c₃.nreg 50122 = hIdx bit P.n ⟨c.nreg a, c.nreg b⟩ := by
    Ξ o₃ _ (⌖), v122, g₁ b hb8.1 hb8.2, d121
    unfold hIdx; simp only
  have hIy : c₃.nreg 50123 = hIdx bit P.n ⟨c.nreg d, c.nreg e⟩ := by
    Ξ v123, o₂ _ (⋄), g₁ e he8.1 he8.2, o₂ _ (⌖), d121, ← hsame
    unfold hIdx; simp only
  obtain ⟨c₄, k₄, e₄, hk₄, s40, s41, s43, s44, r₄⟩ : ∃ c₄ k₄, Exec P W
      (block [.constN 50040 0, .copyN 50041 50122, .constN 50043 0, .copyN 50044 50123]) c₃ c₄ k₄ ∧
      k₄ = 4 ∧ c₄.nreg 50040 = 0 ∧ c₄.nreg 50041 = c₃.nreg 50122 ∧ c₄.nreg 50043 = 0 ∧
      c₄.nreg 50044 = c₃.nreg 50123 ∧
      ∀ r, r ≠ 50040 → r ≠ 50041 → r ≠ 50043 → r ≠ 50044 → c₄.nreg r = c₃.nreg r := by
    have w₃ := e₃.wb_right
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, ?_⟩
      intro r h1 h2 h3 h4
      Θ upd, h1, h2, h3, h4
  have hn := hxe
  have hhx : hIdx bit P.n ⟨c.nreg a, c.nreg b⟩ < P.n := hIdx_lt hxe hx.2.2
  have hhy : hIdx bit P.n ⟨c.nreg d, c.nreg e⟩ < P.n := hIdx_lt (by rw [← hsame]; exact hxe) hy.2.2
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, d₅⟩ := dirTail_exec (P := P) hG hW c₄ e₄.wb_right
    (sa := .vtx (hIdx bit P.n ⟨c.nreg a, c.nreg b⟩))
    (sb := .vtx (hIdx bit P.n ⟨c.nreg d, c.nreg e⟩)) hhx hhy
    ⟨s40, Ρ s41, hIx⟩ ⟨s43, Ρ s44, hIy⟩
  have w₅ := e₅.wb_right
  have e₆ := Exec.constN (P := P) w₅ 50032 1 (⋄)
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50032 1 }
  have p120 : c₆.nreg 50120 = dirCode M (c.nreg a) := by
    show upd c₅.nreg 50032 1 50120 = _
    rw [upd_ne (⌖), f₅.1 50120 (⌖), r₄ _ (⌖) (⌖) (⌖)
      (⌖), o₃ _ (⌖), o₂ _ (⌖), d120]
  have p10 : c₆.nreg 50210 = 0 := by
    show upd c₅.nreg 50032 1 50210 = _
    rw [upd_ne (⌖), f₅.1 50210 (⌖), r₄ _ (⌖) (⌖) (⌖)
      (⌖), o₃ _ (⌖), o₂ _ (⌖), f₁.1 50210 (⌖), h10]
  have p11 : c₆.nreg 50211 = 0 := by
    show upd c₅.nreg 50032 1 50211 = _
    rw [upd_ne (⌖), f₅.1 50211 (⌖), r₄ _ (⌖) (⌖) (⌖)
      (⌖), o₃ _ (⌖), o₂ _ (⌖), f₁.1 50211 (⌖), h11]
  have p02 : c₆.nreg 10502 = NFLoc.dirOf ((Qof P).vtx (hIdx bit P.n ⟨c.nreg a, c.nreg b⟩)).2
      ((Qof P).vtx (hIdx bit P.n ⟨c.nreg d, c.nreg e⟩)).2 := by
    show upd c₅.nreg 50032 1 10502 = _
    rw [upd_ne (⌖), d₅]; rfl
  obtain ⟨c₇, k₇, e₇, hk₇, b1, b2, i1, i2⟩ := iDecide_exec (P := P) e₆.wb_right (⋄)
    (by show upd c₅.nreg 50032 1 50032 = 1; exact upd_eq) p10 p11
    (by rw [p120]; exact dirCode_le_two _ _) (by rw [p02]; exact dirOf_le _ _)
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (1 + k₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ⋄, ⟨b1, ?_⟩, ⟨b2, ?_⟩⟩
  · Ξ i1, p120, p02, dirOf_one, dirOf_two, key_lt_lex hx hy
    have hbase := param_lt_iff_same_edge M (Qof P) (x := ⟨c.nreg a, c.nreg b⟩)
      (y := ⟨c.nreg d, c.nreg e⟩) hsame
    Ξ' interior_hgtY hbit hxe, interior_hgtY hbit (by rw [← hsame]; exact hxe) at hbase
    simp only at hbase ⊢
    Ξ ← hbase
    constructor
    · intro h; exact Or.inr ⟨hsame, h⟩
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h
  · Ξ i2, p120, p02, dirOf_one, dirOf_two, key_lt_lex hy hx
    have hbase := param_lt_iff_same_edge M (Qof P) (x := ⟨c.nreg d, c.nreg e⟩)
      (y := ⟨c.nreg a, c.nreg b⟩) hsame.symm
    Ξ' interior_hgtY hbit (by rw [← hsame]; exact hxe), interior_hgtY hbit hxe at hbase
    simp only at hbase ⊢
    Ξ' hsame at hbase ⊢
    Ξ ← hbase
    constructor
    · intro h; exact Or.inr ⟨rfl, h⟩
    · rintro (h | ⟨-, h⟩)
      · omega
      · exact h


/-- **The key comparison of the interior model.** -/
theorem iKey_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {a b d e bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P))
    (hmd : c.nmem (c.nreg 83000 + 1) = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (h8 : ∀ r ∈ [a, b, d, e], 80000 ≤ r ∧ r < 90000)
    (hx : ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c.nreg a, c.nreg b⟩)
    (hy : ProperPos (interiorModel (Qof P)) (Qof P) P.n ⟨c.nreg d, c.nreg e⟩)
    (hxe : c.nreg a < P.n) (_hye : c.nreg d < P.n) :
    ∃ c' k, Exec P W (iKey a b d e) c c' k ∧ k ≤ 2210 ∧
      BitIs c' 50210 ((interiorModel (Qof P)).key (Qof P) ⟨c.nreg a, c.nreg b⟩ <
        (interiorModel (Qof P)).key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' 50211 ((interiorModel (Qof P)).key (Qof P) ⟨c.nreg d, c.nreg e⟩ <
        (interiorModel (Qof P)).key (Qof P) ⟨c.nreg a, c.nreg b⟩) := by
  have ha8 := h8 a (by simp)
  have hb8 := h8 b (by simp)
  have hd8 := h8 d (by simp)
  have he8 := h8 e (by simp)
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q11, g₁, hm₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.constN 50210 0, .constN 50211 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 50210 = 0 ∧
      c₁.nreg 50211 = 0 ∧ (∀ r, 80000 ≤ r → r < 90000 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, by config_simp, by config_simp, fun r h1 h2 => ?_, rfl⟩
      simp [upd, show r ≠ 50210 by omega, show r ≠ 50211 by omega]
  have w₁ := e₁.wb_right
  have ea := (g₁ a ha8.1 ha8.2).symm
  have eb := (g₁ b hb8.1 hb8.2).symm
  have ed := (g₁ d hd8.1 hd8.2).symm
  have ee := (g₁ e he8.1 he8.2).symm
  simp only [ea, eb, ed, ee] at hx hy hxe _hye ⊢
  have hmd' : c₁.nmem (c₁.nreg 83000 + 1) = bit := by
    rw [hm₁, g₁ 83000 (by norm_num) (by norm_num)]; exact hmd
  have hD' : c₁.nreg 83000 + 1 ≤ W := by rw [g₁ 83000 (by norm_num) (by norm_num)]; exact hD
  unfold iKey
  refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
  by_cases t1 : c₁.nreg a < c₁.nreg d
  · refine spec_ifLtN_true t1 (spec_instr (Exec.constN w₁ _ _ (by omega)) fun _ =>
      ⟨by omega, ⟨by simp [upd], ?_⟩, ⟨by simp [upd, q11], ?_⟩⟩)
    · simp only [upd_eq, true_iff]
      exact (key_lt_lex hx hy).2 (Or.inl t1)
    · simp only [upd_ne (show (50211 : ℕ) ≠ 50210 by decide), q11]
      constructor
      · intro h; omega
      · intro h
        rcases (key_lt_lex hy hx).1 h with h' | ⟨h', -⟩ <;> simp only at h' <;> omega
  · by_cases t2 : c₁.nreg d < c₁.nreg a
    · refine spec_ifLtN_false t1 (spec_ifLtN_true t2 (spec_instr (Exec.constN w₁ _ _ (by omega))
        fun _ => ⟨by omega, ⟨by simp [upd, q10], ?_⟩, ⟨by simp [upd], ?_⟩⟩))
      · simp only [upd_ne (show (50210 : ℕ) ≠ 50211 by decide), q10]
        constructor
        · intro h; omega
        · intro h
          rcases (key_lt_lex hx hy).1 h with h' | ⟨h', -⟩ <;> simp only at h' <;> omega
      · simp only [upd_eq, true_iff]
        exact (key_lt_lex hy hx).2 (Or.inl t2)
    · have hsame : c₁.nreg a = c₁.nreg d := by omega
      refine spec_ifLtN_false t1 (spec_ifLtN_false t2 ?_)
      obtain ⟨c', k, ex, hk, b1, b2⟩ := iSame_exec (P := P) hG hW w₁ hbit hmd' hD' h8 q10 q11
        hsame hx hy hxe
      exact ⟨c', k, ex, by omega, b1, b2⟩

end

end Restore

end Chazelle.Core
