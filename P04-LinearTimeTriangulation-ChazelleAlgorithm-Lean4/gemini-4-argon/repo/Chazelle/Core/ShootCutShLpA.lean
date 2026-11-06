module

public import Chazelle.Core.ShootCutShRec
public import Chazelle.Core.ShootCutShK0

/-!
# WP-G, part 57: the loop over the piece records

After the core, the ray-shooter walks its piece records (`140110`: the record pointer, up to the
end `140100` of the records) and shoots at each piece: a kind-0 piece segment by segment
(`pieceK0`), a kind-1 piece by a query of its Lemma 3.6 structure (`pieceK1`).  The best first
hit so far is kept in `140210 …` (`CandAt`).

* `lpInit_exec`: the set-up (`140334 := 2m + 7`, the record pointer, no candidate);
* `lpLoad_exec`: the nine words of a record into `140250 …`;
* `LpCtx`: the fixed facts of the loop; `LpI`: its invariant; `FrameNK`: a frame without its
  step bound.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Chazelle.Core

namespace ShootCut

open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim

@[expose] public section

/-! ## The programs -/

/-- The set-up of the loop: `140334 := 2m + 7` (from the chain descriptor at `140403`), the
record pointer `140110 := A₀ + 1`, no candidate. -/
def lpInit : Stmt := block [.addN 140113 140403 K1, .addN 140113 140113 K1, .loadN 140112 140113,
  .addN 140114 140112 140112, .constN 140115 7, .addN 140334 140114 140115,
  .addN 140110 140101 K1, .constN 140210 0]

/-- The first five words of a record. -/
def lpLoadA : Stmt := block [.loadN 140250 140110, .addN 140110 140110 K1,
  .loadN 140251 140110, .addN 140110 140110 K1, .loadN 140252 140110, .addN 140110 140110 K1,
  .loadN 140253 140110, .addN 140110 140110 K1, .loadN 140254 140110, .addN 140110 140110 K1]

/-- The last four words of a record. -/
def lpLoadB : Stmt := block [.loadN 140255 140110, .addN 140110 140110 K1,
  .loadN 140256 140110, .addN 140110 140110 K1, .loadN 140257 140110, .addN 140110 140110 K1,
  .loadN 140258 140110, .addN 140110 140110 K1]

/-- A record into `140250 …`. -/
def lpLoad : Stmt := .seq lpLoadA lpLoadB

/-- One piece. -/
def lpBody (query : Stmt) : Stmt := .seq lpLoad (.ifLtN 140254 K1 pieceK0 (pieceK1 query))

/-- **The loop over the pieces.** -/
def shLoop (query : Stmt) : Stmt := .seq lpInit (.whileLtN 140110 140100 (lpBody query))

/-- The registers written by `lpInit`. -/
def Blpi (r : ℕ) : Bool := decide (140110 ≤ r ∧ r < 140116) || r == 140334 || r == 140210

/-- The registers written by `lpLoad`. -/
def Blpl (r : ℕ) : Bool := decide (140250 ≤ r ∧ r < 140259) || r == 140110

theorem wr_lpInit : wr Blpi lpInit = true := by decide

theorem wr_lpLoad : wr Blpl lpLoad = true := by decide

/-! ## The set-up and the loads -/

variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

theorem noHit_empty : NoHit (∅ : Set Point) z σ := fun _ _ hm => hm

theorem lpInit_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {D A₀ m : ℕ}
    (h403 : c.nreg 140403 = D) (hm : c.nmem (D + 2) = m) (h101 : c.nreg 140101 = A₀)
    (hD : D + 2 ≤ W) (hmW : 2 * m + 7 ≤ W) (hA : A₀ + 1 ≤ W) :
    ∃ c' k, Exec P W lpInit c c' k ∧ k = 8 ∧ c'.nreg 140334 = 2 * m + 7 ∧
      c'.nreg 140110 = A₀ + 1 ∧ c'.nreg 140210 = 0 ∧ FrameB Blpi c c' := by
  have h1' : c.nreg 140401 = 1 := h1
  obtain ⟨c', k, ex, hk, v34, v10, v210⟩ : ∃ c' k, Exec P W lpInit c c' k ∧ k = 8 ∧
      c'.nreg 140334 = 2 * m + 7 ∧ c'.nreg 140110 = A₀ + 1 ∧ c'.nreg 140210 = 0 := by
    unfold lpInit
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; rw [h403, h1']; omega) |
      (config_simp; rw [h403, h1', show D + 1 + 1 = D + 2 by omega, hm]; omega) |
      (config_simp; rw [h101, h1']; omega) | skip
  exact ⟨c', k, ex, hk, v34, v10, v210, exec_frameB ex wr_lpInit⟩

theorem lpLoadA_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W lpLoadA c c' k ∧ k = 10 ∧ c'.nreg 140110 = p + 5 ∧
      c'.nreg 140250 = c.nmem p ∧ c'.nreg 140251 = c.nmem (p + 1) ∧
      c'.nreg 140252 = c.nmem (p + 2) ∧ c'.nreg 140253 = c.nmem (p + 3) ∧
      c'.nreg 140254 = c.nmem (p + 4) := by
  have h1' : c.nreg 140401 = 1 := h1
  unfold lpLoadA
  simp only [K1]
  exec_block
  all_goals first | (config_simp; rw [h10, h1']; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h10, h1']
  all_goals first | (split_ifs <;> first | rfl | omega) | skip

theorem lpLoadB_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 4 ≤ W) :
    ∃ c' k, Exec P W lpLoadB c c' k ∧ k = 8 ∧ c'.nreg 140110 = p + 4 ∧
      c'.nreg 140255 = c.nmem p ∧ c'.nreg 140256 = c.nmem (p + 1) ∧
      c'.nreg 140257 = c.nmem (p + 2) ∧ c'.nreg 140258 = c.nmem (p + 3) := by
  have h1' : c.nreg 140401 = 1 := h1
  unfold lpLoadB
  simp only [K1]
  exec_block
  all_goals first | (config_simp; rw [h10, h1']; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [upd, Config.nreg_mk, Config.nmem_mk, h10, h1']
  all_goals first | (split_ifs <;> first | rfl | omega) | skip

theorem lpLoad_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W lpLoad c c' k ∧ k = 18 ∧ c'.nreg 140110 = p + 9 ∧
      c'.nreg 140250 = c.nmem p ∧ c'.nreg 140251 = c.nmem (p + 1) ∧
      c'.nreg 140252 = c.nmem (p + 2) ∧ c'.nreg 140253 = c.nmem (p + 3) ∧
      c'.nreg 140254 = c.nmem (p + 4) ∧ c'.nreg 140255 = c.nmem (p + 5) ∧
      c'.nreg 140256 = c.nmem (p + 6) ∧ c'.nreg 140257 = c.nmem (p + 7) ∧
      c'.nreg 140258 = c.nmem (p + 8) ∧ FrameB Blpl c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q0, q1, q2, q3, q4⟩ := lpLoadA_exec (P := P) c hw h1 h10 hp
  have f₁ := exec_frameB (B := Blpl) e₁ (by decide)
  have g1 : c₁.nreg K1 = 1 := by rwa [f₁.1 _ (by decide)]
  obtain ⟨c₂, k₂, e₂, hk₂, u10, u5, u6, u7, u8⟩ := lpLoadB_exec (P := P) c₁ e₁.wb_right g1 q10
    (by omega)
  have f₂ := exec_frameB (B := fun r => decide (140255 ≤ r ∧ r < 140259) || r == 140110) e₂
    (by decide)
  have ex : Exec P W lpLoad c c₂ (k₁ + k₂) := .seq e₁ e₂
  have hm : c₁.nmem = c.nmem := f₁.2.2.1
  refine ⟨c₂, _, ex, by omega, by rw [u10], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    exec_frameB ex wr_lpLoad⟩
  · rw [f₂.1 _ (by decide), q0]
  · rw [f₂.1 _ (by decide), q1]
  · rw [f₂.1 _ (by decide), q2]
  · rw [f₂.1 _ (by decide), q3]
  · rw [f₂.1 _ (by decide), q4]
  · rw [u5, hm]
  · rw [u6, hm, show p + 5 + 1 = p + 6 by omega]
  · rw [u7, hm, show p + 5 + 2 = p + 7 by omega]
  · rw [u8, hm, show p + 5 + 3 = p + 8 by omega]

/-! ## The invariant -/

/-- The point set of a piece. -/
noncomputable def pcSetOf (C : Chain) (Q : Polygon) (pc : Pc) : Set Point :=
  (chainModel C).arcSet ((chainModel C).key Q pc.s) ((chainModel C).key Q pc.e)

/-- The point set of a list of pieces. -/
noncomputable def psSet (C : Chain) (Q : Polygon) (l : List Pc) : Set Point :=
  ⋃ pc ∈ l, pcSetOf C Q pc

theorem psSet_nil (C : Chain) (Q : Polygon) : psSet C Q [] = ∅ := by simp [psSet]

theorem psSet_append (C : Chain) (Q : Polygon) (l : List Pc) (pc : Pc) :
    psSet C Q (l ++ [pc]) = psSet C Q l ∪ pcSetOf C Q pc := by
  ext x; simp [psSet, or_comm]

/-- A frame for the bands of the oracles, without its bound on the growth of the allocator. -/
def FrameNK (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ oracleBands → c'.rreg r = c.rreg r) ∧
    (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
    (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC

theorem FrameNK.refl (c : Config) : FrameNK c c :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl⟩

theorem FrameNK.step {c c₁ c₂ : Config} {k : ℕ} (h₁ : FrameNK c c₁)
    (h₂ : Frame oracleBands c₁ c₂ k) : FrameNK c c₂ := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁⟩ := h₁
  obtain ⟨r₂, rr₂, m₂, rm₂, o₂, a₂, -⟩ := h₂
  exact ⟨fun r hr hra => by rw [r₂ r hr hra, r₁ r hr hra], fun r hr => by rw [rr₂ r hr, rr₁ r hr],
    fun a ha => by rw [m₂ a (lt_of_lt_of_le ha a₁), m₁ a ha],
    fun a ha => by rw [rm₂ a (lt_of_lt_of_le ha a₁), rm₁ a ha], o₂.trans o₁, a₁.trans a₂⟩

theorem FrameNK.frame {c c' : Config} {k : ℕ} (h : FrameNK c c')
    (hk : c'.nreg ALLOC ≤ c.nreg ALLOC + k) : Frame oracleBands c c' k :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hk⟩

/-- **The fixed facts of the loop.** -/
structure LpCtx (O : OracleIface) (P : Polygon) (W : ℕ) (C : Chain) (z : Point)
    (m₀ : ℕ → ℕ) (h γ A₀ : ℕ) (s e : WPos) (ps : List Pc) : Prop where
  hV : O.Valid
  arc : ArcOK C (Qof P) s e ps
  ok : ∀ pc ∈ ps, PcOK P C m₀ h γ pc
  hsP : ProperPos (chainModel C) (Qof P) P.n s
  heP : ProperPos (chainModel C) (Qof P) P.n e
  hs1 : s.edge < 2 * C.m + 7
  he1 : e.edge < 2 * C.m + 7
  hsin : s.hgt = 0 ∨ |((chainModel C).pos (Qof P) s).2| < C.radius
  hein : e.hgt = 0 ∨ |((chainModel C).pos (Qof P) e).2| < C.radius
  hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e) ≤ γ
  hz : z ∉ (chainModel C).arcSet ((chainModel C).key (Qof P) s) ((chainModel C).key (Qof P) e)
  hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀
  hQs : (Qof P).Simple
  hnW : 2 * C.m + 7 + 1 ≤ W

/-- **The invariant of the loop** (start `cs`, per-piece bound `K`). -/
def LpI (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (m₀ : ℕ → ℕ)
    (A₀ : ℕ) (ps : List Pc) (cs : Config) (K : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ ShEnv P W H C z σ c ∧ OrgOK P C z σ c ∧ dirOf (c.nreg 140008) = σ ∧
    c.nreg 140334 = 2 * C.m + 7 ∧ c.nreg 140100 = A₀ + 1 + 9 * ps.length ∧
    Rec9 c.nmem A₀ ps ∧ (∀ a, a < A₀ → c.nmem a = m₀ a) ∧
    A₀ + 1 + 9 * ps.length ≤ c.nreg ALLOC ∧ FrameNK cs c ∧
    c.nreg ALLOC + (A₀ + 1 + 9 * ps.length - c.nreg 140110) * (K + 2) ≤ W ∧
    ∃ j, j ≤ ps.length ∧ c.nreg 140110 = A₀ + 1 + 9 * j ∧
      CandAt P C c 140210 (psSet C (Qof P) (ps.take j)) z σ

end

end ShootCut

end Chazelle.Core
