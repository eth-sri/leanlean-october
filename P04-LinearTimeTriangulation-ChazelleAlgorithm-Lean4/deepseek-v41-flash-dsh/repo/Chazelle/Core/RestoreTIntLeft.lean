module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTDisp
public import Chazelle.Core.RestoreTLeftMath

/-!
# WP-E, the candidate test on the RAM, part 18: the sector test in the interior model

`iLeft`: inside a walk edge (height code `≠ 0`, a positive parameter by the canonical coding),
the sector test is the turn from the edge (`left_inside_iff`); at a walk vertex it combines the
two turns with the orientation of the corner, one run of the sign kernel on the three vertices of
`Q` (`left_vertex_iff`).  The vertices of the interior walk are vertices of `Q` (`intIdx`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim NFLoc SignK
open Chazelle.Chain (sideCross)

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- Copy the bit `50210 = 1` into `r`. -/
def copyBit (r : ℕ) : Stmt :=
  .seq (.instr (.constN r 0)) (.ifLtN 50210 83023 .skip (.ifLtN 83023 50210 .skip (setB r)))

theorem copyBit_exec {r : ℕ} (hr : 50100 ≤ r ∧ r < 50200) {p : Prop} (hI : TInv W c₀ c)
    (hp : c.nreg 50210 = 1 ↔ p) :
    ∃ c' k, Exec P W (copyBit r) c c' k ∧ k ≤ 6 ∧ c'.nreg r ≤ 1 ∧ (c'.nreg r = 1 ↔ p) ∧
      TStep W c₀ c c' k ∧ FrameB (fun q => q == r) c c' := by
  have hw := hI.hw
  have h23 := hI.h23
  have hW1 : 1 ≤ W := by have := hw.1 83023; omega
  have e₁ := Exec.constN (P := P) hw r 0 (⋄)
  set c₁ : Config := { c with nreg := upd c.nreg r 0 }
  have w₁ := e₁.wb_right
  have q10 : c₁.nreg 50210 = c.nreg 50210 := upd_ne (⋄)
  have q23 : c₁.nreg 83023 = 1 := by
    rw [show c₁.nreg 83023 = c.nreg 83023 from upd_ne (⋄)]; exact h23
  have fin : ∀ c' k, Exec P W (copyBit r) c c' k → c'.nreg r ≤ 1 → (c'.nreg r = 1 ↔ p) →
      k ≤ 6 → ∃ c' k, Exec P W (copyBit r) c c' k ∧ k ≤ 6 ∧ c'.nreg r ≤ 1 ∧
        (c'.nreg r = 1 ↔ p) ∧ TStep W c₀ c c' k ∧ FrameB (fun q => q == r) c c' :=
    fun c' k ex h1 h2 hk =>
    ⟨c', k, ex, hk, h1, h2, hI.stepB ex.wb_right (B := fun q => q == r)
      (exec_frameB ex (⊚ copyBit, setB, wr, wrOK)) (fun q hq => by
        ϴ' beq_iff_eq at hq; subst hq
        exact ⟨by simp only [primBands, bandOf, bLocate, bSign, Finset.mem_insert,
          Finset.mem_singleton]; omega, by unfold ALLOC; omega⟩) k,
      exec_frameB ex (⊚ copyBit, setB, wr, wrOK)⟩
  unfold copyBit
  by_cases a : c₁.nreg 50210 < c₁.nreg 83023
  · refine fin _ _ (.seq e₁ (.ifLtN_true a (.skip w₁))) (⊚ c₁, upd) ?_ (⋄)
    ϴ c₁, upd_eq, zero_ne_one, false_iff
    intro h; have := hp.2 h; omega
  · by_cases b : c₁.nreg 83023 < c₁.nreg 50210
    · refine fin _ _ (.seq e₁ (.ifLtN_false a (.ifLtN_true b (.skip w₁)))) (⊚ c₁, upd) ?_
        (⋄)
      ϴ c₁, upd_eq, zero_ne_one, false_iff
      intro h; have := hp.2 h; omega
    · refine fin _ _ (.seq e₁ (.ifLtN_false a (.ifLtN_false b (Exec.constN w₁ r 1 hW1))))
        (⊚ upd) ?_ (⋄)
      ϴ upd_eq, true_iff
      exact hp.1 (⋄)


/-! ## The corner -/

/-- The three vertices of `Q` at the candidate vertex `p` of the interior walk (previous, `p`,
next) as symbolic points in `50140`, `50143`, `50146`. -/
def cornerS : Stmt :=
  .seq (.seq (block [.copyN 50000 83000, .constN 50032 1])
    (.ifLtN 83005 83023 (block [.inputSize 50002, .subN 50002 50002 50032])
      (.instr (.subN 50002 83005 50032))))
    (.seq intIdx (.seq (block [.copyN 50141 50041, .copyN 50144 50044, .copyN 50002 83005])
      (.seq intIdx (block [.copyN 50147 50044, .constN 50140 0, .constN 50143 0,
        .constN 50146 0]))))

/-- The registers `cornerS` writes. -/
def Bcor (r : ℕ) : Bool :=
  Bdir r || r == 50000 || r == 50002 || r == 50140 || r == 50141 || r == 50143 || r == 50144 ||
    r == 50146 || r == 50147

theorem wr_cornerS : wr Bcor cornerS = true := by
  have h1 : wr Bcor intIdx = true := wr_mono wr_intIdx (fun r h => ⊚ Bcor, h)
  ϴ cornerS, wr, block, wrOK, h1, Bool.and_true, Bool.true_and
  decide

/-- The previous vertex index. -/
theorem prev_succ {p n : ℕ} (hp : p < n) : ((p + n - 1) % n + 1) % n = p := by
  have hn : 0 < n := ⋄
  rcases Nat.eq_zero_or_pos p with rfl | h0
  · rw [Nat.zero_add, Nat.mod_eq_of_lt (show n - 1 < n by omega), Nat.sub_add_cancel hn,
      Nat.mod_self]
  · rw [show p + n - 1 = (p - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show p - 1 < n by omega), Nat.sub_add_cancel h0, Nat.mod_eq_of_lt hp]

theorem cornerS_exec (_hG : GoodEnv P) (hW : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {bit : ℕ} (hmd : c.nmem (c.nreg 83000 + 1) = bit) (hD : c.nreg 83000 + 1 ≤ W)
    (hp : c.nreg 83005 < P.n) (h23 : c.nreg 83023 = 1) :
    ∃ c' k, Exec P W cornerS c c' k ∧ k ≤ 50 ∧
      SymPtIn c' 50140 (.vtx (iIdx bit P.n ((c.nreg 83005 + P.n - 1) % P.n))) ∧
      SymPtIn c' 50143 (.vtx (iIdx bit P.n (c.nreg 83005))) ∧
      SymPtIn c' 50146 (.vtx (iIdx bit P.n ((c.nreg 83005 + 1) % P.n))) := by
  set p := c.nreg 83005
  have hn : 0 < P.n := ⋄
  set pe := (p + P.n - 1) % P.n with hpe
  have hpeL : pe < P.n := Nat.mod_lt _ hn
  obtain ⟨c₁, k₁, e₁, hk₁, q1⟩ : ∃ c₁ k₁, Exec P W
      (.seq (block [.copyN 50000 83000, .constN 50032 1])
        (.ifLtN 83005 83023 (block [.inputSize 50002, .subN 50002 50002 50032])
          (.instr (.subN 50002 83005 50032)))) c c₁ k₁ ∧ k₁ ≤ 6 ∧
      (c₁.nreg 50000 = c.nreg 83000 ∧ c₁.nreg 50002 = pe ∧ c₁.nmem = c.nmem ∧
        c₁.nreg 83005 = p) := by
    refine spec_seq ?_
    obtain ⟨c', k', e', hk', p00, p32, pm, p05, p23⟩ : ∃ c' k', Exec P W
        (block [.copyN 50000 83000, .constN 50032 1]) c c' k' ∧ k' = 2 ∧
        c'.nreg 50000 = c.nreg 83000 ∧ c'.nreg 50032 = 1 ∧ c'.nmem = c.nmem ∧
        c'.nreg 83005 = c.nreg 83005 ∧ c'.nreg 83023 = c.nreg 83023 := by
      exec_block
      · omega
      · exact ⟨rfl, by config_simp, by config_simp, rfl, by config_simp, by config_simp⟩
    refine ⟨c', k', e', ?_⟩
    have w' := e'.wb_right
    by_cases h0 : c'.nreg 83005 < c'.nreg 83023
    · refine spec_ifLtN_true h0 ?_
      have hp0 : p = 0 := by rw [p05, p23, h23] at h0; omega
      exec_block
      · omega
      · refine ⟨⋄, by config_simp; exact p00, ?_, pm, by config_simp; exact p05⟩
        config_simp
        Ξ p32, hpe, hp0, Nat.zero_add, Nat.mod_eq_of_lt (⋄)
    · refine spec_ifLtN_false h0 (spec_instr (Exec.subN w' _ _ _) fun _ => ?_)
      have hp1 : 0 < p := by rw [p05, p23, h23] at h0; omega
      refine ⟨⋄, by config_simp; exact p00, ?_, pm, by config_simp; exact p05⟩
      config_simp
      rw [p32, p05, hpe, show p + P.n - 1 = (p - 1) + P.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (⋄)]
  obtain ⟨q00, q02, qm, q05⟩ := q1
  obtain ⟨c₂, k₂, e₂, hk₂, r41, r44⟩ := intIdx_exec (P := P) hW c₁ e₁.wb_right
    (by rw [q02]; exact hpeL) (by rw [q00]; exact hD)
  Ξ' q00, q02, qm, hmd at r41 r44
  have w₂ := e₂.wb_right
  have f₂ : FrameB Bdir c₁ c₂ := exec_frameB e₂ wr_intIdx
  have q05' : c₂.nreg 83005 = p := Ρ f₂.1 83005 (⌖), q05
  have q00' : c₂.nreg 50000 = c.nreg 83000 := by
    Ξ f₂.1 50000 (⌖), q00
  have qm' : c₂.nmem = c.nmem := Ρ f₂.2.2.1, qm
  obtain ⟨c₃, k₃, e₃, hk₃, s141, s144, s02, s00, sm⟩ : ∃ c₃ k₃, Exec P W
      (block [.copyN 50141 50041, .copyN 50144 50044, .copyN 50002 83005]) c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 50141 = c₂.nreg 50041 ∧ c₃.nreg 50144 = c₂.nreg 50044 ∧
      c₃.nreg 50002 = c₂.nreg 83005 ∧ c₃.nreg 50000 = c₂.nreg 50000 ∧ c₃.nmem = c₂.nmem := by
    exec_block
    exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, rfl⟩
  obtain ⟨c₄, k₄, e₄, hk₄, t41, t44⟩ := intIdx_exec (P := P) hW c₃ e₃.wb_right
    (by rw [s02, q05']; exact hp) (by rw [s00, q00']; exact hD)
  Ξ' s00, q00', sm, qm', hmd, s02, q05' at t41 t44
  have f₄ : FrameB Bdir c₃ c₄ := exec_frameB e₄ wr_intIdx
  obtain ⟨c₅, k₅, e₅, hk₅, u147, u140, u143, u146, u141, u144⟩ : ∃ c₅ k₅, Exec P W
      (block [.copyN 50147 50044, .constN 50140 0, .constN 50143 0, .constN 50146 0]) c₄ c₅ k₅ ∧
      k₅ = 4 ∧ c₅.nreg 50147 = c₄.nreg 50044 ∧ c₅.nreg 50140 = 0 ∧ c₅.nreg 50143 = 0 ∧
      c₅.nreg 50146 = 0 ∧ c₅.nreg 50141 = c₄.nreg 50141 ∧ c₅.nreg 50144 = c₄.nreg 50144 := by
    have w₄ := e₄.wb_right
    exec_block
    · omega
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
        by config_simp⟩
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ⋄, ⟨u140, ?_⟩, ⟨u143, ?_⟩,
    ⟨u146, ?_⟩⟩
  · rw [u141, f₄.1 50141 (⌖), s141, r41]; rfl
  · rw [u144, f₄.1 50144 (⌖), s144, r44, prev_succ hp]; rfl
  · rw [u147, t44]; rfl


/-! ## Combining -/

/-- `50210 := (o ∧ n ∧ p) ∨ (¬ o ∧ (n ∨ p))` for the bits `o = 50150`, `n = 50130`,
`p = 50131`. -/
def combineS : Stmt :=
  .seq (.instr (.constN 50210 0)) (.ifLtN 50150 83023
    (.ifLtN 50130 83023 (.ifLtN 50131 83023 .skip (setB 50210)) (setB 50210))
    (.ifLtN 50130 83023 .skip (.ifLtN 50131 83023 .skip (setB 50210))))

theorem combineS_exec {c : Config} (hw : WordsBounded W c) (hW1 : 1 ≤ W) (h23 : c.nreg 83023 = 1)
    {po pn pp : Prop} (ho : BitIs c 50150 po) (hn : BitIs c 50130 pn) (hp : BitIs c 50131 pp) :
    ∃ c' k, Exec P W combineS c c' k ∧ k ≤ 8 ∧
      BitIs c' 50210 ((po ∧ pn ∧ pp) ∨ (¬ po ∧ (pn ∨ pp))) ∧
      ∀ r, r ≠ 50210 → c'.nreg r = c.nreg r := by
  have e₁ := Exec.constN (P := P) hw 50210 0 (⋄)
  set c₁ : Config := { c with nreg := upd c.nreg 50210 0 }
  have w₁ := e₁.wb_right
  have g : ∀ r, r ≠ 50210 → c₁.nreg r = c.nreg r := fun r hr => upd_ne hr
  have ho' := ho.of_eq (g 50150 (⌖))
  have hn' := hn.of_eq (g 50130 (⌖))
  have hp' := hp.of_eq (g 50131 (⌖))
  have h23' : c₁.nreg 83023 = 1 := by rw [g _ (⌖), h23]
  have h10 : c₁.nreg 50210 = 0 := by show upd c.nreg 50210 0 50210 = 0; exact upd_eq
  unfold combineS
  refine spec_seq ⟨c₁, 1, e₁, ?_⟩
  rcases bit01 ho' with ⟨qo, no⟩ | ⟨qo, no⟩ <;>
  rcases bit01 hn' with ⟨qn, nn⟩ | ⟨qn, nn⟩ <;>
  rcases bit01 hp' with ⟨qp, np⟩ | ⟨qp, np⟩
  all_goals
    repeat (first
      | (refine spec_ifLtN_true (⋄) ?_)
      | (refine spec_ifLtN_false (⋄) ?_))
  all_goals first
    | exact spec_skip w₁ ⟨⋄, ⟨by omega, by simp [h10, no, nn, np]⟩,
        fun r hr => g r hr⟩
    | exact spec_instr (Exec.constN w₁ _ _ hW1) fun _ => ⟨⋄, ⟨by simp [upd],
        ⊚ upd, no, nn, np⟩, fun r hr => by
          show upd c₁.nreg 50210 1 r = c.nreg r
          rw [upd_ne hr, g r hr]⟩


/-! ## The sector test -/

theorem primReg {r : ℕ} (h : (10000 ≤ r ∧ r < 20000) ∨ (50000 ≤ r ∧ r < 60000)) :
    bandOf r ∈ primBands ∧ r ≠ ALLOC := by
  refine ⟨?_, by unfold ALLOC; omega⟩
  ϴ primBands, bandOf, bSign, bLocate, Finset.mem_insert, Finset.mem_singleton
  omega

/-- Reset a turn code other than `1` to `0`. -/
def fixBit : Stmt := .ifLtN 83023 50210 (.instr (.constN 50210 0)) .skip

/-- The vertex case of the interior sector test. -/
def iVertexLeft : Stmt :=
  .seq tTurnN (.seq (copyBit 50130) (.seq tTurnP (.seq (copyBit 50131) (.seq cornerS
    (.seq (kbit 50140 50143 50146 2 50150) combineS)))))

/-- **The sector test of the interior model.** -/
def iLeft : Stmt := .ifLtN 83006 83023 iVertexLeft (.seq tTurnN fixBit)

theorem interior_vtx {bit : ℕ} (hbit : bit = 1 ↔ Mountain.LeftInside (Qof P)) {q : ℕ}
    (hq : q < P.n) : (interiorModel (Qof P)).W.vtx q = (Qof P).vtx (iIdx bit P.n q) :=
  interior_wa hbit hq

theorem iIdx_inj {bit n p q : ℕ} (hp : p < n) (hq : q < n) (h : iIdx bit n p = iIdx bit n q) :
    p = q := by
  unfold iIdx at h; split_ifs at h <;> omega

theorem wr_combineS : wr (fun q => q == 50210) combineS = true := ⌖

theorem iLeft_ok_vertex (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hM : M = interiorModel (Qof P)) (hbit : c₀.nmem (c₀.nreg 83000 + 1) = 1 ↔
      Mountain.LeftInside (Qof P)) (hv : c₀.nreg 83006 = 0)
    (hroom : c.nreg ALLOC + 11000 ≤ W) :
    ∃ c' k, Exec P W iVertexLeft c c' k ∧ k ≤ 11000 ∧
      BitIs c' 50210 (LeftB M P (xOf c₀) (c₀.nreg 83008)) ∧ TStep W c₀ c c' k := by
  have hG := hE.hG
  have hWn : P.n + 3 ≤ W := by have := hE.hW; unfold hostWords at this; omega
  have hn3 := hG.1.1
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : M.W.n = P.n := by rw [hM]; exact interior_n
  have hp : c₀.nreg 83005 < P.n := by rw [← hn]; exact hE.hxe
  set bit := c₀.nmem (c₀.nreg 83000 + 1)
  have hbit' := hbit
  -- the next turn
  obtain ⟨c₁, k₁, e₁, hk₁, t₁, s₁⟩ := turn_ok.1 P W M N c₀ c hE hI (⋄)
  have f₁ : FrameB Bturn c c₁ := exec_frameB e₁ wr_tTurnN
  obtain ⟨c₂, k₂, e₂, hk₂, b₂0, b₂, s₂, f₂⟩ := copyBit_exec (P := P) (r := 50130) (⋄)
    s₁.1 t₁
  -- the previous turn
  obtain ⟨c₃, k₃, e₃, hk₃, t₃, s₃⟩ := turn_ok.2 P W M N c₀ c₂ hE s₂.1 hv
    (by have := s₁.2.1.2.2.2.2.2.2; have := s₂.2.1.2.2.2.2.2.2; omega)
  have f₃ : FrameB Bturn c₂ c₃ := exec_frameB e₃ wr_tTurnP
  obtain ⟨c₄, k₄, e₄, hk₄, b₄0, b₄, s₄, f₄⟩ := copyBit_exec (P := P) (r := 50131) (⋄)
    s₃.1 t₃
  have hA₄ : c₄.nreg ALLOC ≤ c.nreg ALLOC + (k₁ + k₂ + k₃ + k₄) := by
    have := s₁.2.1.2.2.2.2.2.2; have := s₂.2.1.2.2.2.2.2.2; have := s₃.2.1.2.2.2.2.2.2
    have := s₄.2.1.2.2.2.2.2.2; omega
  have n30 : c₄.nreg 50130 = c₂.nreg 50130 := by
    Ξ f₄.1 50130 (⌖), f₃.1 50130 (⌖)
  -- the corner
  have hI₄ := s₄.1
  have i0 := hI₄.hin 83000 (⊛) (⊛)
  have i5 := hI₄.hin 83005 (⊛) (⊛)
  have hmd : c₄.nmem (c₄.nreg 83000 + 1) = bit := by
    Ξ i0, hI₄.hm _ (by have := hE.hwfMD.1; omega)
  have hD : c₄.nreg 83000 + 1 ≤ W := by
    have := (hI₄.modelDesc hE).2.1; have := hI₄.hw.1 ALLOC; omega
  obtain ⟨c₅, k₅, e₅, hk₅, y40, y43, y46⟩ := cornerS_exec (P := P) hG hWn hI₄.hw hmd hD
    (by rw [i5]; exact hp) hI₄.h23
  Ξ' i5 at y40 y43 y46
  have f₅ : FrameB Bcor c₄ c₅ := exec_frameB e₅ wr_cornerS
  have s₅ : TStep W c₀ c₄ c₅ k₅ := hI₄.stepB e₅.wb_right f₅ (fun r hr => primReg (by
    ϴ' Bcor, Bdir, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq at hr; omega)) k₅
  -- the orientation
  set p := c₀.nreg 83005
  set pe := (p + P.n - 1) % P.n
  set pb := (p + 1) % P.n
  have hpe : pe < P.n := Nat.mod_lt _ (⋄)
  have hpb : pb < P.n := Nat.mod_lt _ (⋄)
  obtain ⟨c₆, k₆, e₆, hk₆, f₆, o₆0, o₆⟩ := kbit_exec (P := P) hG hWn c₅ e₅.wb_right
    (a := 50140) (b := 50143) (d := 50146) (op := 2) (dst := 50150)
    (sa := .vtx (iIdx bit P.n pe)) (sb := .vtx (iIdx bit P.n p)) (sd := .vtx (iIdx bit P.n pb))
    (⊛) (⊛) (⊛) (⊛) (⊛)
    (show (iIdx bit P.n pe) < P.n from iIdx_lt hpe) (show (iIdx bit P.n p) < P.n from iIdx_lt hp)
    (show (iIdx bit P.n pb) < P.n from iIdx_lt hpb) y40 y43 y46
  have s₆ : TStep W c₀ c₅ c₆ k₆ := s₅.1.stepB e₆.wb_right f₆ (fun r hr => primReg (by
    ϴ' Bkb, WalkKey.Bk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq at hr; omega)) k₆
  -- the combination
  have g30 : c₆.nreg 50130 = c₂.nreg 50130 := by
    Ξ f₆.1 50130 (⌖), f₅.1 50130 (⌖), n30
  have g31 : c₆.nreg 50131 = c₄.nreg 50131 := by
    Ξ f₆.1 50131 (⌖), f₅.1 50131 (⌖)
  obtain ⟨c₇, k₇, e₇, hk₇, bit₇, -⟩ := combineS_exec (P := P) e₆.wb_right (⋄)
    s₆.1.h23 ⟨o₆0, o₆⟩ (BitIs.of_eq ⟨b₂0, b₂⟩ g30) (BitIs.of_eq ⟨b₄0, b₄⟩ g31)
  have f₇ : FrameB (fun q => q == 50210) c₆ c₇ := exec_frameB e₇ wr_combineS
  have s₇ : TStep W c₀ c₆ c₇ k₇ := s₆.1.stepB e₇.wb_right f₇ (fun r hr => primReg (by
    ϴ' beq_iff_eq at hr; omega)) k₇
  refine ⟨c₇, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + k₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ⋄, ?_,
    s₁.trans (s₂.trans (s₃.trans (s₄.trans (s₅.trans (s₆.trans s₇)))))⟩
  refine ⟨bit₇.1, bit₇.2.trans ?_⟩
  -- the corner in terms of the walk
  have hx0 : M.param (Qof P) (xOf c₀) = 0 := WalkKey.param_of_code_zero hv
  have wv : M.W.vtx p = (Qof P).vtx (iIdx bit P.n p) := by rw [hM]; exact interior_vtx hbit' hp
  have wb : M.W.vtx ((p + 1) % M.W.n) = (Qof P).vtx (iIdx bit P.n pb) := by
    rw [hn, hM]; exact interior_vtx hbit' hpb
  have wa : M.W.vtx ((p + M.W.n - 1) % M.W.n) = (Qof P).vtx (iIdx bit P.n pe) := by
    rw [hn, hM]; exact interior_vtx hbit' hpe
  have hD' := distinct_Qof hG
  have hne : ∀ q, q < P.n → q ≠ p → ((Qof P).vtx (iIdx bit P.n q)).2 ≠
      ((Qof P).vtx (iIdx bit P.n p)).2 := fun q hq hqp => hD' _ _ (by rw [hQn]; exact iIdx_lt hq)
    (by rw [hQn]; exact iIdx_lt hp) (fun h => hqp (iIdx_inj hq hp h))
  have hbp : pb ≠ p := by
    intro h
    ϴ' pb at h
    rcases Nat.lt_or_ge (p + 1) P.n with h1 | h1
    · Ξ' Nat.mod_eq_of_lt h1 at h; omega
    · have : p + 1 = P.n := ⋄
      Ξ' this, Nat.mod_self at h; omega
  have hep : pe ≠ p := by
    intro h
    have h2 := prev_succ (n := P.n) hp
    Ξ' show (p + P.n - 1) % P.n = pe from rfl, h at h2
    exact hbp h2
  have hcross : sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p)
      (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) =
      det ((Qof P).vtx (iIdx bit P.n pe)) ((Qof P).vtx (iIdx bit P.n p))
        ((Qof P).vtx (iIdx bit P.n pb)) := by
    Ξ wb, wv, wa, Chazelle.Chain.sideCross_corner
  have hb' : (M.W.vtx (((xOf c₀).edge + 1) % M.W.n)).2 ≠ (M.W.vtx (xOf c₀).edge).2 := by
    show (M.W.vtx ((p + 1) % M.W.n)).2 ≠ (M.W.vtx p).2
    rw [wb, wv]; exact hne _ hpb hbp
  have ha' : (M.W.vtx (((xOf c₀).edge + M.W.n - 1) % M.W.n)).2 ≠ (M.W.vtx (xOf c₀).edge).2 := by
    show (M.W.vtx ((p + M.W.n - 1) % M.W.n)).2 ≠ (M.W.vtx p).2
    rw [wa, wv]; exact hne _ hpe hep
  Ξ left_vertex_iff hx0 hb' ha'
  show _ ↔ (0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p)
      (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) ∧ _) ∨
    (¬ 0 < sideCross (M.W.vtx ((p + 1) % M.W.n) - M.W.vtx p)
      (M.W.vtx ((p + M.W.n - 1) % M.W.n) - M.W.vtx p) ∧ _)
  Ξ hcross
  ϴ SymPt.eval, SignTest

end

end Restore

end Chazelle.Core
