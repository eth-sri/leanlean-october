module

public import Chazelle.Core.DownPhaseOracleRamB
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ConfigTactics

/-!
# WP-M (E7-B, RAM part 3): the normalized query

`normI` computes, from the saved subarc ends `⟨e₁, h₁⟩`, `⟨e₂, h₂⟩`:

* `170030`: the normalized end code `h₂' = nh e₂ h₂` (`normA`);
* `170031`: the offset `ee = eeOf e₁ h₁ e₂ h₂'` of the end edge (`normB`, `normC`; on one edge,
  the key order by two sign tests, `ltS`);
* `170032`: the number `L = spanL ee h₂'` of walk edges met (`normD`).

Scratch: `170092 … 170129` and the sign kernel.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

variable {Q : Polygon}

/-! ## Mathematics -/

/-- The height vertex of a position of the interior walk (the start vertex for the code `0`). -/
noncomputable def hI (Q : Polygon) (e h : ℕ) : ℕ := if h = 0 then iv Q e else h - 1

theorem mi_hgtY {e h : ℕ} (he : e < Q.n) :
    (interiorModel Q).hgtY Q ⟨e, h⟩ = (Q.vtx (hI Q e h)).2 := by
  unfold hI Model.hgtY
  cases h with
  | zero => simp only [↓reduceIte]; rw [mi_wa he]
  | succ h => simp

/-- **Parameters on one edge of the interior walk** compare like the heights of their height
vertices, in the direction of the edge. -/
theorem param_lt_iff_iw (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {e h h' : ℕ} (he : e < Q.n) :
    (interiorModel Q).param Q ⟨e, h⟩ < (interiorModel Q).param Q ⟨e, h'⟩ ↔
      ((Q.vtx (iv Q e)).2 < (Q.vtx (iv Q ((e + 1) % Q.n))).2 ∧
          (Q.vtx (hI Q e h)).2 < (Q.vtx (hI Q e h')).2) ∨
        (¬ (Q.vtx (iv Q e)).2 < (Q.vtx (iv Q ((e + 1) % Q.n))).2 ∧
          (Q.vtx (hI Q e h')).2 < (Q.vtx (hI Q e h)).2) := by
  have hnh : ((interiorModel Q).wa e).2 ≠ ((interiorModel Q).wb e).2 := by
    rw [mi_wa he, mi_wb he]
    refine hD _ _ (iv_lt he) (iv_lt (Nat.mod_lt _ (by omega))) ?_
    unfold iv
    split_ifs
    · intro hc
      rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
      · rwo [Nat.mod_eq_of_lt h3] at hc
      · rwo [h3, Nat.mod_self] at hc
    · intro hc
      rcases (show e + 1 < Q.n ∨ e + 1 = Q.n by omega) with h3 | h3
      · rwo [Nat.mod_eq_of_lt h3] at hc
      · rwo [h3, Nat.mod_self] at hc
  have hk := Model.key_lt_key_iff_of_same_edge (M := interiorModel Q) (Q := Q)
    (x := ⟨e, h⟩) (y := ⟨e, h'⟩) rfl hnh
  unfold Model.key at hk
  simp only [add_lt_add_iff_left] at hk
  rw [hk, mi_hgtY he, mi_hgtY he, mi_wa he, mi_wb he]
  have hnh' := hnh
  rw [mi_wa he, mi_wb he] at hnh'
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨by linarith, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨lt_of_le_of_ne (not_lt.1 h1) (Ne.symm hnh'), h2⟩

theorem dOf_eq {n e₁ e₂ : ℕ} (h1 : e₁ < n) (h2 : e₂ < n) :
    WalkEmbed.dOf n e₁ e₂ = if e₂ + n - e₁ < n then e₂ + n - e₁ else e₂ + n - e₁ - n := by
  unfold WalkEmbed.dOf
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-! ## The programs -/

/-- The normalized end code into `170030`. -/
def normA : Stmt :=
  .seq (block [.copyN 170095 170003]) (.seq ivF
    (.seq (block [.copyN 170100 170096, .copyN 170030 170004, .subN 170101 170004 170011])
      (.ifLtN 170012 170004
        (.ifLtN 170101 170100 .skip (.ifLtN 170100 170101 .skip (block [.constN 170030 0])))
        .skip)))

/-- `170102 := dOf n e₁ e₂`. -/
def normB : Stmt :=
  .seq (block [.addN 170102 170003 170010, .subN 170102 170102 170001])
    (.ifLtN 170102 170010 .skip (block [.subN 170102 170102 170010]))

/-- The kernel slots of the key comparison on one edge. -/
def ltSlots : Stmt :=
  block [.constN 170110 0, .copyN 170111 170106, .constN 170113 0, .copyN 170114 170107,
    .constN 170116 0, .copyN 170117 170104, .constN 170119 0, .copyN 170120 170105]

/-- The preparation of the key comparison: the four height vertices into the kernel slots. -/
def ltPrep : Stmt :=
  .seq (block [.copyN 170095 170001]) (.seq ivF
    (.seq (block [.copyN 170106 170096, .addN 170095 170001 170011])
      (.seq (.ifLtN 170095 170010 .skip (block [.constN 170095 0]))
        (.seq ivF
          (.seq (block [.copyN 170107 170096, .copyN 170104 170106, .subN 170105 170030 170011])
            (.seq (.ifLtN 170012 170002 (block [.subN 170104 170002 170011]) .skip)
              ltSlots))))))

/-- The two sign tests of the key comparison. -/
def ltKer : Stmt :=
  .seq (SweepPrim.kbit 170110 170113 170110 1 170108)
    (.ifLtN 170012 170108 (SweepPrim.kbit 170116 170119 170116 1 170103)
      (SweepPrim.kbit 170119 170116 170119 1 170103))

/-- **The key order on the start edge** (`170103`), for a nonzero end code. -/
def ltK : Stmt := .seq ltPrep ltKer

/-- The key order on the start edge: false for the end code `0`. -/
def ltS : Stmt := .ifLtN 170030 170011 (block [.constN 170103 0]) ltK

/-- The offset of the end edge into `170031`. -/
def normC : Stmt :=
  .ifLtN 170012 170102 (block [.copyN 170031 170102])
    (.seq ltS (.ifLtN 170012 170103 (block [.constN 170031 0]) (block [.copyN 170031 170010])))

/-- The number of edges met into `170032`. -/
def normD : Stmt :=
  .seq (block [.copyN 170032 170031])
    (.ifLtN 170012 170030 (block [.addN 170032 170032 170011]) .skip)

/-- **The normalized query.** -/
def normI : Stmt := .seq normA (.seq normB (.seq normC normD))

/-- The registers `normI` writes: `170030 … 170032`, the scratch `170090 … 170129`, the
kernel. -/
def Bnorm (r : ℕ) : Bool :=
  decide (170030 ≤ r ∧ r < 170033) || decide (170090 ≤ r ∧ r < 170130) || Bk r

theorem wr_normI : wr Bnorm normI = true := by
  have hk : ∀ a b d op dst, 170090 ≤ dst → dst < 170130 → wr Bnorm (SweepPrim.kbit a b d op dst) = true :=
    fun a b d op dst h1 h2 => SweepPrim.wr_mono (SweepPrim.wr_kbit a b d op dst) (fun r hr => by
      simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      unfold Bnorm; rcases hr with hr | hr
      · simp [hr]
      · subst hr; sio)
  simp only [normI, normA, normB, normC, normD, ltS, ltK, ltPrep, ltKer, ltSlots, ivF, wr, block,
    wrOK,
    hk _ _ _ _ 170108 (by norm_num) (by norm_num), hk _ _ _ _ 170103 (by norm_num) (by norm_num),
    Bool.and_true, Bool.true_and]
  decide

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **The normalized end code.** -/
theorem normA_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) :
    ∃ c' k, Exec P W normA c c' k ∧ k ≤ 14 ∧ c'.nreg 170030 = nh (Qof P) s.e₂ s.h₂ ∧
      (∀ r, r ≠ 170030 → r ≠ 170095 → r ≠ 170096 → r ≠ 170100 → r ≠ 170101 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold normA
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := ivF_exec (P := P) _ ‹_› (by config_simp; exact hS.r11)
  refine ⟨_, _, e₁, ?_⟩
  have w₁ := e₁.wb_right
  refine spec_seq ?_
  exec_block
  have hσ : ivV (c.nreg 170014) (c.nreg 170019) (c.nreg 170003) = iv (Qof P) s.e₂ := by
    rw [hS.ivv, hS.r3]
  by_cases h0 : c.nreg 170012 < c.nreg 170004
  · refine spec_ifLtN_true (by config_simp; exact h0) ?_
    by_cases h1 : c.nreg 170004 - 1 < iv (Qof P) s.e₂
    · refine spec_ifLtN_true (by config_simp; rwx [hS.r11, hσ]) ?_
      refine spec_skip ‹_› ⟨by omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; unfold nh; rw [hS.r4, ite_eq_right (by rwo [hS.r4] at h1)]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    by_cases h2 : iv (Qof P) s.e₂ < c.nreg 170004 - 1
    · refine spec_ifLtN_false (by config_simp; rwx [hS.r11, hσ])
        (spec_ifLtN_true (by config_simp; rwx [hS.r11, hσ]) ?_)
      refine spec_skip ‹_› ⟨by omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; unfold nh; rw [hS.r4, ite_eq_right (by rwo [hS.r4] at h2)]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rwx [hS.r11, hσ])
        (spec_ifLtN_false (by config_simp; rwx [hS.r11, hσ]) ?_)
      exec_block
      all_goals first | omega | skip
      refine ⟨by omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; unfold nh
        rw [hS.r12, hS.r4] at h0; rw [hS.r4] at h1 h2
        rw [ite_eq_left ⟨by omega, by omega⟩]
      · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by config_simp; exact h0) ?_
    refine spec_skip ‹_› ⟨by omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; unfold nh; rw [hS.r12, hS.r4] at h0; rw [hS.r4, ite_eq_right (by omega)]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega

/-- **The offset of the end edge** (`dOf`). -/
theorem normB_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (h1 : s.e₁ < P.n) (h2 : s.e₂ < P.n) :
    ∃ c' k, Exec P W normB c c' k ∧ k ≤ 5 ∧ c'.nreg 170102 = WalkEmbed.dOf P.n s.e₁ s.e₂ ∧
      c' = { c with nreg := upd c.nreg 170102 (c'.nreg 170102) } := by
  have hW := hS.hW
  unfold hostWords at hW
  unfold normB
  refine spec_seq ?_
  exec_block
  · config_simp; rwo [hS.r3, hS.r10]
  by_cases hc : s.e₂ + P.n - s.e₁ < P.n
  · refine spec_ifLtN_true (by config_simp; rwx [hS.r3, hS.r10, hS.r1]) ?_
    refine spec_skip ‹_› ⟨by omega, ?_, ?_⟩
    · config_simp; rw [hS.r3, hS.r10, hS.r1, dOf_eq h1 h2, ite_eq_left hc]
    · simp only [Config.nreg_mk, upd_upd_same, upd_same]
  · refine spec_ifLtN_false (by config_simp; rwx [hS.r3, hS.r10, hS.r1]) ?_
    exec_block
    refine ⟨by omega, ?_, ?_⟩
    · config_simp; rw [hS.r3, hS.r10, hS.r1, dOf_eq h1 h2, ite_eq_right hc]
    · simp only [Config.nreg_mk, upd_upd_same, upd_same]

end exec

/-- The registers `ltS` writes. -/
def BltS (r : ℕ) : Bool :=
  decide (r = 170092 ∨ r = 170095 ∨ r = 170096 ∨ (170103 ≤ r ∧ r < 170122)) || Bk r

theorem wr_ltS : wr BltS ltS = true := by
  have hk : ∀ a b d op dst, 170103 ≤ dst → dst < 170122 →
      wr BltS (SweepPrim.kbit a b d op dst) = true :=
    fun a b d op dst h1 h2 => SweepPrim.wr_mono (SweepPrim.wr_kbit a b d op dst) (fun r hr => by
      simp only [SweepPrim.Bkb, Bool.or_eq_true, beq_iff_eq] at hr
      unfold BltS; rcases hr with hr | hr
      · simp [hr]
      · subst hr; sio)
  simp only [ltS, ltK, ltPrep, ltKer, ltSlots, ivF, wr, block, wrOK,
    hk _ _ _ _ 170108 (by norm_num) (by norm_num), hk _ _ _ _ 170103 (by norm_num) (by norm_num),
    Bool.and_true, Bool.true_and]
  decide

section exec2

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The registers `ltPrep` writes. -/
def Bprep (r : ℕ) : Bool :=
  decide (r = 170092 ∨ r = 170095 ∨ r = 170096 ∨ (170104 ≤ r ∧ r < 170122))

theorem wr_ltPrep : wr Bprep ltPrep = true := by decide

/-- **The preparation**: the kernel slots hold the vertices `iv e₁`, `iv (e₁ + 1)` (the ends of
the start edge) and the height vertices of the two positions. -/
theorem ltPrep_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) {h₂ : ℕ} (h30 : c.nreg 170030 = h₂) :
    ∃ c' k, Exec P W ltPrep c c' k ∧ k ≤ 40 ∧
      SymPtIn c' 170110 (.vtx (iv (Qof P) s.e₁)) ∧
      SymPtIn c' 170113 (.vtx (iv (Qof P) ((s.e₁ + 1) % P.n))) ∧
      SymPtIn c' 170116 (.vtx (hI (Qof P) s.e₁ s.h₁)) ∧
      SymPtIn c' 170119 (.vtx (h₂ - 1)) ∧ FrameB Bprep c c' := by
  have hW := hS.nW
  obtain ⟨c', k, ex, hk, post⟩ : ∃ c' k, Exec P W ltPrep c c' k ∧ k ≤ 40 ∧
      (SymPtIn c' 170110 (.vtx (iv (Qof P) s.e₁)) ∧
      SymPtIn c' 170113 (.vtx (iv (Qof P) ((s.e₁ + 1) % P.n))) ∧
      SymPtIn c' 170116 (.vtx (hI (Qof P) s.e₁ s.h₁)) ∧
      SymPtIn c' 170119 (.vtx (h₂ - 1))) := by
    unfold ltPrep
    refine spec_seq ?_
    exec_block
    refine spec_seq ?_
    obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := ivF_exec (P := P) _ ‹_› (by config_simp; exact hS.r11)
    refine ⟨_, _, e₁, ?_⟩
    have w₁ := e₁.wb_right
    refine spec_seq ?_
    exec_block
    · config_simp; rwo [hS.r1, hS.r11]
    refine spec_seq ?_
    -- `(e₁ + 1) mod n` in `170095`
    obtain ⟨k₂, e₂, hk₂⟩ := exec_ite_upd (P := P) (W := W) (a := 170095) (b := 170010)
      (r := 170095) (s₁ := .skip) (s₂ := block [.constN 170095 0]) (v₂ := 0) (K := 1) _
      (fun _ => ⟨0, exec_skip_upd ‹_› 170095, by omega⟩)
      (fun _ => ⟨1, exec_constN_upd ‹_› 170095 0 (by omega), le_rfl⟩)
    refine ⟨_, _, e₂, ?_⟩
    have w₂ := e₂.wb_right
    refine spec_seq ?_
    obtain ⟨c₃, k₃, e₃, hk₃, rfl⟩ := ivF_exec (P := P) _ w₂ (by config_simp; exact hS.r11)
    refine ⟨_, _, e₃, ?_⟩
    have w₃ := e₃.wb_right
    refine spec_seq ?_
    exec_block
    refine spec_seq ?_
    obtain ⟨k₄, e₄, hk₄⟩ := exec_ite_upd (P := P) (W := W) (a := 170012) (b := 170002)
      (r := 170104) (s₁ := block [.subN 170104 170002 170011]) (s₂ := .skip) (K := 1) _
      (fun _ => ⟨1, exec_subN_upd ‹_› 170104 170002 170011, le_rfl⟩)
      (fun _ => ⟨0, exec_skip_upd ‹_› 170104, by omega⟩)
    refine ⟨_, _, e₄, ?_⟩
    have w₄ := e₄.wb_right
    unfold ltSlots
    exec_block
    all_goals first | omega | skip
    have hlb := hS.lb
    have hlb1 := hS.lb1
    have hQ : (Qof P).n = P.n := shear_n _ _
    refine ⟨by omega, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩,
      ⟨by config_simp, ?_⟩⟩
    · config_simp; rw [hS.ivv, hS.r1]
    · config_simp
      rw [hS.r1, hS.r11, hS.r10, hS.ivv]
      congr 1
      split_ifs with hc
      · rw [Nat.mod_eq_of_lt hc]
      · rw [show s.e₁ + 1 = P.n by omega, Nat.mod_self]
    · config_simp
      rw [hS.r12, hS.r2, hS.r11, hS.ivv, hS.r1]
      unfold hI
      split_ifs with h1 h2 h2 <;> first | rfl | omega
    · config_simp; rw [h30, hS.r11]
  exact ⟨c', k, ex, hk, post.1, post.2.1, post.2.2.1, post.2.2.2, exec_frameB ex wr_ltPrep⟩

/-- **The two sign tests**: the bit `170103` is the key order of the two positions. -/
theorem ltKer_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (h12 : c.nreg 170012 = 0) {a b x y : ℕ} (ha : a < P.n) (hb : b < P.n) (hx : x < P.n)
    (hy : y < P.n) (s1 : SymPtIn c 170110 (.vtx a)) (s2 : SymPtIn c 170113 (.vtx b))
    (s3 : SymPtIn c 170116 (.vtx x)) (s4 : SymPtIn c 170119 (.vtx y)) :
    ∃ c' k, Exec P W ltKer c c' k ∧ k ≤ 490 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 ∧ ((Qof P).vtx x).2 < ((Qof P).vtx y).2 ∨
        ¬ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 ∧ ((Qof P).vtx y).2 < ((Qof P).vtx x).2) := by
  unfold ltKer
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, b₁, t₁⟩ := SweepPrim.kbit_exec (P := P) hG hW c hw
    (a := 170110) (b := 170113) (d := 170110) (op := 1) (dst := 170108) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sa := .vtx a) (sb := .vtx b)
    (sd := .vtx a) ha hb ha s1 s2 s1
  have kp : ∀ r, 10500 ≤ r → r ≠ 170108 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    F₁.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; exact ⟨by omega, h2⟩)
  have s3' : SymPtIn c₁ 170116 (.vtx x) := NFLoc.symPtIn_copy s3 (kp _ (by omega) (by omega))
    (kp _ (by omega) (by omega)) (kp _ (by omega) (by omega))
  have s4' : SymPtIn c₁ 170119 (.vtx y) := NFLoc.symPtIn_copy s4 (kp _ (by omega) (by omega))
    (kp _ (by omega) (by omega)) (kp _ (by omega) (by omega))
  simp only [SignTest, SymPt.eval] at t₁
  have h12' : c₁.nreg 170012 = 0 := by rw [kp _ (by omega) (by omega), h12]
  by_cases hup : c₁.nreg 170012 < c₁.nreg 170108
  · obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec (P := P) hG hW c₁ e₁.wb_right
      (a := 170116) (b := 170119) (d := 170116) (op := 1) (dst := 170103) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sa := .vtx x) (sb := .vtx y)
      (sd := .vtx x) hx hy hx s3' s4' s3'
    simp only [SignTest, SymPt.eval] at t₂
    have hu : ((Qof P).vtx a).2 < ((Qof P).vtx b).2 := t₁.1 (by omega)
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true hup e₂), by omega, b₂, ?_⟩
    rw [t₂]
    constructor
    · intro h; exact Or.inl ⟨hu, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd hu h
  · obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec (P := P) hG hW c₁ e₁.wb_right
      (a := 170119) (b := 170116) (d := 170119) (op := 1) (dst := 170103) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (sa := .vtx y) (sb := .vtx x)
      (sd := .vtx y) hy hx hy s4' s3' s4'
    simp only [SignTest, SymPt.eval] at t₂
    have hu : ¬ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 := fun h => by
      have := t₁.2 h; omega
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false hup e₂), by omega, b₂, ?_⟩
    rw [t₂]
    constructor
    · intro h; exact Or.inr ⟨hu, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hu
      · exact h

/-- **The key order on the start edge** (`170103`, for the end code in `170030`). -/
theorem ltS_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (hh1 : s.h₁ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩) {h₂ : ℕ}
    (h30 : c.nreg 170030 = h₂) (h2n : h₂ ≤ P.n) :
    ∃ c' k, Exec P W ltS c c' k ∧ k ≤ 840 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩ <
        (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, h₂⟩) ∧ FrameB BltS c c' := by
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hD  := ShootCut.goodEnv_distinct hS.good
  have hn := hS.n3
  have hW := hS.nW
  obtain ⟨c', k, ex, hk, b, t⟩ : ∃ c' k, Exec P W ltS c c' k ∧ k ≤ 840 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩ <
        (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, h₂⟩) := by
    unfold ltS
    by_cases h0 : c.nreg 170030 < c.nreg 170011
    · have hz : h₂ = 0 := by rw [← h30]; rwo [hS.r11] at h0
      refine spec_ifLtN_true h0 ?_
      exec_block
      all_goals first | omega | skip
      refine ⟨by omega, by cso, ?_⟩
      config_simp
      rw [hz, param_zero]
      constructor
      · intro h; exact absurd h (by simp)
      · intro h; linarith
    · refine spec_ifLtN_false h0 ?_
      have h21 : 1 ≤ h₂ := by rw [← h30]; rwo [hS.r11] at h0
      obtain ⟨c₁, k₁, e₁, hk₁, s1, s2, s3, s4, F₁⟩ := ltPrep_exec c hw hS he1 h30
      have k12 : c₁.nreg 170012 = 0 := by
        rw [F₁.1 _ (by ufd Bprep)]; exact hS.r12
      have hl : ∀ {i}, i < P.n → i < P.n := id
      obtain ⟨c₂, k₂, e₂, hk₂, b₂, t₂⟩ := ltKer_exec c₁ e₁.wb_right hS.good hW k12
        (by have := iv_lt (Q := Qof P) (p := s.e₁) (by rwx [hQ]); rwa [hQ] at this) (by
          have := iv_lt (Q := Qof P) (p := (s.e₁ + 1) % P.n) (by rw [hQ]; exact Nat.mod_lt _ (by omega))
          rwa [hQ] at this)
        (by unfold hI; split_ifs
            · have := iv_lt (Q := Qof P) (p := s.e₁) (by rwx [hQ]); rwa [hQ] at this
            · omega)
        (by omega) s1 s2 s3 s4
      refine ⟨c₂, _, .seq e₁ e₂, by omega, b₂, ?_⟩
      rw [t₂, param_lt_iff_iw hD (by rwx [hQ]) (by rwx [hQ]), hQ]
      have : hI (Qof P) s.e₁ h₂ = h₂ - 1 := by unfold hI; rw [ite_eq_right (by omega)]
      rw [this]
  exact ⟨c', k, ex, hk, b, t, exec_frameB ex wr_ltS⟩

theorem wr_normC : wr (fun r => BltS r || decide (r = 170031)) normC = true := by
  have h := wr_ltS
  simp only [normC, wr, block, wrOK, Bool.and_true, Bool.true_and]
  refine Bool.and_eq_true_iff.2 ⟨by decide, Bool.and_eq_true_iff.2
    ⟨SweepPrim.wr_mono h (fun r hr => by simp [hr]), by decide⟩⟩

/-- **The offset of the end edge** into `170031`. -/
theorem normC_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (he2 : s.e₂ < P.n) (hh1 : s.h₁ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩) {h₂ : ℕ}
    (h30 : c.nreg 170030 = h₂) (h2n : h₂ ≤ P.n)
    (h102 : c.nreg 170102 = WalkEmbed.dOf P.n s.e₁ s.e₂) :
    ∃ c' k, Exec P W normC c c' k ∧ k ≤ 850 ∧ c'.nreg 170031 = eeOf (Qof P) s.e₁ s.h₁ s.e₂ h₂ ∧
      (∀ r, r ≠ 170031 → BltS r = false → c'.nreg r = c.nreg r) := by
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hW := hS.nW
  unfold normC eeOf
  rw [hQ]
  by_cases hd : c.nreg 170012 < c.nreg 170102
  · refine spec_ifLtN_true hd ?_
    exec_block
    refine ⟨by omega, ?_, fun r h1 h2 => ?_⟩
    · config_simp; rw [h102, ite_eq_right (by rwo [hS.r12, h102] at hd)]
    · simp only [Config.nreg_mk, upd]; split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false hd ?_
    have hd0 : WalkEmbed.dOf P.n s.e₁ s.e₂ = 0 := by rwo [hS.r12, h102] at hd
    have he : s.e₂ = s.e₁ := by
      have := WalkEmbed.add_dOf he1 he2
      rw [hd0, Nat.add_zero, Nat.mod_eq_of_lt he1] at this; exact this.symm
    obtain ⟨c₁, k₁, e₁, hk₁, b₁, t₁, F₁⟩ := ltS_exec c hw hS he1 hh1 hx0 h30 h2n
    have k12 : c₁.nreg 170012 = 0 := by
      rw [F₁.1 _ (by ufd BltS Bk)]; exact hS.r12
    have k10 : c₁.nreg 170010 = P.n := by
      rw [F₁.1 _ (by ufd BltS Bk)]; exact hS.r10
    have w₁ := e₁.wb_right
    refine spec_seq ⟨c₁, k₁, e₁, ?_⟩
    rw [ite_eq_left hd0, he]
    by_cases hb : c₁.nreg 170012 < c₁.nreg 170103
    · refine spec_ifLtN_true hb ?_
      exec_block
      all_goals first | omega | skip
      refine ⟨by omega, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [ite_eq_left (t₁.1 (by omega))]
      · simp only [Config.nreg_mk, upd]; rw [ite_eq_right h1]; exact F₁.1 r h2
    · refine spec_ifLtN_false hb ?_
      exec_block
      refine ⟨by omega, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [k10, ite_eq_right (fun h => by have := t₁.2 h; omega)]
      · simp only [Config.nreg_mk, upd]; rw [ite_eq_right h1]; exact F₁.1 r h2

/-- **The number of edges met** into `170032`. -/
theorem normD_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {h₂ ee : ℕ}
    (h30 : c.nreg 170030 = h₂) (h31 : c.nreg 170031 = ee) (hee : ee + 1 ≤ W) :
    ∃ c' k, Exec P W normD c c' k ∧ k ≤ 4 ∧ c'.nreg 170032 = spanL ee h₂ ∧
      c' = { c with nreg := upd c.nreg 170032 (c'.nreg 170032) } := by
  unfold normD spanL
  refine spec_seq ?_
  exec_block
  by_cases h : c.nreg 170012 < c.nreg 170030
  · refine spec_ifLtN_true (by config_simp; exact h) ?_
    exec_block
    · config_simp; rwo [h31, hS.r11]
    refine ⟨by omega, ?_, ?_⟩
    · config_simp; rw [h31, hS.r11, ite_eq_right (by rwo [hS.r12, h30] at h)]
    · simp only [Config.nreg_mk, upd_upd_same, upd_same]
  · refine spec_ifLtN_false (by config_simp; exact h) ?_
    refine spec_skip ‹_› ⟨by omega, ?_, ?_⟩
    · config_simp; rw [h31, ite_eq_left (by rwo [hS.r12, h30] at h), Nat.add_zero]
    · simp only [Config.nreg_mk, upd_upd_same, upd_same]

theorem eeOf_le {Q : Polygon} {e₁ h₁ e₂ h₂ : ℕ} (hn : 0 < Q.n) : eeOf Q e₁ h₁ e₂ h₂ ≤ Q.n := by
  unfold eeOf
  have := WalkEmbed.dOf_lt hn e₁ e₂
  splao

/-- **The normalized query.** -/
theorem normI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (he2 : s.e₂ < P.n) (hh1 : s.h₁ ≤ P.n) (hh2 : s.h₂ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel (Qof P)).param (Qof P) ⟨s.e₁, s.h₁⟩) :
    ∃ c' k, Exec P W normI c c' k ∧ k ≤ 900 ∧
      c'.nreg 170030 = nh (Qof P) s.e₂ s.h₂ ∧
      c'.nreg 170031 = eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂) ∧
      c'.nreg 170032 = spanL (eeOf (Qof P) s.e₁ s.h₁ s.e₂ (nh (Qof P) s.e₂ s.h₂))
        (nh (Qof P) s.e₂ s.h₂) ∧ FrameB Bnorm c c' := by
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hW := hS.hW
  unfold hostWords at hW
  obtain ⟨c₁, k₁, e₁, hk₁, a30, ka, ma, -, -, -⟩ := normA_exec c hw hS
  have S₁ : SEnv P W O s c₁ := hS.keep (fun r h1 h2 => ka r (by omega) (by omega) (by omega)
    (by omega) (by omega)) (fun a _ => by rw [ma]) (by rw [ka _ (by decide) (by decide)
      (by decide) (by decide) (by decide)])
  obtain ⟨c₂, k₂, e₂, hk₂, b102, hc₂⟩ := normB_exec c₁ e₁.wb_right S₁ he1 he2
  have kb : ∀ r, r ≠ 170102 → c₂.nreg r = c₁.nreg r := fun r hr => by
    rw [hc₂]; simp [upd, hr]
  have S₂ : SEnv P W O s c₂ := S₁.keep (fun r h1 h2 => kb r (by omega))
    (fun a _ => by rw [hc₂]) (by rw [kb _ (by decide)])
  have h2n : nh (Qof P) s.e₂ s.h₂ ≤ P.n := le_trans nh_le hh2
  obtain ⟨c₃, k₃, e₃, hk₃, c31, kc⟩ := normC_exec c₂ e₂.wb_right S₂ he1 he2 hh1 hx0
    (h₂ := nh (Qof P) s.e₂ s.h₂) (by rwx [kb _ (by decide)]) h2n b102
  have S₃ : SEnv P W O s c₃ := S₂.keep (fun r h1 h2 => kc r (by omega)
      (by unfold BltS Bk; sio only [Bool.or_eq_false_iff, decide_eq_false_iff_not]))
    (fun a _ => by rw [(exec_frameB e₃ (wr_normC)).2.2.1]) (by
      rw [kc _ (by decide) (by decide)])
  have hee := eeOf_le (Q := Qof P) (e₁ := s.e₁) (h₁ := s.h₁) (e₂ := s.e₂)
    (h₂ := nh (Qof P) s.e₂ s.h₂) (by rwo [hQ])
  rw [hQ] at hee
  obtain ⟨c₄, k₄, e₄, hk₄, d32, hc₄⟩ := normD_exec c₃ e₃.wb_right S₃
    (h₂ := nh (Qof P) s.e₂ s.h₂) (by rwx [kc _ (by decide) (by decide), kb _ (by decide)])
    c31 (by omega)
  have ex : Exec P W normI c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, _, ex, by omega, ?_, ?_, d32, exec_frameB ex wr_normI⟩
  · rw [hc₄]; simp only [Config.nreg_mk, upd]
    rwx [kc _ (by decide) (by decide), kb _ (by decide)]
  · rw [hc₄]; simp only [Config.nreg_mk, upd]; exact c31

end exec2

end

end IOrc

end Chazelle.Core
