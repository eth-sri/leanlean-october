module

public import Chazelle.Core.NFLocate

/-!
# Double identification: the direction of the query edge, interior model (WP-C, target 2)

The direction code (`WalkKey.dirCode`) of a walk edge compares the heights of its two walk
vertices.  `dirTail` does this for two symbolic points of `Q` held in `lr 40 … lr 42` and
`lr 43 … lr 45` (two runs of the sign kernel, test `1`), writing the code into `10502`
(`dirTail_exec`).  For the **interior model** the walk vertices of edge `e` are vertices of `Q`,
`e` and `(e + 1) mod n` in the direction of the orientation bit, reversed otherwise
(`interiorWalk_vtx`); `intDir` computes them (`intDir_exec`).  The chain model is in
`NFLocateChain`.
-/

namespace Chazelle.Core

namespace NFLoc

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

/-! ## The height comparison of two symbolic points -/

/-- The direction code of two heights: `1` if `a < b`, `2` if `b < a`, `0` if equal. -/
noncomputable def dirOf (a b : ℝ) : ℕ := if a < b then 1 else if b < a then 2 else 0

theorem dirCode_eq (M : Model) (e : ℕ) : dirCode M e = dirOf (M.wa e).2 (M.wb e).2 := rfl

/-- Load the points of `lr 40` (first and third) and `lr 43` (second) into the kernel, test `1`. -/
def kerLoad (a b : ℕ) : Stmt := block [.copyN 10000 a, .copyN 10001 (a + 1), .copyN 10002 (a + 2),
  .copyN 10003 b, .copyN 10004 (b + 1), .copyN 10005 (b + 2), .copyN 10006 a,
  .copyN 10007 (a + 1), .copyN 10008 (a + 2), .constN 10009 1]

/-- **The height comparison**: `10502 := dirOf y(lr 40) y(lr 43)`. -/
def dirTail : Stmt :=
  .seq (kerLoad 50040 50043) (.seq signProg (.seq (.instr (.copyN 50037 10010))
    (.seq (kerLoad 50043 50040) (.seq signProg (.seq (.instr (.constN 50032 1))
      (.ifLtN 50037 50032
        (.ifLtN 10010 50032 (.instr (.constN 10502 0)) (.instr (.constN 10502 2)))
        (.instr (.constN 10502 1))))))))

theorem wr_dirTail : wr Bdir dirTail = true := by decide

/-- A symbolic point in three registers is copied by three copies. -/
theorem symPtIn_copy {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg (r' + 1) = c.nreg (r + 1))
    (h2 : c'.nreg (r' + 2) = c.nreg (r + 2)) : SymPtIn c' r' s := by
  cases s with
  | vtx i => exact ⟨h0.trans h.1, h1.trans h.2⟩
  | onEdge e hh => exact ⟨h0.trans h.1, h1.trans h.2.1, h2.trans h.2.2⟩

/-- Loading the kernel. -/
theorem kerLoad_exec_ab {P : Polygon} {W : ℕ} (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sb : SymPt} (hsa : SymPtIn c 50040 sa) (hsb : SymPtIn c 50043 sb) :
    ∃ c' k, Exec P W (kerLoad 50040 50043) c c' k ∧ k = 10 ∧ SymPtIn c' 10000 sa ∧
      SymPtIn c' 10003 sb ∧ SymPtIn c' 10006 sa ∧ c'.nreg 10009 = 1 ∧
      (∀ r, (r < 10000 ∨ 10010 ≤ r) → c'.nreg r = c.nreg r) := by
  unfold kerLoad
  exec_block
  all_goals try exact hW
  refine ⟨rfl, ?_, ?_, ?_, by config_simp, fun r hr => ?_⟩
  · exact symPtIn_copy hsa (by config_simp) (by config_simp) (by config_simp)
  · exact symPtIn_copy hsb (by config_simp) (by config_simp) (by config_simp)
  · exact symPtIn_copy hsa (by config_simp) (by config_simp) (by config_simp)
  · simp only [upd]
    split_ifs <;> first | rfl | omega

/-- Loading the kernel, the other order. -/
theorem kerLoad_exec_ba {P : Polygon} {W : ℕ} (hW : 1 ≤ W) (c : Config) (hw : WordsBounded W c)
    {sa sb : SymPt} (hsa : SymPtIn c 50043 sa) (hsb : SymPtIn c 50040 sb) :
    ∃ c' k, Exec P W (kerLoad 50043 50040) c c' k ∧ k = 10 ∧ SymPtIn c' 10000 sa ∧
      SymPtIn c' 10003 sb ∧ SymPtIn c' 10006 sa ∧ c'.nreg 10009 = 1 ∧
      (∀ r, (r < 10000 ∨ 10010 ≤ r) → c'.nreg r = c.nreg r) := by
  unfold kerLoad
  exec_block
  all_goals try exact hW
  refine ⟨rfl, ?_, ?_, ?_, by config_simp, fun r hr => ?_⟩
  · exact symPtIn_copy hsa (by config_simp) (by config_simp) (by config_simp)
  · exact symPtIn_copy hsb (by config_simp) (by config_simp) (by config_simp)
  · exact symPtIn_copy hsa (by config_simp) (by config_simp) (by config_simp)
  · simp only [upd]
    split_ifs <;> first | rfl | omega

/-- **The height comparison of two symbolic points** (at most `490` steps). -/
theorem dirTail_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) {sa sb : SymPt} (hla : sa.Lt P.n) (hlb : sb.Lt P.n)
    (hsa : SymPtIn c 50040 sa) (hsb : SymPtIn c 50043 sb) :
    ∃ c' k, Exec P W dirTail c c' k ∧ k ≤ 490 ∧ FrameB Bdir c c' ∧
      c'.nreg 10502 = dirOf (sa.eval (Qof P)).2 (sb.eval (Qof P)).2 := by
  obtain ⟨c₁, k₁, e₁, hk₁, i1, i2, i3, o1, r1⟩ := kerLoad_exec_ab (P := P) (by omega) c hw
    hsa hsb
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, bit₂, sig₂⟩ := sig_exec (P := P) c₁ e₁.wb_right hG hW
    (by omega) hla hlb hla i1 i2 i3
  rw [o1] at sig₂
  simp only [SignTest] at sig₂
  have w₂ := e₂.wb_right
  have e₃ := Exec.copyN (P := P) w₂ 50037 10010
  have w₃ := e₃.wb_right
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50037 (c₂.nreg 10010) }
  have k2 : ∀ r, (r < 10000 ∨ 10500 ≤ r) → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r (by unfold Bk; simp only [decide_eq_false_iff_not]; omega)
  have sa₃ : SymPtIn c₃ 50040 sa := symPtIn_copy hsa
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
  have sb₃ : SymPtIn c₃ 50043 sb := symPtIn_copy hsb
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
    (by simp only [c₃, upd]; rw [ite_eq_right (by omega), k2 _ (by omega), r1 _ (by omega)])
  have up₃ : c₃.nreg 50037 = c₂.nreg 10010 := by simp [c₃]
  obtain ⟨c₄, k₄, e₄, hk₄, j1, j2, j3, o4, r4⟩ := kerLoad_exec_ba (P := P) (by omega) c₃ w₃
    sb₃ sa₃
  obtain ⟨c₅, k₅, e₅, hk₅, f₅, bit₅, sig₅⟩ := sig_exec (P := P) c₄ e₄.wb_right hG hW
    (by omega) hlb hla hlb j1 j2 j3
  rw [o4] at sig₅
  simp only [SignTest] at sig₅
  have w₅ := e₅.wb_right
  have up₅ : c₅.nreg 50037 = c₂.nreg 10010 := by
    rw [f₅.1 _ (by decide), r4 _ (by omega), up₃]
  have e₆ := Exec.constN (P := P) w₅ 50032 1 (by omega)
  have w₆ := e₆.wb_right
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 50032 1 }
  have h6a : c₆.nreg 50037 = c₂.nreg 10010 := by simp [c₆, up₅]
  have h6b : c₆.nreg 10010 = c₅.nreg 10010 := by simp [c₆]
  have h6c : c₆.nreg 50032 = 1 := by simp [c₆]
  set ya := (sa.eval (Qof P)).2
  set yb := (sb.eval (Qof P)).2
  obtain ⟨c₇, k₇, e₇, hk₇, r₇⟩ : ∃ c₇ k₇, Exec P W (.ifLtN 50037 50032
      (.ifLtN 10010 50032 (.instr (.constN 10502 0)) (.instr (.constN 10502 2)))
      (.instr (.constN 10502 1))) c₆ c₇ k₇ ∧ k₇ ≤ 4 ∧ c₇.nreg 10502 = dirOf ya yb := by
    unfold dirOf
    by_cases hab : ya < yb
    · have : c₂.nreg 10010 = 1 := sig₂.2 hab
      refine spec_ifLtN_false (by rw [h6a, h6c, this]; omega)
        (spec_instr (Exec.constN w₆ _ _ (by omega)) fun _ => ⟨by omega, ?_⟩)
      simp [hab]
    · have h0 : c₂.nreg 10010 = 0 := by have := mt sig₂.1 hab; omega
      refine spec_ifLtN_true (by rw [h6a, h6c, h0]; omega) ?_
      by_cases hba : yb < ya
      · have : c₅.nreg 10010 = 1 := sig₅.2 hba
        refine spec_ifLtN_false (by rw [h6b, h6c, this]; omega)
          (spec_instr (Exec.constN w₆ _ _ (by omega)) fun _ => ⟨by omega, ?_⟩)
        simp [hab, hba]
      · have h0' : c₅.nreg 10010 = 0 := by have := mt sig₅.1 hba; omega
        refine spec_ifLtN_true (by rw [h6b, h6c, h0']; omega)
          (spec_instr (Exec.constN w₆ _ _ (by omega)) fun _ => ⟨by omega, ?_⟩)
        simp [hab, hba]
  have ex : Exec P W dirTail c c₇ (k₁ + (k₂ + (1 + (k₄ + (k₅ + (1 + k₇)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  exact ⟨c₇, _, ex, by omega, exec_frameB ex wr_dirTail, r₇⟩

/-! ## The interior model -/

/-- The walk of the interior model has `n` vertices. -/
theorem interiorWalk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  unfold interiorWalk
  split_ifs
  · rfl
  · simp [Polygon.n]

open Classical in
/-- **The vertices of the interior walk**: vertex `p < n` is vertex `p` of `Q` (orientation bit
set) or vertex `n - 1 - p`. -/
theorem interiorWalk_vtx (Q : Polygon) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx p = if Mountain.LeftInside Q then Q.vtx p else Q.vtx (Q.n - 1 - p) := by
  unfold interiorWalk
  split_ifs with h
  · rfl
  · unfold Polygon.vtx Polygon.n at *
    have hp' : p < Q.vertices.reverse.length := by simpa using hp
    rw [getD_of_lt _ hp', List.getElem_reverse, getD_of_lt _ (by omega)]

/-- The indices of the interior model: bit, `(e + 1) mod n`, and the two vertex indices. -/
def intIdx : Stmt :=
  .seq (block [.inputSize 50030, .constN 50032 1, .addN 50031 50002 50032,
      .addN 50033 50000 50032, .loadN 50033 50033])
    (.seq (.ifLtN 50031 50030 .skip (.instr (.constN 50031 0)))
      (.ifLtN 50033 50032 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
          .subN 50044 50036 50031])
        (.ifLtN 50032 50033 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
            .subN 50044 50036 50031])
          (block [.copyN 50041 50002, .copyN 50044 50031]))))

/-- **The direction procedure of the interior model.** -/
def intDir : Stmt :=
  .seq intIdx (.seq (block [.constN 50040 0, .constN 50043 0]) dirTail)

/-- The indices computed by `intIdx`. -/
theorem intIdx_exec {P : Polygon} {W : ℕ} (hW : P.n + 3 ≤ W) (c : Config) (hw : WordsBounded W c)
    (he : c.nreg 50002 < P.n) (hD : c.nreg 50000 + 1 ≤ W) :
    ∃ c' k, Exec P W intIdx c c' k ∧ k ≤ 14 ∧
      c'.nreg 50041 = (if c.nmem (c.nreg 50000 + 1) = 1 then c.nreg 50002
        else P.n - 1 - c.nreg 50002) ∧
      c'.nreg 50044 = (if c.nmem (c.nreg 50000 + 1) = 1 then (c.nreg 50002 + 1) % P.n
        else P.n - 1 - (c.nreg 50002 + 1) % P.n) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.inputSize 50030, .constN 50032 1,
      .addN 50031 50002 50032, .addN 50033 50000 50032, .loadN 50033 50033]) c c₁ k₁ ∧ k₁ = 5 ∧
      (c₁.nreg 50030 = P.n ∧ c₁.nreg 50032 = 1 ∧ c₁.nreg 50031 = c.nreg 50002 + 1 ∧
        c₁.nreg 50033 = c.nmem (c.nreg 50000 + 1) ∧ c₁.nreg 50002 = c.nreg 50002) := by
    exec_block
    · omega
    · omega
    · config_simp; omega
    · config_simp; omega
    · exact ⟨rfl, by config_simp⟩
  obtain ⟨q30, q32, q31, q33, q02⟩ := q
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, s31, s30, s32, s33, s02⟩ : ∃ c₂ k₂, Exec P W
      (.ifLtN 50031 50030 .skip (.instr (.constN 50031 0))) c₁ c₂ k₂ ∧ k₂ ≤ 3 ∧
      c₂.nreg 50031 = (c.nreg 50002 + 1) % P.n ∧ c₂.nreg 50030 = P.n ∧ c₂.nreg 50032 = 1 ∧
      c₂.nreg 50033 = c.nmem (c.nreg 50000 + 1) ∧ c₂.nreg 50002 = c.nreg 50002 := by
    by_cases h : c.nreg 50002 + 1 < P.n
    · refine spec_ifLtN_true (by rwa [q31, q30]) (spec_skip w₁ ⟨by omega, ?_⟩)
      rw [q31, Nat.mod_eq_of_lt h]
      exact ⟨rfl, q30, q32, q33, q02⟩
    · refine spec_ifLtN_false (by rwa [q31, q30])
        (spec_instr (Exec.constN w₁ _ _ (by omega)) fun _ => ⟨by omega, ?_⟩)
      have : c.nreg 50002 + 1 = P.n := by omega
      config_simp
      rw [this, Nat.mod_self]
      exact ⟨rfl, q30, q32, q33, q02⟩
  have w₂ := e₂.wb_right
  set b := c.nmem (c.nreg 50000 + 1)
  set e := c.nreg 50002
  set e1 := (c.nreg 50002 + 1) % P.n
  have hrev : ∀ (d : Config) , WordsBounded W d → d.nreg 50030 = P.n → d.nreg 50032 = 1 →
      d.nreg 50002 = e → d.nreg 50031 = e1 →
      ∃ c' k, Exec P W (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
        .subN 50044 50036 50031]) d c' k ∧ k = 3 ∧ c'.nreg 50041 = P.n - 1 - e ∧
        c'.nreg 50044 = P.n - 1 - e1 := by
    intro d hd a b' c'' d''
    exec_block
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> rw [a, b'] <;> simp [c'', d'']
  obtain ⟨c₃, k₃, e₃, hk₃, r41, r44⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 50033 50032
      (block [.subN 50036 50030 50032, .subN 50041 50036 50002, .subN 50044 50036 50031])
      (.ifLtN 50032 50033 (block [.subN 50036 50030 50032, .subN 50041 50036 50002,
          .subN 50044 50036 50031])
        (block [.copyN 50041 50002, .copyN 50044 50031]))) c₂ c₃ k₃ ∧ k₃ ≤ 6 ∧
      c₃.nreg 50041 = (if b = 1 then e else P.n - 1 - e) ∧
      c₃.nreg 50044 = (if b = 1 then e1 else P.n - 1 - e1) := by
    by_cases h0 : b < 1
    · obtain ⟨c', k, ex, hk, a, a'⟩ := hrev c₂ w₂ s30 s32 s02 s31
      refine ⟨c', k + 1, .ifLtN_true (by rwa [s33, s32]) ex, by omega, ?_, ?_⟩
      · rw [a, ite_eq_right (by omega)]
      · rw [a', ite_eq_right (by omega)]
    · by_cases h2 : 1 < b
      · obtain ⟨c', k, ex, hk, a, a'⟩ := hrev c₂ w₂ s30 s32 s02 s31
        refine ⟨c', k + 1 + 2, .ifLtN_false (by rwa [s33, s32])
          (.ifLtN_true (by rwa [s33, s32]) ex), by omega, ?_, ?_⟩
        · rw [a, ite_eq_right (by omega)]
        · rw [a', ite_eq_right (by omega)]
      · have hb1 : b = 1 := by omega
        refine spec_ifLtN_false (by rwa [s33, s32])
          (spec_ifLtN_false (by rwa [s33, s32]) ?_)
        exec_block
        refine ⟨by omega, ?_, ?_⟩ <;> config_simp <;> rw [ite_eq_left hb1]
        · exact s02
        · exact s31
  exact ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, r41, r44⟩

/-- **The direction procedure of the interior model** (at most `510` steps). -/
theorem intDir_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (he : c.nreg 50002 < P.n) (hD : c.nreg 50000 + 1 ≤ W)
    (hbit : c.nmem (c.nreg 50000 + 1) = 1 ↔ Mountain.LeftInside (Qof P)) :
    ∃ c' k, Exec P W intDir c c' k ∧ k ≤ 510 ∧
      c'.nreg 10502 = dirCode (interiorModel (Qof P)) (c.nreg 50002) := by
  obtain ⟨c₁, k₁, e₁, hk₁, r41, r44⟩ := intIdx_exec (P := P) hW c hw he hD
  have w₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, a, b, x41, x44⟩ : ∃ c₂ k₂, Exec P W
      (block [.constN 50040 0, .constN 50043 0]) c₁ c₂ k₂ ∧ k₂ = 2 ∧ c₂.nreg 50040 = 0 ∧
      c₂.nreg 50043 = 0 ∧ c₂.nreg 50041 = c₁.nreg 50041 ∧ c₂.nreg 50044 = c₁.nreg 50044 := by
    exec_block
    · omega
    · omega
    · exact ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp⟩
  have hn : (Qof P).n = P.n := shear_n _ P
  have hn0 : 0 < P.n := by omega
  set e := c.nreg 50002
  set ia := (if c.nmem (c.nreg 50000 + 1) = 1 then e else P.n - 1 - e)
  set ib := (if c.nmem (c.nreg 50000 + 1) = 1 then (e + 1) % P.n else P.n - 1 - (e + 1) % P.n)
  have hia : ia < P.n := by simp only [ia]; split_ifs <;> omega
  have hib : ib < P.n := by
    have := Nat.mod_lt (e + 1) hn0
    simp only [ib]; split_ifs <;> omega
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, d₃⟩ := dirTail_exec (P := P) hG hW c₂ e₂.wb_right
    (sa := .vtx ia) (sb := .vtx ib) hia hib ⟨a, by rw [x41, r41]⟩ ⟨b, by rw [x44, r44]⟩
  have ex : Exec P W intDir c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  refine ⟨c₃, _, ex, by omega, ?_⟩
  rw [d₃, dirCode_eq]
  simp only [SymPt.eval, Model.wa, Model.wb, interiorModel]
  rw [interiorWalk_n, hn, interiorWalk_vtx _ (by rwa [hn]),
    interiorWalk_vtx _ (by rw [hn]; exact Nat.mod_lt _ hn0), hn]
  simp only [ia, ib]
  by_cases hL : Mountain.LeftInside (Qof P)
  · rw [ite_eq_left hL, ite_eq_left hL, ite_eq_left (hbit.2 hL), ite_eq_left (hbit.2 hL)]
  · rw [ite_eq_right hL, ite_eq_right hL, ite_eq_right (mt hbit.1 hL),
      ite_eq_right (mt hbit.1 hL)]

end

end NFLoc

end Chazelle.Core
