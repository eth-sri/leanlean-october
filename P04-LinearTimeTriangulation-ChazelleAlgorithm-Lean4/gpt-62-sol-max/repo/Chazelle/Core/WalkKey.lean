module

public import Chazelle.Core.SignKernel
public import Chazelle.Core.NFKey
public import Chazelle.Core.NFSearch

/-!
# Comparing walk keys on the RAM (WP-C, target 1)

Double identification (`LocateSpec`) searches the arc-sequence table of a normal form for the
query position `x`: the monotone predicate is "the start `s` of the arc lies before `x`",

* `key s < key x` if `x` has height code `0` (a vertex of the walk), and
* `key s ≤ key x` otherwise (`KeyPred`).

Both reduce to comparisons of edge indices and at most **one height test** of two vertices of
`Q = Qof P`, provided both positions lie on the walk proper (`ProperPos`: parameter in `[0, 1)`,
height code at most `n`) and the **direction code** of the query edge (`dirCode`: `1` upward, `2`
downward, `0` horizontal) is known (`keyDec_iff`, from `NFKey.key_lt_key_iff_of_same_edge`).  The
direction is computed once per query (it needs the walk vertices, see `NFLocate`), so each
comparison costs a constant.

## The comparison procedure `keyCmp`

Registers read (band `bSign`, above the part `10000 … 10499` that the sign kernel writes):
`10500` the query edge, `10501` the query height code, `10502` the direction code, `10503` the
base `AB` of the arc area of the normal form, `10504` the number `A` of arcs.  The item (an arc
index `j`) is in `lr 100`; the answer goes to `lr 102`.  It loads the start of arc `j` (words
`AB + 5 j + 1`, `AB + 5 j + 2`) and runs the sign kernel `SignK.signProg` (test `1`) on the two
height vertices when needed.  Written registers: `lr 101`, `lr 102` and `10000 … 10499`
(`Bcmp`); no memory.

Main result: `keyCmp_predOK`, the contract `SearchR.PredOK` of the binary search, with the
invariant `CmpJ` (stable under the search, `cmpJ_stable`) and the predicate `cmpPr`.
-/

namespace Chazelle.Core

namespace WalkKey

open Machine Machine.Stmt Programs SignK SearchR

@[expose] public section

/-! ## The sign kernel with an explicit write set -/

/-- The registers written by the sign kernel: `10000 … 10499`. -/
def Bk (r : ℕ) : Bool := decide (10000 ≤ r ∧ r < 10500)

/-- **The sign kernel** as an execution lemma with the explicit frame `Bk` (no allocator, no
memory): three symbolic points in `10000 …`, `10003 …`, `10006 …`, the test in `10009`, the
answer bit in `10010`. -/
theorem sig_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P)
    (hW : P.n + 3 ≤ W) (hop : c.nreg 10009 ≤ 3) {s₁ s₂ s₃ : SymPt} (hl₁ : s₁.Lt P.n)
    (hl₂ : s₂.Lt P.n) (hl₃ : s₃.Lt P.n) (hi₁ : SymPtIn c 10000 s₁) (hi₂ : SymPtIn c 10003 s₂)
    (hi₃ : SymPtIn c 10006 s₃) :
    ∃ c' k, Exec P W signProg c c' k ∧ k ≤ 230 ∧ FrameB Bk c c' ∧ c'.nreg 10010 ≤ 1 ∧
      (c'.nreg 10010 = 1 ↔
        SignTest (c.nreg 10009) (s₁.eval (Qof P)) (s₂.eval (Qof P)) (s₃.eval (Qof P))) := by
  have hW' : P.n ≤ W := by omega
  obtain ⟨c1, k1, e1, hk1, p1n, p11, p12, p13, p1z⟩ := prelude_spec (P := P) c hw hW
  have f1 := exec_frameB e1 (B := Bpre) (by decide)
  obtain ⟨c2, k2, e2, hk2, hr1⟩ := loadPt_spec 10000 10100 (Or.inl ⟨rfl, rfl⟩) c1 e1.wb_right
    p1n p11 p1z hW' s₁ hl₁
    (symPtIn_of_eq hi₁ fun j h1 h2 => f1.1 j (by simp [Bpre]; omega))
  have f2 := exec_frameB e2 (B := Bload 10100) (by decide)
  obtain ⟨c3, k3, e3, hk3, hr2⟩ := loadPt_spec 10003 10110 (Or.inr (Or.inl ⟨rfl, rfl⟩)) c2
    e2.wb_right ((f2.1 _ (by decide)).trans p1n) ((f2.1 _ (by decide)).trans p11)
    ((f2.2.1 _ (by decide)).trans p1z) hW' s₂ hl₂
    (symPtIn_of_eq hi₂ fun j h1 h2 =>
      (f2.1 j (by simp [Bload]; omega)).trans (f1.1 j (by simp [Bpre]; omega)))
  have f3 := exec_frameB e3 (B := Bload 10110) (by decide)
  obtain ⟨c4, k4, e4, hk4, hr3⟩ := loadPt_spec 10006 10120 (Or.inr (Or.inr ⟨rfl, rfl⟩)) c3
    e3.wb_right ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans p1n))
    ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans p11))
    ((f3.2.1 _ (by decide)).trans ((f2.2.1 _ (by decide)).trans p1z)) hW' s₃ hl₃
    (symPtIn_of_eq hi₃ fun j h1 h2 =>
      (f3.1 j (by simp [Bload]; omega)).trans
        ((f2.1 j (by simp [Bload]; omega)).trans (f1.1 j (by simp [Bpre]; omega))))
  have f4 := exec_frameB e4 (B := Bload 10120) (by decide)
  obtain ⟨c5, k5, e5, hk5, hx, hy, hd⟩ := polyStmt_spec (P := P) c4 e4.wb_right
    (repAt_of_eq hr1 fun j h1 h2 =>
      (f4.2.1 j (by simp [Bload]; omega)).trans (f3.2.1 j (by simp [Bload]; omega)))
    (repAt_of_eq hr2 fun j h1 h2 => f4.2.1 j (by simp [Bload]; omega)) hr3
  have f5 := exec_frameB e5 (B := Bpoly) (by decide)
  have n21 : c5.nreg 10021 = 1 := (f5.1 _ (by decide)).trans ((f4.1 _ (by decide)).trans
    ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans p11)))
  have n22 : c5.nreg 10022 = 2 := (f5.1 _ (by decide)).trans ((f4.1 _ (by decide)).trans
    ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans p12)))
  have n23 : c5.nreg 10023 = 3 := (f5.1 _ (by decide)).trans ((f4.1 _ (by decide)).trans
    ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans p13)))
  have z5 : c5.rreg 10020 = 0 := (f5.2.1 _ (by decide)).trans ((f4.2.1 _ (by decide)).trans
    ((f3.2.1 _ (by decide)).trans ((f2.2.1 _ (by decide)).trans p1z)))
  have o5 : c5.nreg 10009 = c.nreg 10009 := (f5.1 _ (by decide)).trans ((f4.1 _ (by decide)).trans
    ((f3.1 _ (by decide)).trans ((f2.1 _ (by decide)).trans (f1.1 _ (by decide)))))
  obtain ⟨c6, k6, e6, hk6, hsel⟩ := selStmt_spec (P := P) c5 e5.wb_right n21 n22 hx hy hd
  have f6 := exec_frameB e6 (B := Bsel) (by decide)
  obtain ⟨c7, k7, e7, hk7, hb1, hb2, hpos, hzero⟩ :=
    lexStmt_spec (P := P) 10020 10410 10411 (by decide) (by omega)
      [10400, 10401, 10402, 10403, 10404] c6 e6.wb_right ((f6.2.1 _ (by decide)).trans z5)
  have f7 := exec_frameB e7 (B := Blex) (by decide)
  obtain ⟨c8, k8, e8, hk8, hf1, hf2⟩ := finStmt_spec (P := P) c7 e7.wb_right
    ((f7.1 _ (by decide)).trans ((f6.1 _ (by decide)).trans n23))
  have o7 : c7.nreg 10009 = c.nreg 10009 :=
    (f7.1 _ (by decide)).trans ((f6.1 _ (by decide)).trans o5)
  rw [o7] at hf1 hf2
  rw [hsel, o5] at hpos hzero
  have ex := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  have fb := exec_frameB ex (B := Bk) (by decide)
  refine ⟨c8, _, ex, by simp only [List.length_cons, List.length_nil] at hk7; omega, fb, ?_, ?_⟩
  · by_cases h : c.nreg 10009 < 3
    · rw [hf1 h]; exact hb1
    · rw [hf2 h]; exact hb2
  · have hm := signTest_iff_lex P hG.2 s₁ s₂ s₃ hl₁ hl₂ hl₃ (c.nreg 10009)
    by_cases h : c.nreg 10009 < 3
    · rw [hf1 h, hpos, hm.1 h]
    · rw [hf2 h, hzero, hm.2 (by omega)]

/-! ## The mathematics of the comparison -/

/-- **The direction code** of walk edge `e`: `1` upward, `2` downward, `0` horizontal. -/
noncomputable def dirCode (M : Model) (e : ℕ) : ℕ :=
  if (M.wa e).2 < (M.wb e).2 then 1 else if (M.wb e).2 < (M.wa e).2 then 2 else 0

/-- **The search predicate** for the query `x`: the position `s` lies strictly before `x` (if `x`
has height code `0`) or not after `x` (otherwise). -/
def KeyPred (M : Model) (Q : Polygon) (x s : WPos) : Prop :=
  if x.hgt = 0 then M.key Q s < M.key Q x else M.key Q s ≤ M.key Q x

/-- The predicate is monotone in the key of `s`. -/
theorem KeyPred.mono {M : Model} {Q : Polygon} {x s s' : WPos} (h : KeyPred M Q x s)
    (hle : M.key Q s' ≤ M.key Q s) : KeyPred M Q x s' := by
  unfold KeyPred at h ⊢
  split_ifs at h ⊢ <;> linarith

/-- **The decision computed by the machine**, for any positions (the guard `n < s.hgt` keeps
the sign kernel in range). -/
noncomputable def keyDec (Q : Polygon) (n : ℕ) (x : WPos) (d : ℕ) (s : WPos) : Bool :=
  if s.edge < x.edge then true
  else if x.edge < s.edge then false
  else if x.hgt < 1 then false
  else if d < 1 then true
  else if s.hgt < 1 then true
  else if n < s.hgt then false
  else if d < 2 then !decide ((Q.vtx (x.hgt - 1)).2 < (Q.vtx (s.hgt - 1)).2)
  else !decide ((Q.vtx (s.hgt - 1)).2 < (Q.vtx (x.hgt - 1)).2)

/-- The height of a position with a nonzero code. -/
theorem hgtY_of_pos {M : Model} {Q : Polygon} {x : WPos} (h : 1 ≤ x.hgt) :
    M.hgtY Q x = (Q.vtx (x.hgt - 1)).2 := by
  rcases x with ⟨e, _ | k⟩
  · simp at h
  · rfl

/-- A position with code `0` has parameter `0`. -/
theorem param_of_code_zero {M : Model} {Q : Polygon} {x : WPos} (h : x.hgt = 0) :
    M.param Q x = 0 := by
  rcases x with ⟨e, k⟩
  simp only at h
  subst h
  rfl

/-- **The machine decision is the search predicate** for positions of the walk proper, with the
direction code of the query edge. -/
theorem keyDec_iff {M : Model} {Q : Polygon} {n : ℕ} {x s : WPos} (hx : ProperPos M Q n x)
    (hs : ProperPos M Q n s) :
    keyDec Q n x (dirCode M x.edge) s = true ↔ KeyPred M Q x s := by
  obtain ⟨hx0, hx1, -⟩ := hx
  obtain ⟨hs0, hs1, hsn⟩ := hs
  have kx : M.key Q x = x.edge + M.param Q x := rfl
  have ks : M.key Q s = s.edge + M.param Q s := rfl
  unfold keyDec KeyPred
  by_cases h1 : s.edge < x.edge
  · have : (s.edge : ℝ) + 1 ≤ x.edge := by exact_mod_cast h1
    rw [ite_eq_left h1]
    simp only [true_iff]
    split_ifs <;> linarith
  rw [ite_eq_right h1]
  by_cases h2 : x.edge < s.edge
  · have : (x.edge : ℝ) + 1 ≤ s.edge := by exact_mod_cast h2
    rw [ite_eq_left h2]
    simp only [Bool.false_eq_true, false_iff]
    split_ifs <;> linarith
  rw [ite_eq_right h2]
  have he : s.edge = x.edge := by omega
  have heR : (s.edge : ℝ) = x.edge := by exact_mod_cast he
  by_cases h3 : x.hgt < 1
  · have hx0' : x.hgt = 0 := by omega
    rw [ite_eq_left h3, ite_eq_left hx0']
    simp only [Bool.false_eq_true, false_iff, not_lt]
    rw [kx, ks, param_of_code_zero hx0']
    linarith
  rw [ite_eq_right h3, ite_eq_right (by omega : ¬ x.hgt = 0)]
  by_cases h4 : dirCode M x.edge < 1
  · rw [ite_eq_left h4]
    simp only [true_iff]
    have hh : (M.wa x.edge).2 = (M.wb x.edge).2 := by
      unfold dirCode at h4
      split_ifs at h4 with q1 q2 <;> first | omega | linarith [not_lt.1 q1, not_lt.1 q2]
    have e1 := Model.key_eq_of_horizontal (Q := Q) hh
    have e2 := Model.key_eq_of_horizontal (Q := Q) (x := s) (by rw [he]; exact hh)
    rw [e1, e2, heR]
  rw [ite_eq_right h4]
  have hnh : (M.wa x.edge).2 ≠ (M.wb x.edge).2 := by
    intro hh
    unfold dirCode at h4
    rw [ite_eq_right (by rw [hh]; exact lt_irrefl _), ite_eq_right (by rw [hh]; exact lt_irrefl _)] at h4
    exact h4 Nat.zero_lt_one
  by_cases h5 : s.hgt < 1
  · rw [ite_eq_left h5]
    simp only [true_iff]
    rw [kx, ks, param_of_code_zero (by omega : s.hgt = 0)]
    linarith
  rw [ite_eq_right h5, ite_eq_right (by omega : ¬ n < s.hgt)]
  have hlt := Model.key_lt_key_iff_of_same_edge (M := M) (Q := Q) he.symm hnh
  rw [hgtY_of_pos (by omega), hgtY_of_pos (by omega)] at hlt
  have hle : M.key Q s ≤ M.key Q x ↔ ¬ M.key Q x < M.key Q s := not_lt.symm
  rw [hle, hlt]
  by_cases h6 : dirCode M x.edge < 2
  · have hup : (M.wa x.edge).2 < (M.wb x.edge).2 := by
      unfold dirCode at h4 h6
      split_ifs at h4 h6 with q1 q2 <;> omega
    rw [ite_eq_left h6]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    constructor
    · intro h h'
      rcases h' with ⟨-, h'⟩ | ⟨h'', -⟩
      · exact h h'
      · linarith
    · intro h h'
      exact h (Or.inl ⟨hup, h'⟩)
  · have hdn : (M.wb x.edge).2 < (M.wa x.edge).2 := by
      unfold dirCode at h4 h6
      split_ifs at h4 h6 with q1 q2 <;> omega
    rw [ite_eq_right h6]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    constructor
    · intro h h'
      rcases h' with ⟨h'', -⟩ | ⟨-, h'⟩
      · linarith
      · exact h h'
    · intro h h'
      exact h (Or.inr ⟨hdn, h'⟩)

/-! ## The comparison procedure -/

/-- The height test: `vtx (x.hgt - 1)` against `vtx (s.hgt - 1)` (upward edge) or the reverse
(downward edge), test `1` (ordinate order); the answer is `1 - bit`. -/
def kerPart : Stmt :=
  .seq (block [.constN 10013 2, .constN 10000 0, .constN 10003 0, .constN 10006 0,
      .constN 10009 1, .subN 10015 10501 50102, .subN 10016 10012 50102, .copyN 10007 10015])
    (.seq (.ifLtN 10502 10013 (block [.copyN 10001 10015, .copyN 10004 10016])
        (block [.copyN 10001 10016, .copyN 10004 10015]))
      (.seq signProg (.instr (.subN 50102 50102 10010))))

/-- The decision on a loaded start position (`10011`: edge, `10012`: code); `lr 102` holds `1`
on entry. -/
def cmpPos : Stmt :=
  .ifLtN 10011 10500 .skip
    (.ifLtN 10500 10011 (.instr (.constN 50102 0))
      (.ifLtN 10501 50102 (.instr (.constN 50102 0))
        (.ifLtN 10502 50102 .skip
          (.ifLtN 10012 50102 .skip
            (.seq (.instr (.inputSize 10014))
              (.ifLtN 10014 10012 (.instr (.constN 50102 0)) kerPart))))))

/-- Load the start of arc `lr 100` from the arc area at `10503`. -/
def loadPos : Stmt := block [.addN 50101 50100 50100, .addN 50101 50101 50101,
  .addN 50101 50101 50100, .addN 50101 50101 10503, .addN 50101 50101 50102, .loadN 10011 50101,
  .addN 50101 50101 50102, .loadN 10012 50101]

/-- **The comparison procedure** (answer `0` for items out of range). -/
def keyCmp : Stmt :=
  .seq (.instr (.constN 50102 1))
    (.ifLtN 50100 10504 (.seq loadPos cmpPos) (.instr (.constN 50102 0)))

/-- The instruction writes a real register only if it is accepted by `B` (natural registers
are unrestricted), and is not a store, an `emit` or a control instruction. -/
def wrROK (B : ℕ → Bool) : Instr → Bool
  | .inputSize _ | .constN _ _ | .copyN _ _ | .addN _ _ _ | .subN _ _ _ | .loadN _ _ => true
  | .constR r _ | .copyR r _ | .addR r _ _ | .subR r _ _ | .mulR r _ _ | .divR r _ _ => B r
  | .loadR r _ | .readX r _ | .readY r _ => B r
  | _ => false

/-- Every instruction of the statement satisfies `wrROK B`. -/
def wrR (B : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => wrROK B i
  | .seq s t => wrR B s && wrR B t
  | .ifLtN _ _ t e => wrR B t && wrR B e
  | .ifLtR _ _ t e => wrR B t && wrR B e
  | .whileLtN _ _ b => wrR B b
  | .whileLtR _ _ b => wrR B b

/-- **Real-register frame**: a statement whose real writes are accepted by `B` changes no other
real register. -/
theorem exec_rframe {P : Polygon} {W : ℕ} {B : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : wrR B s = true) : ∀ r, B r = false → c'.rreg r = c.rreg r := by
  induction h with
  | skip _ => exact fun _ _ => rfl
  | @instr ins c c' _ he _ _ =>
    simp only [wrR] at hs
    cases ins <;> simp only [wrROK, Bool.false_eq_true] at hs <;>
      simp only [Instr.effect, Option.some.injEq] at he <;>
      (try split at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;> subst he <;>
      intro j hj <;>
      first
      | rfl
      | (simp only [upd]; split_ifs with hh
         · subst hh; simp_all
         · rfl)
  | seq _ _ ih₁ ih₂ =>
    simp only [wrR, Bool.and_eq_true] at hs
    exact fun r hr => (ih₂ hs.2 r hr).trans (ih₁ hs.1 r hr)
  | ifLtN_true _ _ ih =>
    simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih =>
    simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih =>
    simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih =>
    simp only [wrR, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => exact fun _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)
  | whileLtR_false _ _ => exact fun _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => exact fun r hr => (ih₂ hs r hr).trans (ih₁ hs r hr)

theorem wrR_keyCmp : wrR Bk keyCmp = true := by decide

/-- The registers written by `keyCmp`. -/
def Bcmp (r : ℕ) : Bool := decide (r = 50101) || decide (r = 50102) || Bk r

theorem wr_keyCmp : wr Bcmp keyCmp = true := by decide

/-- The kernel part answers the height test. -/
theorem kerPart_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (h1 : c.nreg 50102 = 1) (hx1 : 1 ≤ c.nreg 10501)
    (hxn : c.nreg 10501 ≤ P.n) (hs1 : 1 ≤ c.nreg 10012) (hsn : c.nreg 10012 ≤ P.n) :
    ∃ c' k, Exec P W kerPart c c' k ∧ k ≤ 245 ∧
      c'.nreg 50102 = (if (if c.nreg 10502 < 2 then
          !decide (((Qof P).vtx (c.nreg 10501 - 1)).2 < ((Qof P).vtx (c.nreg 10012 - 1)).2)
        else !decide (((Qof P).vtx (c.nreg 10012 - 1)).2 < ((Qof P).vtx (c.nreg 10501 - 1)).2))
        then 1 else 0) := by
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 10013 2, .constN 10000 0,
      .constN 10003 0, .constN 10006 0, .constN 10009 1, .subN 10015 10501 50102,
      .subN 10016 10012 50102, .copyN 10007 10015]) c c₁ k₁ ∧ k₁ = 8 ∧
      (c₁.nreg 10013 = 2 ∧ c₁.nreg 10000 = 0 ∧ c₁.nreg 10003 = 0 ∧ c₁.nreg 10006 = 0 ∧
        c₁.nreg 10009 = 1 ∧ c₁.nreg 10015 = c.nreg 10501 - 1 ∧
        c₁.nreg 10016 = c.nreg 10012 - 1 ∧ c₁.nreg 10007 = c.nreg 10501 - 1 ∧
        c₁.nreg 50102 = 1 ∧ c₁.nreg 10502 = c.nreg 10502) := by
    exec_block
    · omega
    · omega
    · omega
    · omega
    · omega
    · refine ⟨rfl, ?_⟩
      config_simp
      simp [h1]
  obtain ⟨q13, q0, q3, q6, q9, q15, q16, q7, q102, q502⟩ := q
  have w₁ := e₁.wb_right
  -- the two orders
  obtain ⟨c₂, k₂, e₂, hk₂, a₁, a₄, r₂⟩ : ∃ c₂ k₂, Exec P W (.ifLtN 10502 10013
      (block [.copyN 10001 10015, .copyN 10004 10016])
      (block [.copyN 10001 10016, .copyN 10004 10015])) c₁ c₂ k₂ ∧ k₂ ≤ 4 ∧
      c₂.nreg 10001 = (if c.nreg 10502 < 2 then c.nreg 10501 - 1 else c.nreg 10012 - 1) ∧
      c₂.nreg 10004 = (if c.nreg 10502 < 2 then c.nreg 10012 - 1 else c.nreg 10501 - 1) ∧
      (∀ r, r ≠ 10001 → r ≠ 10004 → c₂.nreg r = c₁.nreg r) := by
    by_cases hd : c.nreg 10502 < 2
    · refine spec_ifLtN_true (by rw [q502, q13]; exact hd) ?_
      exec_block
      refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [ite_eq_left hd, q15]
      · config_simp; rw [ite_eq_left hd, q16]
      · simp [h1, h2]
    · refine spec_ifLtN_false (by rw [q502, q13]; exact hd) ?_
      exec_block
      refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_⟩
      · config_simp; rw [ite_eq_right hd, q16]
      · config_simp; rw [ite_eq_right hd, q15]
      · simp [h1, h2]
  have w₂ := e₂.wb_right
  set a := (if c.nreg 10502 < 2 then c.nreg 10501 - 1 else c.nreg 10012 - 1) with ha
  set b := (if c.nreg 10502 < 2 then c.nreg 10012 - 1 else c.nreg 10501 - 1) with hb
  have hal : a < P.n := by rw [ha]; split_ifs <;> omega
  have hbl : b < P.n := by rw [hb]; split_ifs <;> omega
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, bit₃, sig₃⟩ := sig_exec (P := P) c₂ w₂ hG hW
    (s₁ := .vtx a) (s₂ := .vtx b) (s₃ := .vtx (c.nreg 10501 - 1))
    (by rw [r₂ _ (by omega) (by omega), q9]; omega) hal hbl (show c.nreg 10501 - 1 < P.n by omega)
    ⟨by rw [r₂ _ (by omega) (by omega), q0], a₁⟩ ⟨by rw [r₂ _ (by omega) (by omega), q3], a₄⟩
    ⟨by rw [r₂ _ (by omega) (by omega), q6], by rw [r₂ _ (by omega) (by omega), q7]⟩
  have w₃ := e₃.wb_right
  have n102 : c₃.nreg 50102 = 1 := by
    rw [f₃.1 _ (by decide), r₂ _ (by omega) (by omega), q102]
  have op : c₂.nreg 10009 = 1 := by rw [r₂ _ (by omega) (by omega), q9]
  rw [op] at sig₃
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (Exec.subN w₃ 50102 50102 10010))), by omega, ?_⟩
  config_simp
  rw [n102]
  simp only [SignTest, SymPt.eval] at sig₃
  by_cases hd : c.nreg 10502 < 2
  · rw [ite_eq_left hd]
    rw [ha, hb, ite_eq_left hd, ite_eq_left hd] at sig₃
    by_cases ht : ((Qof P).vtx (c.nreg 10501 - 1)).2 < ((Qof P).vtx (c.nreg 10012 - 1)).2
    · rw [sig₃.2 ht]; simp [ht]
    · have : c₃.nreg 10010 = 0 := by
        have h' := mt sig₃.1 ht; omega
      rw [this]; simp [ht]
  · rw [ite_eq_right hd]
    rw [ha, hb, ite_eq_right hd, ite_eq_right hd] at sig₃
    by_cases ht : ((Qof P).vtx (c.nreg 10012 - 1)).2 < ((Qof P).vtx (c.nreg 10501 - 1)).2
    · rw [sig₃.2 ht]; simp [ht]
    · have : c₃.nreg 10010 = 0 := by
        have h' := mt sig₃.1 ht; omega
      rw [this]; simp [ht]

/-- The decision on a loaded position. -/
theorem cmpPos_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (h1 : c.nreg 50102 = 1) (hxn : c.nreg 10501 ≤ P.n) :
    ∃ c' k, Exec P W cmpPos c c' k ∧ k ≤ 260 ∧
      c'.nreg 50102 = (if keyDec (Qof P) P.n ⟨c.nreg 10500, c.nreg 10501⟩ (c.nreg 10502)
        ⟨c.nreg 10011, c.nreg 10012⟩ then 1 else 0) := by
  unfold cmpPos keyDec
  simp only
  by_cases t1 : c.nreg 10011 < c.nreg 10500
  · rw [ite_eq_left t1]
    exact spec_ifLtN_true t1 (spec_skip hw ⟨by omega, by rw [h1]; rfl⟩)
  rw [ite_eq_right t1]
  refine spec_ifLtN_false t1 ?_
  by_cases t2 : c.nreg 10500 < c.nreg 10011
  · rw [ite_eq_left t2]
    refine spec_ifLtN_true t2 (spec_instr (Exec.constN hw _ _ (by omega)) fun _ => ?_)
    exact ⟨by omega, by config_simp; simp⟩
  rw [ite_eq_right t2]
  refine spec_ifLtN_false t2 ?_
  by_cases t3 : c.nreg 10501 < 1
  · rw [ite_eq_left t3]
    refine spec_ifLtN_true (by rw [h1]; exact t3)
      (spec_instr (Exec.constN hw _ _ (by omega)) fun _ => ?_)
    exact ⟨by omega, by config_simp; simp⟩
  rw [ite_eq_right t3]
  refine spec_ifLtN_false (by rw [h1]; exact t3) ?_
  by_cases t4 : c.nreg 10502 < 1
  · rw [ite_eq_left t4]
    exact spec_ifLtN_true (by rw [h1]; exact t4) (spec_skip hw ⟨by omega, by rw [h1]; rfl⟩)
  rw [ite_eq_right t4]
  refine spec_ifLtN_false (by rw [h1]; exact t4) ?_
  by_cases t5 : c.nreg 10012 < 1
  · rw [ite_eq_left t5]
    exact spec_ifLtN_true (by rw [h1]; exact t5) (spec_skip hw ⟨by omega, by rw [h1]; rfl⟩)
  rw [ite_eq_right t5]
  refine spec_ifLtN_false (by rw [h1]; exact t5) ?_
  have hn : P.n ≤ W := by omega
  refine spec_seq ⟨_, _, Exec.inputSize hw 10014 hn, ?_⟩
  have w₁ := WordsBounded.upd_nreg hw hn c.pc (r := 10014)
  by_cases t6 : P.n < c.nreg 10012
  · rw [ite_eq_left t6]
    refine spec_ifLtN_true (by config_simp; exact t6)
      (spec_instr (Exec.constN w₁ _ _ (by omega)) fun _ => ?_)
    exact ⟨by omega, by config_simp; simp⟩
  rw [ite_eq_right t6]
  refine spec_ifLtN_false (by config_simp; exact t6) ?_
  obtain ⟨c', k, e, hk, hr⟩ := kerPart_exec (P := P) hG hW _ w₁ (by config_simp; exact h1)
    (by config_simp; omega) (by config_simp; exact hxn) (by config_simp; omega)
    (by config_simp; omega)
  refine ⟨c', k, e, by omega, ?_⟩
  rw [hr]
  config_simp

/-- **The comparison procedure** computes the bit of `cmpPrC`: the decision on the start of arc
`lr 100` (`0` out of range). -/
theorem keyCmp_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (c : Config)
    (hw : WordsBounded W c) (hxn : c.nreg 10501 ≤ P.n)
    (hAB : c.nreg 10503 + 5 * c.nreg 10504 ≤ W) :
    ∃ c' k, Exec P W keyCmp c c' k ∧ k ≤ 275 ∧
      c'.nreg 50102 = (if (if c.nreg 50100 < c.nreg 10504 then
        keyDec (Qof P) P.n ⟨c.nreg 10500, c.nreg 10501⟩ (c.nreg 10502)
          ⟨c.nmem (c.nreg 10503 + 5 * c.nreg 50100 + 1),
            c.nmem (c.nreg 10503 + 5 * c.nreg 50100 + 2)⟩ else false) then 1 else 0) := by
  have w₀ := WordsBounded.upd_nreg hw (show 1 ≤ W by omega) c.pc (r := 50102)
  refine spec_seq ⟨_, _, Exec.constN hw 50102 1 (by omega), ?_⟩
  by_cases hj : c.nreg 50100 < c.nreg 10504
  · rw [ite_eq_left hj]
    refine spec_ifLtN_true (by config_simp; exact hj) ?_
    obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W loadPos
        { c with nreg := upd c.nreg 50102 1 } c₁ k₁ ∧ k₁ = 8 ∧
        (c₁.nreg 10011 = c.nmem (c.nreg 10503 + 5 * c.nreg 50100 + 1) ∧
          c₁.nreg 10012 = c.nmem (c.nreg 10503 + 5 * c.nreg 50100 + 2) ∧
          c₁.nreg 50102 = 1 ∧ c₁.nreg 10500 = c.nreg 10500 ∧ c₁.nreg 10501 = c.nreg 10501 ∧
          c₁.nreg 10502 = c.nreg 10502) := by
      unfold loadPos
      exec_block
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · config_simp; omega
      · refine ⟨rfl, ?_⟩
        config_simp
        refine ⟨?_, ?_⟩ <;> congr 1 <;> omega
    obtain ⟨q11, q12, q102, q500, q501, q502⟩ := q
    obtain ⟨c₂, k₂, e₂, hk₂, hr⟩ := cmpPos_exec (P := P) hG hW c₁ e₁.wb_right q102
      (by rw [q501]; exact hxn)
    refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, ?_⟩
    rw [hr, q11, q12, q500, q501, q502]
  · rw [ite_eq_right hj]
    refine spec_ifLtN_false (by config_simp; exact hj)
      (spec_instr (Exec.constN w₀ _ _ (by omega)) fun _ => ?_)
    exact ⟨by omega, by config_simp; rfl⟩

/-! ## The contract of the search -/

/-- **The invariant of the search** for the query `x`, direction code `d`, arc area `AB` with
`A` arcs, memory `m₀` below `A₀`; register `10505` carries a value `SB` across the search. -/
def CmpJ (x : WPos) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop :=
  c.nreg 10500 = x.edge ∧ c.nreg 10501 = x.hgt ∧ c.nreg 10502 = d ∧ c.nreg 10503 = AB ∧
    c.nreg 10504 = A ∧ c.nreg 10505 = SB ∧ ∀ a, a < A₀ → c.nmem a = m₀ a

/-- **The predicate of the search**: the machine decision on the start of arc `j`. -/
noncomputable def cmpPr (P : Polygon) (x : WPos) (d AB A : ℕ) (m₀ : ℕ → ℕ) (j : ℕ) : Bool :=
  if j < A then keyDec (Qof P) P.n x d ⟨m₀ (AB + 5 * j + 1), m₀ (AB + 5 * j + 2)⟩ else false

/-- The invariant is insensitive to the writes of the search. -/
theorem cmpJ_stable (x : WPos) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) :
    JStableL (CmpJ x d AB A SB A₀ m₀) A₀ := by
  intro c c' h hr _ hm _ _
  obtain ⟨h0, h1, h2, h3, h4, h6, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => (hm a ha).trans (h5 a ha)⟩
  · rw [hr _ (by decide) (by decide), h0]
  · rw [hr _ (by decide) (by decide), h1]
  · rw [hr _ (by decide) (by decide), h2]
  · rw [hr _ (by decide) (by decide), h3]
  · rw [hr _ (by decide) (by decide), h4]
  · rw [hr _ (by decide) (by decide), h6]

/-- **Target 1: the comparison procedure meets the contract of the binary search**, with the
invariant `CmpJ` and the predicate `cmpPr`, in at most `275` steps, writing only `lr 101`,
`lr 102` and the band `bSign`. -/
theorem keyCmp_predOK {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (x : WPos)
    (hx : x.hgt ≤ P.n) (d AB A SB A₀ : ℕ) (m₀ : ℕ → ℕ) (hAB : AB + 5 * A ≤ A₀) (hA₀ : A₀ ≤ W) :
    PredOK P W keyCmp {bSign} (CmpJ x d AB A SB A₀ m₀) (cmpPr P x d AB A m₀) 275 := by
  intro c hw hJ
  obtain ⟨h0, h1, h2, h3, h4, h6, h5⟩ := hJ
  obtain ⟨c', k, e, hk, hr⟩ := keyCmp_exec (P := P) hG hW c hw (by rw [h1]; exact hx)
    (by rw [h3, h4]; omega)
  have fb := exec_frameB e wr_keyCmp
  have hB : ∀ r, Bcmp r = false → c'.nreg r = c.nreg r := fb.1
  refine ⟨c', k, e, hk, ⟨?_, ?_, ?_, ?_, ?_, ?_, fun a ha => by rw [fb.2.2.1]; exact h5 a ha⟩, ?_,
    ?_, ?_, fb.2.2.1, fb.2.2.2.1, fb.2.2.2.2⟩
  · rw [hB _ (by decide), h0]
  · rw [hB _ (by decide), h1]
  · rw [hB _ (by decide), h2]
  · rw [hB _ (by decide), h3]
  · rw [hB _ (by decide), h4]
  · rw [hB _ (by decide), h6]
  · rw [hr, h0, h1, h2, h3, h4]
    unfold cmpPr
    by_cases hj : c.nreg 50100 < A
    · rw [ite_eq_left hj, ite_eq_left hj, h5 _ (by omega), h5 _ (by omega)]
    · rw [ite_eq_right hj, ite_eq_right hj]
  · intro r r0 r1 r2 hb
    apply hB
    unfold Bcmp Bk
    rcases hb with hb | hb
    · simp only [Finset.mem_singleton] at hb
      unfold bandOf bSign at hb
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      omega
    · subst hb; decide
  · intro r hb
    apply exec_rframe e wrR_keyCmp
    unfold Bk
    simp only [Finset.mem_singleton] at hb
    unfold bandOf bSign at hb
    simp only [decide_eq_false_iff_not]
    omega

end

end WalkKey

end Chazelle.Core
