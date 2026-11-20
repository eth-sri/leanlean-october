module

public import Chazelle.Core.Lemma41Ram3
public import Chazelle.Core.Lemma41Junc
public import Chazelle.Core.SweepPrimKer

/-!
# WP-J, part 10: the descriptor of a merged chain on the RAM

`descS`: from the records at `pl` (register `160035`) and `pr` (`160036`) of two consecutive
chains, write at `TD` (`160037`) the descriptor of their union: host, start, length, and the top
index and bit of the part whose top is higher (one sign test, `kbit … 1`, in `160049`).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs SweepPrim SignK WalkKey

@[expose] public section

/-- The loads and the three symbolic points. -/
def descLoadB : Stmt := block [
  .addN 160038 160035 160024, .loadN 160050 160038,
  .addN 160038 160038 160024, .loadN 160051 160038,
  .addN 160038 160038 160024, .loadN 160052 160038,
  .addN 160038 160038 160024, .loadN 160053 160038,
  .addN 160038 160036 160024, .addN 160038 160038 160024, .loadN 160054 160038,
  .addN 160038 160038 160024, .loadN 160055 160038,
  .addN 160038 160038 160024, .loadN 160056 160038,
  .constN 160040 0, .addN 160041 160050 160052,
  .constN 160043 0, .addN 160044 160050 160051, .addN 160044 160044 160055,
  .constN 160046 0, .constN 160047 0]

/-- The first three descriptor words. -/
def descHeadB : Stmt := block [.loadN 160038 160035, .storeN 160037 160038,
  .addN 160038 160037 160024, .storeN 160038 160050,
  .addN 160039 160051 160054, .addN 160038 160038 160024, .storeN 160038 160039]

/-- The top word and the bit: of the left part (flag `0`) or of the right part. -/
def descTopS : Stmt := .ifLtN 160049 160024
  (block [.addN 160038 160038 160024, .storeN 160038 160052,
    .addN 160038 160038 160024, .storeN 160038 160053])
  (block [.addN 160039 160051 160055, .addN 160038 160038 160024, .storeN 160038 160039,
    .addN 160038 160038 160024, .storeN 160038 160056])

/-- **The descriptor of the union.** -/
def descS : Stmt := .seq descLoadB (.seq (kbit 160040 160043 160046 1 160049)
  (.seq descHeadB descTopS))

/-- The registers written by `descS` in band `bL41`. -/
def DescRG (r : ℕ) : Prop := (160038 ≤ r ∧ r ≤ 160056)

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 16000000 in
theorem descLoadB_exec {c : Config} (hw : WordsBounded W c) {pl pr : ℕ}
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h24 : c.nreg 160024 = 1)
    (hW1 : pl + 4 ≤ W) (hW2 : pr + 4 ≤ W)
    (hW3 : c.nmem (pl + 1) + c.nmem (pl + 3) ≤ W)
    (hW4 : c.nmem (pl + 1) + c.nmem (pl + 2) + c.nmem (pr + 3) ≤ W) :
    ∃ c' k, Exec P W descLoadB c c' k ∧ k = 22 ∧ WordsBounded W c' ∧
      c'.nreg 160050 = c.nmem (pl + 1) ∧ c'.nreg 160051 = c.nmem (pl + 2) ∧
      c'.nreg 160052 = c.nmem (pl + 3) ∧ c'.nreg 160053 = c.nmem (pl + 4) ∧
      c'.nreg 160054 = c.nmem (pr + 2) ∧ c'.nreg 160055 = c.nmem (pr + 3) ∧
      c'.nreg 160056 = c.nmem (pr + 4) ∧
      c'.nreg 160040 = 0 ∧ c'.nreg 160041 = c.nmem (pl + 1) + c.nmem (pl + 3) ∧
      c'.nreg 160043 = 0 ∧ c'.nreg 160044 = c.nmem (pl + 1) + c.nmem (pl + 2) + c.nmem (pr + 3) ∧
      c'.nreg 160046 = 0 ∧ c'.nreg 160047 = 0 ∧
      (∀ r, ¬ DescRG r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descLoadB
  exec_block
  all_goals try (config_simp; simp only [h35, h36, h24, Nat.add_assoc, Nat.reduceAdd]; omega)
  all_goals try omega
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => by
      unfold DescRG at hr
      simp only
      repeat (rw [Machine.upd_other _ _ _ (by omega)]),
    rfl, rfl, rfl, rfl⟩
  all_goals (config_simp; try simp only [h35, h36, h24, Nat.add_assoc, Nat.reduceAdd])

set_option maxHeartbeats 8000000 in
theorem descHeadB_exec {c : Config} (hw : WordsBounded W c) {pl TD sl ml mr : ℕ}
    (h35 : c.nreg 160035 = pl) (h37 : c.nreg 160037 = TD) (h24 : c.nreg 160024 = 1)
    (h50 : c.nreg 160050 = sl) (h51 : c.nreg 160051 = ml) (h54 : c.nreg 160054 = mr)
    (hW : TD + 5 ≤ W) (hWm : ml + mr ≤ W) :
    ∃ c' k, Exec P W descHeadB c c' k ∧ k = 7 ∧ WordsBounded W c' ∧
      c'.nmem TD = c.nmem pl ∧ c'.nmem (TD + 1) = sl ∧ c'.nmem (TD + 2) = ml + mr ∧
      (∀ a, a ≠ TD → a ≠ TD + 1 → a ≠ TD + 2 → c'.nmem a = c.nmem a) ∧
      c'.nreg 160038 = TD + 2 ∧
      (∀ r, r ≠ 160038 → r ≠ 160039 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descHeadB
  exec_block
  all_goals try (config_simp; simp only [h35, h37, h24, h50, h51, h54]; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun a a1 a2 a3 => ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h35, h37, h24, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h35, h37, h24, h50, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h35, h37, h24, h50, h51, h54, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h35, h37, h24, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h37, h24]
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem descTopS_exec {c : Config} (hw : WordsBounded W c) {TD f tl bl ml tr br : ℕ}
    (h38 : c.nreg 160038 = TD + 2) (h24 : c.nreg 160024 = 1) (h49 : c.nreg 160049 = f)
    (h52 : c.nreg 160052 = tl) (h53 : c.nreg 160053 = bl) (h51 : c.nreg 160051 = ml)
    (h55 : c.nreg 160055 = tr) (h56 : c.nreg 160056 = br) (hW : TD + 5 ≤ W)
    (hWm : ml + tr ≤ W) :
    ∃ c' k, Exec P W descTopS c c' k ∧ k ≤ 7 ∧ WordsBounded W c' ∧
      c'.nmem (TD + 3) = (if f < 1 then tl else ml + tr) ∧
      c'.nmem (TD + 4) = (if f < 1 then bl else br) ∧
      (∀ a, a ≠ TD + 3 → a ≠ TD + 4 → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 160038 → r ≠ 160039 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descTopS
  by_cases hf : c.nreg 160049 < c.nreg 160024
  · rw [h49, h24] at hf
    obtain ⟨c', k, e, hk, hw', r1, r2, r3, r4, r5, r6, r7⟩ : ∃ c' k, Exec P W
        (block [.addN 160038 160038 160024, .storeN 160038 160052,
          .addN 160038 160038 160024, .storeN 160038 160053]) c c' k ∧ k = 4 ∧
        WordsBounded W c' ∧ c'.nmem (TD + 3) = tl ∧ c'.nmem (TD + 4) = bl ∧
        (∀ a, a ≠ TD + 3 → a ≠ TD + 4 → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 160038 → r ≠ 160039 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try (config_simp; simp only [h38, h24]; omega)
      refine ⟨rfl, ‹_›, ?_, ?_, fun a a1 a2 => ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [h38, h24, h52, h53, Machine.upd_apply]
        split_ifs <;> first | omega
      · config_simp; simp only [h38, h24, h52, h53, Machine.upd_apply]
        split_ifs <;> first | omega
      · config_simp; simp only [h38, h24, Machine.upd_apply]
        split_ifs <;> first | omega
      · simp only
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
    refine ⟨c', k + 1, .ifLtN_true (by rw [h49, h24]; exact hf) e, by omega, hw',
      by rw [ite_eq_left hf]; exact r1, by rw [ite_eq_left hf]; exact r2, r3, r4, r5, r6, r7⟩
  · rw [h49, h24] at hf
    obtain ⟨c', k, e, hk, hw', r1, r2, r3, r4, r5, r6, r7⟩ : ∃ c' k, Exec P W
        (block [.addN 160039 160051 160055, .addN 160038 160038 160024, .storeN 160038 160039,
          .addN 160038 160038 160024, .storeN 160038 160056]) c c' k ∧ k = 5 ∧
        WordsBounded W c' ∧ c'.nmem (TD + 3) = ml + tr ∧ c'.nmem (TD + 4) = br ∧
        (∀ a, a ≠ TD + 3 → a ≠ TD + 4 → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 160038 → r ≠ 160039 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try (config_simp; simp only [h38, h24, h51, h55]; omega)
      refine ⟨rfl, ‹_›, ?_, ?_, fun a a1 a2 => ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
      · config_simp; simp only [h38, h24, h51, h55, h56, Machine.upd_apply]
        split_ifs <;> first | omega
      · config_simp; simp only [h38, h24, h51, h55, h56, Machine.upd_apply]
        split_ifs <;> first | omega
      · config_simp; simp only [h38, h24, Machine.upd_apply]
        split_ifs <;> first | omega
      · simp only
        repeat (rw [Machine.upd_other _ _ _ (by omega)])
    refine ⟨c', k + 2, .ifLtN_false (by rw [h49, h24]; exact hf) e, by omega, hw',
      by rw [ite_eq_right hf]; exact r1, by rw [ite_eq_right hf]; exact r2, r3, r4, r5, r6, r7⟩

theorem top_eq {P : Polygon} {C : Chain} (hC : C.P = Qof P) (hn : C.s + C.m < P.n) :
    C.top = (Qof P).vtx (C.s + C.topIdx) := by
  have := C.topIdx_le
  have hQn : (Qof P).n = P.n := shear_n _ _
  show C.vertex C.topIdx = _
  unfold Chain.vertex Chain.edgeIdx
  rw [hC, hQn, Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 16000000 in
/-- **The descriptor of the union on the RAM.** -/
theorem descS_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {pl pr TD : ℕ} {H : Host} {C₁ C₂ : Chain}
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h37 : c.nreg 160037 = TD)
    (h24 : c.nreg 160024 = 1)
    (hd1 : ChainDescAt c.nmem pl (Qof P) H C₁) (hd2 : ChainDescAt c.nmem pr (Qof P) H C₂)
    (hP1 : C₁.P = Qof P) (hP2 : C₂.P = Qof P) (hs : C₂.s = C₁.s + C₁.m)
    (hn : C₁.s + C₁.m + C₂.m + 1 ≤ P.n) (hlo : pl + 5 ≤ TD) (hlo' : pr + 5 ≤ TD)
    (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k ≤ 300 ∧ WordsBounded W c' ∧
      (∀ _hj : C₁.m + C₂.m + 1 ≤ C₁.P.n, ∀ a, a < TD → c'.nmem a = c.nmem a) ∧
      c'.nmem TD = c.nmem pl ∧ c'.nmem (TD + 1) = C₁.s ∧ c'.nmem (TD + 2) = C₁.m + C₂.m ∧
      c'.nmem (TD + 3) = (if (C₂.top).2 ≤ (C₁.top).2 then C₁.topIdx else C₁.m + C₂.topIdx) ∧
      c'.nmem (TD + 4) = (if (C₂.top).2 ≤ (C₁.top).2 then c.nmem (pl + 4) else c.nmem (pr + 4)) ∧
      (∀ a, (a < TD ∨ TD + 5 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ DescRG r → Bk r = false → c'.nreg r = c.nreg r) ∧
      (∀ r, Bk r = false → r ≠ 160049 → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨-, -, d1s, d1m, d1t, -⟩ := hd1
  obtain ⟨-, -, d2s, d2m, d2t, -⟩ := hd2
  have ht1 := C₁.topIdx_le; have ht2 := C₂.topIdx_le
  -- loads
  obtain ⟨c1, k1, e1, hk1, hw1, l50, l51, l52, l53, l54, l55, l56, l40, l41, l43, l44, l46, l47,
    fr1, hm1, hrr1, hrm1, ho1⟩ := descLoadB_exec (P := P) hw h35 h36 h24 (by omega) (by omega)
    (by rw [d1s, d1t]; omega) (by rw [d1s, d1m, d2t]; omega)
  rw [d1s] at l50 l41 l44; rw [d1m] at l51 l44; rw [d1t] at l52 l41; rw [d2m] at l54
  rw [d2t] at l55 l44
  -- the sign test
  obtain ⟨c2, k2, e2, hk2, fb2, hf2, hiff2⟩ := kbit_exec (P := P) hG hWn c1 hw1
    (a := 160040) (b := 160043) (d := 160046) (op := 1) (dst := 160049) (by omega) (by omega)
    (by omega) (by omega) (by omega) (sa := .vtx (C₁.s + C₁.topIdx))
    (sb := .vtx (C₁.s + C₁.m + C₂.topIdx)) (sd := .vtx 0)
    (show C₁.s + C₁.topIdx < P.n by omega) (show C₁.s + C₁.m + C₂.topIdx < P.n by omega)
    (show 0 < P.n by omega) ⟨l40, l41⟩ ⟨l43, l44⟩ ⟨l46, l47⟩
  obtain ⟨fr2, frr2, hm2, hrm2, ho2⟩ := fb2
  have hw2 := e2.wb_right
  have k2r : ∀ r, Bk r = false → r ≠ 160049 → c2.nreg r = c1.nreg r := fun r h1 h2 =>
    fr2 r (by simp [Bkb, h1, h2])
  have hflag : c2.nreg 160049 = 1 ↔ (C₁.top).2 < (C₂.top).2 := by
    rw [hiff2]
    simp only [SignTest, SymPt.eval]
    rw [top_eq hP1 (by omega), top_eq hP2 (by rw [hs]; omega), hs]
  have bk : ∀ r, 160000 ≤ r → Bk r = false := fun r h => by simp [Bk]; omega
  -- the head words
  obtain ⟨c3, k3, e3, hk3, hw3, m0, m1', m2', mout3, h38, fr3, hrr3, hrm3, ho3⟩ :=
    descHeadB_exec (P := P) hw2 (pl := pl) (TD := TD) (sl := C₁.s) (ml := C₁.m) (mr := C₂.m)
    (by rw [k2r _ (bk _ (by omega)) (by omega), fr1 _ (by unfold DescRG; omega)]; exact h35)
    (by rw [k2r _ (bk _ (by omega)) (by omega), fr1 _ (by unfold DescRG; omega)]; exact h37)
    (by rw [k2r _ (bk _ (by omega)) (by omega), fr1 _ (by unfold DescRG; omega)]; exact h24)
    (by rw [k2r _ (bk _ (by omega)) (by omega)]; exact l50)
    (by rw [k2r _ (bk _ (by omega)) (by omega)]; exact l51)
    (by rw [k2r _ (bk _ (by omega)) (by omega)]; exact l54) hW (by omega)
  -- the top word and the bit
  obtain ⟨c4, k4, e4, hk4, hw4, m3', m4', mout4, fr4, hrr4, hrm4, ho4⟩ :=
    descTopS_exec (P := P) hw3 (TD := TD) (f := c2.nreg 160049) (tl := C₁.topIdx)
    (bl := c.nmem (pl + 4)) (ml := C₁.m) (tr := C₂.topIdx) (br := c.nmem (pr + 4)) h38
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega),
      fr1 _ (by unfold DescRG; omega)]; exact h24)
    (by rw [fr3 _ (by omega) (by omega)])
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega)]; exact l52)
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega), l53])
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega)]; exact l51)
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega)]; exact l55)
    (by rw [fr3 _ (by omega) (by omega), k2r _ (bk _ (by omega)) (by omega), l56])
    hW (by omega)
  have hfle : c2.nreg 160049 < 1 ↔ (C₂.top).2 ≤ (C₁.top).2 := by
    have := hf2
    constructor
    · intro h; by_contra hc; push Not at hc; have := hflag.mpr hc; omega
    · intro h; by_contra hc
      have : c2.nreg 160049 = 1 := by omega
      have := hflag.mp this; linarith
  have mem4 : ∀ a, (a < TD ∨ TD + 5 ≤ a) → c4.nmem a = c.nmem a := fun a ha => by
    rw [mout4 a (by omega) (by omega), mout3 a (by omega) (by omega) (by omega), hm2, hm1]
  refine ⟨c4, k1 + (k2 + (k3 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), by omega, hw4,
    fun _ a ha => mem4 a (Or.inl ha), ?_, ?_, ?_, ?_, ?_, mem4, fun r h1 h2 => ?_, fun r hr hr' => ?_,
    by rw [hrm4, hrm3, hrm2, hrm1], by rw [ho4, ho3, ho2, ho1]⟩
  · rw [mout4 _ (by omega) (by omega), m0, hm2, hm1]
  · rw [mout4 _ (by omega) (by omega), m1']
  · rw [mout4 _ (by omega) (by omega), m2']
  · rw [m3']; split_ifs with a1 a2 a2 <;> first | rfl | (exfalso; exact a2 (hfle.mp a1)) |
      (exfalso; exact a1 (hfle.mpr a2))
  · rw [m4']; split_ifs with a1 a2 a2 <;> first | rfl | (exfalso; exact a2 (hfle.mp a1)) |
      (exfalso; exact a1 (hfle.mpr a2))
  · unfold DescRG at h1
    rw [fr4 r (by omega) (by omega), fr3 r (by omega) (by omega), k2r r h2 (by omega),
      fr1 r (by unfold DescRG; omega)]
  · rw [hrr4, hrr3, frr2 r (by simp [Bkb, hr, hr']), hrr1]

end proofs

end

end Chazelle.Core.L41
