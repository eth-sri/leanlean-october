module

public import Chazelle.Core.UpPhase1
public import Chazelle.Core.BruteRam3

/-!
# WP-J up phase, part 2: the descriptor of a grade-0 chain

`desc0S`: for the edge `v_s v_{s+1}` of `Q` (register `170016 = s`), write at the allocator the
descriptor `[host, s, 1, top, bit]`: the top index by one height test (`kbit`), the orientation
bit by WP-K's `bitS` (`desc0S_exec`).

Registers: `170004` the host, `170001` `n`, `170016` `s`, `170050 … 170060` scratch
(`170060` the descriptor address); constants `170020 = 1`, `170023 = 5`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey
  Chazelle.Core.Brute

@[expose] public section

/-- The top index of a one-edge chain. -/
theorem topIdx_one {C : Chain} (h1 : C.m = 1) :
    C.topIdx = if (C.vertex 0).2 < (C.vertex 1).2 then 1 else 0 := by
  have ht := C.topIdx_le
  have hspec := C.topIdx_spec.2
  split_ifs with h
  · by_contra hc
    have h0 : C.topIdx = 0 := by omega
    have := hspec 1 (by omega)
    rw [h0] at this; linarith
  · have := C.topIdx_min (j := 0) (by omega) (fun i hi => by
      rcases Nat.lt_or_ge i 1 with h2 | h2
      · rw [show i = 0 by omega]
      · rw [show i = 1 by omega]; exact not_lt.mp h)
    omega

/-- The points of the height test. -/
def d0PtsB : Stmt := block [.constN 170050 0, .copyN 170051 170016, .constN 170053 0,
  .addN 170054 170016 170020, .constN 170056 0, .constN 170057 0]

/-- The registers of `bitS`. -/
def d0BitB : Stmt := block [.copyN 180000 170016, .copyN 180010 170001, .constN 180011 1,
  .copyN 180013 170059, .constN 180028 0]

/-- The descriptor words. -/
def d0StoreB : Stmt := block [.copyN 170060 9999, .addN 9999 9999 170023,
  .storeN 170060 170004, .addN 170058 170060 170020, .storeN 170058 170016,
  .addN 170058 170058 170020, .storeN 170058 170020, .addN 170058 170058 170020,
  .storeN 170058 170059, .addN 170058 170058 170020, .storeN 170058 180014]

/-- **The descriptor of a grade-0 chain.** -/
def desc0S : Stmt := .seq d0PtsB (.seq (kbit 170050 170053 170056 1 170059)
  (.seq d0BitB (.seq bitS d0StoreB)))

/-- The registers of band `bUp` written by `desc0S`. -/
def D0RG (r : ℕ) : Prop := 170050 ≤ r ∧ r ≤ 170060

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem d0PtsB_exec {c : Config} (hw : WordsBounded W c) {s : ℕ}
    (h16 : c.nreg 170016 = s) (h20 : c.nreg 170020 = 1) (hW : s + 1 ≤ W) :
    ∃ c' k, Exec P W d0PtsB c c' k ∧ k = 6 ∧ WordsBounded W c' ∧
      SymPtIn c' 170050 (.vtx s) ∧ SymPtIn c' 170053 (.vtx (s + 1)) ∧
      SymPtIn c' 170056 (.vtx 0) ∧
      (∀ r, ¬ D0RG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold d0PtsB
  exec_block
  all_goals try (config_simp; (try simp only [h16, h20]); omega)
  refine ⟨rfl, ‹_›, ⟨by config_simp, by config_simp; exact h16⟩,
    ⟨by config_simp, by config_simp; simp only [h16, h20]⟩, ⟨by config_simp, by config_simp⟩,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  unfold D0RG at hr
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem d0BitB_exec {c : Config} (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W d0BitB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 180000 = c.nreg 170016 ∧ c'.nreg 180010 = c.nreg 170001 ∧ c'.nreg 180011 = 1 ∧
      c'.nreg 180013 = c.nreg 170059 ∧ c'.nreg 180028 = 0 ∧
      (∀ r, r ≠ 180000 → r ≠ 180010 → r ≠ 180011 → r ≠ 180013 → r ≠ 180028 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold d0BitB
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, by config_simp, by config_simp, by config_simp, by config_simp,
    by config_simp, fun r a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  simp only
  repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem d0StoreB_exec {c : Config} (hw : WordsBounded W c) {TD hp s t b : ℕ}
    (hA : c.nreg ALLOC = TD) (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = s)
    (h59 : c.nreg 170059 = t) (h14 : c.nreg 180014 = b) (h20 : c.nreg 170020 = 1)
    (h23 : c.nreg 170023 = 5) (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W d0StoreB c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170060 = TD ∧
      c'.nmem TD = hp ∧ c'.nmem (TD + 1) = s ∧ c'.nmem (TD + 2) = 1 ∧ c'.nmem (TD + 3) = t ∧
      c'.nmem (TD + 4) = b ∧ (∀ a, (a < TD ∨ TD + 5 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ D0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold d0StoreB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h20, h23]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h23]
  · config_simp; simp only [hA]
  · config_simp; simp only [hA, h04, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h16, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h59, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h14, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [hA, h20, Machine.upd_apply]; split_ifs <;> first | omega
  · unfold D0RG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 16000000 in
/-- **The descriptor of a grade-0 chain on the RAM.** -/
theorem desc0S_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp s : ℕ} (hA : c.nreg ALLOC = TD) (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = s)
    (h01 : c.nreg 170001 = P.n) (h20 : c.nreg 170020 = 1) (h23 : c.nreg 170023 = 5)
    (hs : s + 2 ≤ P.n) (hW : TD + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W desc0S c c' k ∧ k ≤ 1900 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170060 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = s → C.m = 1 → HostAt c'.nmem hp (Host.whole P.n) →
        ChainDescAt c'.nmem TD (Qof P) (Host.whole P.n) C) ∧
      (∀ a, (a < TD ∨ TD + 5 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ D0RG r → bandOf r ≠ bBrute → Bk r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, Bk r = false → bandOf r ≠ bUp → bandOf r ≠ bBrute → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn : 1 ≤ P.n := by omega
  -- the points
  obtain ⟨c1, k1, e1, hk1, hw1, p1, p2, p3, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    d0PtsB_exec (P := P) hw h16 h20 (by omega)
  -- the height test
  obtain ⟨c2, k2, e2, hk2, fb2, hf2, hiff2⟩ := kbit_exec (P := P) hG hWn c1 hw1
    (a := 170050) (b := 170053) (d := 170056) (op := 1) (dst := 170059) (by omega) (by omega)
    (by omega) (by omega) (by omega) (sa := .vtx s) (sb := .vtx (s + 1)) (sd := .vtx 0)
    (show s < P.n by omega) (show s + 1 < P.n by omega) (show 0 < P.n by omega) p1 p2 p3
  obtain ⟨fr2, frr2, hm2, hrm2, ho2⟩ := fb2
  have hw2 := e2.wb_right
  have k2r : ∀ r, Bk r = false → r ≠ 170059 → c2.nreg r = c1.nreg r := fun r h1 h2 =>
    fr2 r (by simp [Bkb, h1, h2])
  have bk : ∀ r, 160000 ≤ r → Bk r = false := fun r h => by simp [Bk]; omega
  -- the bit registers
  obtain ⟨c3, k3, e3, hk3, hw3, b00, b10, b11, b13, b28, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    d0BitB_exec (P := P) hw2 (by omega)
  -- the bit
  set t := c2.nreg 170059 with ht
  have hsn : ∀ C : Chain, C.P = Qof P → C.s = s → C.m = 1 → C.topIdx = t := by
    intro C hCP hCs hCm
    rw [topIdx_one hCm]
    have e0 : C.vertex 0 = (Qof P).vtx s := by
      unfold Chain.vertex Chain.edgeIdx; rw [hCP, hQn, hCs, Nat.add_zero,
        Nat.mod_eq_of_lt (by omega)]
    have e1 : C.vertex 1 = (Qof P).vtx (s + 1) := by
      unfold Chain.vertex Chain.edgeIdx; rw [hCP, hQn, hCs, Nat.mod_eq_of_lt (by omega)]
    rw [e0, e1]
    have hiff : t = 1 ↔ ((Qof P).vtx s).2 < ((Qof P).vtx (s + 1)).2 := by
      rw [ht, hiff2]; simp only [SignTest, SymPt.eval]
    split_ifs with h
    · exact (hiff.mpr h).symm
    · have : t ≠ 1 := fun h' => h (hiff.mp h')
      omega
  have c3_00 : c3.nreg 180000 = s := by
    rw [b00, k2r _ (bk _ (by omega)) (by omega), fr1 _ (by unfold D0RG; omega)]; exact h16
  have c3_10 : c3.nreg 180010 = P.n := by
    rw [b10, k2r _ (bk _ (by omega)) (by omega), fr1 _ (by unfold D0RG; omega)]; exact h01
  have c3_13 : c3.nreg 180013 = t := by rw [b13]
  obtain ⟨C0, hC0P, hC0s, hC0m⟩ : ∃ C0 : Chain, C0.P = Qof P ∧ C0.s = s ∧ C0.m = 1 :=
    ⟨⟨Qof P, s, 1, le_rfl, by rw [hQn]; omega⟩, rfl, rfl, rfl⟩
  obtain ⟨c4, k4, e4, hk4, fb4, hb4, hiff4⟩ := bitS_exec hG hWn hW8 (C := C0) hC0P
    (by rw [hC0s, hC0m]; omega) c3 hw3 (by rw [c3_00, hC0s]) c3_10 b11
    (by rw [c3_13, hsn C0 hC0P hC0s hC0m]) b28
  obtain ⟨fr4, frr4, hm4, hrm4, ho4⟩ := fb4
  have hw4 := e4.wb_right
  have k4r : ∀ r, Bbit r = false → c4.nreg r = c3.nreg r := fr4
  have bb : ∀ r, 160000 ≤ r → r < 170061 → Bbit r = false := fun r a b => by
    simp [Bbit, Bk]; omega
  -- the stores
  have c4r : ∀ r, 160000 ≤ r → r < 170050 → c4.nreg r = c.nreg r := fun r a b => by
    rw [k4r r (bb r a (by omega)), fr3 r (by omega) (by omega) (by omega) (by omega) (by omega),
      k2r r (bk r a) (by omega), fr1 r (by unfold D0RG; omega)]
  have c4A : c4.nreg ALLOC = TD := by
    rw [k4r _ (by simp [Bbit, Bk, hAl]), fr3 _ (by rw [hAl]; omega) (by rw [hAl]; omega)
      (by rw [hAl]; omega) (by rw [hAl]; omega) (by rw [hAl]; omega),
      k2r _ (by simp [Bk, hAl]) (by rw [hAl]; omega), fr1 _ (by unfold D0RG; rw [hAl]; omega)]
    exact hA
  obtain ⟨c5, k5, e5, hk5, hw5, h5A, h560, w0, w1, w2, w3, w4, hm5, fr5, hrr5, hrm5, ho5⟩ :=
    d0StoreB_exec (P := P) hw4 (TD := TD) (hp := hp) (s := s) (t := t)
      (b := c4.nreg 180014)
      c4A
      (by rw [c4r _ (by omega) (by omega)]; exact h04) (by rw [c4r _ (by omega) (by omega)]; exact h16)
      (by rw [k4r _ (bb _ (by omega) (by omega)), fr3 _ (by omega) (by omega) (by omega) (by omega)
        (by omega)])
      rfl (by rw [c4r _ (by omega) (by omega)]; exact h20)
      (by rw [c4r _ (by omega) (by omega)]; exact h23) hW
  have hm5c : ∀ a, (a < TD ∨ TD + 5 ≤ a) → c5.nmem a = c.nmem a := fun a ha => by
    rw [hm5 a ha, hm4, hm3, hm2, hm1]
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    by omega, hw5, h5A, h560, w0, fun C hCP hCs hCm hH => ?_, hm5c,
    fun r h1 h2 h3 h4 => ?_, fun r h1 h2 h3 => ?_, by rw [hrm5, hrm4, hrm3, hrm2, hrm1],
    by rw [ho5, ho4, ho3, ho2, ho1]⟩
  · have hC : C = C0 := chain_eq (by rw [hCP, hC0P]) (by rw [hCs, hC0s]) (by rw [hCm, hC0m])
    subst hC
    refine ⟨by rw [w0]; exact hH, ?_, by rw [w1, hCs], by rw [w2, hCm],
      by rw [w3, hsn _ hCP hCs hCm], by rw [w4]; exact hiff4⟩
    rw [hCP]; have := L41.poly_whole (Qof P) (by omega); rw [hQn] at this; exact this.symm
  · have hb' : bandOf r ≠ 18 := h2
    unfold bandOf at hb'
    unfold D0RG at h1
    rw [fr5 r (by unfold D0RG; omega) h4, k4r r (by simp [Bbit, h3]; omega),
      fr3 r (by omega) (by omega) (by omega) (by omega) (by omega),
      k2r r h3 (by omega), fr1 r (by unfold D0RG; omega)]
  · have hb : bandOf r ≠ 17 := h2
    have hb' : bandOf r ≠ 18 := h3
    unfold bandOf at hb hb'
    rw [hrr5, frr4 r (by simp [Bbit, h1]; omega), hrr3, frr2 r (by simp [Bkb, h1]; omega), hrr1]

end proofs

end

end Chazelle.Core.Up
