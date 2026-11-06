module

public meta import Chazelle.Arithmetic

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
  · grind
  · have := C.topIdx_min (j := 0) (by omega) (fun i hi => by
      grind)
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
  refine ⟨rfl, ‹_›, ⟨by config_simp, by ram_simp⟩,
    ⟨by config_simp, by ram_simp⟩, ⟨by config_simp, by config_simp⟩,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  unfold D0RG at hr
  simp only
  repeat ram_simp

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
  all_goals simp_all

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
  all_goals try (config_simp; omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · ram_simp
  · ram_simp
  · simp_all +arith
  · simp_all
  · simp_all
  · simp_all
  all_goals (grind [Machine.upd_apply, D0RG])

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
    fr2 r (by core_grind)
  have bk : ∀ r, 160000 ≤ r → Bk r = false := fun r h => by core_grind
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
    grind [SignTest, SymPt.eval]
  have c3_00 : c3.nreg 180000 = s := by
    ram_grind
  have c3_10 : c3.nreg 180010 = P.n := by
    ram_grind
  
  obtain ⟨C0, hC0P, hC0s, hC0m⟩ : ∃ C0 : Chain, C0.P = Qof P ∧ C0.s = s ∧ C0.m = 1 :=
    ⟨⟨Qof P, s, 1, le_rfl, by omega⟩, rfl, rfl, rfl⟩
  obtain ⟨c4, k4, e4, hk4, fb4, hb4, hiff4⟩ := bitS_exec hG hWn hW8 (C := C0) hC0P
    (by omega) c3 hw3 (by omega) c3_10 b11
    (by ram_grind) b28
  obtain ⟨fr4, frr4, hm4, hrm4, ho4⟩ := fb4
  have hw4 := e4.wb_right
  have k4r : ∀ r, Bbit r = false → c4.nreg r = c3.nreg r := fr4
  have bb : ∀ r, 160000 ≤ r → r < 170061 → Bbit r = false := fun r a b => by
    grind [Bbit, Bk]
  -- the stores
  have c4r : ∀ r, 160000 ≤ r → r < 170050 → c4.nreg r = c.nreg r := fun r a b => by
    rw [k4r r (bb r a (by omega)), fr3 r (by omega) (by omega) (by omega) (by omega) (by omega),
      k2r r (bk r a) (by omega), fr1 r (by omega_nf)]
  have c4A : c4.nreg ALLOC = TD := by
    rw [k4r _ (by grind [Bbit, Bk]), fr3 _ (by omega) (by omega)
      (by omega) (by omega) (by omega),
      k2r _ (by grind [Bk]) (by omega), fr1 _ (by omega_nf)]
    exact hA
  obtain ⟨c5, k5, e5, hk5, hw5, h5A, h560, w0, w1, w2, w3, w4, hm5, fr5, hrr5, hrm5, ho5⟩ :=
    d0StoreB_exec (P := P) hw4 (TD := TD) (hp := hp) (s := s) (t := t)
      (b := c4.nreg 180014)
      c4A
      (by ram_grind) (by ram_grind)
      (by grind)
      rfl (by ram_grind)
      (by ram_grind) hW
  have hm5c : ∀ a, (a < TD ∨ TD + 5 ≤ a) → c5.nmem a = c.nmem a := fun a ha => by
    ram_grind
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))),
    by omega, hw5, h5A, h560, w0, fun C hCP hCs hCm hH => ?_, hm5c,
    fun r h1 h2 h3 h4 => ?_, fun r h1 h2 h3 => ?_, by ram_grind,
    by ram_grind⟩
  · have hC : C = C0 := chain_eq (by grind) (by omega) (by omega)
    subst hC
    refine ⟨by ram_grind, ?_, by rw [w1, hCs], by rw [w2, hCm],
      by ram_grind, by rw [w4]; exact hiff4⟩
    rw [hCP]; have := L41.poly_whole (Qof P) (by omega); grind
  · have hb' : bandOf r ≠ 18 := h2
    unfold bandOf at hb'
    unfold D0RG at h1
    rw [fr5 r (by omega_nf) h4, k4r r (by simp [Bbit, h3]; omega),
      fr3 r (by omega) (by omega) (by omega) (by omega) (by omega),
      k2r r h3 (by omega), fr1 r (by omega_nf)]
  · have hb : bandOf r ≠ 17 := h2
    have hb' : bandOf r ≠ 18 := h3
    unfold bandOf at hb hb'
    rw [hrr5, frr4 r (by simp [Bbit, h1]; omega), hrr3, frr2 r (by grind [Bkb]), hrr1]

end proofs

end

end Chazelle.Core.Up
