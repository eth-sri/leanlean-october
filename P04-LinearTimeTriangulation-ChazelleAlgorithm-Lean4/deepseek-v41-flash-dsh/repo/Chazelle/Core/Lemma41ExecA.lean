module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Main

/-!
# WP-J, part 26a: the prologue of Lemma 4.1, executed

`l41A_exec`: the constants, the table reads, `Gλ` and the whole host (`l41A`), with the
register values the cover loop and the merge tree need, the frame outside band `bL41`, and
the memory below the entry allocator kept.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle Chazelle.Merge

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}


/-- **The prologue on the RAM.** -/
theorem l41A_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {c : Config} (hw : WordsBounded W c) {A h a L lam : ℕ}
    (hA : c.nreg ALLOC = A) (r0 : c.nreg 160000 = h) (r1 : c.nreg 160001 = a)
    (r2 : c.nreg 160002 = L) (r3 : c.nreg 160003 = lam)
    (hR : Robust A c.nmem fun m' => GradeRaw O P m' h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ (lam - 1) < L) (_hL2 : L ≤ 2 ^ lam)
    (hbud : A + 20 * lam + 100 ≤ W) :
    ∃ c5 k, Exec P W l41A c c5 k ∧ k ≤ 9 * lam + 70 ∧ 9 ≤ k ∧ WordsBounded W c5 ∧
      c5.nreg ALLOC = A + 7 ∧ HostAt c5.nmem A (Host.whole P.n) ∧
      (∀ x, x < A → c5.nmem x = c.nmem x) ∧ c5.rreg = c.rreg ∧ c5.rmem = c.rmem ∧
      c5.output = c.output ∧
      (∀ r, (r < 160000 ∨ 170000 ≤ r) → r ≠ ALLOC → c5.nreg r = c.nreg r) ∧
      c5.nreg 160000 = h ∧ c5.nreg 160010 = a ∧ c5.nreg 160011 = a + L ∧
      c5.nreg 160014 = 0 ∧ c5.nreg 160015 = A + 7 ∧ c5.nreg 160020 = c.nmem (h + 3) ∧
      c5.nreg 160021 = c.nmem (h + 1) + 2 ∧ c5.nreg 160022 = c.nmem (h + 2) ∧
      c5.nreg 160024 = 1 ∧ c5.nreg 160026 = lam ∧ c5.nreg 160027 = A ∧
      c5.nreg 160032 = gradeGran lam ∧ c5.nreg 160033 = gradeGran (lam - 1) ∧
      c5.nreg 160080 = 2 ∧ c5.nreg 160081 = 5 ∧ c5.nreg 160082 = 6 ∧ c5.nreg 160083 = 3 ∧
      c5.nreg 160084 = 4 ∧ c5.nreg 160087 = 8 := by
  have hAl : ALLOC = 9999 := rfl
  have hn3 := hG.1.1
  have hWn' : 128 * P.n + 3 ≤ W := by unfold hostWords at hWh; omega
  have hRaw := hR.holds
  have hΛ : 1 ≤ c.nmem h := by omega
  have hΛtg := hRaw.1
  obtain ⟨t0, t1, t2, t3, tS0, tS1, tS1lt, tpow, thalf, tent⟩ := tab_lt hR (by omega) hΛ
  obtain ⟨S, hS⟩ : ∃ S, c.nmem (h + 1) = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, c.nmem (h + 2) = T := ⟨_, rfl⟩
  rw [hS] at tS0 tS1 tS1lt tpow
  rw [hT] at tent
  have hltg : lam ≤ topGrade P.n + 1 := by omega
  have hcb : Cost.ceilBeta lam ≤ lam := Cost.ceilBeta_le lam
  have hpowl := tpow lam hltg
  have hpowcb := tpow (Cost.ceilBeta lam) (by omega)
  obtain ⟨e0T, e0O, e0G, e0G'⟩ := tent (lam - 1) 0 (by omega) (Nat.succ_pos _)
  simp only [Nat.mul_zero, Nat.add_zero] at e0O e0G e0G'
  have eTl : T + lam - 1 = T + (lam - 1) := by omega
  have hGcap := gradeGran_cap (g := lam) h7
  have hGl : 2 ^ Cost.ceilBeta lam + lam * (Nat.clog 2 lam + 2) = gradeGran lam := by
    unfold gradeGran fuseLoss; ring
  have hcl : Nat.clog 2 lam ≤ lam := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hpl : 2 ^ (lam - 1) ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) (by omega)
  clear tent thalf
  -- 1. constants
  obtain ⟨c1, k1, e1, hk1, hw1, q24, q80, q81, q82, q83, q84, q86, q87, q29, fr1, hm1, hrr1,
    hrm1, ho1⟩ := proC_exec (P := P) hw (by omega)
  -- 2. the table reads
  obtain ⟨c2, k2, e2, hk2, hw2, p10, p11, p26, p20, p101, p21, p22, p33, p102, p103, p32, p14, fr2,
      hm2, hrr2, hrm2, ho2⟩ :=
    proL_exec (P := P) hw1 (h := h) (a := a) (L := L) (lam := lam)
      (by rw [fr1 _ (Or.inl (by decide))]; exact r0) (by rw [fr1 _ (Or.inl (by decide))]; exact r1)
      (by rw [fr1 _ (Or.inl (by decide))]; exact r2) (by rw [fr1 _ (Or.inl (by decide))]; exact r3)
      q24 q80 q83 q84 (by omega)
      (by omega) (by omega) (by rw [hm1, hS]; omega) (by rw [hm1, hT]; omega)
      (by rw [hm1, hT, eTl]; omega) (by rw [hm1, hT, eTl]; omega)
      (by rw [hm1, hS, tS1]; omega) (by rw [hm1, hS, tS1, hpowl.2.1]; omega)
  rw [hm1] at p20; rw [hm1, hS] at p21; rw [hm1] at p22
  rw [hm1, hT, eTl, e0G] at p33
  rw [hm1, hS, tS1, hpowl.2.1, hpowcb.1] at p32
  rw [hm1] at hm2
  have c2r := fr2
  have c2_03 : c2.nreg 160003 = lam := by
    rw [c2r _ (by unfold ProRG; decide), fr1 _ (Or.inl (by decide))]; exact r3
  have c2_24 : c2.nreg 160024 = 1 := by rw [c2r _ (by unfold ProRG; decide)]; exact q24
  -- 3. ⌈log₂ λ⌉
  obtain ⟨c3, k3, e3, hk3, hw3, s04, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    clogS_exec (P := P) hw2 p21 c2_03 c2_24
      (fun i hi => by rw [hm2]; exact (tpow i (by omega)).1) (by omega) (by omega)
  -- 4. Gλ
  obtain ⟨c4, k4, e4, hk4, hw4, s32, fr4, hm4, hrr4, hrm4, ho4⟩ :=
    mulS_exec (P := P) hw3 (lam := lam) (cl := Nat.clog 2 lam) (G2 := 2 ^ Cost.ceilBeta lam)
      s04 (by rw [fr3 _ (by decide) (by decide) (by decide)]; exact c2_03)
      (by rw [fr3 _ (by decide) (by decide) (by decide)]; exact p32)
      (by rw [fr3 _ (by decide) (by decide) (by decide)]; exact c2_24)
      (by rw [fr3 _ (by decide) (by decide) (by decide), c2r _ (by unfold ProRG; decide)];
          exact q80)
      (by rw [hGl]; omega)
  rw [hGl] at s32
  have c42 : ∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → r ≠ 160104 →
      r ≠ 160105 → r ≠ 160031 → c4.nreg r = c2.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    rw [fr4 r a1 a2 a3 a4, fr3 r a5 a6 a7]
  have c41 : ∀ r, ¬ ProRG r → r ≠ 160104 → r ≠ 160105 → r ≠ 160106 → r ≠ 160107 →
      r ≠ 160108 → c4.nreg r = c1.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    unfold ProRG at a1
    rw [c42 r (by omega) a4 a5 a6 a2 a3 (by omega)]
    exact c2r r (by unfold ProRG; exact a1)
  -- 5. the host
  have c4A : c4.nreg ALLOC = A := by
    rw [c41 _ (by rw [hAl]; unfold ProRG; decide) (by rw [hAl]; decide) (by rw [hAl]; decide)
      (by rw [hAl]; decide) (by rw [hAl]; decide) (by rw [hAl]; decide),
      fr1 _ (Or.inl (by rw [hAl]; decide))]; exact hA
  have c4c : ∀ r, 160024 ≤ r → r ≤ 160029 ∨ (160080 ≤ r ∧ r ≤ 160087) → r ≠ 160026 →
      r ≠ 160025 → c4.nreg r = c1.nreg r := fun r a1 a2 a3 a4 =>
    c41 r (by unfold ProRG; omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c5, k5, e5, hk5, hw5, h5A, h527, h515, hhost, hm54, fr5, hrr5, hrm5, ho5⟩ :=
    proH_exec (P := P) hw4 c4A
      (by rw [c4c _ (by decide) (by decide) (by decide) (by decide)]; exact q24)
      (by rw [c4c _ (by decide) (by decide) (by decide) (by decide)]; exact q29)
      (by rw [c4c _ (by decide) (by decide) (by decide) (by decide)]; exact q86) (by omega)
      (by omega) (by omega)
  have c52 : ∀ r, r ≠ 160032 → r ≠ 160106 → r ≠ 160107 → r ≠ 160108 → r ≠ 160104 →
      r ≠ 160105 → r ≠ 160031 → r ≠ 160027 → r ≠ 160028 → r ≠ 160030 → r ≠ 160015 →
      r ≠ ALLOC → c5.nreg r = c2.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 => by
    rw [fr5 r a8 a9 a10 a11 a12]; exact c42 r a1 a2 a3 a4 a5 a6 a7
  have c5c : ∀ r, 160024 ≤ r → r ≤ 160029 ∨ (160080 ≤ r ∧ r ≤ 160087) → r ≠ 160026 →
      r ≠ 160025 → r ≠ 160027 → r ≠ 160028 → c5.nreg r = c1.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [fr5 r a5 a6 (by omega) (by omega) (by rw [hAl]; omega)]; exact c4c r a1 a2 a3 a4
  have p52 : ∀ r, (r = 160010 ∨ r = 160011 ∨ r = 160014 ∨ r = 160020 ∨ r = 160021 ∨
      r = 160022 ∨ r = 160026 ∨ r = 160033) → c5.nreg r = c2.nreg r := fun r hr =>
    c52 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by rw [hAl]; omega)
  refine ⟨c5, k1 + (k2 + (k3 + (k4 + k5))), .seq e1 (.seq e2 (.seq e3 (.seq e4 e5))), by omega,
    by omega, hw5, h5A, hhost, fun x hx => by rw [hm54 x (Or.inl hx), hm4, hm3, hm2],
    by rw [hrr5, hrr4, hrr3, hrr2, hrr1], by rw [hrm5, hrm4, hrm3, hrm2, hrm1],
    by rw [ho5, ho4, ho3, ho2, ho1], fun r hr hra => ?_, ?_, by rw [p52 _ (by decide)]; exact p10,
    by rw [p52 _ (by decide)]; exact p11, by rw [p52 _ (by decide)]; exact p14, h515,
    by rw [p52 _ (by decide)]; exact p20, by rw [p52 _ (by decide), p21, hS],
    by rw [p52 _ (by decide)]; exact p22,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q24,
    by rw [p52 _ (by decide)]; exact p26, h527,
    by rw [fr5 _ (by decide) (by decide) (by decide) (by decide) (by rw [hAl]; decide)]; exact s32,
    by rw [p52 _ (by decide)]; exact p33,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q80,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q81,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q82,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q83,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q84,
    by rw [c5c _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact q87⟩
  · rw [fr5 r (by omega) (by omega) (by omega) (by omega) hra,
      c41 r (by unfold ProRG; omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact fr1 r (by omega)
  · rw [c52 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by rw [hAl]; decide),
      c2r _ (by unfold ProRG; decide), fr1 _ (Or.inl (by decide))]
    exact r0

end proofs

end

end Chazelle.Core.L41
