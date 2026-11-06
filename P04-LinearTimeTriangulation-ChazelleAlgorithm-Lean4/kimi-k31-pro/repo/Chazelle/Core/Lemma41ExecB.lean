module

public import Chazelle.Core.Lemma41ExecA
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 16000000

/-!
# WP-J, part 26b: the leaves of Lemma 4.1, executed

`l41B_exec`: after the prologue, the cover loop, the base register and the level array of the
leaves (`l41B`) produce the first level of the merge tree (`LevelAt` of `leafShp`).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle Chazelle.Merge

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

/-- **The leaves on the RAM.** -/
theorem l41B_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {c c5 : Config} (hw5 : WordsBounded W c5) {A h a L lam : ℕ}
    (hR : Robust A c.nmem fun m' => GradeRaw O P m' h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ (lam - 1) < L) (hL2 : L ≤ 2 ^ lam)
    (m5c : ∀ x, x < A → c5.nmem x = c.nmem x) (hhost : HostAt c5.nmem A (Host.whole P.n))
    (h5A : c5.nreg ALLOC = A + 7) (s10 : c5.nreg 160010 = a) (s11 : c5.nreg 160011 = a + L)
    (s14 : c5.nreg 160014 = 0) (s15 : c5.nreg 160015 = A + 7)
    (s20 : c5.nreg 160020 = c.nmem (h + 3)) (s21 : c5.nreg 160021 = c.nmem (h + 1) + 2)
    (s22 : c5.nreg 160022 = c.nmem (h + 2)) (s24 : c5.nreg 160024 = 1)
    (s26 : c5.nreg 160026 = lam) (s27 : c5.nreg 160027 = A) (s81 : c5.nreg 160081 = 5)
    (s82 : c5.nreg 160082 = 6) (s87 : c5.nreg 160087 = 8)
    (hbud : A + 40 * lam ^ 2 + 160 * lam + 11 * (cover lam (a + L) a).length + 30 ≤ W) :
    ∃ c8 k, Exec P W l41B c5 c8 k ∧
      k ≤ 40 * lam ^ 2 + 160 * lam + 11 * (cover lam (a + L) a).length + 10 ∧
      WordsBounded W c8 ∧ c8.nreg ALLOC = A + 7 + 8 * (cover lam (a + L) a).length ∧
      c8.nreg ALLOC ≤ A + 7 + k ∧
      LevelAt P c8.nmem (A + 7 + 8 * (cover lam (a + L) a).length)
        (A + 7 + 6 * (cover lam (a + L) a).length) A (leafShp lam (a + L) a) ∧
      (∀ x, x < A → c8.nmem x = c.nmem x) ∧
      c8.nreg 160014 = (cover lam (a + L) a).length ∧
      c8.nreg 160066 = A + 7 + 6 * (cover lam (a + L) a).length ∧
      (∀ r, ¬ CovRG r → ¬ L0RG r → r ≠ 160066 → r ≠ ALLOC → c8.nreg r = c5.nreg r) ∧
      c8.rreg = c5.rreg ∧ c8.rmem = c5.rmem ∧ c8.output = c5.output := by
  have hAl : ALLOC = 9999 := rfl
  have hn3 : 3 ≤ P.n := hG.1.1
  have hWn' : 128 * P.n + 3 ≤ W := by ufo hostWords at hWh
  have hRaw := hR.holds
  have hΛ : 1 ≤ c.nmem h := by omega
  obtain ⟨t0, t1, t2, t3, tS0, tS1, tS1lt, tpow, thalf, tent⟩ := tab_lt hR (by omega) hΛ
  obtain ⟨S, hS⟩ : ∃ S, c.nmem (h + 1) = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, c.nmem (h + 2) = T := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, c.nmem (h + 3) = D := ⟨_, rfl⟩
  rw [hS] at tS0 tS1 tS1lt tpow s21
  rw [hD] at thalf s20
  rw [hT] at tent s22
  have hltg : lam ≤ topGrade P.n + 1 := by have := hRaw.1; omega
  have hpl : 2 ^ lam = 2 * 2 ^ (lam - 1) := by rw [← pow_succ']; congr 1; omega
  have hj2l : (cover lam (a + L) a).length ≤ 2 * lam := cover_length_le (by omega) (by omega)
  have hsq : 40 * lam ^ 2 + 160 * lam = (20 * lam + 80) * (2 * lam) := by ring
  -- 6. the cover
  have hCR : CovRegs c5 lam (a + L) D (S + 2) T A := ⟨s11, s26, s24, s20, s21, s22, s27⟩
  have hent5 : ∀ g, g ≤ lam - 1 → ∀ i, (i + 1) * 2 ^ g ≤ a + L →
      c5.nmem (T + g) + 3 * i + 1 < A + 7 ∧ c5.nmem (c5.nmem (T + g) + 3 * i) + 4 < A + 7 := by
    intro g hg i hi
    have hgΛ : g < c.nmem h := by omega
    have hpos : 0 < 2 ^ g := by positivity
    have hic : i < gradeCount P.n g := by
      unfold gradeCount
      have : i * 2 ^ g ≤ P.n - 2 := by
        have := Nat.one_le_two_pow (n := g)
        have e : (i + 1) * 2 ^ g = i * 2 ^ g + 2 ^ g := by ring
        omega
      have := (Nat.le_div_iff_mul_le hpos).mpr this
      omega
    obtain ⟨eT, eO, -, -⟩ := tent g i hgΛ hic
    obtain ⟨-, -, -, -, hwf, -⟩ := hRaw.2.2.2 g i hgΛ hic
    rw [hT] at hwf
    have := hwf.1
    rw [m5c _ eT, m5c _ (by omega)]
    omega
  have hCT : CovTab c5.nmem lam (a + L) D (S + 2) T (A + 7) W :=
    ⟨fun y hy => by rw [m5c _ (thalf y (by omega)).2]; exact (thalf y (by omega)).1,
      fun i hi => by
        rw [m5c _ (tpow i (by omega)).2.2.1]
        exact (tpow i (by omega)).1,
      by have := (thalf (a + L) (by omega)).2; omega,
      by have := (tpow lam hltg).2.2.1; omega,
      by have := (tent (lam - 1) 0 (by omega) (Nat.succ_pos _)).1; omega, hent5,
      by omega, by nlinarith⟩
  obtain ⟨c6, k6, e6, hk6, hw6, h614, h615, hrec, hm65, fr6, hrr6, hrm6, ho6⟩ :=
    coverS_exec (P := P) hw5 hCR hCT (by omega) s10 (by omega) (by omega) s14 s15
  set j := (cover lam (a + L) a).length with hj
  -- 7. the base of the leaves
  obtain ⟨c7, k7, e7, hk7, hw7, b66, fr7, hm7, hrr7, hrm7, ho7⟩ := baseB_exec (P := P) hw6
  have c75 : ∀ r, r ≠ 160066 → ¬ CovRG r → c7.nreg r = c5.nreg r := fun r a1 a2 => by
    rw [fr7 r a1, fr6 r a2]
  have c7A : c7.nreg ALLOC = A + 7 := by
    rw [c75 _ (by rwd [hAl]) (by rw [hAl]; ufd CovRG AscRG)]; exact h5A
  -- 8. the level array of the leaves
  obtain ⟨c8, k8, e8, hk8, hw8, h8A, h8Ak, hent8, hm87, fr8, hrr8, hrm8, ho8⟩ :=
    l0S_exec (P := P) hw7 c7A (by rwx [fr7 _ (by decide)])
      (by rwx [fr7 _ (by decide)])
      (by rwx [c75 _ (by decide) (by ufd CovRG AscRG)])
      (by rwx [c75 _ (by decide) (by ufd CovRG AscRG)])
      (by rwx [c75 _ (by decide) (by ufd CovRG AscRG)])
      (by rwx [c75 _ (by decide) (by ufd CovRG AscRG)])
      (by nlinarith)
  have m65 : ∀ x, x < A + 7 → c6.nmem x = c5.nmem x := fun x hx => hm65 x (Or.inl hx)
  have m86 : ∀ x, x < A + 7 + 6 * j → c8.nmem x = c6.nmem x := fun x hx => by
    rw [hm87 x (Or.inl hx), hm7]
  have hLev : LevelAt P c8.nmem (A + 7 + 8 * j) (A + 7 + 6 * j) A (leafShp lam (a + L) a) :=
    leaves_levelAt hR (by omega) hlΛ (by omega) (by omega) (by omega)
      (m5c) hhost (by rwx [hT]) m65
      (fun k hk => by
        obtain ⟨u1, u2⟩ := hent8 k hk
        exact ⟨u1, by rw [u2, hm7]⟩)
      m86
  refine ⟨c8, k6 + (k7 + k8), .seq e6 (.seq e7 e8), by nlinarith, hw8, h8A, by omega, hLev,
    fun x hx => by rw [m86 x (by omega), m65 x (by omega), m5c x hx], ?_, ?_,
    fun r a1 a2 a3 a4 => by rw [fr8 r a2 a4]; exact c75 r a3 a1, by rw [hrr8, hrr7, hrr6],
    by rw [hrm8, hrm7, hrm6], by rw [ho8, ho7, ho6]⟩
  · rw [fr8 _ (by ufd L0RG) (by rwd [hAl]), fr7 _ (by decide)]; exact h614
  · rw [fr8 _ (by ufd L0RG) (by rwd [hAl]), b66]; exact h615

end proofs

end

end Chazelle.Core.L41
