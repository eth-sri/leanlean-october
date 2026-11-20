module

public import Chazelle.Core.UpPhase10

/-!
# WP-J up phase, part 11: the descriptor of a chain from the grade record

`descU_exec`: both cases of `descU` (grade `0`, and the children of grade `g - 1` read from the
record `UpTab`) with a uniform result and the frame `Kept`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey

@[expose] public section

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

/-- The children of chain `i` of grade `g ≥ 1` exist. -/
theorem two_mul_lt_gradeCount {n g i : ℕ} (hg : 1 ≤ g) (hi : i < gradeCount n g) :
    2 * i < gradeCount n (g - 1) := by
  have e := gradeCount_succ n (g - 1)
  rw [show g - 1 + 1 = g by omega] at e
  obtain ⟨Q, hQ⟩ : ∃ Q, (n - 2) / 2 ^ (g - 1) = Q := ⟨_, rfl⟩
  rw [hQ] at e
  unfold gradeCount; rw [hQ]; omega

theorem Kept.not_d0 {r : ℕ} (h : Kept r) : ¬ D0RG r := by
  have := h.range; unfold D0RG; omega

theorem Kept.not_desc {r : ℕ} (h : Kept r) : ¬ DescRG r := by
  have := h.range; unfold DescRG; omega

theorem Kept.bk {r : ℕ} (h : Kept r) : Bk r = false := by
  have := h.range; unfold Bk; simp only [decide_eq_false_iff_not]; omega

theorem Kept.not_brute {r : ℕ} (h : Kept r) : bandOf r ≠ bBrute := by
  have := h.range; unfold bandOf bBrute; omega

theorem outB_bk {r : ℕ} (h : OutB (bandOf r)) : Bk r = false := by
  unfold OutB bandOf at h; unfold Bk; simp only [decide_eq_false_iff_not]; omega

set_option maxHeartbeats 16000000 in
/-- **The descriptor of chain `(g, i)`** from the grade record. -/
theorem descU_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R A γ : ℕ}
    (hu : URegs c P.n hp h g (gradeCount P.n g) γ (gradeCount P.n (g - 1)) R)
    (hA : c.nreg ALLOC = A) (h16 : c.nreg 170016 = gradeStart g i)
    (h35 : c.nreg 170035 = 6 * i) (h36 : c.nreg 170036 = 2 * i + 1)
    (hi : i < gradeCount P.n g) (hT : UpTab O P c.nmem h hp A) (hmh : c.nmem h = g)
    (hR : 1 ≤ g → c.nmem (c.nmem (h + 2) + (g - 1)) = R) (hW : A + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 1902 ∧ WordsBounded W c' ∧
      A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + 5 ∧ c'.nreg 170030 + 5 ≤ c'.nreg ALLOC ∧
      c'.nmem (c'.nreg 170030) = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ChainDescAt c'.nmem (c'.nreg 170030) (Qof P) (Host.whole P.n) C) ∧
      (∀ a, a < A → c'.nmem a = c.nmem a) ∧
      (∀ r, Kept r → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨-, -, -, hH, hhp, -, -, hrow, hE⟩ := hT
  rcases Nat.eq_zero_or_pos g with hg0 | hg1
  · subst hg0
    have hfit := gradeLen_fit (g := 0) hn hi
    have hl1 : gradeLen P.n 0 i = 1 := by
      have := gradeLen_pos (g := 0) hn hi; have := gradeLen_le P.n 0 i; simp at this; omega
    unfold gradeStart at h16 hfit; simp only [pow_zero, Nat.mul_one] at h16 hfit
    obtain ⟨c', k, e, hk, hw', hA', o30, w0, hdesc, hm, fr, frr, hrm, ho⟩ :=
      descU_exec0 (P := P) hG hWn hw hu.r07 hu.r20 hA hu.r04 h16 hu.r01 hu.r23 (by omega)
        hH (by omega) hW hW8
    refine ⟨c', k, e, hk, hw', by omega, by omega, by omega, by rw [o30]; exact w0,
      fun C h1 h2 h3 => by rw [o30]; exact hdesc C h1 h2 h3,
      fun a ha => hm a (Or.inl ha), fun r hr => fr r hr.not_d0 (by
        rintro rfl; have := hr.range; omega) hr.not_brute hr.bk hr.ne_alloc,
      fun r hr => frr r (outB_bk hr) (by unfold OutB at hr; unfold bUp; omega)
        (by unfold OutB at hr; unfold bBrute; omega), hrm, ho⟩
  · have hR' := hR hg1
    have h2i := two_mul_lt_gradeCount hg1 hi
    have hgm : g - 1 < c.nmem h := by omega
    have hrw := hrow (g - 1) hgm
    rw [hR'] at hrw
    obtain ⟨hNL, -⟩ := hE (g - 1) (2 * i) hgm h2i
    have e6 : ∀ x, x + 3 * (2 * i) = x + 6 * i := fun x => by ring
    simp only [rowE, hR', e6] at hNL
    have hL : ∀ C : Chain, C.P = Qof P → C.s = gradeStart (g - 1) (2 * i) →
        C.m = gradeLen P.n (g - 1) (2 * i) →
        ChainDescAt c.nmem (c.nmem (R + 6 * i)) (Qof P) (Host.whole P.n) C :=
      fun C a b d => (hNL C a b d).1
    obtain ⟨CL, hCLP, hCLs, hCLm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart (g - 1) (2 * i) ∧ C.m = gradeLen P.n (g - 1) (2 * i) :=
      ⟨gChain P (g - 1) (2 * i) hn h2i, rfl, rfl, rfl⟩
    obtain ⟨-, -, hLh, hL5, -⟩ := hNL CL hCLP hCLs hCLm
    have hRc : 2 * i + 1 < gradeCount P.n (g - 1) → ∀ C : Chain, C.P = Qof P →
        C.s = gradeStart (g - 1) (2 * i + 1) → C.m = gradeLen P.n (g - 1) (2 * i + 1) →
        NodeOK P c.nmem A hp (c.nmem (R + 6 * i + 3)) (c.nmem (R + 6 * i + 3 + 1)) C
          (gradeGran (g - 1)) := fun h2 C a b d => by
      obtain ⟨hNR, -⟩ := hE (g - 1) (2 * i + 1) hgm h2
      have e6 : ∀ x, x + 3 * (2 * i + 1) = x + 6 * i + 3 := fun x => by ring
      simp only [rowE, hR', e6] at hNR
      exact hNR C a b d
    obtain ⟨c', k, e, hk, hw', hA1, hA2, o30, w0, hdesc, hm, fr, frr, hrm, ho⟩ :=
      descU_execG (P := P) (TD := A) (hp := hp) hG hWn hw hu.r07 hg1 hu.r20 hA hu.r14 h35 h36
        hu.r12 hu.r22 hu.r23 rfl hi hn hL hLh hL5
        (fun h2 C a b d => (hRc h2 C a b d).1)
        (fun h2 => by
          obtain ⟨CR, e1, e2, e3⟩ : ∃ C : Chain, C.P = Qof P ∧
              C.s = gradeStart (g - 1) (2 * i + 1) ∧ C.m = gradeLen P.n (g - 1) (2 * i + 1) :=
            ⟨gChain P (g - 1) (2 * i + 1) hn h2, rfl, rfl, rfl⟩
          exact (hRc h2 CR e1 e2 e3).2.2.1)
        (fun h2 => by
          obtain ⟨CR, e1, e2, e3⟩ : ∃ C : Chain, C.P = Qof P ∧
              C.s = gradeStart (g - 1) (2 * i + 1) ∧ C.m = gradeLen P.n (g - 1) (2 * i + 1) :=
            ⟨gChain P (g - 1) (2 * i + 1) hn h2, rfl, rfl, rfl⟩
          exact (hRc h2 CR e1 e2 e3).2.2.2.1)
        (by omega) hW (by omega)
    refine ⟨c', k, e, by omega, hw', hA1, hA2, o30, w0, hdesc, hm,
      fun r hr => fr r hr.not_desc hr.bk ?_ ?_ ?_ ?_ ?_ ?_ hr.ne_alloc,
      fun r hr => frr r (outB_bk hr) (by rintro rfl; unfold OutB bandOf at hr; omega), hrm,
      ho⟩ <;>
      (rintro rfl; have := hr.range; omega)

end proofs

end

end Chazelle.Core.Up
