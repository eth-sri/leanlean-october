module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Of

/-!
# WP-J up phase, part 1: the halving table

`halfS`: at the allocator `D`, write `m (D + x) = x / 2` for `x ≤ n + 1` (two cells per step,
the allocator bumped by two per step, so its growth stays below the step count) (`halfS_exec`).

Registers (band `bUp = 17`): `170001` `n`, `170003` the base `D`, `170040` the index `t`,
`170041` the half `y`, `170042` the bound `n + 1`, `170043` scratch; constants `170020 = 1`,
`170021 = 2`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- One step: two cells `D + t`, `D + t + 1` hold `y`. -/
def halfBody : Stmt := block [.addN 170043 170003 170040, .storeN 170043 170041,
  .addN 170043 170043 170020, .storeN 170043 170041, .addN 170040 170040 170021,
  .addN 170041 170041 170020, .addN 9999 9999 170021]

/-- **The halving table.** -/
def halfS : Stmt := .seq (block [.copyN 170003 9999, .constN 170040 0, .constN 170041 0,
  .addN 170042 170001 170020]) (.whileLtN 170040 170042 halfBody)

/-- The registers written by `halfS` (besides the allocator). -/
def HalfRG (r : ℕ) : Prop := r = 170003 ∨ (170040 ≤ r ∧ r ≤ 170043)

/-- The registers written by `halfBody` (besides the allocator). -/
def HalfBRG (r : ℕ) : Prop := r = 170040 ∨ r = 170041 ∨ r = 170043

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem halfBody_exec {c : Config} (hw : WordsBounded W c) {D t y Al : ℕ}
    (h03 : c.nreg 170003 = D) (h40 : c.nreg 170040 = t) (h41 : c.nreg 170041 = y)
    (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (hW : D + t + 2 ≤ W) (hWy : y + 1 ≤ W) (hWA : Al + 2 ≤ W) :
    ∃ c' k, Exec P W halfBody c c' k ∧ k = 7 ∧ WordsBounded W c' ∧
      c'.nreg 170040 = t + 2 ∧ c'.nreg 170041 = y + 1 ∧ c'.nreg ALLOC = Al + 2 ∧
      c'.nmem (D + t) = y ∧ c'.nmem (D + t + 1) = y ∧
      (∀ a, a ≠ D + t → a ≠ D + t + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ HalfBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold halfBody
  exec_block
  all_goals try (config_simp; (try simp only [h03, h40, h41, hA, h20, h21]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h40, h21]
  · config_simp; simp only [h41, h20]
  · config_simp; simp only [hA, h21]
  · config_simp; simp only [h03, h40, h41, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h03, h40, h41, h20, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h03, h40, h20, Machine.upd_apply]; split_ifs <;> first | omega
  · unfold HalfBRG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (⋄)])

set_option maxHeartbeats 16000000 in
/-- **The halving table on the RAM.** -/
theorem halfS_exec {c : Config} (hw : WordsBounded W c) {n D : ℕ}
    (hA : c.nreg ALLOC = D) (h01 : c.nreg 170001 = n) (h20 : c.nreg 170020 = 1)
    (h21 : c.nreg 170021 = 2) (hW : D + n + 4 ≤ W) :
    ∃ c' k, Exec P W halfS c c' k ∧ k ≤ 9 * n + 24 ∧ WordsBounded W c' ∧
      c'.nreg 170003 = D ∧ D + n + 1 ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ D + n + 3 ∧
      c'.nreg ALLOC ≤ D + k ∧
      (∀ x, x ≤ n → c'.nmem (D + x) = x / 2) ∧
      (∀ a, a < D → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ HalfRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i03, i40, i41, i42, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 170003 9999, .constN 170040 0, .constN 170041 0, .addN 170042 170001 170020])
      c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 170003 = D ∧ c1.nreg 170040 = 0 ∧
      c1.nreg 170041 = 0 ∧ c1.nreg 170042 = n + 1 ∧ (∀ r, ¬ HalfRG r → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h01, h20]); omega)
    refine ⟨rfl, ‹_›, by config_simp; rw [← hAl, hA], by config_simp, by config_simp,
      by config_simp; simp only [h01, h20], fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold HalfRG at hr
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have r1 := fr1
  let I := fun c' => WordsBounded W c' ∧ ∃ k, 2 * k ≤ n + 2 ∧
    c'.nreg 170040 = 2 * k ∧ c'.nreg 170041 = k ∧ c'.nreg 170042 = n + 1 ∧
    c'.nreg 170003 = D ∧ c'.nreg ALLOC = D + 2 * k ∧
    (∀ x, x < 2 * k → c'.nmem (D + x) = x / 2) ∧ (∀ a, a < D → c'.nmem a = c.nmem a) ∧
    (∀ r, ¬ HalfRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨hw', t, ht, h40', h41', h42', h03', hA', hent, hlow, fr', hrr', hrm', ho'⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170040) (b := 170042) (body := halfBody) I
      (fun c' => 9 * (n + 2 - c'.nreg 170040)) (fun c' => c'.nreg ALLOC) (fun c' h => h.1)
      (fun c2 ⟨hw2, t, ht, h40, h41, h42, h03, hA2, hent, hlow, fr2, hrr2, hrm2, ho2⟩ htest => by
        rw [h40, h42] at htest
        have g := fr2
        obtain ⟨c3, k3, e3, hk3, hw3, q40, q41, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          halfBody_exec (P := P) hw2 h03 h40 h41 hA2
            (by rw [g _ (by unfold HalfRG; omega) (by rw [hAl]; omega)]; exact h20)
            (by rw [g _ (by unfold HalfRG; omega) (by rw [hAl]; omega)]; exact h21)
            (by omega) (by omega) (by omega)
        refine ⟨c3, k3, e3, ⟨hw3, t + 1, by omega, by rw [q40]; ring, q41,
          by rw [fr3 170042 (by unfold HalfBRG; omega) (by rw [hAl]; omega)]; exact h42,
          by rw [fr3 170003 (by unfold HalfBRG; omega) (by rw [hAl]; omega)]; exact h03,
          by rw [qA]; ring, fun x hx => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by rw [hrr3, hrr2], by rw [hrm3, hrm2], by rw [ho3, ho2]⟩, ?_, ?_⟩
        · rcases Nat.lt_or_ge x (2 * t) with h1 | h1
          · rw [qm _ (by omega) (by omega)]; exact hent x h1
          · rcases Nat.lt_or_ge x (2 * t + 1) with h2 | h2
            · have hx2 : x = 2 * t := by omega
              subst hx2; rw [qm0]; omega
            · have hx2 : x = 2 * t + 1 := by omega
              subst hx2; rw [show D + (2 * t + 1) = D + 2 * t + 1 by ring, qm1]; omega
        · rw [qm _ (by omega) (by omega)]; exact hlow a ha
        · rw [fr3 r (by unfold HalfBRG; unfold HalfRG at h1; omega) h2]; exact fr2 r h1 h2
        · show 9 * (n + 2 - c3.nreg 170040) + k3 + 2 ≤ 9 * (n + 2 - c2.nreg 170040)
          rw [q40, h40]; omega
        · show c3.nreg ALLOC ≤ c2.nreg ALLOC + k3
          rw [qA]; omega)
      ⟨hw1, 0, by omega, i40, i41, i42, i03,
        by rw [r1 _ (by unfold HalfRG; rw [hAl]; omega), hA]; ring,
        fun x hx => by omega, fun a _ => by rw [hm1], fun r h1 _ => r1 r h1, hrr1, hrm1, ho1⟩
  rw [h40', h42'] at htest
  have hk' : k ≤ 9 * (n + 2) + 2 := by
    have := hk; simp only [i40, Nat.sub_zero] at this; exact this
  have hψ' := hψ
  have hA1 : c1.nreg ALLOC = D := by rw [r1 _ (by unfold HalfRG; rw [hAl]; omega)]; exact hA
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', h03', by omega, by omega, by omega,
    fun x hx => hent x (by omega), hlow, fr', hrr', hrm', ho'⟩
  · -- the loop runs `⌈(n+1)/2⌉` times; the potential bound suffices
    omega

end proofs

end

end Chazelle.Core.Up
