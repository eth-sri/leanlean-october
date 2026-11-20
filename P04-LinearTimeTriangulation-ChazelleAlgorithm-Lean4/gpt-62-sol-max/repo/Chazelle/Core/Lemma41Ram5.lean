module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.Lemma41Ram4

/-!
# WP-J, part 12: the level array of the leaves

`l0S`: for the `j` cover records at `R₀ = ALLOC` (six words each), write the level array `L₀` at
`B₀ = R₀ + 6j` (register `160015` after the cover loop): entry `k` is `[R₀ + 6k, NF of record k]`
(two words).  The allocator is bumped by `8` per entry, so that it ends at `R₀ + 8j`, just above
the records and `L₀`, and it never grows faster than the step count (`l0S_exec`).


Registers: `160070` counter, `160071` record pointer, `160072` entry pointer, `160073` scratch,
`160014` the count `j`, constants `160024 = 1`, `160081 = 5`, `160082 = 6`, `160087 = 8`.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs

@[expose] public section

/-- One entry of `L₀`. -/
def l0Body : Stmt := block [.storeN 160072 160071, .addN 160073 160071 160081,
  .loadN 160073 160073, .addN 160072 160072 160024, .storeN 160072 160073,
  .addN 160072 160072 160024, .addN 160071 160071 160082, .addN 9999 9999 160087,
  .addN 160070 160070 160024]

/-- **The level array of the leaves.** -/
def l0S : Stmt := .seq (block [.constN 160070 0, .copyN 160071 9999, .copyN 160072 160015])
  (.whileLtN 160070 160014 l0Body)

/-- The registers written by `l0S` (besides the allocator). -/
def L0RG (r : ℕ) : Prop := 160070 ≤ r ∧ r ≤ 160073

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem l0Body_exec {c : Config} (hw : WordsBounded W c) {i p q Al : ℕ}
    (h70 : c.nreg 160070 = i) (h71 : c.nreg 160071 = p) (h72 : c.nreg 160072 = q)
    (hA : c.nreg ALLOC = Al) (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5)
    (h82 : c.nreg 160082 = 6) (h87 : c.nreg 160087 = 8)
    (hW : q + 2 ≤ W) (hWp : p + 6 ≤ W) (hWA : Al + 8 ≤ W) (hWi : i + 1 ≤ W) (hpq : p + 5 < q) :
    ∃ c' k, Exec P W l0Body c c' k ∧ k = 9 ∧ WordsBounded W c' ∧
      c'.nreg 160070 = i + 1 ∧ c'.nreg 160071 = p + 6 ∧ c'.nreg 160072 = q + 2 ∧
      c'.nreg ALLOC = Al + 8 ∧ c'.nmem q = p ∧ c'.nmem (q + 1) = c.nmem (p + 5) ∧
      (∀ a, a ≠ q → a ≠ q + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ L0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold l0Body
  exec_block
  all_goals try (config_simp; (try simp only [h70, h71, h72, hA, h24, h81, h82, h87]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · ram_finish
  · ram_finish
  · config_simp; simp only [h72, h24]
  · ram_finish
  · simp_all <;> omega
  · ram_finish
  · frame_finish
  · unfold L0RG at h1
    frame_finish

set_option maxHeartbeats 8000000 in
/-- **The level array of the leaves.** -/
theorem l0S_exec {c : Config} (hw : WordsBounded W c) {R0 j : ℕ}
    (hA : c.nreg ALLOC = R0) (h15 : c.nreg 160015 = R0 + 6 * j) (h14 : c.nreg 160014 = j)
    (h24 : c.nreg 160024 = 1) (h81 : c.nreg 160081 = 5) (h82 : c.nreg 160082 = 6)
    (h87 : c.nreg 160087 = 8) (hW : R0 + 8 * j + 8 ≤ W) :
    ∃ c' k, Exec P W l0S c c' k ∧ k ≤ 11 * j + 5 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = R0 + 8 * j ∧ c'.nreg ALLOC ≤ R0 + k ∧
      (∀ k, k < j → c'.nmem (R0 + 6 * j + 2 * k) = R0 + 6 * k ∧
        c'.nmem (R0 + 6 * j + 2 * k + 1) = c.nmem (R0 + 6 * k + 5)) ∧
      (∀ a, (a < R0 + 6 * j ∨ R0 + 8 * j ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ L0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  set B0 := R0 + 6 * j with hB0
  obtain ⟨c1, k1, e1, hk1, hw1, h70, h71, h72, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.constN 160070 0, .copyN 160071 9999, .copyN 160072 160015]) c c1 k1 ∧ k1 = 3 ∧
      WordsBounded W c1 ∧ c1.nreg 160070 = 0 ∧ c1.nreg 160071 = R0 ∧ c1.nreg 160072 = B0 ∧
      (∀ r, ¬ L0RG r → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧
      c1.rmem = c.rmem ∧ c1.output = c.output := by
    ram_exec [hA, L0RG, Machine.upd_other]
  have r1 := fr1
  let I := fun i c' => WordsBounded W c' ∧ c'.nreg 160070 = i ∧
    c'.nreg ALLOC = R0 + 8 * i ∧ c'.nreg 160071 = R0 + 6 * i ∧ c'.nreg 160072 = B0 + 2 * i ∧
    (∀ k, k < i → c'.nmem (B0 + 2 * k) = R0 + 6 * k ∧
      c'.nmem (B0 + 2 * k + 1) = c.nmem (R0 + 6 * k + 5)) ∧
    (∀ a, (a < B0 ∨ B0 + 2 * i ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, ¬ L0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨i, ⟨hw', h70', hA', h71', h72', hent, hout, fr', hrr', hrm', ho'⟩, hij⟩,
      htest, hk, hψ⟩ :=
    Exec.whileLtN_growth (P := P) (W := W) (a := 160070) (b := 160014) (body := l0Body)
      (fun c' => ∃ i, I i c' ∧ i ≤ j) (fun c' => 11 * (j - c'.nreg 160070))
      (fun c' => c'.nreg ALLOC) (fun c' ⟨i, h, _⟩ => h.1)
      (fun c2 ⟨i, ⟨hw2, h70, hA2, h71, h72, hent, hout, fr2, hrr2, hrm2, ho2⟩, hij⟩ htest => by
        have g := fr2
        have c14 : c2.nreg 160014 = j := by
          rwa [g _ (by unfold L0RG; omega) (by rw [hAl]; omega)]
        rw [h70, c14] at htest
        obtain ⟨c3, k3, e3, hk3, hw3, q70, q71, q72, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          l0Body_exec (P := P) hw2 h70 h71 h72 hA2
            (by rwa [g _ (by unfold L0RG; omega) (by rw [hAl]; omega)])
            (by rwa [g _ (by unfold L0RG; omega) (by rw [hAl]; omega)])
            (by rwa [g _ (by unfold L0RG; omega) (by rw [hAl]; omega)])
            (by rwa [g _ (by unfold L0RG; omega) (by rw [hAl]; omega)])
            (by omega) (by omega) (by omega) (by omega) (by omega)
        have hrec : c2.nmem (R0 + 6 * i + 5) = c.nmem (R0 + 6 * i + 5) :=
          hout _ (Or.inl (by omega))
        refine ⟨c3, k3, e3, ⟨i + 1, ⟨hw3, q70, by rw [qA]; ring, by rw [q71]; ring,
          by rw [q72]; ring, fun k hk => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by rw [hrr3, hrr2], by rw [hrm3, hrm2], by rw [ho3, ho2]⟩, by omega⟩, ?_, ?_⟩
        · rcases Nat.lt_or_ge k i with hki | hki
          · ram_rw [qm, qm]; exact hent k hki
          · have : k = i := by omega
            subst this
            exact ⟨qm0, by rw [qm1, hrec]⟩
        · ram_rw [qm]; exact hout a (by omega)
        · ram_finish
        · simp only [q70, h70] <;> omega
        · simp only [qA] <;> omega)
      ⟨0, ⟨hw1, h70, by rw [r1 _ (by unfold L0RG; rw [hAl]; omega), hA]; ring,
        by rw [h71]; ring, by rw [h72]; ring, fun k hk => by omega, fun a _ => by rw [hm1],
        fun r h1 _ => r1 r h1, hrr1, hrm1, ho1⟩, Nat.zero_le _⟩
  have c14 : c'.nreg 160014 = j := by
    rwa [fr' _ (by unfold L0RG; omega) (by rw [hAl]; omega)]
  have hij' : i = j := by rw [h70', c14] at htest; omega
  subst hij'
  have hk' : k ≤ 11 * i + 2 := by
    have := hk; simp only [h70, Nat.sub_zero] at this; exact this
  
  have hA1 : c1.nreg ALLOC = R0 := by rwa [r1 _ (by unfold L0RG; rw [hAl]; omega)]
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hA', by omega, hent,
    fun a ha => hout a (by omega), fr', hrr', hrm', ho'⟩

end proofs

end

end Chazelle.Core.L41
