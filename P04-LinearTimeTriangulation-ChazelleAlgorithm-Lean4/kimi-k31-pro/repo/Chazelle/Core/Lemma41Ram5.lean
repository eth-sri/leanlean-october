module

public import Chazelle.Core.Lemma41Merge
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 8000000

/-!
# WP-J, part 12: the level array of the leaves

`l0S`: for the `j` cover records at `R₀ = ALLOC` (six words each), write the level array `L₀` at
`B₀ = R₀ + 6j` (register `160015` after the cover loop): entry `k` is `[R₀ + 6k, NF of record k]`
(two words).  The allocator is bumped by `8` per entry, so that it ends at `R₀ + 8j`, just above
the records and `L₀`, and it never grows faster than the step count (`l0S_exec`).

Also `whileLtN_potential_lb'`: the loop rule with a potential and a growth bound.

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

/-- The loop rule with a potential and a growth bound `ψ c' ≤ ψ c + k`. -/
theorem whileLtN_potential_lb' {a b : ℕ} {body : Stmt}
    (I : Config → Prop) (Φ ψ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c ∧ ψ c' ≤ ψ c + k)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 ∧ ψ c' ≤ ψ c + k := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ, hψ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂, hψ'⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega, by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega, by omega⟩

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
  · config_simp; simp only [h70, h24]
  · config_simp; simp only [h71, h82]
  · config_simp; simp only [h72, h24]
  · config_simp; simp only [hA, h87]
  · config_simp; simp only [h71, h72, h24, h81, Machine.upd_apply]; splao
  · config_simp; simp only [h71, h72, h24, h81, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [h72, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · unfold L0RG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

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
    exec_block
    all_goals try omega
    refine ⟨rfl, ‹_›, by config_simp, by config_simp; rw [← hAl, hA], by config_simp; exact h15,
      fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold L0RG at hr
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])
  have r1 : ∀ r, ¬ L0RG r → c1.nreg r = c.nreg r := fr1
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 160070 = i ∧
    c'.nreg ALLOC = R0 + 8 * i ∧ c'.nreg 160071 = R0 + 6 * i ∧ c'.nreg 160072 = B0 + 2 * i ∧
    (∀ k, k < i → c'.nmem (B0 + 2 * k) = R0 + 6 * k ∧
      c'.nmem (B0 + 2 * k + 1) = c.nmem (R0 + 6 * k + 5)) ∧
    (∀ a, (a < B0 ∨ B0 + 2 * i ≤ a) → c'.nmem a = c.nmem a) ∧
    (∀ r, ¬ L0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨i, ⟨hw', h70', hA', h71', h72', hent, hout, fr', hrr', hrm', ho'⟩, hij⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 160070) (b := 160014) (body := l0Body)
      (fun c' => ∃ i, I i c' ∧ i ≤ j) (fun c' => 11 * (j - c'.nreg 160070))
      (fun c' => c'.nreg ALLOC) (fun c' ⟨i, h, _⟩ => h.1)
      (fun c2 ⟨i, ⟨hw2, h70, hA2, h71, h72, hent, hout, fr2, hrr2, hrm2, ho2⟩, hij⟩ htest => by
        have g : ∀ r, ¬ L0RG r → r ≠ ALLOC → c2.nreg r = c.nreg r := fr2
        have c14 : c2.nreg 160014 = j := by
          rw [g _ (by ufo L0RG) (by rwo [hAl])]; exact h14
        rw [h70, c14] at htest
        obtain ⟨c3, k3, e3, hk3, hw3, q70, q71, q72, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          l0Body_exec (P := P) hw2 h70 h71 h72 hA2
            (by rw [g _ (by ufo L0RG) (by rwo [hAl])]; exact h24)
            (by rw [g _ (by ufo L0RG) (by rwo [hAl])]; exact h81)
            (by rw [g _ (by ufo L0RG) (by rwo [hAl])]; exact h82)
            (by rw [g _ (by ufo L0RG) (by rwo [hAl])]; exact h87)
            (by omega) (by omega) (by omega) (by omega) (by omega)
        have hrec : c2.nmem (R0 + 6 * i + 5) = c.nmem (R0 + 6 * i + 5) :=
          hout _ (Or.inl (by omega))
        refine ⟨c3, k3, e3, ⟨i + 1, ⟨hw3, q70, by rwring [qA], by rwring [q71],
          by rwring [q72], fun k hk => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by rw [hrr3, hrr2], by rw [hrm3, hrm2], by rw [ho3, ho2]⟩, by omega⟩, ?_, ?_⟩
        · rcases Nat.lt_or_ge k i with hki | hki
          · rw [qm _ (by omega) (by omega), qm _ (by omega) (by omega)]; exact hent k hki
          · have : k = i := by omega
            subst this
            exact ⟨qm0, by rw [qm1, hrec]⟩
        · rw [qm _ (by omega) (by omega)]; exact hout a (by omega)
        · rw [fr3 r h1 h2]; exact fr2 r h1 h2
        · show 11 * (j - c3.nreg 160070) + k3 + 2 ≤ 11 * (j - c2.nreg 160070)
          rwo [q70, h70]
        · show c3.nreg ALLOC ≤ c2.nreg ALLOC + k3
          rwo [qA])
      ⟨0, ⟨hw1, h70, by rw [r1 _ (by uro L0RG [hAl]), hA]; ring,
        by rwring [h71], by rwring [h72], fun k hk => by omega, fun a _ => by rw [hm1],
        fun r h1 _ => r1 r h1, hrr1, hrm1, ho1⟩, Nat.zero_le _⟩
  have c14 : c'.nreg 160014 = j := by
    rw [fr' _ (by ufo L0RG) (by rwo [hAl])]; exact h14
  have hij' : i = j := by rwo [h70', c14] at htest
  subst hij'
  have hk' : k ≤ 11 * i + 2 := by
    have := hk; simp only [h70, Nat.sub_zero] at this; exact this
  have hψ' : c'.nreg ALLOC ≤ c1.nreg ALLOC + k := hψ
  have hA1 : c1.nreg ALLOC = R0 := by rw [r1 _ (by uro L0RG [hAl])]; exact hA
  exact ⟨c', k1 + k, .seq e1 e, by omega, hw', hA', by omega, hent,
    fun a ha => hout a (by omega), fr', hrr', hrm', ho'⟩

end proofs

end

end Chazelle.Core.L41
