module

public import Chazelle.Core.UpPhase9

/-!
# WP-J up phase, part 10: the registers of a grade and the cell of a chain

* `URegs`: the registers fixed during a grade; `Kept`: the registers a chain step keeps (the
  core band but the allocator; the grade registers of band `bUp`);
* `cellB`: the cell `[desc, NF, oracle, prev]` at the allocator, and the counters of the next
  chain (`cellB_exec`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- The bands outside the phase bands `1 … 24`. -/
def OutB (b : ℕ) : Prop := b = 0 ∨ 25 ≤ b

/-- The registers kept by the parts of a chain step (the chain counters `170015 … 170018`,
`170035`, `170036` included). -/
def Kept (r : ℕ) : Prop :=
  ((OutB (bandOf r) ∨ r = 230000) ∧ r ≠ ALLOC) ∨
    (bandOf r = bUp ∧ (r < 170030 ∨ (170035 ≤ r ∧ r ≤ 170037) ∨ 170080 ≤ r))

/-- **The registers fixed during grade `g`.** -/
structure URegs (c : Config) (n hp h g cnt γ cntP R : ℕ) : Prop where
  r01 : c.nreg 170001 = n
  r04 : c.nreg 170004 = hp
  r05 : c.nreg 170005 = h
  r07 : c.nreg 170007 = g
  r08 : c.nreg 170008 = cnt
  r10 : c.nreg 170010 = 2 ^ g
  r11 : c.nreg 170011 = γ
  r12 : c.nreg 170012 = cntP
  r14 : c.nreg 170014 = R
  r19 : c.nreg 170019 = 2 ^ (g - 1)
  r20 : c.nreg 170020 = 1
  r21 : c.nreg 170021 = 2
  r22 : c.nreg 170022 = 3
  r23 : c.nreg 170023 = 5
  r25 : c.nreg 170025 = 4
  r26 : c.nreg 170026 = 6
  r28 : c.nreg 170028 = n - 1
  r29 : c.nreg 170029 = 0
  r37 : c.nreg 170037 = 7

/-- The cell of a chain and the counters of the next chain. -/
def cellB : Stmt := block [.copyN 170034 9999, .storeN 170034 170030,
  .addN 170034 170034 170020, .storeN 170034 170031,
  .addN 170034 170034 170020, .storeN 170034 170032,
  .addN 170034 170034 170020, .storeN 170034 170018,
  .copyN 170018 9999, .addN 9999 9999 170025,
  .addN 170015 170015 170020, .addN 170016 170016 170010,
  .addN 170035 170035 170026, .addN 170036 170036 170021]

section proofs

variable {P : Polygon} {W : ℕ}

theorem kept_of {r : ℕ} (h : bandOf r = bUp)
    (h' : r < 170030 ∨ (170035 ≤ r ∧ r ≤ 170037) ∨ 170080 ≤ r) : Kept r :=
  Or.inr ⟨h, h'⟩

theorem Kept.ne_alloc {r : ℕ} (h : Kept r) : r ≠ ALLOC := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · intro e; rw [e] at h; revert h; decide

/-- A kept register is outside a set of phase bands without `bCore` and `bUp`. -/
theorem Kept.not_mem {r : ℕ} {B : Finset ℕ} (h : Kept r) (hsub : ∀ b ∈ B, 1 ≤ b ∧ b ≤ 24)
    (h23 : bCore ∉ B) (h17 : bUp ∉ B) : bandOf r ∉ B := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨h, -⟩
  · intro hm; have := hsub _ hm; unfold OutB at h1; omega
  · rwa [h1]
  · rwa [h]

/-- A register of an outside band is outside a set of phase bands. -/
theorem OutB.not_mem {r : ℕ} {B : Finset ℕ} (h : OutB (bandOf r))
    (hsub : ∀ b ∈ B, 1 ≤ b ∧ b ≤ 24) : bandOf r ∉ B := by
  intro hm; have := hsub _ hm; unfold OutB at h; omega

/-- A kept register is in one of the listed ranges. -/
theorem Kept.range {r : ℕ} (h : Kept r) :
    r < 10000 ∨ r = 230000 ∨ 250000 ≤ r ∨ (170000 ≤ r ∧ r < 170030) ∨
      (170035 ≤ r ∧ r ≤ 170037) ∨ (170080 ≤ r ∧ r < 180000) := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨h, h'⟩
  · unfold OutB bandOf at h1; omega
  · omega
  · unfold bandOf bUp at h; omega

/-- The registers of `URegs`. -/
def URegR (r : ℕ) : Prop := (170000 ≤ r ∧ r < 170015) ∨ (170019 ≤ r ∧ r < 170030) ∨ r = 170037

theorem URegR.kept {r : ℕ} (h : URegR r) : Kept r :=
  kept_of (by unfold URegR at h; unfold bandOf bUp; omega) (by unfold URegR at h; omega)

theorem URegs.of_frame {c c' : Config} {n hp h g cnt γ cntP R : ℕ}
    (hu : URegs c n hp h g cnt γ cntP R) (hk : ∀ r, URegR r → c'.nreg r = c.nreg r) :
    URegs c' n hp h g cnt γ cntP R := by
  have k : ∀ r, 170000 ≤ r → r < 170015 → c'.nreg r = c.nreg r := fun r a b =>
    hk r (Or.inl ⟨a, b⟩)
  have k' : ∀ r, 170019 ≤ r → r < 170030 → c'.nreg r = c.nreg r := fun r a b =>
    hk r (Or.inr (Or.inl ⟨a, b⟩))
  exact ⟨(k _ (by omega) (by omega)).trans hu.r01, (k _ (by omega) (by omega)).trans hu.r04,
    (k _ (by omega) (by omega)).trans hu.r05, (k _ (by omega) (by omega)).trans hu.r07,
    (k _ (by omega) (by omega)).trans hu.r08, (k _ (by omega) (by omega)).trans hu.r10,
    (k _ (by omega) (by omega)).trans hu.r11, (k _ (by omega) (by omega)).trans hu.r12,
    (k _ (by omega) (by omega)).trans hu.r14, (k' _ (by omega) (by omega)).trans hu.r19,
    (k' _ (by omega) (by omega)).trans hu.r20, (k' _ (by omega) (by omega)).trans hu.r21,
    (k' _ (by omega) (by omega)).trans hu.r22, (k' _ (by omega) (by omega)).trans hu.r23,
    (k' _ (by omega) (by omega)).trans hu.r25, (k' _ (by omega) (by omega)).trans hu.r26,
    (k' _ (by omega) (by omega)).trans hu.r28, (k' _ (by omega) (by omega)).trans hu.r29,
    (hk _ (Or.inr (Or.inr rfl))).trans hu.r37⟩

theorem URegs.of_kept {c c' : Config} {n hp h g cnt γ cntP R : ℕ}
    (hu : URegs c n hp h g cnt γ cntP R) (hk : ∀ r, Kept r → c'.nreg r = c.nreg r) :
    URegs c' n hp h g cnt γ cntP R :=
  hu.of_frame fun r hr => hk r hr.kept

/-- A chain is determined by its polygon, start and length. -/
theorem chain_eq {C C' : Chain} (h1 : C.P = C'.P) (h2 : C.s = C'.s) (h3 : C.m = C'.m) :
    C = C' := by
  cases C; cases C'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

set_option maxHeartbeats 16000000 in
/-- **The cell of a chain.** -/
theorem cellB_exec {c : Config} (hw : WordsBounded W c) {A d f o x i s pg q t : ℕ}
    (hA : c.nreg ALLOC = A) (h30 : c.nreg 170030 = d) (h31 : c.nreg 170031 = f)
    (h32 : c.nreg 170032 = o) (h18 : c.nreg 170018 = x) (h15 : c.nreg 170015 = i)
    (h16 : c.nreg 170016 = s) (h10 : c.nreg 170010 = pg) (h35 : c.nreg 170035 = q)
    (h36 : c.nreg 170036 = t) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (h25 : c.nreg 170025 = 4) (h26 : c.nreg 170026 = 6)
    (hWA : A + 4 ≤ W) (hWi : i + 1 ≤ W) (hWs : s + pg ≤ W) (hWq : q + 6 ≤ W) (hWt : t + 2 ≤ W) :
    ∃ c' k, Exec P W cellB c c' k ∧ k = 14 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 4 ∧ c'.nreg 170018 = A ∧ c'.nreg 170015 = i + 1 ∧
      c'.nreg 170016 = s + pg ∧ c'.nreg 170035 = q + 6 ∧ c'.nreg 170036 = t + 2 ∧
      c'.nmem A = d ∧ c'.nmem (A + 1) = f ∧ c'.nmem (A + 2) = o ∧ c'.nmem (A + 3) = x ∧
      (∀ a, (a < A ∨ A + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 170034 → r ≠ 170018 → r ≠ 170015 → r ≠ 170016 → r ≠ 170035 → r ≠ 170036 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold cellB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h30, h31, h32, h18, h15, h16, h10, h35, h36,
    h20, h21, h25, h26]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [hA, h25]
  · config_simp; simp only [hA]
  · config_simp; simp only [h15, h20]
  · config_simp; simp only [h16, h10]
  · config_simp; simp only [h35, h26]
  · config_simp; simp only [h36, h21]
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    split_ifs <;> first | omega
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    split_ifs <;> first | omega
  · simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

end proofs

end

end Chazelle.Core.Up
