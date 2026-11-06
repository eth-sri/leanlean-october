module

public import Chazelle.Golf

public import Chazelle.Core.UpPhase17

/-!
# WP-J up phase, part 18: one grade

`gradeB = chainsL; rowS; recA; copyL; recB; gamS` and `gradeB_exec`: from the grade invariant
`GradeInv` at grade `g ≤ p` to the invariant at grade `g + 1`, at cost `gradeC n g`.
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- **One grade.** -/
def gradeB (sB sL sG sP : Stmt) : Stmt :=
  .seq (chainsL sB sL sG sP) (.seq rowS (.seq recA (.seq copyL (.seq recB gamS))))

/-- **The grade invariant** at the head of grade `g`: the registers of the grade and the grade
record `h` with grades `< g` (the row of grade `g - 1` at `R`), the setup record `S` and the
halving table `D`. -/
def GradeInv (O : OracleIface) (P : Polygon) (c : Config) (g h hp R S D : ℕ) : Prop :=
  URegs c P.n hp h g (gradeCount P.n g) (gradeGran g) (gradeCount P.n (g - 1)) R ∧
    c.nreg 170000 = S ∧ c.nreg 170002 = topGrade P.n ∧ c.nreg 170003 = D ∧
    c.nreg 170006 = topGrade P.n + 1 ∧ c.nreg 170009 = (P.n - 2) / 2 ^ g ∧
    c.nreg 170015 = 0 ∧ c.nreg 170016 = 0 ∧ c.nreg 170035 = 0 ∧ c.nreg 170036 = 1 ∧
    Robust (c.nreg ALLOC) c.nmem fun m => UpTab O P m h hp (c.nreg ALLOC) ∧ m h = g ∧
      (1 ≤ g → m (m (h + 2) + (g - 1)) = R) ∧ m (h + 1) = S ∧ m (h + 3) = D

/-- The cost bound of grade `g`. -/
noncomputable def gradeC (κB κL : ℕ) (κG : ℕ → ℕ) (κO n g : ℕ) : ℕ :=
  gradeCount n g * (stepB κB κL κG κO g + 19) + 17 * g + 100

/-- The registers kept by a grade (besides the grade registers it updates). -/
def GK (r : ℕ) : Prop :=
  ((OutB (bandOf r) ∨ r = 230000) ∧ r ≠ ALLOC) ∨ r = 170000 ∨ r = 170001 ∨ r = 170002 ∨
    r = 170003 ∨ r = 170004 ∨ r = 170006 ∨ (170020 ≤ r ∧ r ≤ 170029) ∨ r = 170037 ∨
    (170080 ≤ r ∧ r < 180000)

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

theorem two_pow_le_of_le_top {n g : ℕ} (hn : 2 ≤ n) (hg : g ≤ topGrade n) : 2 ^ g ≤ 2 * n := by
  have h1 : 2 ^ g ≤ 2 ^ topGrade n := Nat.pow_le_pow_right (by norm_num) hg
  rcases Nat.lt_or_ge 1 (n - 1) with h | h
  · have h2 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    unfold topGrade at h1
    have h3 : 1 ≤ Nat.clog 2 (n - 1) := by
      rcases Nat.eq_zero_or_pos (Nat.clog 2 (n - 1)) with h0 | h0
      · have := Nat.le_pow_clog (b := 2) (by norm_num) (n - 1); rw [h0] at this; simp at this
        omega
      · exact h0
    have e : 2 ^ Nat.clog 2 (n - 1) = 2 * 2 ^ (Nat.clog 2 (n - 1)).pred := by
      rw [← pow_succ', show (Nat.clog 2 (n - 1)).pred + 1 = Nat.clog 2 (n - 1) by rw [Nat.pred_eq_sub_one]; omega]
    omega
  · have : topGrade n = 0 := by
      unfold topGrade; rw [show n - 1 = 1 by omega]; simp
    rw [this] at h1; simp at h1; omega

theorem GK.kept {r : ℕ} (h : GK r) : Kept r ∧ r ≠ 170015 ∧ r ≠ 170016 ∧ r ≠ 170017 ∧
    r ≠ 170018 ∧ r ≠ 170035 ∧ r ≠ 170036 := by
  unfold GK at h
  rcases h with ⟨h1, h2⟩ | h
  · refine ⟨Or.inl ⟨h1, h2⟩, ?_⟩
    rcases h1 with h1 | h1
    · unfold OutB bandOf at h1; omega
    · omega
  · refine ⟨Or.inr ⟨by unfold bandOf bUp; omega, ⋄⟩, ⋄⟩

theorem GK.ne_alloc {r : ℕ} (h : GK r) : r ≠ ALLOC := h.kept.1.ne_alloc

theorem GK.range {r : ℕ} (h : GK r) : r < 10000 ∨ r = 230000 ∨ 250000 ≤ r ∨
    (170000 ≤ r ∧ r ≤ 170004) ∨ r = 170006 ∨ (170020 ≤ r ∧ r ≤ 170029) ∨ r = 170037 ∨
    (170080 ≤ r ∧ r < 180000) := by
  unfold GK at h
  rcases h with ⟨h1 | h1, -⟩ | h
  · unfold OutB bandOf at h1; omega
  · omega
  · omega

end proofs

end

end Chazelle.Core.Up
