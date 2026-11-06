module

public import Chazelle.Core.UpPhase19
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 32000000

/-!
# WP-J up phase, part 20: all grades

`gradesL = while g < p + 1 do gradeB` and `gradesL_exec`: from `GradeInv` at grade `0` to
`GradeInv` at grade `p + 1`, at cost `upT n + 2` (`upT n = Σ_{g ≤ p} gT g`).
-/

namespace Chazelle.Core.Up

open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41

@[expose] public section

/-- **All grades.** -/
def gradesL (sB sL sG sP : Stmt) : Stmt := .whileLtN 170007 170006 (gradeB sB sL sG sP)

/-- The budget of grade `g`. -/
noncomputable def gT (κB κL : ℕ) (κG : ℕ → ℕ) (κO n g : ℕ) : ℕ :=
  gradeC κB κL κG κO n g + stepB κB κL κG κO g + 10

/-- **The cost bound of all grades.** -/
noncomputable def upT (κB κL : ℕ) (κG : ℕ → ℕ) (κO n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (topGrade n + 1), gT κB κL κG κO n j

section proofs

variable {O : OracleIface} {P : Polygon} {W : ℕ}

theorem sq_le_two_pow (p : ℕ) : (p + 3) ^ 2 ≤ 16 * 2 ^ p := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ 2 k]
    have h : (k + 1 + 3) ^ 2 ≤ 2 * (k + 3) ^ 2 := by ring_nf; omega
    linarith

/-- `γ'_{g+1}` is small against the word bound. -/
theorem gradeGran_succ_le {n g : ℕ} (hn : 2 ≤ n) (hg : g ≤ topGrade n) :
    gradeGran (g + 1) + g + 3 ≤ 128 * n := by
  have h2 := two_pow_le_of_le_top hn hg
  have hp := two_pow_le_of_le_top hn (le_refl (topGrade n))
  have hsq := sq_le_two_pow g
  have hgp : 2 ^ g ≤ 2 ^ topGrade n := Nat.pow_le_pow_right (by norm_num) hg
  have hcb : Cost.ceilBeta (g + 1) ≤ g + 1 := Cost.ceilBeta_le _
  have h3 : 2 ^ Cost.ceilBeta (g + 1) ≤ 2 ^ (g + 1) := Nat.pow_le_pow_right (by norm_num) hcb
  have hcl : Nat.clog 2 (g + 1) ≤ g + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have h4 : (g + 1) * (Nat.clog 2 (g + 1) + 2) ≤ (g + 3) ^ 2 := by nlinarith
  unfold gradeGran fuseLoss
  rw [pow_succ 2 g] at h3
  have hg2 : g ≤ 2 ^ g := Nat.lt_two_pow_self.le
  omega

/-- **All grades.** -/
theorem gradesL_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ} (hB : BruteM sB κB)
    (hL : L41M O sL κL) (hGr : GranM sG κG) (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config} (hw : WordsBounded W c)
    {h hp R S D : ℕ} (hI : GradeInv O P c 0 h hp R S D)
    (hW : c.nreg ALLOC + upT κB κL κG O.κ P.n ≤ W) :
    ∃ c' k h' R', Exec P W (gradesL sB sL sG O.prep) c c' k ∧
      k ≤ upT κB κL κG O.κ P.n + 2 ∧ WordsBounded W c' ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      GradeInv O P c' (topGrade P.n + 1) h' hp R' S D ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ r, GK r → c'.nreg r = c.nreg r) ∧
      (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r) := by
  set p := topGrade P.n with hp_def
  set F := gT κB κL κG O.κ P.n with hF
  obtain ⟨A0, hA0⟩ : ∃ A0, c.nreg ALLOC = A0 := ⟨_, rfl⟩
  rw [hA0] at hW ⊢
  have hWn : P.n + 3 ≤ W := by ufo hostWords at hWh
  let I : Config → Prop := fun c' => ∃ g h' R', g ≤ p + 1 ∧ WordsBounded W c' ∧
    GradeInv O P c' g h' hp R' S D ∧ A0 ≤ c'.nreg ALLOC ∧
    c'.nreg ALLOC ≤ A0 + ∑ j ∈ Finset.range g, F j ∧
    (∀ a, a < A0 → c'.nmem a = c.nmem a) ∧ (∀ a, a < A0 → c'.rmem a = c.rmem a) ∧
    c'.output = c.output ∧ (∀ r, GK r → c'.nreg r = c.nreg r) ∧
    (∀ r, OutB (bandOf r) → c'.rreg r = c.rreg r)
  have hI0 : I c := ⟨0, h, R, by omega, hw, hI, by omega, by simp [hA0],
    fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  have hsplit : ∀ g, g < p + 1 → ∑ j ∈ Finset.Ico g (p + 1), F j =
      F g + ∑ j ∈ Finset.Ico (g + 1) (p + 1), F j := fun g hg =>
    Finset.sum_eq_sum_Ico_succ_bot hg F
  have htot : ∀ g, g ≤ p + 1 → ∑ j ∈ Finset.range g, F j + ∑ j ∈ Finset.Ico g (p + 1), F j =
      upT κB κL κG O.κ P.n := fun g hg => by
    unfold upT; rw [← hp_def, ← hF, Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (by omega) hg,
      Finset.range_eq_Ico]
  obtain ⟨c', k, e, ⟨g, h', R', hgp, hw', hI', a1, a2, mm, mr, mo, fr, frr⟩, htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170007) (b := 170006)
      (body := gradeB sB sL sG O.prep) I
      (fun c' => ∑ j ∈ Finset.Ico (c'.nreg 170007) (p + 1), F j)
      (fun c' => c'.nreg ALLOC) (fun c' ⟨_, _, _, _, h, _⟩ => h)
      (fun c2 ⟨g, h2, R2, hgp, hw2, hI2, a1, a2, mm, mr, mo, fr, frr⟩ htest => by
        rw [hI2.1.r07, hI2.2.2.2.2.1] at htest
        have hg : g ≤ p := by omega
        have hsum := htot g (by omega)
        have hs := hsplit g htest
        have hFg : F g = gradeC κB κL κG O.κ P.n g + stepB κB κL κG O.κ g + 10 := rfl
        obtain ⟨c3, k3, h3, R3, e3, hk3, hw3, b1, b2, hI3, m3, r3, o3, f3, ff3⟩ :=
          gradeB_exec (O := O) hB hL hGr hV hG hWh hn hw2 hI2 hg (by omega)
            (by have := gradeGran_succ_le hn hg; ufo hostWords at hWh)
        refine ⟨c3, k3, e3, ⟨g + 1, h3, R3, by omega, hw3, hI3, by omega, ?_,
          fun a ha => by rw [m3 a (by omega), mm a ha],
          fun a ha => by rw [r3 a (by omega), mr a ha], by rw [o3, mo],
          fun r hr => by rw [f3 r hr, fr r hr], fun r hr => by rw [ff3 r hr, frr r hr]⟩, ?_,
          by omega⟩
        · rwo [Finset.sum_range_succ]
        · rwo [hI3.1.r07, hI2.1.r07]) hI0
  have hgp' : g = p + 1 := by rwo [hI'.1.r07, hI'.2.2.2.2.1] at htest
  subst hgp'
  refine ⟨c', k, h', R', e, ?_, hw', a1, by omega, hI', mm, mr, mo, fr, frr⟩
  have := htot 0 (by omega)
  rw [hI.1.r07] at hk
  simp only [Finset.range_zero, Finset.sum_empty, zero_add] at this
  omega

end proofs

end

end Chazelle.Core.Up
