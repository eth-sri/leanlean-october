module

public import Chazelle.Core.NFBuildPassRam
public import Chazelle.Core.SortRam
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Down-phase driver (RAM side): small loop library

* `forLoop`: a counted loop `while i < N do body` whose body raises the counter register by one
  and keeps an invariant `Inv j c` indexed by the counter value, with a fixed cost bound per
  iteration;
* `forLoopSum`: the same with a per-iteration cost `f j`, total `Σ (f j + 2) + 2`;
* `frameM_of`: the frame of a statement with a syntactic write set (`NFBuildPassRam.wrM`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs

@[expose] public section

section loops

variable {P : Polygon} {W : ℕ}

/-- **A counted loop with a fixed cost per iteration.** -/
theorem forLoop {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c → ∃ c' k, Exec P W body c c' k ∧ Inv (j + 1) c' ∧ k ≤ Kb)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W (.whileLtN ir nr body) c c' k ∧ Inv N c' ∧ k ≤ (Kb + 2) * (N - j) + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    have hjN : j = N := by omega
    subst hjN
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    exact ⟨c, 2, .whileLtN_false (by rwo [h1, h2]) hw, hc, by omega⟩
  | succ t ih =>
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    have hlt : j < N := by omega
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂⟩ := ih hI₁ (by omega) (by omega)
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true (by rwx [h1, h2]) e₁ e₂, hI', ?_⟩
    rw [Nat.mul_succ]
    omega

/-- **A counted loop with a cost `f j` for the iteration at counter value `j`.** -/
theorem forLoopSum {ir nr : ℕ} {body : Stmt} (Inv : ℕ → Config → Prop) (f : ℕ → ℕ) (N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv (j + 1) c' ∧ k ≤ f j)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W (.whileLtN ir nr body) c c' k ∧ Inv N c' ∧
      k ≤ (∑ i ∈ Finset.Ico j N, (f i + 2)) + 2 := by
  induction hn : N - j generalizing j c with
  | zero =>
    have hjN : j = N := by omega
    subst hjN
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    exact ⟨c, 2, .whileLtN_false (by rwo [h1, h2]) hw, hc, by simp⟩
  | succ t ih =>
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    have hlt : j < N := by omega
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂⟩ := ih hI₁ (by omega) (by omega)
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true (by rwx [h1, h2]) e₁ e₂, hI', ?_⟩
    rw [Finset.sum_eq_sum_Ico_succ_bot hlt]
    omega

end loops

end

end DrvR

end Chazelle.Core
