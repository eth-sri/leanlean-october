/-
Released under Apache 2.0 license, as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Logic

@[expose] public section

namespace Light

/-- Unroll a list of stages, with no run-time loop overhead. -/
def Stmt.chain {β : Type} (body : β → Stmt) (xs : List β) : Stmt :=
  xs.foldr (fun x s => body x ;; s) .skip

/-- Compose stage specifications by folding their effects on an abstract state. -/
theorem Ends.chain {α β : Type} {lim : Limits} {P : Program} {d : ℕ}
    (xs : List β) (body : β → Stmt) (cost : β → ℕ) (step : α → β → α)
    (R : α → State → Prop)
    (run : ∀ b ∈ xs, ∀ a σ, R a σ → Ends lim P d (body b) σ (cost b) (R (step a b)))
    {a : α} {σ : State} (h : R a σ) :
    Ends lim P d (Stmt.chain body xs) σ (xs.map cost).sum (R (xs.foldl step a)) := by
  induction xs generalizing a σ with
  | nil => exact Ends.skip h
  | cons b bs ih =>
    exact Ends.seq (cost b) (bs.map cost).sum
      ((run b (by simp) a σ h).mono le_rfl (fun σ' h' =>
        ih (fun c hc => run c (List.mem_cons_of_mem _ hc)) h')) le_rfl

/-- An unrolled sequence whose invariant depends on the number of completed stages. -/
theorem Ends.chainFin {n : ℕ} {lim : Limits} {P : Program} {d : ℕ}
    (body : Fin n → Stmt) (cost : Fin n → ℕ) (R : ℕ → State → Prop)
    (run : ∀ i σ, R i.val σ → Ends lim P d (body i) σ (cost i) (R (i.val + 1)))
    {σ : State} (h : R 0 σ) :
    Ends lim P d (Stmt.chain body (List.finRange n)) σ ((List.finRange n).map cost).sum (R n) := by
  induction n generalizing σ R with
  | zero => simpa [Stmt.chain] using Ends.skip h (T := 0)
  | succ n ih =>
    simp only [List.finRange_succ, Stmt.chain, List.map_cons, List.foldr_cons, List.foldr_map,
      List.sum_cons, List.map_map]
    refine Ends.seq (cost 0) _ ((run 0 σ h).mono le_rfl ?_) le_rfl
    intro σ' h'
    exact ih (body ∘ Fin.succ) (cost ∘ Fin.succ) (fun i => R (i + 1)) (fun i => run i.succ) h'

end Light
