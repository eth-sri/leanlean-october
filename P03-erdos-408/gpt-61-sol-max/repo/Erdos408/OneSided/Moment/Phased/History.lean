module
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import Erdos408.OneSided.Moment.Chain.Births
import Erdos408.OneSided.Moment.Phased.Rows

public import Erdos408.OneSided.Moment.Chain

/-!
# The history expansion with visit-dependent coefficients

The phased operators of `Moment/Phased.lean` carry at each visit and each edge the phases of
their own addresses, so their coefficients depend on the position in the product. This file
expands such products into histories.

* `foldr_finRange_eq_sum_history`: for ghost coefficients `G j` at each visit `j` and edge
  coefficients `E j` at each edge `j`, the product `𝒢^{G₀} ℰ^{E₀} 𝒢^{G₁} ⋯ ℰ^{E_{N-1}} 𝒢^{G_N}`
  applied to `f` at `s` is `∑_h ∏_j G_j(visit_j, h.1 j) ∏_j E_j(…, h.2 j) f(end(s, h))`.
-/

@[expose] public section

section

namespace Erdos408.OneSided

open Finset

variable {K : ℕ}



variable {x : ℝ} {d : Data K} {Y d₀ u v r : ℝ} {B : ℕ}

/-- The visits of a history after its first edge are the visits of its tail from the state
after that edge. -/
private alias chainVisit_cons_succ := _root_.SharedProofs.chainVisit_cons_succ

/-- The end of a history is the end of its tail from the state after its first edge. -/
private alias chainEnd_cons := _root_.SharedProofs.chainEnd_cons

/-- A history with no edges is a single ghost choice. -/
private theorem sum_histories_zero (F : History x d Y d₀ u v r 0 → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B 0, F h =
      ∑ c ∈ multBox B ×ˢ multBox B, F (fun _ => c, Fin.elim0) := by solve_by_elim [_root_.SharedProofs.shared_sum_histories_zero]

/-- A history with `N + 1` edges is a first ghost choice, a first edge choice, and a history
with `N` edges. -/
private theorem sum_histories_succ {N : ℕ} (F : History x d Y d₀ u v r (N + 1) → ℂ) :
    ∑ h ∈ histories x d Y d₀ u v r B (N + 1), F h =
      ∑ c ∈ multBox B ×ˢ multBox B, ∑ e ∈ edgeChoices x d Y d₀ u v r,
        ∑ h ∈ histories x d Y d₀ u v r B N, F (Fin.cons c h.1, Fin.cons e h.2) := by solve_by_elim [_root_.SharedProofs.shared_sum_histories_succ]

/-- The history expansion with visit-dependent coefficients: with ghost coefficients `G j` at
the visits and edge coefficients `E j` at the edges, `𝒢^{G₀} ℰ^{E₀} ⋯ ℰ^{E_{N-1}} 𝒢^{G_N} f (s)`
is `∑_h ∏_j G_j(visit_j(s, h), h.1 j) ∏_j E_j(…, h.2 j) f(end(s, h))`. -/
theorem foldr_finRange_eq_sum_history  f   N  :
    ∀ (G : Fin (N + 1) → ChainState x d Y d₀ u v r B → GhostChoice x d → ℂ)
      (E : Fin N → ChainState x d Y d₀ u v r B → EdgeChoice x d Y d₀ u v r → ℂ)
      (s : ChainState x d Y d₀ u v r B),
      (List.finRange N).foldr
          (fun j g => choiceOp (multBox B ×ˢ multBox B) (G j.castSucc)
            (chainGhostOut x d Y d₀ u v r B)
            (choiceOp (edgeChoices x d Y d₀ u v r) (E j) (chainEdgeOut x d Y d₀ u v r B) g))
          (choiceOp (multBox B ×ˢ multBox B) (G (Fin.last N)) (chainGhostOut x d Y d₀ u v r B)
            f) s =
        ∑ h ∈ histories x d Y d₀ u v r B N,
          (∏ j : Fin (N + 1), G j (chainVisit s h j) (h.1 j)) *
            (∏ j : Fin N,
              E j (chainGhostOut x d Y d₀ u v r B (chainVisit s h j.castSucc) (h.1 j.castSucc))
                (h.2 j)) *
            f (chainEnd s h) := by
  induction N with
  | zero =>
    intro G E s
    rw [sum_histories_zero]
    simp only [List.finRange_zero, List.foldr_nil, choiceOp, Fin.prod_univ_succ,
      Fin.prod_univ_zero, mul_one]
    rfl
  | succ N ih =>
    intro G E s
    -- peel off `𝒢^{G₀} ℰ^{E₀}` and expand the rest from the state after the first edge
    rw [List.finRange_succ, List.foldr_cons, List.foldr_map, sum_histories_succ]
    simp only [← Fin.succ_castSucc, ← Fin.succ_last, Fin.castSucc_zero]
    rw [funext (ih (fun j => G j.succ) (fun j => E j.succ))]
    have h0 : ∀ h : History x d Y d₀ u v r N, ∀ c e,
        chainVisit (N := N + 1) s (Fin.cons c h.1, Fin.cons e h.2) 0 = s := fun _ _ _ => rfl
    simp only [choiceOp, Fin.prod_univ_succ (n := N + 1), Fin.prod_univ_succ (n := N),
      ← Fin.succ_castSucc, Fin.castSucc_zero, chainVisit_cons_succ, chainEnd_cons, Fin.cons_succ,
      Fin.cons_zero, h0, mul_sum]
    exact sum_congr rfl fun c _ => sum_congr rfl fun e _ => sum_congr rfl fun h _ => by ring



end Erdos408.OneSided
