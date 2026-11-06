module

public import ADR11.Coalescent.Factorization
/-!
# The population above the root: Kingman's coalescent run for an infinite time

As `t → ∞`, `g_kj(t) → 1` if `j = 1` and `→ 0` otherwise (for `k ≥ 1`), so `exp(tQ)(F, G)`
converges to the probability that the jump chain, run until one root is left, ends at `G`.

## Main results

* `tendsto_spectrum`: the limits of `g_kj(t)`.
* `tendsto_kingmanTransition`: the entries of `exp(tQ)` at a forest converge to those of
  `kingmanAbsorption`.
* `kingmanAbsorption_eq_jump`: `kingmanAbsorption F G = J^{k-1}(F, G)`.
* `kingmanTransition_mul_kingmanAbsorption`: running for a finite time and then for an infinite
  time is running for an infinite time.
-/

@[expose] public section

namespace ADR11

open Finset Filter Topology

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {F : Family L}

/-- The limit of `exp(tQ)(F, G)`, computed from the factorization. -/
private theorem absorb_tendsto (hF : IsForest F) (G : Family L) :
    Tendsto (fun t => kingmanTransition t F G) atTop
      (𝓝 ((jumpMatrix ^ (#(roots F) - 1)) F G)) := by
  by_cases h0 : #(roots F) = 0
  · simp [h0, kingmanTransition_of_card_roots_le_one hF (by omega), Matrix.one_apply, eq_comm]
  · simp_rw [kingmanTransition_apply hF]
    convert (tendsto_spectrum _ _ (by omega : 1 ≤ #(roots F))).mul_const
      ((jumpMatrix ^ (#(roots F) - #(roots G))) F G) using 2
    split_ifs with hG
    · simp_all
    · grind [→ jumpMatrix_pow_support]

theorem kingmanAbsorption_eq_jump (hF : IsForest F) (G : Family L) :
    kingmanAbsorption F G = (jumpMatrix ^ (#(roots F) - 1)) F G :=
  (absorb_tendsto hF G).limUnder_eq

theorem tendsto_kingmanTransition (hF : IsForest F) (G : Family L) :
    Tendsto (fun t => kingmanTransition t F G) atTop (𝓝 (kingmanAbsorption F G)) := by
  rw [kingmanAbsorption_eq_jump hF]
  exact absorb_tendsto hF G

theorem kingmanTransition_mul_kingmanAbsorption (hF : IsForest F)
    (t : ℝ) (G : Family L) :
    ∑ F', kingmanTransition t F F' * kingmanAbsorption F' G = kingmanAbsorption F G := by
  have hlim :=
    (tendsto_kingmanTransition hF G).comp (tendsto_atTop_add_const_left atTop t tendsto_id)
  simp [Function.comp_def, kingmanTransition_add] at hlim
  exact tendsto_nhds_unique (by
    refine tendsto_finsetSum _ fun F' _ => ?_
    by_cases h : kingmanTransition t F F' = 0
    · simp only [h, zero_mul]
      exact tendsto_const_nhds
    · have hF' : IsForest F' := by
        rw [kingmanTransition_apply hF] at h
        exact (jumpMatrix_pow_support hF (right_ne_zero_of_mul h)).1
      exact (tendsto_kingmanTransition hF' G).const_mul _
  ) hlim

end ADR11
