/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower

universe w w'

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {N : Type w'} {n : ℕ}

/-- If `y` avoids the pulled-back tuple `t ∘ e⁻¹`, then `e y` avoids `t`. -/
theorem not_mem_range_trans_of_not_mem {e : M ≃ N} {t : Fin n ↪ N} {y : M}
    (hy : y ∉ Set.range (t.trans e.symm.toEmbedding)) : e y ∉ Set.range t := by
  rintro ⟨i, hi⟩
  exact hy ⟨i, by simp_all⟩

/-- Concatenation commutes with pulling back along `e⁻¹`:
`(t⌢(e y)) ∘ e⁻¹ = (t ∘ e⁻¹)⌢y`. -/
theorem snoc_trans_symm (e : M ≃ N) (t : Fin n ↪ N) {y : M}
    (hy : y ∉ Set.range (t.trans e.symm.toEmbedding)) :
    (snoc t (e y) (not_mem_range_trans_of_not_mem hy)).trans e.symm.toEmbedding =
      snoc (t.trans e.symm.toEmbedding) y hy := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/-- **Realized families push forward along a bijection of carriers**: if `R` realizes some
member of `U` over the pulled-back tuple `t ∘ e⁻¹` as a coface of `p`, then `R.map e` realizes
the same member over `t`.  The stage-type data (`q ∈ U`, `IsCoface p q`) is untouched: only
the witnesses move, through `e`. -/
theorem RealizesSome.map {R : KnightRealization α M} (e : M ≃ N) {t : Fin n ↪ N}
    {p : S α.1 n} {U : Set (S α.1 (n + 1))}
    (h : R.RealizesSome (t.trans e.symm.toEmbedding) p U) :
    RealizesSome (R.map e) t p U := by
  obtain ⟨y, hy, q, hqU, hqc, hq⟩ := h
  refine ⟨e y, not_mem_range_trans_of_not_mem hy, q, hqU, hqc, ?_⟩
  rw [Realization.map_eval, snoc_trans_symm e t hy, hq]

/-- **Modelhood transports along a bijection of carriers** (the missing lemma of the #73
audit; the prerequisite of the #46 limit probe): the push-forward `R.map e` of a model is a
model.  Clauses (2)/(3) are the generic #111 transports; the four existential-closure clauses
push their witnesses through `e` (`RealizesSome.map`). -/
theorem IsModel.map {R : KnightRealization α M} (h : R.IsModel) (e : M ≃ N) :
    IsModel (R.map e) := by
  have he : R.IsIso (R.map e) e := Realization.isIso_map e R
  refine ⟨h.nonempty.map e, he.isExactParentConsistent h.consistent,
    he.isInitialSegmentCovering h.covering, ?_, ?_, ?_, ?_⟩
  all_goals
    intro n t p hp
    rw [Realization.map_eval] at hp
    intros
    apply RealizesSome.map
    first | solve_by_elim [h.genSat] | solve_by_elim [h.bottomPattern]
          | solve_by_elim [h.uniformity] | solve_by_elim [h.highGradeDominance]

end KnightRealization

end VaughtConjecture.Knight
