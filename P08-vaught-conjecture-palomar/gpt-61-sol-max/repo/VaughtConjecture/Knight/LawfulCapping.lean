
import VaughtConjecture.Knight.PointwiseLabels
import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.Coface
import VaughtConjecture.Knight.WitnessSplice
import VaughtConjecture.Knight.PositiveNormalization

/-! # Lawful capping and finite protected cutoffs

Choose permitted caps below a limit stage, preserving finite protected values.
Arbitrary observation cutoffs need not themselves preserve lawfulness.
The historical capping names are retained in their original namespace.
-/

namespace VaughtConjecture.Knight.FiniteCutCapping
open Value ExtOrd

/-- Capping a respecting labelling of a whole finite scheme uses the existing lower-set
cap theorem. No new transformation witness is needed. -/
theorem respects_cap {n} {D : SemScheme (n + 1)}
    {q} (hq : RespectsSemantics D.rows q) {γ}
    (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ) :
    RespectsSemantics D.rows (fun d => min (q d) γ) :=
  ((hq.toBelow (Finset.univ, n + 1)).cap hγ).toRespects
    (StageType.gradedLe_univ_succ D.scheme)

/-- A finite family strictly below a nonzero limit has a nonbottom self-visible upper
bound still below that limit. In particular, the cap obstruction needs no extra bound
hypothesis when every old label is below a limit cut. -/
theorem exists_cap_below_limit {I : Type*} [Finite I] (p : I → ExtOrd)
    {β : Ordinal₀} (hβ : Order.IsSuccLimit β) (hp : ∀ d, p d < ofOrd β) (K : ℕ) :
    ∃ γ , extVisibilityReplace γ K K = γ ∧ γ ≠ ⊥ ∧
      (BoundedBy p γ) ∧ γ < ofOrd β := by
  
  let _ := Fintype.ofFinite I
  let m : ExtOrd := max (ofOrd 0) (Finset.univ.sup p)
  have hm : m < ofOrd β := max_lt (ofOrd_lt_ofOrd.mpr hβ.pos)
    ((Finset.sup_lt_iff (bot_lt_ofOrd β)).mpr (fun d _ => hp d))
  have hm0 : ofOrd 0 ≤ m := le_max_left _ _
  have hpm : BoundedBy p m := fun d =>
    (Finset.le_sup (Finset.mem_univ d)).trans (le_max_right _ _)
  rcases ExtOrd.cases m with hb | ht | ⟨μ, hμ⟩
  · simp_all
  · simp_all
  rw [hμ] at hm hpm
  refine ⟨ofOrd (visibilityReplace μ K K), ?_, ofOrd_ne_bot _, ?_, ?_⟩
  · rw [extVisibilityReplace_ofOrd, ofOrd_inj, visibilityReplace_self_iff]
    unfold visibilityReplace
    split_ifs with h
    · exact (finitePart_limitPart_add_nat μ K).symm ▸ le_rfl
    · exact not_lt.mp h
  · exact fun d => (hpm d).trans (le_extVisibilityReplace_self (ofOrd μ) K)
  · exact ofOrd_lt_ofOrd.mpr (visReplace_lt_of_lt_limit hβ (ofOrd_lt_ofOrd.mp hm) K K)

/-- A permitted ordinal cutoff strictly above a finite family and a requested floor.
The family may be empty; bottom labels are allowed. -/
theorem exists_ordinal_cap_below_limit {I : Type*} [Finite I] (p : I → ExtOrd)
    {α : Ordinal₀} (hα : Order.IsSuccLimit α) (hp : ∀ i, p i < ofOrd α)
    {δ : Ordinal₀} (hδ : δ < α) (K : ℕ) :
    ∃ b , b < α ∧ δ < b ∧ SelfVis K (ofOrd b) ∧
      ∀ i, p i < ofOrd b := by
  
  let _ := Fintype.ofFinite I
  let a := max δ (Finset.univ.sup fun i => ordOf (p i))
  have ha : a < α := by
    apply max_lt hδ
    apply (Finset.sup_lt_iff hα.pos).mpr
    intro i _
    rcases ExtOrd.cases (p i) with hb | ht | ⟨μ, hμ⟩
    · have hbot : ordOf (⊥) = 0 := by
        simp_all [VaughtConjecture.Knight.ordOf, VaughtConjecture.Knight.ExtOrd.ofOrd]
      simpa only [hb, hbot] using hα.pos
    · exact (not_lt_of_ge le_top (ht ▸ hp i)).elim
    · simpa only [hμ, ordOf_ofOrd] using ofOrd_lt_ofOrd.mp (hμ ▸ hp i)
  have hab : a < a + (K + 1) := by
    simp_all
  have hb : a + (K + 1 : ℕ) < α := by
    exact?
  refine ⟨a + (K + 1 : ℕ), hb, (le_max_left _ _).trans_lt hab, ?_, ?_⟩
  · rw [selfVis_ofOrd_iff]
    have he : a + ((K + 1 : ℕ)) =
        limitPart a + ((finitePart a + (K + 1) : ℕ)) := by
      conv_lhs => rw [← limitPart_add_finitePart a]
      simp only [add_assoc, Nat.cast_add]
    rw [he, finitePart_limitPart_add_nat]
    omega
  · intro i
    rcases ExtOrd.cases (p i) with hb | ht | ⟨μ, hμ⟩
    · rw [hb]; exact bot_lt_ofOrd _
    · exact (not_lt_of_ge le_top (ht ▸ hp i)).elim
    · rw [hμ, ofOrd_lt_ofOrd]
      have hi := Finset.le_sup (f := fun i => ordOf (p i)) (Finset.mem_univ i)
      rw [hμ, ordOf_ofOrd] at hi
      exact (hi.trans (le_max_right _ _)).trans_lt hab

end VaughtConjecture.Knight.FiniteCutCapping

namespace VaughtConjecture.Knight.StageType
open Value ExtOrd 

/-- A lawful cutoff above every proper label of a stage type and a requested floor. -/
theorem exists_lawful_cutoff {α : LimitStage} {n : ℕ} (p : S α.1 n)
    {δ : Ordinal₀} (hδ : δ < α.1) (K : ℕ) :
    ∃ b : Ordinal₀, b < α.1 ∧ δ < b ∧ SelfVis K (ofOrd b) ∧
      ∀ d, p.label d ≠ ⊤ → p.label d < ofOrd b := by
  obtain ⟨b, hb, hδb, hvis, hp⟩ := FiniteCutCapping.exists_ordinal_cap_below_limit
    (fun d : {d : Cell p.scheme.scheme // p.label d ≠ ⊤} => p.label d.1)
    α.2 (fun d => (p.label_bound d.1).resolve_right d.2) hδ K
  exact ⟨b, hb, hδb, hvis, fun d hd => hp ⟨d, hd⟩⟩

