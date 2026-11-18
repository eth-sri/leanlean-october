/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ControllerPrefixFamily

/-! # Mixed-grade interpolation: orbit blocks, not just source order

A grade-two witness can interpolate one grade-one-visible value followed by an arbitrary
finite monotone list of grade-two-visible values. The source template is fixed in advance:
`ω + 1` for the low probe and `ω * (i + 2) + 2` for the high probes. The witness is one orbit
strip and a finite maximum of limit steps. Bottom, top, and repeated high values are allowed.

This does not assemble a controller family or establish bountifulness. In particular, separate
source blocks cannot be used indiscriminately: equal capped targets that are not visible at
the controller grade must come from the same source block. The latter is a necessary law for
every actual maximal-grade controller locality, not just the interpolation template.
-/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- A monotone map commuting with self-replacement can identify two separated source blocks
only at a self-visible output. -/
theorem selfVis_of_equal_images_separated_blocks {τ : ExtOrd → ExtOrd} {K : ℕ}
    (hm : Monotone τ)
    (hc : ∀ x, τ (extVisibilityReplace x K K) = extVisibilityReplace (τ x) K K)
    {a b : Ordinal.{0}} (hab : limitPart a < limitPart b)
    (he : τ (ofOrd a) = τ (ofOrd b)) : SelfVis K (τ (ofOrd a)) := by
  have hsrc : extVisibilityReplace (ofOrd a) K K ≤ ofOrd b := by
    by_cases ha : finitePart a < K
    · rw [extVisibilityReplace_of_finitePart_lt ha, ofOrd_le_ofOrd]
      exact (limitPart_add_nat_le_of_lt hab K).trans (limitPart_le b)
    · rw [extVisibilityReplace_of_le_finitePart (not_lt.mp ha), ofOrd_le_ofOrd,
        ← decomposition a]
      exact (limitPart_add_nat_le_of_lt hab (finitePart a)).trans (limitPart_le b)
  exact le_antisymm (by simpa only [hc, ← he] using hm hsrc)
    (le_extVisibilityReplace_self _ _)

/-- At a non-visible ordinal output, bounded replacement commutation determines the source's
finite part exactly, not just an upper bound on it. -/
theorem finitePart_eq_of_nonvisible_image {τ : ExtOrd → ExtOrd} {K : ℕ}
    (hc : ∀ x i, i ≤ K →
      τ (extVisibilityReplace x K i) = extVisibilityReplace (τ x) K i)
    {a t : Ordinal.{0}} (ht : τ (ofOrd a) = ofOrd t) (hft : finitePart t < K) :
    finitePart a = finitePart t := by
  have hfa : finitePart a < K := by
    by_contra hfa
    have hh := hc (ofOrd a) K le_rfl
    rw [extVisibilityReplace_of_le_finitePart (not_lt.mp hfa), ht] at hh
    exact (not_le_of_gt hft) (selfVis_ofOrd_iff.mp hh.symm)
  have hh := hc (ofOrd a) (finitePart a) hfa.le
  rw [extVisibilityReplace_of_finitePart_lt hfa, decomposition a, ht,
    extVisibilityReplace_of_finitePart_lt hft, ofOrd_inj] at hh
  have hf := congrArg finitePart hh
  rw [finitePart_limitPart_add_nat] at hf
  exact hf.symm

/-- Finite pointwise suprema preserve witnesses with a common suppressor, provided the empty
supremum has a witness too. This is a construction tool, not composition of transformations. -/
theorem Witness.finset_sup {ι : Type*} {g : ℕ → ExtOrd} {f : ι → ExtOrd → ExtOrd}
    (hbot : Witness g (fun _ => ⊥)) (s : Finset ι) (hf : ∀ i ∈ s, Witness g (f i)) :
    Witness g (fun a => s.sup (fun i => f i a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using hbot
  | @insert i s hi ih =>
    simpa only [Finset.sup_insert] using
      (hf i (Finset.mem_insert_self _ _)).max
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

namespace MixedGradeInterpolation

/-- The constant-bottom shifter is a witness at every grade. -/
theorem zero_witness (K : ℕ) : Witness (gTop K) (fun _ => ⊥) where
  anti := (witness_id K).anti
  vis := (witness_id K).vis
  bot := rfl
  mono := monotone_const
  clause5 := by intros; exact (extVisibilityReplace_bot _ _).symm

/-! ## A non-vacuous mixed-grade tie regression -/

end MixedGradeInterpolation
end VaughtConjecture.Knight
