
import Mathlib.Tactic

import VaughtConjecture.Knight.FullScopeBountiful
import VaughtConjecture.Knight.Domain

/-!
# Extending a full-scope lower labelling by bottom

This explicit extension preserves respect for every semantics: lower-grade controllers see
the original labelling, and every higher controller has bottom target. Availability stays
within a grade. No consistency, completeness, or bountifulness assumption is required.
This is a grade extension, not an extension across a proper scope.
-/

namespace VaughtConjecture.Knight

open Transform  

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {K : ℕ}

local notation "below₀" => D.below (A, K)

namespace CellScheme

/-- A lower labelling at full scope, with bottom at every higher-grade cell. -/
noncomputable def zeroAbove (q : below₀ → ExtOrd) (d : Cell D) :=
  if hd : D.grade d ≤ K then
    q ⟨d, D.scope_subset d, hd⟩ else ⊥

theorem zeroAbove_low (q : below₀ → ExtOrd) (d : below₀) :
    zeroAbove q d.1 = q d := by
  have hd : D.grade d.1 ≤ K := d.2.2
  rw [zeroAbove, dite_of_pos hd]
  rfl

theorem zeroAbove_high {q : below₀ → ExtOrd} {d : Cell D} (hd : ¬ D.grade d ≤ K) :
    zeroAbove q d = ⊥ := by rw [zeroAbove, dite_of_neg hd]

end CellScheme

/-- Extending a respecting full-scope lower labelling by bottom preserves respect. -/
theorem RespectsSemanticsBelow.zeroAbove {sem : Semantics D} {q : below₀ → ExtOrd}
    (hq : RespectsSemanticsBelow sem (A, K) q) :
    RespectsSemantics sem (CellScheme.zeroAbove q) := by
  have mem (d : Cell D) (hd : D.grade d ≤ K) : GradedLe (D.cell d) (A, K) :=
    ⟨D.scope_subset d, hd⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d
    by_cases hd : D.grade d ≤ K
    · rw [CellScheme.zeroAbove_low q ⟨d, mem d hd⟩]
      exact hq.orderly ⟨d, mem d hd⟩
    · simp_all [CellScheme.zeroAbove_high]
  · intro Sig
    by_cases hSig : D.grade Sig ≤ K
    · refine transformsTo_congr rfl rfl ?_ (hq.locality ⟨Sig, mem Sig hSig⟩)
      funext d
      rw [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩,
        CellScheme.zeroAbove_low q ⟨d.1, mem d.1 (d.2.2.trans hSig)⟩]
      rfl
    · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot)
      funext d
      rw [CellScheme.zeroAbove_high hSig, min_eq_right bot_le]
  · intro Sig Xi₀ hs hg
    by_cases hSig : D.grade Sig ≤ K
    · have hXi₀ : D.grade Xi₀ ≤ K := hg ▸ hSig
      obtain ⟨Xi, hc, hle⟩ :=
        hq.availability ⟨Sig, mem Sig hSig⟩ ⟨Xi₀, mem Xi₀ hXi₀⟩ hs hg
      refine ⟨Xi.1, hc, ?_⟩
      rw [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩, CellScheme.zeroAbove_low q Xi]
      exact hle
    · grind only [CellScheme.zeroAbove_high]

