
import VaughtConjecture.Knight.PointwiseLabels

import Mathlib.Tactic

import VaughtConjecture.Knight.AlignedCutEncoding
import VaughtConjecture.Knight.CanonicalPairedInverse

namespace VaughtConjecture.Knight
open  Value ExtOrd 

/-- A lawful aligned completion can be made top-free without changing its
prescribed face or its agreement below the source cut. -/
theorem exists_topFree_aligned_completion
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {BJ : GradedIndex ι} [Fintype (D.below BJ)]
    {K b : ℕ} {h δ : ExtOrd} {u : CellLabels D}
    {s p : BelowLabels D BJ}
    (hroom : h < ofOrd (Ordinal.omega0 * b))
    (hu : RespectsSemantics sem u) (hK : BoundedBy D.grade K)
    (hface : ∀ e , u e.1 = AlignedCutEncoding.encode s p K b h δ e) :
    ∃ v , RespectsSemantics sem v ∧ (AvoidsValue v ⊤) ∧
      (CappedEq v u h) ∧ ∀ e : D.below BJ, v e.1 = u e.1 := by
  
  let S := RelativePrefixEncoding.inventory p δ
  let T := S.card + b
  let C := CanonicalPairedInverse.grid K (T + 1)
  have hC : SelfVis K C := CanonicalPairedInverse.grid_visible _ _
  have hhC : h ≤ C := hroom.le.trans (ofOrd_le_ofOrd.mpr (le_trans
    (by gcongr; dsimp [T]; omega) le_self_add))
  have hfC (e : D.below BJ) : u e.1 ≤ C := by
    rw [hface]
    by_cases he : p e ≤ δ
    · rw [AlignedCutEncoding.encode_of_le he]
      exact (min_le_right _ _).trans hhC
    · rw [AlignedCutEncoding.encode_of_gt _ _ hroom e (not_le.mp he)]
      rcases mem_codedAlphabet_iff.mp (PaddedSourceDecoder.encode_mem S K b (p e)) with
        hb | ⟨a, n, ha, _, he⟩
      · rw [hb]; exact bot_le
      · rw [he]
        exact ofOrd_le_ofOrd.mpr ((code_add_lt_mul
          (Nat.cast_lt.mpr (by dsimp [T]; omega)) n).le.trans le_self_add)
  refine ⟨fun d => min (u d) C,
    ((hu.toBelow (A, K)).cap hC).toRespects
      (fun d => ⟨D.scope_subset d, hK d⟩), ?_, ?_, ?_⟩
  · intro d hd
    change min (u d) C = ⊤ at hd
    exact ofOrd_ne_top _ (top_le_iff.mp (hd ▸ min_le_right (u d) C))
  · intro d
    rw [min_assoc, min_eq_right hhC]
  · exact fun e => min_eq_left (hfC e)

