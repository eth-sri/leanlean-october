
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.HighLayerBountiful
import VaughtConjecture.Knight.GradeSplice
import VaughtConjecture.Knight.SourceBlockLocalityTransport
import VaughtConjecture.Knight.WitnessSplice

/-! # Literal section supply with a zero high tail

This construction accepts arbitrary lawful old values, including literal top.
It requires neither positive continuation nor a supported canonical encoding.
-/

namespace VaughtConjecture.Knight.HighLayerBountiful
open    CoatomBoundaryExtension SourceLayerCarrier GradeTailRestoration


variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
variable (D : CellScheme A) (Q : Type*) [Fintype Q] (l : ℕ) (hl : 0 < l) (hlA : l ≤ A.card)
variable (K : ℕ) (hK : BoundedBy D.grade K) (hKl : K < l)
variable (sem : Semantics D) (out : Semantics (scheme D Q l hl hlA))
variable (hrow : ∀ c d,
  out.E (old D Q l hl hlA c)
    (SeparatedSourceLayerCarrier.ownerEquiv D Q l hl hlA (separated D l K hK hKl) c d) =
    sem.E c d)

local notation "scheme₀" => scheme D Q l hl hlA

include hrow in
theorem exists_zero_tail {p} (hp : RespectsSemantics sem p) :
    ∃ r ,
      RespectsSemantics out r ∧
      (∀ d, r (old D Q l hl hlA d) = p d) ∧
      ∀ q , r (SourceLayerCarrier.controller D Q l hl hlA q).1 = ⊥ := by
  let e := equiv D Q l hl hlA (A, K) (fun h => (not_le_of_gt hKl) h.2)
  let v : (scheme₀).below (A, K) → ExtOrd := fun d => p (e.symm d).1
  have hv  :=
    (respects_iff D Q l hl hlA K hK hKl sem out hrow (A, K)
      (fun h => (not_le_of_gt hKl) h.2) _).mp (hp.toBelow _)
  let u : (scheme₀).below (A, l) → ExtOrd := fun _ => ⊥
  have hu  :=
    (bottomSection out (A, l) (A, l)).left_lawful
  have hs  :=
    splice_respects hKl.le hu hv (M := ⊥) (fun _ _ => le_rfl)
      (fun _ => by simp  )
  have hall (d : Cell (scheme₀)) :
      GradedLe ((scheme₀).cell d) (A, l) := by
    refine ⟨(scheme₀).scope_subset d, ?_⟩
    rw [cell_eq]
    cases toOcc D Q l hl hlA d with
    | inl x => exact (hK x).trans hKl.le
    | inr q => exact le_rfl
  refine ⟨fun d => splice u v ⟨d, hall d⟩, hs.toRespects hall, ?_, ?_⟩
  · intro d
    have hd : (scheme₀).grade (old D Q l hl hlA d) ≤ K := by
      simpa only [CellScheme.grade,  cell_toCell, index] using hK d
    apply (splice_low u v ⟨old D Q l hl hlA d, hall _⟩ hd).trans
    let d₀ : D.below (A, K) := ⟨d, D.scope_subset d, hK d⟩
    change p (e.symm (e d₀)).1 = p d
    rw [Equiv.symm_apply_apply]
  · intro q
    apply splice_high u v
    change ¬ ((scheme₀).cell
      (SourceLayerCarrier.controller D Q l hl hlA q).1).2 ≤ K
    rw [(SourceLayerCarrier.controller D Q l hl hlA q).2]
    exact not_le_of_gt hKl


