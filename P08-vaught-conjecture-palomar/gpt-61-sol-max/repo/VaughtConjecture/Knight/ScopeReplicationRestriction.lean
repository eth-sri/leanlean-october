/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.ScopeReplicationAuxExtension

/-! # Restriction determines every auxiliary occurrence

The smaller mixed domain contains a copy of each relevant auxiliary prototype.
Two lawful target sections agreeing there agree at every auxiliary, including
copies at scopes incomparable with the prescribed scope. No field recognition
or hidden-original completion is assumed in this generic lemma.
-/

namespace VaughtConjecture.Knight.ScopeReplicationRestriction
open     ScopeReplicationCarrier
open ScopeReplicationSemantics ScopeReplicationAuxExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (B C : Finset ι)
  (hcover : ∀ c , D.scope c ≠ A → D.scope c ⊆ B ∨ D.scope c ⊆ C)
  (sem : Semantics D) {U V : Finset ι} {j : ℕ}
  (hU : U ∈ D.plan) (hmU : U = A ∨ Mixed B C U) (hjU : j ≤ U.card)
  (hV : V ∈ D.plan) (hmV : V = A ∨ Mixed B C V) (hjV : j ≤ V.card)
  (hUV : U ⊆ V)

local notation "GradedLe₀" => GradedLe (U, j) (V, j)

include hU hmU hjU hV hmV hjV in
theorem auxiliary_eq {p q}
    (hp : RespectsSemanticsBelow (rows hcover sem) (V, j) p)
    (hq : RespectsSemanticsBelow (rows hcover sem) (V, j) q)
    (hag : ∀ d ,
      p (CellScheme.below.mono (show GradedLe₀ from ⟨hUV, le_rfl⟩) d) =
      q (CellScheme.below.mono (show GradedLe₀ from ⟨hUV, le_rfl⟩) d))
    (z : (scheme D B C).below (V, j)) (hz : D.scope (erase D B C z.1) = A) :
    p z = q z := by
  let p₀ := p ∘ CellScheme.below.mono (show GradedLe₀ from ⟨hUV, le_rfl⟩)
  have hpz := cap D B C hcover sem hU hmU hjU hV hmV hjV hUV p₀ hp
    (γ := ⊤) (fun _ => rfl) z hz
  have hqz := cap D B C hcover sem hU hmU hjU hV hmV hjV hUV p₀ hq
     (fun d => congrArg (fun x => min x ⊤) (hag d).symm) z hz
  simp   at hpz hqz
  exact hpz.symm.trans hqz


