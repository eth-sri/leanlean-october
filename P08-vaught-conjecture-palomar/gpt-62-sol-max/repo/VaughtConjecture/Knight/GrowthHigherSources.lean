/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthOrderedBase
public import VaughtConjecture.Knight.RecursiveRungRendering

@[expose] public section

namespace VaughtConjecture.Knight.GrowthHigherSources

open Transform Value ExtOrd Growth GrowthOrderedBase

noncomputable section

section Catalogue

variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  (X : RelativeData DA semA DQ semQ)

instance (j : ℕ) : Fintype (Catalogue X j) := Fintype.ofFinite _

abbrev fields (j : ℕ) (a : Catalogue X j) : Field DA DQ → ExtOrd := a.val

theorem anchor_bound {j : ℕ} (a : Catalogue X j) (f : Field DA DQ) :
    fields X j a f ≤ CanonicalFieldLayer.ceiling j (Field DA DQ) := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

/-- The state is admitted at its own cutoff. No upward admission is used. -/
def state {j : ℕ} (a : Catalogue X j) : State DA DQ := State.ofProfile a.val

theorem state_admitted {j : ℕ} (a : Catalogue X j) :
    Admitted X j (state X a) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  have hs : state X a = S := State.profile_injective
    ((State.profile_ofProfile a.val).trans he.symm)
  exact hs.symm ▸ hS

theorem state_profile {j : ℕ} (a : Catalogue X j) :
    (state X a).profile = fields X j a := State.profile_ofProfile a.val

end Catalogue

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  (I : WholeDonorBoundary.Input A B C R m (n + 1) J)
  (X : I.GrowthData)
  (T : I.GrowthAttachment X)

include T in
theorem anchor_lawful_at {j : ℕ} (a : Catalogue X j) :
    RespectsSemanticsBelow I.rows (A, j)
      (fun d => fields X j a (field I d.1)) := by
  obtain ⟨S, hs, he⟩ := a.property.2
  change RespectsSemanticsBelow I.rows (A, j) (fun d => a.val (field I d.1))
  rw [← he]
  exact GrowthOrderedBase.boundary_lawful I X T hs

end

end VaughtConjecture.Knight.GrowthHigherSources
