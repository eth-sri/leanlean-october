/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.VisibilityAlgebra

/-! # The foundational original-cap lifting calculus

One literal lifting property, its identity and composition laws, old-face transport,
and generation by finite cover relations. These results do not depend on any concrete
carrier, code table, receiver or model. Historical public names remain in the
`CoatomBoundaryExtension` namespace for compatibility.

General lifting asserts existence for each ambient and cap. It does not assert a unique
extension or simultaneous cap preservation; those require injective restriction and are
supplied separately by `CappedLiftOfExtension`.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd
open VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable {sem : Semantics D} {I U J K : Finset ι × ℕ}

/-- A single literal old graded-pair lifting clause, also allowing equal
indices and empty source domains. No new whole-target lift is included. -/
def CappedLift (sem : Semantics D) (h : GradedLe I U) : Prop :=
  ∀ (p : D.below I → ExtOrd) (q : D.below U → ExtOrd) (γ : ExtOrd),
    RespectsSemanticsBelow sem I p → RespectsSemanticsBelow sem U q →
    SelfVis U.2 γ →
    (∀ d, min (q (CellScheme.below.mono h d)) γ = min (p d) γ) →
    ∃ r : D.below U → ExtOrd, RespectsSemanticsBelow sem U r ∧
      (∀ d, min (r d) γ = min (q d) γ) ∧
      ∀ d, r (CellScheme.below.mono h d) = p d

/-- Equal indices require no appeal to strict-pair bountifulness. -/
theorem lift_refl : CappedLift sem (GradedLe.refl I) := fun p q γ hp _ _ hag => ⟨p, hp, fun d => (hag d).symm, fun _ => rfl⟩

/-- Empty overlap needs neither a positive grade nor a fictitious owner. -/
theorem lift_empty (h : GradedLe I U) [IsEmpty (D.below I)] : CappedLift sem h := fun _ q _ _ hq _ _ => ⟨q, hq, fun _ => rfl, fun d => isEmptyElim d⟩

/-- The clause is supplied by the old scheme's actual bountifulness. -/
theorem lift_of_bountiful (hb : sem.IsBountiful)
    (hI : I ∈ Plan.gradedPlan D.plan) (hU : U ∈ Plan.gradedPlan D.plan)
    (h : GradedLe I U) : CappedLift sem h := by
  by_cases he : I = U
  · subst U
    exact lift_refl
  · intro p q γ hp hq hγ hag
    exact hb I U hI hU h he p q γ hp hq hγ hag

/-- Transport a lift along literal lower-domain equivalences. The restriction square must
commute, lawful sections must transport, and the old target grade must permit the new cap.
No global carrier equivalence or output bountifulness is assumed. -/
theorem CappedLift.of_equiv
    {ι' : Type*} [DecidableEq ι'] {A' : Finset ι'} {D' : CellScheme A'}
    {sem' : Semantics D'} {I' U' : Finset ι' × ℕ}
    {h : GradedLe I U} {h' : GradedLe I' U'}
    (eI : D'.below I' ≃ D.below I) (eU : D'.below U' ≃ D.below U)
    (hsquare : ∀ d, eU (CellScheme.below.mono h' d) = CellScheme.below.mono h (eI d))
    (hgrade : U'.2 ≤ U.2)
    (hsource : ∀ p, RespectsSemanticsBelow sem I p →
      RespectsSemanticsBelow sem' I' (p ∘ eI))
    (htarget : ∀ q, RespectsSemanticsBelow sem U q ↔
      RespectsSemanticsBelow sem' U' (q ∘ eU))
    (hl : CappedLift sem' h') : CappedLift sem h := by
  intro p q γ hp hq hγ hag
  obtain ⟨r, hr, hc, hf⟩ := hl (p ∘ eI) (q ∘ eU) γ (hsource p hp)
    ((htarget q).mp hq) (hγ.mono hgrade) (fun d => by
      simpa only [Function.comp_apply, hsquare] using hag (eI d))
  refine ⟨r ∘ eU.symm, (htarget _).mpr ?_, ?_, ?_⟩
  · simpa only [Function.comp_def, Equiv.symm_apply_apply] using hr
  · intro d
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hc (eU.symm d)
  · intro d
    have he : eU.symm (CellScheme.below.mono h d) = CellScheme.below.mono h' (eI.symm d) := by
      apply eU.injective
      rw [Equiv.apply_symm_apply, hsquare, Equiv.apply_symm_apply]
    rw [Function.comp_apply, he, hf, Function.comp_apply, Equiv.apply_symm_apply]


theorem CappedLift.comp {hIJ : GradedLe I J} {hJK : GradedLe J K}
    (hleft : CappedLift sem hIJ) (hright : CappedLift sem hJK) :
    CappedLift sem (hIJ.trans hJK) := by
  intro p q γ hp hq hγ hag
  obtain ⟨u, hu, hucap, huread⟩ := hleft p (q ∘ CellScheme.below.mono hJK) γ hp
    (hq.mono hJK) (hγ.mono hJK.2) hag
  obtain ⟨r, hr, hcap, hread⟩ := hright u q γ hu hq hγ (fun d => (hucap d).symm)
  exact ⟨r, hr, hcap, fun d => (hread (CellScheme.below.mono hIJ d)).trans (huread d)⟩

