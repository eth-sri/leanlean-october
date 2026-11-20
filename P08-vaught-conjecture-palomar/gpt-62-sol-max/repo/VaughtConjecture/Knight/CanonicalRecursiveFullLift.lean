/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveActiveLift
public import VaughtConjecture.Knight.CanonicalRecursiveTopSections

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveFullLift

open Transform Value ExtOrd CoatomBoundaryExtension

open CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix CanonicalRecursiveActiveLift

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

variable {C : Finset ι} (hC : C ∈ D.plan) (hCA : C ≠ A)

variable (W : CutCover (cutRows sem n) (C, n + 3) (n + 3))

include hC hCA W in
/-- Local bottom-cap supply, not just extension of an already whole boundary.
The prescription may contain literal top. No ambient is needed. -/
theorem exists_section
    {p : (carrier sem n hA).below (C, n + 3) → ExtOrd}
    (hpr : RespectsSemanticsBelow (outputRows sem n hA hp) (C, n + 3) p) :
    ∃ r : target sem n hA → ExtOrd,
      RespectsSemanticsBelow (outputRows sem n hA hp) (A, n + 3) r ∧
      ∀ e, r (CellScheme.below.mono
        (show GradedLe (C, n + 3) (A, n + 3) from
          ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) e) = p e := by
  have hCnot : ¬ A ⊆ C := fun h =>
    hCA (Finset.Subset.antisymm (D.isPlan.subset_of_mem hC) h)
  let E := faceEquiv sem n hA (C, n + 3) hCnot le_rfl
  have hp₀ := pullback_respects sem n hA hp (C, n + 3) hCnot le_rfl hpr
  obtain ⟨b, hb, hbread⟩ := W.section_of (GradeCutBoundary.grade_bound D _) hp₀
  let F := GradeCutBoundary.belowEquiv D (n + 3) (A, n + 3) le_rfl
  have hu := (GradeCutBoundary.respects_iff D (n + 3) sem (A, n + 3) le_rfl _).mp
    (hb.toBelow (A, n + 3))
  obtain ⟨r, hr, hread⟩ := CanonicalRecursiveTopSections.exists_section sem hp n hA hu
  refine ⟨r, hr, ?_⟩
  intro e
  obtain ⟨d, rfl⟩ := E.surjective e
  let dA : (cut (D := D) n).below (A, n + 3) :=
    ⟨d.1, d.2.1.trans (D.isPlan.subset_of_mem hC), d.2.2⟩
  have hd : CellScheme.below.mono
      (show GradedLe (C, n + 3) (A, n + 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) (E d) =
      CanonicalRecursiveTopSections.boundaryTarget sem n hA (F dA) :=
    Subtype.ext (faceEquiv_val sem n hA _ hCnot le_rfl d)
  rw [hd, hread]
  change b (F.symm (F dA)).1 = p (E d)
  rw [Equiv.symm_apply_apply]
  exact hbread d

include hC hCA W in
/-- All original permitted caps at the new same-grade proper-to-full pair.
The predecessor supplies only lower restoration. Old-face clauses supply
only boundary completion. Every actual successor auxiliary cap survives. -/
theorem full_lift
    (hb : CanonicalRecursiveRestoration.LowerBountiful sem n hA (predecessorState sem n hA hp))
    (hCc : n + 3 ≤ C.card)
    (hfull : ∃ c : (cut (D := D) n).below (C, n + 3),
      (cut (D := D) n).cell c.1 = (C, n + 3))
    :
    CappedLift (outputRows sem n hA hp)
      (show GradedLe (C, n + 3) (A, n + 3) from
        ⟨D.isPlan.subset_of_mem hC, le_rfl⟩) := by
  intro p q γ hpr hqr hγ hag
  by_cases hγb : γ = ⊥
  · obtain ⟨r, hr, hread⟩ := exists_section sem n hA hp hC hCA
      W hpr
    exact ⟨r, hr, fun _ => by simp only [hγb, min_bot_right], hread⟩
  by_cases hactive : ∃ d : (carrier sem n hA).below (C, n + 3),
      (carrier sem n hA).grade d.1 = n + 3 ∧ γ < p d
  · exact CanonicalRecursiveActiveLift.exists_lift
      sem n hA hp hb hC hCA hCc hfull hpr hqr hγ hγb hag hactive W
  · exact SingleFaceTailRestoration.lift (outputRows sem n hA hp) (D.isPlan.subset_of_mem hC)
      (CanonicalRecursiveRestoration.lower_clause (CanonicalRecursiveSemantics.step sem hp n hA) hb hC (Nat.le_of_succ_le hCc)) hpr hqr hγ hag
      (fun d hd => not_lt.mp (fun h => hactive ⟨d, hd, h⟩))

end

end VaughtConjecture.Knight.CanonicalRecursiveFullLift
