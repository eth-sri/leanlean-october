/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReducedProjectionRequest
public import VaughtConjecture.AmalgamationPlan.PlanAttachment
public import VaughtConjecture.Knight.Domain

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization AmalgamationPlan Value ExtOrd

universe w

section PlanImage

/-- Restriction commutes with the image along an injection. -/
theorem restrictPlan_image {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (g : ι ↪ κ)
    (S : Finset (Finset ι)) (T : Finset ι) :
    Plan.restrictPlan (S.image (Finset.image g)) (T.image g) =
      (Plan.restrictPlan S T).image (Finset.image g) := by
  ext U
  simp only [Plan.restrictPlan, Finset.mem_inter, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨⟨V, hV, rfl⟩, hsub⟩
    exact ⟨V, ⟨hV, (Finset.image_subset_image_iff g.injective).mp hsub⟩, rfl⟩
  grind

variable {k m : ℕ}

/-- The image of a restricted scheme's plan is the restriction of the plan to the face. -/
theorem image_restrictFace_plan (D : CellScheme (ι := Fin m) Finset.univ) (f : Fin k ↪ Fin m)
    (hr : Finset.univ.image f ∈ D.plan) :
    (D.restrictFace f hr).plan.image (Finset.image f) =
      Plan.restrictPlan D.plan (Finset.univ.image f) := by
  ext S
  simp only [Finset.mem_image, CellScheme.mem_restrictFace_plan D f hr, Plan.restrictPlan,
    Finset.mem_inter, Finset.mem_powerset]
  constructor
  · grind
  · rintro ⟨hS, hsub⟩
    obtain ⟨T, -, rfl⟩ := Finset.subset_image_iff.mp hsub
    lia

theorem univ_image_onePointProj (e : Fin k ↪ Fin m) :
    (Finset.univ : Finset (Fin (k + 1))).image (onePointProj e) =
      Finset.univ.image (e.trans Fin.castSuccEmb) ∪ {Fin.last m} := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast i => aesop
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨Fin.castSucc i, onePointProj_castSucc e i⟩
    · exact ⟨Fin.last k, onePointProj_last e⟩

theorem image_castSuccEmb_union_last :
    (Finset.univ : Finset (Fin m)).image Fin.castSuccEmb ∪ {Fin.last m} = Finset.univ := by aesop

end PlanImage

end VaughtConjecture.Knight
