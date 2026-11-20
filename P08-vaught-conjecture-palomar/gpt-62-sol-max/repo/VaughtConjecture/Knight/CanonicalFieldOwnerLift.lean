/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldPrefix
public import VaughtConjecture.Knight.CanonicalOwnerLift
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalFieldOwnerLift

open Transform Value ExtOrd SharpWitnessComposition CanonicalFieldLayer

open CoatomBoundaryExtension SourcePrefixRows

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

variable (hj : 0 < j) (hA : j ≤ A.card)

variable (hproper : ∀ d : Cell D, D.scope d ≠ A) (hg : ∀ d : Cell D, D.grade d ≤ j)

abbrev target := (scheme sem j X occ hj hA).below (A, j)

abbrev oldTarget (d : Cell D) : target sem j X occ hj hA :=
  ScopedSourcePrefixAmbient.atGrade (old sem j X occ hj hA d) (max_grade sem j X occ hj hA hg _)

theorem oldTarget_grade (d : Cell D) :
    (scheme sem j X occ hj hA).grade (oldTarget sem j X occ hj hA hg d).1 =
      D.grade d := by
  simp only [oldTarget, ScopedSourcePrefixAmbient.atGrade, old, CellScheme.grade,
    SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem source_short (a : Profile sem j X occ)
    (d : Cell (scheme sem j X occ hj hA)) :
    Short j (source sem j X occ hj hA hproper hg a d) := by
  let F := data sem j X occ hj hA hproper hg
  by_cases he : (scheme sem j X occ hj hA).cell d = (A, j)
  · have hh : source sem j X occ hj hA hproper hg a d ∈ F.grid := by
      change F.profile (controller sem j X occ hj hA a) d ∈ F.grid
      rw [show d = (⟨d, he⟩ : SourcePrefixLayer.Controller _ j).1 from rfl, F.profile_new]
      exact cut_mem F.bot_mem _ _
    exact grid_short j X hh
  · obtain ⟨e, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile sem j X occ)
      j hj hA d he
    rw [source_old]
    apply profile_short

theorem exists_owner_capped_lift (hinj : Function.Injective occ) :
    CanonicalOwnerLift.Capped sem (rows sem j X occ hj hA hproper hg) (oldTarget sem j X occ hj hA hg) := by
  refine CanonicalOwnerLift.of_layer (data sem j X occ hj hA hproper hg) occ
    (SeparatedSourceLayerCarrier.controllerEquiv D (Profile sem j X occ) j hj hA
      (SeparatedSourceLayerCarrier.separated_of_proper D j hproper))
    (oldTarget sem j X occ hj hA hg) hg (oldTarget_grade sem j X occ hj hA hg)
    (source_short sem j X occ hj hA hproper hg)
    (source_old sem j X occ hj hA hproper hg) ?_
  intro a v B hv hvt hB hvg
  obtain ⟨w, hw, hread, hcap⟩ := CanonicalFieldPrefix.exists_boundary_section
    sem j X occ hj hA hproper hg hinj a hv hvt hB hvg
  exact ⟨w, hw.toBelow _, hread, hcap⟩

end

end VaughtConjecture.Knight.CanonicalFieldOwnerLift
