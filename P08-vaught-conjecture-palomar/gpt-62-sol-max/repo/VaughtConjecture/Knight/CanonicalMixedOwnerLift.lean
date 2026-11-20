/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedPrefix
public import VaughtConjecture.Knight.CanonicalOwnerLift

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalMixedOwnerLift

open Transform Value ExtOrd SharpWitnessComposition CanonicalMixedGradeLayers

open CoatomBoundaryExtension

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (M : Frame D)

local notation "sem" => M.sem
local notation "j" => M.lower
local notation "k" => M.upper
local notation "hj" => M.pos
local notation "hjA" => M.lower_card
local notation "hk" => M.upper_pos
local notation "hkA" => M.height
local notation "hjk" => M.strict
local notation "hg" => M.grade
local notation "hproper" => M.proper

abbrev target := (scheme M).below (A, k)

abbrev oldTarget (d : Cell D) : target M :=
  ScopedSourcePrefixAmbient.atGrade (oldCell M (lowerOld M d))
    (max_grade M _)

theorem oldTarget_grade (d : Cell D) :
    (scheme M).grade
      (oldTarget M d).1 = D.grade d := by
  change (SourceLayerCarrier.scheme _ _ _ _ _).grade
    (SourceLayerCarrier.toCell _ _ _ _ _ (.inl
      (SourceLayerCarrier.toCell _ _ _ _ _ (.inl d)))) = _
  simp only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]

theorem exists_owner_capped_lift :
    CanonicalOwnerLift.Capped sem (rows M)
      (oldTarget M) := by
  refine CanonicalOwnerLift.of_layer (data M) id
    (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme M)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
      (lower_separated M))
    (oldTarget M) hg (oldTarget_grade M)
    (source_short M)
    (source_boundary M) ?_
  intro a v B hv hvt hB hvg
  obtain ⟨w, hw, hread, hcap⟩ := CanonicalMixedPrefix.exists_section M a hv hvt hB hvg
  exact ⟨w, hw.toBelow _, hread, hcap⟩

end

end VaughtConjecture.Knight.CanonicalMixedOwnerLift
