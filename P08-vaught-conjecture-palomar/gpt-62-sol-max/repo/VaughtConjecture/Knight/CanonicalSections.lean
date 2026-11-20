/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift
public import VaughtConjecture.Knight.CanonicalProperSupply

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalSections

open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift

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

/-- Every lawful whole OLD boundary extends, with arbitrary proper values
and literal top. This supplies sections, not agreement with an ambient. -/
theorem exists_whole {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ r : target M → ExtOrd,
      RespectsSemanticsBelow (rows M) (A, k) r ∧
      ∀ d, r (oldTarget M d) = p d := by
  obtain ⟨r, hr, hread⟩ := (hp.toBelow (A, k)).supply_from_proper (fun d => oldTarget M d.1) (by
    intro v hv ht
    refine ⟨fun d => sectionOf M hv ht ∅ ⊤ d.1,
      (section_lawful M hv ht (by simp) (extVisibilityReplace_top k k)).toBelow _, ?_⟩
    exact fun d => section_boundary M hv ht (by simp) (extVisibilityReplace_top k k) d.1)
  exact ⟨r, hr, fun d => hread ⟨d, D.scope_subset d, hg d⟩⟩

/-- Bottom-cap supply from a proper prescribed face uses only the two old
face clauses. Empty prescribed domains require no owner or positive label. -/
theorem exists_section {I : Finset ι × ℕ} (W : CutCover sem I k)
    {p : D.below I → ExtOrd} (hp : RespectsSemanticsBelow sem I p) :
    ∃ r : target M → ExtOrd,
      RespectsSemanticsBelow (rows M) (A, k) r ∧
      ∀ d : D.below I, r (oldTarget M d.1) = p d := by
  obtain ⟨b, hb, hread⟩ := W.section_of hg hp
  grind [exists_whole]

end

end VaughtConjecture.Knight.CanonicalSections
