/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers
public import VaughtConjecture.Knight.CanonicalPrefixDecoding

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalMixedPrefix

open Transform Value ExtOrd SourcePrefixRows CanonicalMixedGradeLayers

open CanonicalPairedInverse PairedSlotEncoding

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

/-- No supported inverse, coded completion, or output lawfulness is assumed.
The proper repaired old boundary is the input produced by ordinary old-face
amalgamation. Every actual controller coordinate retains its source cap. -/
theorem exists_section
    (a : CanonicalFieldLayer.Profile sem k (Cell D) id)
    {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val d) (grid k B) = min (p d) (grid k B)) :
    ∃ r : Cell (scheme M) → ExtOrd,
      RespectsSemantics (rows M) r ∧
      (∀ d, r (oldCell M (lowerOld M d)) = p d) ∧
      (∀ d, min (r d) (grid k B) =
        min (source M a d) (grid k B)) := by
  let F := data M
  let b := normalized M hp ht
  obtain ⟨δ, hr, hread, hc⟩ := CanonicalPrefixDecoding.exists_decoder a.property.2 ht hB hag
    (source M a) (source M b)
    (F.profile_respects (controller M a)) (F.profile_respects (controller M b))
    (source_supported M a) (source_agreement M b a)
  refine ⟨_, hr.toRespects (fun d => ⟨(scheme M).scope_subset d, max_grade M d⟩), fun d => ?_, hc⟩
  exact (congrArg δ (source_boundary M b d)).trans (hread d)

end

end VaughtConjecture.Knight.CanonicalMixedPrefix
