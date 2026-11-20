/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.CanonicalPrefixDecoding

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursivePrefix

open Transform Value ExtOrd SourcePrefixRows CanonicalRecursiveSuccessorRows

open CanonicalPairedInverse PairedSlotEncoding

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

/-- The repair is an old-boundary input; its whole recursive extension,
supported inverse and all auxiliary source-cap equations are constructed. -/
theorem exists_section
    (a : Profile sem n)
    {p : Cell D → ExtOrd}
    (hpr : RespectsSemanticsBelow sem (A, (n + 3)) (fun d => p d.1)) (ht : ∀ d, p d ≠ ⊤)
    {B : ℕ} (hB : B ≤ 2 * Fintype.card (Cell D) + 1)
    (hag : ∀ d, min (a.val d) (CanonicalPairedInverse.grid (n + 3) B) =
      min (p d) (CanonicalPairedInverse.grid (n + 3) B)) :
    ∃ r : Cell (carrier sem n hA) → ExtOrd,
      RespectsSemanticsBelow (rows S) (A, (n + 3)) (fun d => r d.1) ∧
      (∀ d, r (boundary sem n hA d) = p d) ∧
      (∀ d, min (r d) (CanonicalPairedInverse.grid (n + 3) B) =
        min (source S a d) (CanonicalPairedInverse.grid (n + 3) B)) := by
  let F := data S
  let b := CanonicalRecursiveInventory.encode sem n hpr ht
  obtain ⟨δ, hr, hread, hc⟩ := CanonicalPrefixDecoding.exists_decoder a.property.2 ht hB hag
    (source S a) (source S b)
    (F.profile_respects (controller sem n hA a)) (F.profile_respects (controller sem n hA b))
    (source_supported S a) (source_agreement_all S b a)
  refine ⟨_, hr, fun d => ?_, hc⟩
  exact (congrArg δ (source_boundary S b d)).trans (hread d)

end

end VaughtConjecture.Knight.CanonicalRecursivePrefix
