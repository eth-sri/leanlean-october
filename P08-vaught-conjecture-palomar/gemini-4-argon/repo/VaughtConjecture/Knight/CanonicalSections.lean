/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedOwnerLift

/-! # Independent section supply on the canonical two-layer carrier

First glue the two old faces at bottom cap. Normalize the resulting lawful
boundary with a bottom-reflecting finite encoder, construct its proper-profile
section, and decode. Literal top is restored by the outer decoder; it is not
inserted into the fixed proper-profile catalogue. No output lift is used.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSections
open Transform Value ExtOrd CanonicalMixedGradeLayers CanonicalMixedOwnerLift CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

/-- Every lawful whole OLD boundary extends, with arbitrary proper values
and literal top. This supplies sections, not agreement with an ambient. -/
theorem exists_whole {p : Cell D → ExtOrd} (hp : RespectsSemantics sem p) :
    ∃ r : CanonicalMixedAmbient.target sem j hj hjA k hk hkA → ExtOrd,
      RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) r ∧
      ∀ d, r (oldTarget sem j hj hjA hproper k hg hk hkA hjk d) = p d := by
  obtain ⟨S, v, hv, ht, hdecode⟩ := hp.exists_coded_representative hg
  let s := sectionOf sem j hj hjA hproper k hg hk hkA hjk hv ht ∅ ⊤
  have hs := section_lawful sem j hj hjA hproper k hg hk hkA hjk hv ht
    (G := ∅) (by simp) (extVisibilityReplace_top k k)
  refine ⟨fun d => canonicalDecoder S k (s d.1),
    (hs.toBelow (A, k)).decoded S (fun d => d.2.2), fun d =>
    (congrArg (canonicalDecoder S k) (section_boundary sem j hj hjA hproper k hg hk hkA hjk hv ht
      (G := ∅) (by simp) (extVisibilityReplace_top k k) d)).trans (hdecode d)⟩

