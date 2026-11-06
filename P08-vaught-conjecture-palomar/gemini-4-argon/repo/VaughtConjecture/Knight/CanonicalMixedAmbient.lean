/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalMixedGradeLayers
public import VaughtConjecture.Knight.SourcePrefixAmbient

/-! # Arbitrary ambients on the constructed two-grade carrier

Availability on the new canonical rows chooses an actual canonical upper source
profile. Its clipped locality
witness reads the complete ambient cap vector, including both controller
layers. No hypothesis identifies the ambient with a constructed section.
The first reaching grid cut is produced, but prescribed-owner retuning at
that cut is not asserted here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalMixedAmbient

open Transform Value ExtOrd SourcePrefixRows CanonicalMixedGradeLayers

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (j : ℕ) (hj : 0 < j) (hjA : j ≤ A.card)
  (hproper : ∀ d : Cell D, D.scope d ≠ A)
  (k : ℕ) (hg : ∀ d : Cell D, D.grade d ≤ k)
  (hk : 0 < k) (hkA : k ≤ A.card) (hjk : j < k)

abbrev target := (scheme sem j hj hjA k hk hkA).below (A, k)

theorem exists_capped_source {q : target sem j hj hjA k hk hkA → ExtOrd}
    (hq : RespectsSemanticsBelow (rows sem j hj hjA hproper k hg hk hkA hjk) (A, k) q)
    (d : target sem j hj hjA k hk hkA)
    (hd : (scheme sem j hj hjA k hk hkA).grade d.1 = k)
    {γ : ExtOrd} (hγ : SelfVis k γ) (hactive : γ ≤ q d) :
    ∃ (a : CanonicalFieldLayer.Profile sem k (Cell D) id) (τ : ExtOrd → ExtOrd),
      Witness (gTop k) τ ∧ (∀ x, τ x ≤ γ) ∧
      ∀ x : target sem j hj hjA k hk hkA,
        τ (source sem j hj hjA hproper k hg hk hkA hjk a x.1) = min (q x) γ := by
  obtain ⟨c, τ, hτ, hbound, hread⟩ := SourcePrefixAmbient.exists_active_source
    (data sem j hj hjA hproper k hg hk hkA hjk)
    (controller sem j hj hjA k hk hkA (CanonicalFieldLayer.encode sem k (Cell D) id hg
      (p := fun _ => ⊥) (RespectsSemantics.bot sem) (fun _ => bot_ne_top)))
    hq d hd hγ hactive
  have ha : controller sem j hj hjA k hk hkA (member sem j hj hjA hproper k hk hkA hjk c) = c :=
    (SeparatedSourceLayerCarrier.controllerEquiv (lowerScheme sem j hj hjA)
      (CanonicalFieldLayer.Profile sem k (Cell D) id) k hk hkA
      (lower_separated sem j hj hjA hproper k hjk)).apply_symm_apply c
  refine ⟨member sem j hj hjA hproper k hk hkA hjk c, τ, hτ, hbound, fun x => ?_⟩
  change τ ((data sem j hj hjA hproper k hg hk hkA hjk).profile
    (controller sem j hj hjA k hk hkA (member sem j hj hjA hproper k hk hkA hjk c)) x.1) = _
  rw [ha]
  exact hread x
