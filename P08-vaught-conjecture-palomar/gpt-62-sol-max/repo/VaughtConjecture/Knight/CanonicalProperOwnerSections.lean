/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalProperOwnerLayer
public import VaughtConjecture.Knight.CanonicalPairLocalSections
public import VaughtConjecture.Knight.ScopedSourcePrefixAmbient
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.AlignedCutEncoding
public import VaughtConjecture.Knight.HighLayerBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalProperOwnerSections

open Transform Value ExtOrd CanonicalProperOwnerLayer

open SharpWitnessComposition CoatomBoundaryExtension PairedSlotEncoding

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem lower_full_short (c : Cell (lowerScheme sem k h2k hkA))
    (hc : (lowerScheme sem k h2k hkA).scope c = A)
    (d : (lowerScheme sem k h2k hkA).below ((lowerScheme sem k h2k hkA).cell c)) :
    Short ((lowerScheme sem k h2k hkA).grade c) ((lowerSem sem k h2k hkA hp).E c d) :=
  CanonicalPairLocalSections.full_source_short sem (two_le k h2k hkA) hp c hc d

end

end VaughtConjecture.Knight.CanonicalProperOwnerSections
