/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorAdmission
public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.LadderScalarRendering
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.AmbientGradeCharts

@[expose] public section

namespace VaughtConjecture.Knight.ReceivingCatalogueRanks

open Transform Value ExtOrd CappedDonor CappedDonor.Ref

open LadderScalarRendering

noncomputable section

/-- A bottom-preserving round trip induces an injection of occupied values. -/
theorem values_transport {X : Type*} [Fintype X] (p : X → ExtOrd) {f g : ExtOrd → ExtOrd}
    (hf : f ⊥ = ⊥) (hg : g ⊥ = ⊥) (hinv : ∀ d, g (f (p d)) = p d) :
    values (f ∘ p) = (values p).image f ∧ Set.InjOn f (values p : Set ExtOrd) := by
  have hb (d : X) : f (p d) ≠ ⊥ ↔ p d ≠ ⊥ :=
    ⟨fun h hd => h (hd ▸ hf), fun h hd => h ((hinv d).symm.trans ((congrArg g hd).trans hg))⟩
  constructor
  · ext y
    simp only [Finset.mem_image, mem_values, Function.comp_apply]
    constructor
    · rintro ⟨hy, d, rfl⟩
      exact ⟨p d, ⟨(hb d).mp hy, d, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨hx, d, rfl⟩, rfl⟩
      exact ⟨(hb d).mpr hx, d, rfl⟩
  · intro x hx y hy h
    obtain ⟨_, d, rfl⟩ := mem_values.mp hx
    obtain ⟨_, e, rfl⟩ := mem_values.mp hy
    rw [← hinv d, ← hinv e, h]

/-- A tracked monotone encoding with a monotone inverse preserves finite ranks. -/
theorem fieldRank_of_leftInverse {X : Type*} [Fintype X] (p : X → ExtOrd)
    {f g : ExtOrd → ExtOrd} (hf : Monotone f) (hg : Monotone g)
    (hfbot : f ⊥ = ⊥) (hgbot : g ⊥ = ⊥)
    (hinv : ∀ d, g (f (p d)) = p d) (d : X) :
    fieldRank (fun e => f (p e)) d = fieldRank p d := by
  classical
  obtain ⟨he, hinj⟩ := values_transport p hfbot hgbot hinv
  change fieldRank (f ∘ p) d = fieldRank p d
  unfold fieldRank LadderScalarRendering.rank
  rw [he, Finset.filter_image, Finset.card_image_of_injOn
    (hinj.mono (Finset.coe_subset.mpr (Finset.filter_subset ..)))]
  congr 1
  apply Finset.filter_congr
  rintro x hx
  obtain ⟨_, e, rfl⟩ := mem_values.mp hx
  exact ⟨fun h => by simpa only [Function.comp_apply, hinv] using hg h, fun h => hf h⟩

/-- Paired-slot normalization preserves all ranks, not just the bottom pattern. -/
theorem fieldRank_normalize {X : Type*} [Fintype X] (j : ℕ) (p : X → ExtOrd)
    (hp : ∀ d, p d ≠ ⊤) (d : X) :
    fieldRank (PairedSlotEncoding.normalize j p) d = fieldRank p d := by
  let f := PairedSlotIncoming.encoder j (PairedSlotEncoding.values p)
  let g := PairedSlotDecoder.decode j (PairedSlotEncoding.values p) ∅ ⊥
  have hf := PairedSlotIncoming.encoder_bounded j (PairedSlotEncoding.values p)
  have hg : Witness (gTop j) g :=
    PairedSlotDecoder.decode_witness (by simp) (selfVis_bot j)
  have hinv (e : X) : g (f (p e)) = p e := by
    dsimp only [f, g]
    rw [PairedSlotIncoming.encoder_profile]
    exact PairedSlotDecoder.decode_normalize (by simp) (selfVis_bot j) hp e
  have h := fieldRank_of_leftInverse p hf.mono hg.mono hf.bot hg.bot hinv d
  simpa [f, PairedSlotIncoming.encoder_profile] using h

end

end VaughtConjecture.Knight.ReceivingCatalogueRanks
