/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorAdmission
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.LadderScalarRendering
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.PrivateRowFactorization
public import VaughtConjecture.Knight.CappedDonorLowHighNormalization
public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.PairedSlotComparison
public import VaughtConjecture.Knight.OrbitPrefixSupport

/-! # Rank preservation for downward catalogue normalization

The finite rank table depends on order, equality and bottom, not the numerical
choice of codes. A monotone encoder with a monotone left inverse on the tracked
field values preserves every field rank. Paired-slot normalization has such a
decoder for proper profiles, including profiles invisible at the lower grade.

Consequently each existing grade-two controller has an actual grade-one
catalogue image with identical ranks and identical lower ladder readings.
There is no converse: a newly repaired grade-one source is not thereby an
installed grade-two controller. No carrier or row is changed here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.ReceivingCatalogueRanks
open Transform Value ExtOrd CappedDonor CappedDonor.Ref LadderScalarRendering

/-- A tracked monotone encoding with a monotone inverse preserves finite ranks. -/
theorem fieldRank_of_leftInverse {X : Type*} [Fintype X] (p : X → ExtOrd)
    {f g : ExtOrd → ExtOrd} (hf : Monotone f) (hg : Monotone g)
    (hfbot : f ⊥ = ⊥) (hgbot : g ⊥ = ⊥)
    (hinv : ∀ d, g (f (p d)) = p d) (d : X) :
    fieldRank (fun e => f (p e)) d = fieldRank p d := by
  classical
  have hpos (e : X) : f (p e) ≠ ⊥ ↔ p e ≠ ⊥ := by
    constructor
    · intro h he
      exact h (he ▸ hfbot)
    · intro h he
      exact h ((hinv e).symm.trans ((congrArg g he).trans hgbot))
  have he : (values (fun e => f (p e))).filter (· ≤ f (p d)) =
      ((values p).filter (· ≤ p d)).image f := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyval, hyle⟩ := Finset.mem_filter.mp hy
      obtain ⟨hypos, e, rfl⟩ := mem_values.mp hyval
      refine Finset.mem_image.mpr ⟨p e,
        Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos e).mp hypos, e, rfl⟩, ?_⟩, rfl⟩
      simpa only [hinv] using hg hyle
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxval, hxle⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxpos, e, rfl⟩ := mem_values.mp hxval
      exact Finset.mem_filter.mpr ⟨mem_values.mpr ⟨(hpos e).mpr hxpos, e, rfl⟩, hf hxle⟩
  change ((values (fun e => f (p e))).filter (· ≤ f (p d))).card =
    ((values p).filter (· ≤ p d)).card
  rw [he]
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  obtain ⟨_, e, rfl⟩ := mem_values.mp (Finset.mem_filter.mp hx).1
  obtain ⟨_, e', rfl⟩ := mem_values.mp (Finset.mem_filter.mp hy).1
  simpa only [hinv] using congrArg g hxy

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
  simpa only [f, PairedSlotIncoming.encoder_profile] using h
