/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.GradeCutBoundary

/-! # Coding from finite canonical fields and supported orbits

Shortness alone does not bound the ordinal block. These lemmas use the
actual coded field inventory and grid, and retain coding under replacement.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalCodingSupport
open Transform Value ExtOrd PairedSlotComparison SourcePrefixRows
noncomputable section

theorem replacement {k i} {x} (hx : IsCodedLabel k x) (hi : i ≤ k) :
    IsCodedLabel k (extVisibilityReplace x k i) := by
  rcases hx with rfl | ⟨b, j, hj, rfl⟩
  · solve_by_elim
  · by_cases h : j < k
    · rw [extVisibilityReplace_ofOrd, visibilityReplace,
        ite_eq_left (by rwa [finitePart_mul_add]), ordinalReplace, limitPart_mul_add]
      grind [IsCodedLabel]
    · rw [extVisibilityReplace_of_le_finitePart (by
        rw [finitePart_mul_add]; omega)]
      grind [IsCodedLabel]

theorem supported {X : Type*} {k} {G} {p : X → ExtOrd}
    (hG : ∀ x ∈ G, IsCodedLabel k x) (hp : ∀ d, IsCodedLabel k (p d))
    {x} (hx : OrbitPrefixSupport.Supported k G p x) : IsCodedLabel k x := by
  rcases hx with rfl | hx | ⟨d, i, hi, rfl⟩
  · solve_by_elim
  · simp_all
  simp_all [replacement]

theorem grid k B {x} (hx : x ∈ sourceGrid k B) : IsCodedLabel k x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · solve_by_elim
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hx
    grind [IsCodedLabel]

theorem field {ι X : Type*} [DecidableEq ι] [Fintype X]
    {A : Finset ι} {D : CellScheme A} sem k (occ : Cell D → X)
    (q : CanonicalFieldLayer.Profile sem k X occ) d : IsCodedLabel k (q.val d) := by
  rcases mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded X k q.property.2 d)
    with hb | ⟨b, i, _, hi, he⟩
  · solve_by_elim
  grind [IsCodedLabel, CanonicalFieldLayer.Profile]

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-- Coding transport over an appended layer uses the actual inherited row
equivalences; no consistency or catalogue equivalence is substituted. -/
theorem layer D (Q : Type*) [Fintype Q]
    k (hk : 0 < k) (hA : k ≤ A.card)
    (hs : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))
    (sem : Semantics D) (out : Semantics (SourceLayerCarrier.scheme D Q k hk hA))
    (hc : sem.IsCoded)
    (hold : ∀ c d, out.E (SourceLayerCarrier.toCell D Q k hk hA (.inl c))
      (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)
    (hnew : ∀ q d, IsCodedLabel k
      (out.E (SourceLayerCarrier.toCell D Q k hk hA (.inr q)) d)) : out.IsCoded := by
  intro c d
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration D Q k hk hA).surjective c
  change IsCodedLabel ((SourceLayerCarrier.scheme D Q k hk hA).grade
    (SourceLayerCarrier.toCell D Q k hk hA x))
    (out.E (SourceLayerCarrier.toCell D Q k hk hA x) d)
  rw [CellScheme.grade, SourceLayerCarrier.cell_toCell]
  cases x with
  | inl c =>
    obtain ⟨e, rfl⟩ := (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c).surjective d
    rw [hold]
    solve_by_elim
  | inr q => solve_by_elim

end
end VaughtConjecture.Knight.CanonicalCodingSupport
