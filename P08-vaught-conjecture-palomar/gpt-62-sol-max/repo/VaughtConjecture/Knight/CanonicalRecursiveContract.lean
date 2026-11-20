/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveInventory
public import VaughtConjecture.Knight.CanonicalPairLocalSections

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveContract

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

open SharpWitnessComposition

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

abbrev stageCarrier (sem : Semantics D) (n : ℕ) (hA : n + 2 ≤ A.card) :=
  CanonicalRecursiveInventory.scheme sem (n + 2) hA

abbrev stageBoundary (sem : Semantics D) (n : ℕ) (hA : n + 2 ≤ A.card) :=
  CanonicalRecursiveInventory.boundary sem (n + 2) hA

structure Stage (sem : Semantics D) (n : ℕ) (hA : n + 2 ≤ A.card) where
  rows : Semantics (stageCarrier sem n hA)
  consistent : sem.IsConsistent → rows.IsConsistent
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    rows.E (stageBoundary sem n hA c) ⟨stageBoundary sem n hA d.1, by
      rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
      exact d.2⟩ = sem.E c d
  full_short : ∀ c : Cell (stageCarrier sem n hA), (stageCarrier sem n hA).scope c = A →
    ∀ d : (stageCarrier sem n hA).below ((stageCarrier sem n hA).cell c),
      Short ((stageCarrier sem n hA).grade c) (rows.E c d)
  sectionOf : ∀ {K : ℕ}, n + 2 ≤ K → ∀ {p : Cell D → ExtOrd},
    RespectsSemanticsBelow sem (A, K) (fun d => p d.1) → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell (stageCarrier sem n hA) → ExtOrd
  section_boundary : ∀ {K} (hK : n + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 2) z) → SelfVis (n + 2) C → ∀ d,
      sectionOf hK (p := p) hpr ht G C (stageBoundary sem n hA d) = p d
  section_lawful : ∀ {K} (hK : n + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 2) z) → SelfVis (n + 2) C →
      RespectsSemanticsBelow rows (A, K) (fun d => sectionOf hK (p := p) hpr ht G C d.1)
  section_bound : ∀ {K} (hK : n + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    SelfVis (n + 2) C → (∀ d, p d ≤ C) → ∀ d, sectionOf hK (p := p) hpr ht G C d ≤ C
  section_supported : ∀ {K} (hK : n + 2 ≤ K) {p : Cell D → ExtOrd} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd} {L : ℕ},
    n + 2 ≤ L → C ∈ G → ∀ d,
      OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (sectionOf hK (p := p) hpr ht G C d)
  section_agreement : ∀ {K} (hK : n + 2 ≤ K) {p q : Cell D → ExtOrd}
    (hpr) (htp) (hqr) (htq) {G : Finset ExtOrd} {C h : ExtOrd},
    (∀ z ∈ G, SelfVis (n + 2) z) → SelfVis (n + 2) C → h ∈ G → h ≤ C →
    Agree p q h → Agree (sectionOf hK (p := p) hpr htp G C)
      (sectionOf hK (p := q) hqr htq G C) h

abbrev carrier (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  CanonicalRecursiveInventory.scheme sem (n + 3) hA

abbrev boundary (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  CanonicalRecursiveInventory.boundary sem (n + 3) hA

abbrev State (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) :=
  Stage sem (n + 1) hA

/-- A successor uses a single proper boundary and its preceding stage. -/
structure Step (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card) where
  proper : ∀ d : Cell D, D.scope d ≠ A
  prev : Stage sem n (Nat.le_of_succ_le hA)

/-- The two-grade section operator is the initial stage of the recursive contract. -/
def base (sem : Semantics D) (hA : 2 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A) :
    Stage sem 0 hA where
  rows := CanonicalPairLocalSections.semantics sem hA hp
  consistent := CanonicalPairBoundary.consistent sem 1 2 (by decide)
    (CanonicalPairLocalSections.one_le hA) (by decide) hA hp (by decide)
  row := GradeCutPairRows.old_row D _ _ 1 2 (by decide)
    (CanonicalPairLocalSections.one_le hA) (by decide) hA hp (by decide) sem
    (CanonicalPairLocalSections.smallRows sem hA hp)
  full_short := CanonicalPairLocalSections.full_source_short sem hA hp
  sectionOf := CanonicalPairLocalSections.sectionOf sem hA hp
  section_boundary := fun {_} hK {_} hpr ht {_ _} _ _ =>
    CanonicalPairLocalSections.section_old sem hA hp hK hpr ht
  section_lawful := CanonicalPairLocalSections.section_lawful sem hA hp
  section_bound := CanonicalPairLocalSections.section_bound sem hA hp
  section_supported := CanonicalPairLocalSections.section_supported sem hA hp
  section_agreement := fun {_} hK {_ _} hpr htp hqr htq =>
    CanonicalPairLocalSections.section_agreement sem hA hp hK hpr htp hqr htq

end

end VaughtConjecture.Knight.CanonicalRecursiveContract
