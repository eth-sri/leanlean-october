/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveInventory
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer

/-! # The recursive selected-section contract

The original proper boundary is fixed. Stage `n` here means the actual
recursive carrier through grade `n`. The contract is a semantic induction
invariant, not a hypothesis of future completion or bountifulness.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveContract
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
open SharpWitnessComposition
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

abbrev carrier (sem : Semantics D) (n : ℕ) (hA : n ≤ A.card) :=
  CanonicalRecursiveInventory.scheme sem n hA
abbrev boundary (sem : Semantics D) (n : ℕ) (hA : n ≤ A.card) :=
  CanonicalRecursiveInventory.boundary sem n hA

structure State (sem : Semantics D) (n : ℕ) (hA : n ≤ A.card) where
  rows : Semantics (carrier sem n hA)
  consistent : sem.IsConsistent → rows.IsConsistent
  proper_lawful : ∀ {J : Finset ι × ℕ}, ¬ A ⊆ J.1 →
    ∀ {p : D.Labelling}, RespectsSemanticsBelow sem J (fun d => p d.1) →
    ∀ {r : (carrier sem n hA).Labelling},
      (∀ d, r (boundary sem n hA d) = p d) →
      RespectsSemanticsBelow rows J (fun d => r d.1)
  full_short : ∀ c : Cell (carrier sem n hA), (carrier sem n hA).scope c = A →
    ∀ d : (carrier sem n hA).RowDomain c,
      Short ((carrier sem n hA).grade c) (rows.E c d)
  sectionOf : ∀ {K : ℕ}, n ≤ K → ∀ {p : D.Labelling},
    RespectsSemanticsBelow sem (A, K) (fun d => p d.1) → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → (carrier sem n hA).Labelling
  section_boundary : ∀ {K} (hK : n ≤ K) {p : D.Labelling} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis n z) → SelfVis n C → ∀ d,
      sectionOf hK (p := p) hpr ht G C (boundary sem n hA d) = p d
  section_lawful : ∀ {K} (hK : n ≤ K) {p : D.Labelling} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    (∀ z ∈ G, SelfVis n z) → SelfVis n C →
      RespectsSemanticsBelow rows (A, K) (fun d => sectionOf hK (p := p) hpr ht G C d.1)
  section_bound : ∀ {K} (hK : n ≤ K) {p : D.Labelling} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd},
    SelfVis n C → (∀ d, p d ≤ C) → ∀ d, sectionOf hK (p := p) hpr ht G C d ≤ C
  section_supported : ∀ {K} (hK : n ≤ K) {p : D.Labelling} (hpr) (ht)
    {G : Finset ExtOrd} {C : ExtOrd} {L : ℕ},
    n ≤ L → C ∈ G → ∀ d,
      OrbitPrefixSupport.Supported L (G : Set ExtOrd) p (sectionOf hK (p := p) hpr ht G C d)
  section_agreement : ∀ {K} (hK : n ≤ K) {p q : D.Labelling}
    (hpr) (htp) (hqr) (htq) {G : Finset ExtOrd} {C h : ExtOrd},
    (∀ z ∈ G, SelfVis n z) → SelfVis n C → h ∈ G → h ≤ C →
    Agree p q h → Agree (sectionOf hK (p := p) hpr htp G C)
      (sectionOf hK (p := q) hqr htq G C) h

/-- Before installing any full-scope cells, a section is its own extension. -/
def seed (sem : Semantics D) (hA : 0 ≤ A.card) (hp : D.AvoidsScope A) :
    State sem 0 hA where
  rows := sem
  consistent := id
  proper_lawful := by
    intro J _ p hpr r hr
    have he : r = p := funext hr
    change RespectsSemanticsBelow sem J (fun d => r d.1)
    rw [he]
    exact hpr
  full_short c hc := (hp c hc).elim
  sectionOf := fun {_} _ {p} _ _ _ _ => p
  section_boundary := by intros; rfl
  section_lawful := by intros; assumption
  section_bound := by intros; solve_by_elim
  section_supported := by intros; apply PairedSlotDecoder.supported_boundary
  section_agreement := by intros; assumption

end
end VaughtConjecture.Knight.CanonicalRecursiveContract
