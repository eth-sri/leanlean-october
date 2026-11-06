/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorOrdinaryLift
public import VaughtConjecture.Knight.CanonicalOneCoatom
public import VaughtConjecture.Knight.OrdinaryScopeMute

/-! # A constructed ordinary scope operator at every positive height

The output record below is populated by `build`, from the actual two legal
input facets. It is not a new induction hypothesis asserting future completion.
The grade-one, grade-two and recursive cases use their checked, unchanged rows.
The mute completion is separate, so no active maximal apex is introduced.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryScopeOperator
open AmalgamationPlan Transform Value ExtOrd SourcePrefixRows OrbitPrefixSupport
open WholeDonorOrdinarySections WholeDonorOrdinaryLift
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Receipts for the actual rows and specified renderer returned by `build`. -/
structure Core (sem : Semantics D) (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  plan : carrier.plan = D.plan
  original : Cell D ↪o Cell carrier
  index : ∀ d, carrier.cell (original d) = D.cell d
  coverage : ∀ d, (∃ c, original c = d) ∨ carrier.scope d = A
  row : ∀ (c : Cell D) (d : D.below (D.cell c)),
    rows.E (original c) ⟨original d.1, by rw [index, index]; exact d.2⟩ = sem.E c d
  consistent : rows.IsConsistent
  coded : rows.IsCoded
  bountiful : rows.IsBountiful
  grade : ∀ d, carrier.grade d ≤ k
  complete : ∀ J ∈ Plan.gradedPlan carrier.plan, J.2 ≤ k → ∃ d, carrier.cell d = J
  short : ∀ c, carrier.scope c = A → ∀ d,
    SharpWitnessComposition.Short (carrier.grade c) (rows.E c d)
  render : ∀ {p : Cell D → ExtOrd}, RespectsSemantics sem p → (∀ d, p d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  readback : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → ∀ d, render hp ht G θ (original d) = p d
  lawful : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, (∀ z ∈ G, SelfVis k z) → SelfVis k θ → RespectsSemantics rows (render hp ht G θ)
  bound : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G θ}, SelfVis k θ → (∀ d, p d ≤ θ) → ∀ d, render hp ht G θ d ≤ θ
  support : ∀ {p} (hp : RespectsSemantics sem p) (ht : ∀ d, p d ≠ ⊤)
    {G : Finset ExtOrd} {θ : ExtOrd} {K : ℕ}, k ≤ K → θ ∈ G → ∀ d,
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p (render hp ht G θ d)
  agreement : ∀ {p q} (hp : RespectsSemantics sem p) (htp : ∀ d, p d ≠ ⊤)
    (hq : RespectsSemantics sem q) (htq : ∀ d, q d ≠ ⊤) {G θ γ},
    (∀ z ∈ G, SelfVis k z) → SelfVis k θ → γ ∈ G → γ ≤ θ → Agree p q γ →
    Agree (render hp htp G θ) (render hq htq G θ) γ

variable {B C : Finset ι} {R : Finset (Finset ι)} {m nL nR : ℕ}

namespace Core
variable {sem : Semantics D} {k : ℕ} (S : Core sem k)
variable (hk : 0 < k) (hcard : A.card = k + 1)

/-- Close this scope with its actual zero highest row. The selected renderer
is extended by bottom; no original or earlier auxiliary value is recoded. -/
def finish (S : Core sem k) (hk : 0 < k) (hcard : A.card = k + 1) : Core sem (k + 1) where
  carrier := OrdinaryScopeMute.carrier S.carrier k (k + 1) (by omega) hcard.ge
  rows := OrdinaryScopeMute.rows S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
  plan := S.plan
  original := S.original.trans (OrderEmbedding.ofStrictMono
    (OrdinaryScopeMute.old S.carrier k (k + 1) (by omega) hcard.ge)
    (SourceLayerCarrier.old_order _ _ _ _ _))
  index d := (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge
    (S.original d)).trans (S.index d)
  coverage d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with
      ⟨c, rfl⟩ | rfl
    · rcases S.coverage c with ⟨a, rfl⟩ | ha
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ((congrArg Prod.fst
          (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).trans ha)
    · exact Or.inr (congrArg Prod.fst
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge))
  row c d := (OrdinaryScopeMute.inherited_row S.carrier S.rows k (k + 1) S.grade
    (by omega) hcard.ge (S.original c)
      ⟨S.original d.1, by rw [S.index, S.index]; exact d.2⟩).trans (S.row c d)
  consistent := OrdinaryScopeMute.consistent _ _ _ _ _ _ _ S.consistent
  coded := OrdinaryScopeMute.coded _ _ _ _ _ _ _ S.coded
  bountiful := OrdinaryScopeMute.bountiful _ _ _ _ _ _ _ hk S.bountiful
  grade d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge d with
      ⟨c, rfl⟩ | rfl
    · exact (congrArg Prod.snd
        (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).le.trans
          ((S.grade c).trans (Nat.le_succ k))
    · exact (congrArg Prod.snd
        (MaximalFullLayer.apex_index S.carrier k (k + 1) (by omega) hcard.ge)).le
  complete J hJ _ := OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega)
    hcard.ge hcard rfl S.complete J hJ
  short c hc d := by
    rcases OrdinaryScopeMute.covered S.carrier k (k + 1) (by omega) hcard.ge c with
      ⟨c, rfl⟩ | rfl
    · apply OrdinaryScopeMute.inherited_short S.carrier S.rows k (k + 1) S.grade
        (by omega) hcard.ge c
      apply S.short c
      exact (congrArg Prod.fst
        (MaximalFullLayer.old_index S.carrier k (k + 1) (by omega) hcard.ge c)).symm.trans hc
    · have h := OrdinaryScopeMute.apex_short S.carrier S.rows k (k + 1) S.grade
        (by omega) hcard.ge d
      exact (congrArg (fun j => SharpWitnessComposition.Short j _)
        (congrArg Prod.snd (MaximalFullLayer.apex_index S.carrier k (k + 1)
          (by omega) hcard.ge))).mpr h
  render := fun hp ht G θ => OrdinaryScopeMute.render S.carrier k (k + 1)
    (by omega) hcard.ge (S.render hp ht G θ)
  readback := by
    intro p hp ht G θ hG hθ d
    exact (OrdinaryScopeMute.render_old S.carrier k (k + 1) (by omega) hcard.ge _ _).trans
      (S.readback hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) d)
  lawful := by
    intro p hp ht G θ hG hθ
    exact OrdinaryScopeMute.render_lawful S.carrier S.rows k (k + 1) S.grade (by omega) hcard.ge
      (S.lawful hp ht (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)))
  bound := by
    intro p hp ht G θ hθ hb
    exact OrdinaryScopeMute.render_bound S.carrier k (k + 1)
      (by omega) hcard.ge (S.bound hp ht (selfVis_mono hθ (Nat.le_succ k)) hb)
  support := by
    intro p hp ht G θ K hK hθ
    exact OrdinaryScopeMute.render_supported S.carrier k (k + 1)
      (by omega) hcard.ge (S.support hp ht ((Nat.le_succ k).trans hK) hθ)
  agreement := by
    intro p q hp ht hq htq G θ γ hG hθ hγ hγθ hag
    exact OrdinaryScopeMute.render_agreement S.carrier k (k + 1) (by omega) hcard.ge
      (S.agreement hp ht hq htq (fun z hz => selfVis_mono (hG z hz) (Nat.le_succ k))
        (selfVis_mono hθ (Nat.le_succ k)) hγ hγθ hag)

theorem finish_complete : (S.finish hk hcard).carrier.IsComplete :=
  OrdinaryScopeMute.complete_last S.carrier k (k + 1) (by omega) hcard.ge hcard rfl S.complete

end Core

end
end VaughtConjecture.Knight.OrdinaryScopeOperator
