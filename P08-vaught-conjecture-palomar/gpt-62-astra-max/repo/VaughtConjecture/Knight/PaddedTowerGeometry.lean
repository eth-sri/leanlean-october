/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerIteration
public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.SeparatedLayerFace

/-! # Coded rows and inherited faces throughout a padded tower -/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedTower.Layer
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison
open RecursiveRungRendering (grid ceiling)
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)]
variable {F : System D X Q} {k : ℕ} (P : Layer F k)

open AmalgamationPlan CoatomBoundaryExtension

def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows F.sem) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face D
    (RelativeLadderLayer.Point (X := X) (Q := Q 1))
    1 Nat.one_pos F.positive (RelativeLadderLayer.separated D
      F.proper) F.sem F.baseRows
    (RelativeLadderLayer.inherited_row D F.sem F.positive
      F.field (@F.values 1) F.proper) G hT
  exact {
    map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ T at hz
          rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }
open Step

theorem build_coded (hc : F.sem.IsCoded) (t : ℕ) (ht : t+1 ≤ A.card) : (build F t ht).rows.IsCoded := by
  induction t with
  | zero => exact RelativeLadderLayer.coded _ _ _ _ _ _ hc
  | succ t ih =>
    let L := build F t (by omega)
    apply CanonicalCodingSupport.layer L.carrier (Q (t+2)) (t+2) (Nat.succ_pos _) ht
      (L.separated (Nat.succ_pos _)) L.rows (Step.rows L (Nat.succ_pos _) ht) (ih _) (inherited_row L _ ht)
    intro a d
    have he := (data L (Nat.succ_pos _) ht).row_new (controller L ht a) d
    change IsCodedLabel _ ((data L _ ht).rows.E (controller L ht a).1 d)
    rw [he]
    apply CanonicalCodingSupport.supported (fun _ hz => CanonicalCodingSupport.grid _ _ hz) _
      (source_supported L (Nat.succ_pos _) ht a d.1)
    intro x
    rcases mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded X _ (F.canonical a) x)
      with hb | ⟨b,i,_, hi, he⟩
    · exact Or.inl hb
    · exact Or.inr ⟨b,i,hi,he⟩

end
end VaughtConjecture.Knight.PaddedTower.Layer
