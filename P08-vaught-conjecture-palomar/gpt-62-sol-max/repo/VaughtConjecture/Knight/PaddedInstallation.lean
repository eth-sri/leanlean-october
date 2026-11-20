/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedInitial
public import VaughtConjecture.Knight.PaddedIteration
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.CanonicalCodingSupport

@[expose] public section

namespace VaughtConjecture.Knight.Padded

open Transform Value ExtOrd AmalgamationPlan

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

namespace Spec

variable (K : Spec A)

theorem field_coded {j : ℕ} (a : K.Anchor j) (d : K.Field) :
    IsCodedLabel j (K.fields j a d) := by
  rcases mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded _ _ (K.canonical j a) d)
    with hb | ⟨b, i, _, hi, he⟩
  all_goals tauto

end Spec

namespace Layer

variable {K : Spec A} {k : ℕ} (P : Layer K k)

/-- Copies of proper faces are obtained from the base map, independently of the layer count. -/
def face {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows K.boundaryRows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows := by
  let L := SeparatedLayerFace.face K.boundary
    (RelativeLadderLayer.Point (X := K.Field) (Q := K.Anchor 1))
    1 Nat.one_pos K.one (RelativeLadderLayer.separated K.boundary K.proper)
    K.boundaryRows K.baseRows
    (RelativeLadderLayer.inherited_row K.boundary K.boundaryRows K.one
      K.field (K.fields 1) K.proper) G hT
  exact L.through ⟨P.baseMap, P.base_mono.injective⟩ P.base_index (fun z hz => by
    rcases P.cases z with h | ⟨hs, _, _⟩
    · exact h.imp (fun _ hd => hd.symm)
    · exact (hT (hs ▸ hz)).elim) P.base_row

theorem face_mono {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows K.boundaryRows) (hT : ¬ A ⊆ T) (hG : StrictMono G.map) :
    StrictMono (P.face G hT).map :=
  P.base_mono.comp ((SourceLayerCarrier.old_order _ _ _ _ _).comp hG)

theorem full_occupied (hk : 1 ≤ k) (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ∃ d, P.carrier.cell d = (A, j) := by
  let a := K.seed k hk
  obtain ⟨d, hd, _⟩ := P.ceiling_at le_rfl (K.state a) (K.state_admitted a) (K.state_proper a)
    (G := ∅) (H := ⊤) (by simp) (by simp [SelfVis]) (fun _ => le_top) j hj hjk
  exact ⟨d, hd⟩

end Layer

open CanonicalCodingSupport in
theorem attachment_coded {K : Spec A} {D : CellScheme A} {k : ℕ}
    (I : SourceAttachment D k K.Field (K.Anchor k)) (hfields : I.fields = K.fields k)
    (hc : I.sem.IsCoded) (hgrid : ∀ x ∈ I.grid, IsCodedLabel k x)
    (hsupp : ∀ a d, OrbitPrefixSupport.Supported k (I.grid : Set ExtOrd) (I.fields a) (I.source a d)) :
    I.rows.IsCoded := by
  apply layer D (K.Anchor k) k I.pos I.height I.separated I.sem I.rows hc I.inherited_row
  intro a d
  have hf : ∀ f, IsCodedLabel k (I.fields a f) := by rw [hfields]; exact K.field_coded a
  exact (congrArg (IsCodedLabel k) (I.data.row_new (I.controller a) d)).mpr
    (supported (fun _ h => hgrid _ h) hf (hsupp a d.1))

theorem build_coded {K : Spec A} (hs : K.boundaryRows.IsConsistent) (hc : K.boundaryRows.IsCoded)
    (t : ℕ) (ht : t + 2 ≤ A.card) : (build (Initial.layer K hs) t ht).rows.IsCoded := by
  induction t with
  | zero =>
    exact attachment_coded (Initial.input K) rfl
      (RelativeLadderLayer.coded K.boundary K.boundaryRows K.one K.field (K.fields 1) K.proper hc)
      (fun _ => CanonicalCodingSupport.grid _ _) (Initial.source_supported K)
  | succ t ih =>
    let P := build (Initial.layer K hs) t (by omega)
    exact attachment_coded (StepRows.attachment P (by omega) ht) rfl (ih (by omega))
      (fun _ => CanonicalCodingSupport.grid _ _) (StepRows.source_supported P (by omega) ht)

end

end VaughtConjecture.Knight.Padded
