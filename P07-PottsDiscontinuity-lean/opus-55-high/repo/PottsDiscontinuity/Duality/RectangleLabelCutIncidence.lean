/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleLabelCut

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

noncomputable section

def rectangleCutDualEdgeOfBond (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) : RectangleDualEdgeCarrier a w h :=
  rectanglePrimalDualEdgeEquiv a w h (rectangleCutEdgeOfBond a w h b hs ht)

section
variable (a : LatticeVertex) (w h : ℕ) (σ : RectangleVertex a w h → Bool) (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h)
theorem rectangleCutEdgeOfBond_mem_cut_iff  :
    rectangleCutEdgeOfBond a w h b hs ht ∈ rectangleLabelCutEdgeCarrier a w h σ ↔
      σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
  simp [rectangleLabelCutEndpointStates,
    rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond]

theorem rectangleCutDualEdgeOfBond_adj_iff  :
    (rectangleLabelCutDualGraph a w h σ).Adj
      (rectangleDualEdgeSource a w h (rectangleCutDualEdgeOfBond a w h b hs ht))
      (rectangleDualEdgeTarget a w h (rectangleCutDualEdgeOfBond a w h b hs ht)) ↔
        σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ := by
  constructor
  · intro hadj
    obtain ⟨e, hcut, hpair⟩ :=
      (rectangleLabelCutDual_adj_iff a w h σ _ _).mp hadj
    have hpair' : (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond.toSym2 =
        e.crossingBond.toSym2 := by
      have h := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair
      tauto
    have hcross := LatticeBond.toSym2_injective hpair'
    have hbond : rectanglePrimalEdgeBond a w h e.primalEdge = b := by
      have hleft : primalBondOfDual
          (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond = b := by
        simp
        exact rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond a w h b hs ht
      simp_all
    aesop
  · intro hdiff
    have hcut := (rectangleCutEdgeOfBond_mem_cut_iff a w h σ b hs ht).2 hdiff
    apply (rectangleLabelCutDual_adj_iff a w h σ _ _).2
    aesop
end

section
variable (a : LatticeVertex) (w h : ℕ) (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h) (ht : b.target ∈ latticeRectangle a w h)
theorem rectangleCutDualEdgeOfBond_crossingBond  :
    (rectangleCutDualEdgeOfBond a w h b hs ht).crossingBond = dualBondOfPrimal b := by
  change rectangleCrossingDualBond a w h
    (rectangleCutEdgeOfBond a w h b hs ht) = dualBondOfPrimal b
  simp [rectangleCrossingDualBond, rectanglePrimalEdgeBond_of_rectangleCutEdgeOfBond]

theorem rectangleCutDualEdgeOfBond_source_val  :
    (rectangleDualEdgeSource a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase false := by
  simp [rectangleCutDualEdgeOfBond_crossingBond]

theorem rectangleCutDualEdgeOfBond_target_val  :
    (rectangleDualEdgeTarget a w h
      (rectangleCutDualEdgeOfBond a w h b hs ht)).val = b.faceBase true := by
  simp [rectangleCutDualEdgeOfBond_crossingBond]
end

theorem rectangleLabelCutDual_adj_iff_bond (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (u v : RectangleDualVertex a w h) :
    (rectangleLabelCutDualGraph a w h σ).Adj u v ↔
      ∃ b : LatticeBond, ∃ hs : b.source ∈ latticeRectangle a w h,
        ∃ ht : b.target ∈ latticeRectangle a w h,
          σ ⟨b.source, hs⟩ != σ ⟨b.target, ht⟩ ∧
            ((u.val = b.faceBase false ∧ v.val = b.faceBase true) ∨
              (u.val = b.faceBase true ∧ v.val = b.faceBase false)) := by
  constructor
  · intro hadj
    obtain ⟨e, hcut, hpair⟩ :=
      (rectangleLabelCutDual_adj_iff a w h σ u v).mp hadj
    let b := rectanglePrimalEdgeBond a w h e.primalEdge
    have hdiff : σ ⟨b.source, (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge |>.1)⟩ != σ ⟨b.target, (rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge |>.2)⟩ := by
      aesop
    have hcross : e.crossingBond = dualBondOfPrimal b := by
      rw [e.crossingBond_eq]
      rfl
    have hpair' : s(u.val, v.val) = s(b.faceBase false, b.faceBase true) := by
      have hh := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.1)) hpair
      simp_all [rectangleDualCarrierPair]
    rcases Sym2.eq_iff.mp hpair' with ⟨hu, hv⟩ | ⟨hu, hv⟩ <;> grind
  · rintro ⟨b, hs, ht, hdiff, huv | huv⟩
    · have hadj := (rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht).2 hdiff
      have hs' :=
        rectangleCutDualEdgeOfBond_source_val a w h b hs ht
      have ht' :=
        rectangleCutDualEdgeOfBond_target_val a w h b hs ht
      grind
    · have hadj := (rectangleCutDualEdgeOfBond_adj_iff a w h σ b hs ht).2 hdiff
      have hs' :=
        rectangleCutDualEdgeOfBond_source_val a w h b hs ht
      have ht' :=
        rectangleCutDualEdgeOfBond_target_val a w h b hs ht
      have hu : u = rectangleDualEdgeTarget a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        grind
      have hv : v = rectangleDualEdgeSource a w h
          (rectangleCutDualEdgeOfBond a w h b hs ht) := by
        grind
      rw [hu, hv]
      tauto

end

end PottsDiscontinuity.FK
