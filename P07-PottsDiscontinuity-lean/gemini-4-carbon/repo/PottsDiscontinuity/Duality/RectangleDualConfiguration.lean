/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualCarrier

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

theorem rectanglePrimalEdgeBond_toSym2_public
    (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply wholePlaneBondEdgeEquiv
    (rectanglePrimalEdgeToSquareEdge a w h e))

theorem rectanglePrimalEdgeBond_endpoints_mem_public
    (a : LatticeVertex) (w h : ℕ) (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hm : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 = s(p.1.val, p.2.val) := by
    rw [← hrepr]; rfl
  have heq : s((rectanglePrimalEdgeBond a w h e).source,
      (rectanglePrimalEdgeBond a w h e).target) = s(p.1.val, p.2.val) := by
    simpa [LatticeBond.toSym2] using (rectanglePrimalEdgeBond_toSym2_public a w h e).trans hm
  rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨hs.symm ▸ p.1.2, ht.symm ▸ p.2.2⟩
  · exact ⟨hs.symm ▸ p.2.2, ht.symm ▸ p.1.2⟩

def rectanglePrimalBondToEdge (a : LatticeVertex) (w h : ℕ)
    (b : RectanglePrimalBond a w h) : rectanglePrimalEdgeCarrier a w h :=
  ⟨s(⟨b.1.source, b.2.1⟩, ⟨b.1.target, b.2.2⟩), (rectangleGraph_adj_iff a w h _ _).2 b.1.adjacent⟩

noncomputable def rectanglePrimalEdgeBondEquiv (a : LatticeVertex) (w h : ℕ) :
    rectanglePrimalEdgeCarrier a w h ≃ RectanglePrimalBond a w h where
  toFun e := ⟨rectanglePrimalEdgeBond a w h e, rectanglePrimalEdgeBond_endpoints_mem_public a w h e⟩
  invFun := rectanglePrimalBondToEdge a w h
  left_inv e := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    let b := rectanglePrimalEdgeBond a w h e
    have hbond := rectanglePrimalEdgeBond_toSym2_public a w h e
    change Sym2.map (fun z : RectangleVertex a w h => z.val)
        (s(⟨b.source, (rectanglePrimalEdgeBond_endpoints_mem_public a w h e).1⟩,
           ⟨b.target, (rectanglePrimalEdgeBond_endpoints_mem_public a w h e).2⟩)) = _
    simpa [b, LatticeBond.toSym2] using hbond
  right_inv b := by
    apply Subtype.ext
    apply LatticeBond.toSym2_injective
    exact rectanglePrimalEdgeBond_toSym2_public a w h (rectanglePrimalBondToEdge a w h b)

noncomputable def rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    Configuration (rectangleDualGraph a w h) :=
  Finset.map (rectangleDualGraphEdgeEquiv a w h).toEmbedding
    (rectangleDualComplementEquiv a w h A)

@[simp] theorem mem_rectangleDualConfiguration (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h))
    (e : RectangleDualEdgeCarrier a w h) :
    rectangleDualGraphEdgeEquiv a w h e ∈ rectangleDualConfiguration a w h A ↔
      e.primalEdge ∉ A := by
  classical
  simp [rectangleDualConfiguration, mem_rectangleDualComplementEquiv]

/-- The actual finite dual configuration is the open complement of the primal
configuration, transported across the true labelled-edge/graph-edge bijection. -/
noncomputable def rectangleDualConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃ Configuration (rectangleDualGraph a w h) := by
  exact (rectangleDualComplementEquiv a w h).trans
    (Equiv.finsetCongr (rectangleDualGraphEdgeEquiv a w h))

@[simp] theorem rectangleDualConfigurationEquiv_apply (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualConfigurationEquiv a w h A = rectangleDualConfiguration a w h A := by
  simp [rectangleDualConfigurationEquiv, rectangleDualConfiguration,
    Equiv.finsetCongr_apply]

@[simp] theorem rectangleDualConfigurationEquiv_card (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    (rectangleDualConfigurationEquiv a w h A).card =
      (rectangleDualComplementEquiv a w h A).card := by
  simp [rectangleDualConfigurationEquiv, Equiv.finsetCongr_apply, Finset.card_map]

theorem rectangleDualConfiguration_card_add (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfigurationEquiv a w h A).card =
      Nat.card (rectangleDualGraph a w h).edgeSet := by
  classical
  rw [rectangleDualConfigurationEquiv_card]
  have hcard := rectangleDualComplement_card_add a w h A
  calc
    A.card + (rectangleDualComplementEquiv a w h A).card =
        Fintype.card (rectanglePrimalEdgeCarrier a w h) := hcard
    _ = Nat.card (rectangleDualGraph a w h).edgeSet := by
      calc
        Fintype.card (rectanglePrimalEdgeCarrier a w h) =
            Nat.card (rectanglePrimalEdgeCarrier a w h) := (Nat.card_eq_fintype_card (α := rectanglePrimalEdgeCarrier a w h)).symm
        _ = Nat.card (rectangleDualGraph a w h).edgeSet :=
          (Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
            (rectanglePrimalDualEdgeEquiv a w h).symm)).symm
  

theorem rectangleDualGraph_edgeSet_card_eq_primal_edgeSet (a : LatticeVertex)
    (w h : ℕ) :
    Nat.card (rectangleDualGraph a w h).edgeSet =
      Nat.card (rectangleGraph a w h).edgeSet := by
  exact Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
    (rectanglePrimalDualEdgeEquiv a w h).symm)

theorem rectangleDualConfiguration_card_add_eq_primal_edgeSet
    (a : LatticeVertex) (w h : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfiguration a w h A).card =
      Nat.card (rectangleGraph a w h).edgeSet := by
  rw [← rectangleDualConfigurationEquiv_apply]
  rw [rectangleDualConfiguration_card_add]
  exact rectangleDualGraph_edgeSet_card_eq_primal_edgeSet a w h

end PottsDiscontinuity.FK
