import RequestProject.PresCoverCylinderRelatorBoundary
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverCylinderRelatorBoundary_cycle p :
    Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) = 0 := by
  rwd [bdry1_chain1, relatorCircleFundamentalChain_cycle, map_zero]

theorem presCoverCylinderRelatorBoundaryChain_cycle c :
    Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0 := by
  lin_ind c p n =>
    simp [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, map_smul, presCoverCylinderRelatorBoundary_cycle, smul_zero]

/-- A relator vector with actual collapsed boundary zero has an actual finite cylinder filling. -/
theorem exists_presCover_relator_cylinder_filling c
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        presCoverCylinderRelatorBoundaryChain w f hf c := by
  obtain ⟨d, hd⟩ := strict_oneCycle_comparable_boundary id _
    monotone_id _
    ((coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      _ (le_cylIn_cylRetr _))
    _
    (presCoverCylinderRelatorBoundaryChain_cycle w f hf c)
  rwd [hc, normalizedStrictChain1_id, zero_sub] at hd
  exact ⟨-d, by simp_all⟩

/-- Actual cylinder triangle chains have zero genuine relator coordinates. -/
theorem presCoverRelatorChain_cylinder_zero hpos
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :
    presCoverRelatorChain w f hf hpos
      (chain2 (strictSubposetIncl {p | f p ∈ coneAdjBaseSet (S := circSet w)}) c) = 0 := by
  classical
  lin_ind c with c d hc hd => simp_all [map_add, hc, hd, add_zero]
  | t n =>
    ext p
    rwd [presCoverRelatorChain_apply, Finsupp.zero_apply]
    have hn : (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF t ≠
        presCoverRelatorTriangle w f hf hpos p := by
      intro he
      have hv := congrArg (f ·.1.2.2) he
      change f t.1.2.2.val = f p.1.1 at hv
      have hp := t.1.2.2.property
      simp_all [hv, p.2, coneAdjBaseSet, ConeAdj.inc, apexOf, ConeAdj.apex]
    simp_all

/-- Actual collapsed-boundary cycles are realized by genuine finite cover two-cycles. -/
theorem exists_presCover_cycle_of_collapsed_relator_boundary
    hpos c
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ z : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) z = 0 ∧
      presCoverRelatorChain w f hf hpos z = c := by
  cases' exists_presCover_relator_cylinder_filling w f hf c hc with d hd
  let I := strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}
  let L : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} → StrictOrdTri P :=
    fun t => ⟨(t.1.1.val, t.1.2.1.val, t.1.2.2.val), t.2⟩
  let u := Finsupp.mapDomain L d
  have hb : Comb.bdry2 _ u =
      Comb.bdry2 (strictOrderCx P) (presCoverRelatorFanChain w f hf c) :=
    (bdry2_chain2 I d).trans ((congrArg _ hd).trans
      (presCoverCylinderRelatorBoundaryChain_inclusion w f hf c))
  have hu : presCoverRelatorChain w f hf hpos u = 0 :=
    presCoverRelatorChain_cylinder_zero w f hf hpos d
  refine ⟨presCoverRelatorFanChain w f hf c - u, ?_, ?_⟩
  · simp_all
  · simp [map_sub, presCoverRelatorChain_fanChain, hu, sub_zero]
