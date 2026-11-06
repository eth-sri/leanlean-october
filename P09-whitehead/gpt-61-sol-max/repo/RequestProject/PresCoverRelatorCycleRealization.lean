import Mathlib.Tactic

import RequestProject.PresCoverCylinderRelatorBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f)

theorem presCoverCylinderRelatorBoundary_cycle (p : PresCoverRelator w f) :
    Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundary w f hf p) = 0 := by
  change Comb.bdry1 _ (chain1 (strictOrderCxMap (presCoverCircleCylinderInclusion w f hf p)
    (presCoverCircleCylinderInclusion_strictMono w f hf p)) _) = 0
  rw  [bdry1_chain1, relatorCircleFundamentalChain_cycle, map_zero]

variable (c : PresCoverRelator w f →₀ ℤ)
theorem presCoverCylinderRelatorBoundaryChain_cycle  :
    Comb.bdry1 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)})
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0 := by
  induction c using Finsupp.induction_linear <;> simp_all [presCoverCylinderRelatorBoundaryChain, presCoverCylinderRelatorBoundary_cycle]

/-- A relator vector with actual collapsed boundary zero has an actual finite cylinder filling. -/
theorem exists_presCover_relator_cylinder_filling 
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ d : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ,
      Comb.bdry2 (strictOrderCx {p : P // f p ∈ coneAdjBaseSet (S := circSet w)}) d =
        presCoverCylinderRelatorBoundaryChain w f hf c := by
  obtain ⟨d, hd⟩ := strict_oneCycle_comparable_boundary id (presCoverCylinderCollapse w f hf)
    monotone_id (presCoverCylinderCollapse_monotone w f hf)
    ((coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      (cylCollapse (aHom w)) (le_cylIn_cylRetr (aHom w)))
    (presCoverCylinderRelatorBoundaryChain w f hf c)
    (presCoverCylinderRelatorBoundaryChain_cycle w f hf c)
  rw  [hc, normalizedStrictChain1_id, zero_sub] at hd
  exact ⟨-d, by simp_all⟩

variable (hpos : ∀ j, 0 < (w j).length)
/-- Actual cylinder triangle chains have zero genuine relator coordinates. -/
theorem presCoverRelatorChain_cylinder_zero 
    (c : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} →₀ ℤ) :
    presCoverRelatorChain w f hf hpos
      (chain2 (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}) c) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [map_add]
  | single t n =>
    change presCoverRelatorChain w f hf hpos
      (Finsupp.mapDomain (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF
        (Finsupp.single t n)) = 0
    rw  [Finsupp.mapDomain_single]
    ext p
    rw  [presCoverRelatorChain_apply, Finsupp.zero_apply]
    have hn : (strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}).onF t ≠
        presCoverRelatorTriangle w f hf hpos p := by
      intro he
      have hv := congrArg (fun r : StrictOrdTri P => f r.1.2.2) he
      change f t.1.2.2.val = f p.1.1 at hv
      have hp := t.1.2.2.property
      rw  [hv, p.2] at hp
      simp [coneAdjBaseSet, ConeAdj.inc, apexOf, ConeAdj.apex] at hp
    simp [hn]

/-- Actual collapsed-boundary cycles are realized by genuine finite cover two-cycles. -/
theorem exists_presCover_cycle_of_collapsed_relator_boundary
     (c : PresCoverRelator w f →₀ ℤ)
    (hc : normalizedStrictChain1 (presCoverCylinderCollapse w f hf)
      (presCoverCylinderCollapse_monotone w f hf)
      (presCoverCylinderRelatorBoundaryChain w f hf c) = 0) :
    ∃ z : StrictOrdTri P →₀ ℤ, Comb.bdry2 (strictOrderCx P) z = 0 ∧
      presCoverRelatorChain w f hf hpos z = c := by
  obtain ⟨d, hd⟩ := exists_presCover_relator_cylinder_filling w f hf c hc
  let I := strictSubposetIncl {p : P | f p ∈ coneAdjBaseSet (S := circSet w)}
  let L : StrictOrdTri {p : P // f p ∈ coneAdjBaseSet (S := circSet w)} → StrictOrdTri P :=
    fun t => ⟨(t.1.1.val, t.1.2.1.val, t.1.2.2.val), t.2⟩
  let u  := Finsupp.mapDomain L d
  have hb  :=
    (bdry2_chain2 I d).trans ((congrArg (chain1 I) hd).trans
      (presCoverCylinderRelatorBoundaryChain_inclusion w f hf c))
  have hu : presCoverRelatorChain w f hf hpos u = 0 :=
    presCoverRelatorChain_cylinder_zero w f hf hpos d
  refine ⟨presCoverRelatorFanChain w f hf c - u, ?_, ?_⟩
  · rw (config := { transparency := .default }) [map_sub, hb, sub_self]
  · simp_all [FiniteChains.PresModel.presCoverRelatorChain_fanChain]

end FiniteChains.PresModel
