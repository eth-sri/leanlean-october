import Mathlib.Tactic

import RequestProject.CellularChainMapZero
import RequestProject.RoseCoverGeneratorChain
import RequestProject.RelatorCircleFundamentalChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel
open Comb
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool)) (j : J)
  (f : P → Rose α) (hf : IsPosetCover f) (m : RelatorCircle w j → P)
  (hm : StrictMono m) (hp : ∀ x, f (m x) = aFun w x.val)

variable (k : Fin (w j).length)
/-- The actual lifted midpoint belonging to a specified actual attaching letter. -/
def roseCoverLetterMidpoint  (a : α × Bool)
    (ha : (w j)[k.val]? = some a) : roseCoverMidpoints f :=
  ⟨(m (relatorCirclePoint w j k CPos.cmid), a.1),
    (hp _).trans (aFun_pt_cmid_of_get w ha)⟩

/-- Each actual lifted letter chain is the appropriately signed genuine generator chain. -/
theorem roseCoverLetterChain_map  (a : α × Bool)
    (ha : (w j)[k.val]? = some a) :
    chain1 (strictOrderCxMap m hm) (relatorCircleLetterChain w j k) =
      (if a.2 then (1 : ℤ) else -1) •
        roseCoverGeneratorChain f hf (roseCoverLetterMidpoint w j f m hp k a ha) := by
  classical
  let p := roseCoverLetterMidpoint w j f m hp k a ha
  let M := strictOrderCxMap m hm
  have h1 : M.onE (relatorCircleEdge1 w j k) = roseCoverMidpointEndEdge f hf p (!a.2) := by
    apply hf.strictEdgeLiftFrom_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cmid_of_get w ha))
        ((hp _).trans (aFun_pt_cedgL_of_get w ha))
    · rfl
  have h2 : M.onE (relatorCircleEdge2 w j k) = roseCoverMidpointEndEdge f hf p a.2 := by
    apply hf.strictEdgeLiftFrom_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cmid_of_get w ha))
        ((hp _).trans (aFun_pt_cedgR_of_get w ha))
    · rfl
  have h0 : M.onE (relatorCircleEdge0 w j k) = roseCoverMidpointBaseEdge f hf p (!a.2) := by
    apply hf.strictEdgeLiftTo_unique
    · apply Subtype.ext
      exact Prod.ext ((hp _).trans (aFun_pt_cor w j k.val))
        ((hp _).trans (aFun_pt_cedgL_of_get w ha))
    grind [strictOrderCxMap, relatorCircleEdge0, relatorCircleEdge1]
  have h3 : M.onE (relatorCircleEdge3 w j k) = roseCoverMidpointBaseEdge f hf p a.2 := by
    apply hf.strictEdgeLiftTo_unique
    · classical solve_by_elim (transparency := .default) (maxDepth := 10) [Subtype.ext, FiniteChains.Comb.IsPosetCover.strictMono, Prod.ext, Eq.trans, FiniteChains.PresModel.aFun_pt_cor, FiniteChains.PresModel.aFun_pt_cedgR_of_get, Subtype.ext, Prod.ext]
    grind [strictOrderCxMap, relatorCircleEdge2, relatorCircleEdge3]
  change chain1 M (relatorCircleLetterChain w j k) = _
  unfold relatorCircleLetterChain
  rw  [map_sub, map_add, map_sub]
  change Finsupp.mapDomain M.onE (Finsupp.single _ 1) -
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) +
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) -
    Finsupp.mapDomain M.onE (Finsupp.single _ 1) = _
  rw  [Finsupp.mapDomain_single, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, Finsupp.mapDomain_single, h0, h1, h2, h3]
  change _ = (if a.2 then (1 : ℤ) else -1) • roseCoverGeneratorChain f hf p
  cases hb : a.2 <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, one_smul, neg_smul, roseCoverGeneratorChain]; abel

/-- The genuine lifted attaching-circle chain is the signed sum of its actual generator chains. -/
theorem roseCoverFundamentalChain_map :
    chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          roseCoverGeneratorChain f hf
            (roseCoverLetterMidpoint w j f m hp k ((w j)[k.val])
              (List.getElem?_eq_getElem k.isLt)) := by
  classical
  rw  [relatorCircleFundamentalChain, map_sum]
  apply Finset.sum_congr rfl
  grind [roseCoverLetterChain_map]

/-- The actual generator coefficients of the attaching circle are the signed sum of its lifted letters. -/
theorem roseCoverFundamentalChain_coordinates :
    roseCoverGeneratorCoordinates f hf
      (chain1 (strictOrderCxMap m hm) (relatorCircleFundamentalChain w j)) =
      ∑ k : Fin (w j).length,
        (if ((w j)[k.val]).2 then (1 : ℤ) else -1) •
          Finsupp.single (roseCoverMidpointEdge f hf
            (roseCoverLetterMidpoint w j f m hp k ((w j)[k.val])
              (List.getElem?_eq_getElem k.isLt))) 1 := by
  classical
  rw  [roseCoverFundamentalChain_map w j f hf m hm hp, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw  [map_smul, roseCoverGeneratorChain_coordinates]

end FiniteChains.PresModel
