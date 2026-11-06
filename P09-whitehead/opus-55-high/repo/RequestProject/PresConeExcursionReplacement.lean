import RequestProject.OrderConePathReplacement
import RequestProject.RelatorCircleConnected
import RequestProject.RelatorConeFundamentalChain
import RequestProject.ConeAdjBaseCover


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Actual mapped circle paths remain below their actual presentation apex. -/
theorem relatorCirclePath_below_apex l :
    PathIn (· ≤ apexOf w j)
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(relatorCirclePresInclusion_lt_apex w j r.1.val.1).le,
    (relatorCirclePresInclusion_lt_apex w j r.1.val.2).le⟩

/-- Actual mapped circle paths stay in the actual cylinder part of the presentation poset. -/
theorem relatorCirclePath_in_cylinder l :
    PathIn (· ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨⟨cylOuter _ r.1.val.1.val, rfl⟩,
    ⟨cylOuter _ r.1.val.2.val, rfl⟩⟩

/-- An actual two-edge apex excursion can be replaced by an actual path in the cylinder. -/
theorem exists_presCone_excursion_replacement (hpos : 0 < (w j).length)
    x y :
    ∃ l,
      IsPathX (orderCx (PresPos w)) l (iCirc w x.val) (iCirc w y.val) ∧
      PathIn (· ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) (iCirc w x.val) (iCirc w y.val)
        [ordPos (relatorCirclePresInclusion_lt_apex w j x).le,
          ordNeg (relatorCirclePresInclusion_lt_apex w j y).le] l := by
  cases' relatorCircle_isConnected w j hpos x y with l hl
  let I := orderCxMap _
    (relatorCirclePresInclusion_strictMono w j).monotone
  refine ⟨mapPath I l, isPath_mapPath I hl, relatorCirclePath_in_cylinder w j l, ?_⟩
  exact (htpy_path_through_upper_bound _
    _
    _
    (isPath_mapPath I hl) (relatorCirclePath_below_apex w j l)).symm

/-- Every genuine apex excursion, with arbitrary actual strict lower endpoints, has a cylinder replacement. -/
theorem exists_presCone_strict_excursion_replacement (hpos : 0 < (w j).length)
    x y (hx : x < apexOf w j) (hy : y < apexOf w j) :
    ∃ l,
      IsPathX (orderCx (PresPos w)) l x y ∧
      PathIn (· ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy (orderCx (PresPos w)) x y [ordPos hx.le, ordNeg hy.le] l := by
  cases' relatorCircleToBelow_surjective w j ⟨x, hx⟩ with a ha
  cases' relatorCircleToBelow_surjective w j ⟨y, hy⟩ with b hb
  have hax : iCirc w a.val = x := congrArg Subtype.val ha
  have hby : iCirc w b.val = y := congrArg Subtype.val hb
  subst x
  subst y
  exact exists_presCone_excursion_replacement w j hpos a b
