module

public import RequestProject.OrderConePathReplacement
public import RequestProject.RelatorCircleConnected
public import RequestProject.RelatorConeFundamentalChain


@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

variable (l : List ((orderCx (RelatorCircle w j)).E × Bool))

/-- Actual mapped circle paths remain below their actual presentation apex. -/
theorem relatorCirclePath_below_apex :
    PathIn (fun p => p ≤ apexOf w j)
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(relatorCirclePresInclusion_lt_apex w j _).le,
    (relatorCirclePresInclusion_lt_apex w j _).le⟩

/-- Actual mapped circle paths stay in the actual cylinder part of the presentation poset. -/
theorem relatorCirclePath_in_cylinder :
    PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w))
      (mapPath (orderCxMap (relatorCirclePresInclusion w j)
        (relatorCirclePresInclusion_strictMono w j).monotone) l) := by
  intro e he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he
  exact ⟨⟨cylOuter _ _, rfl⟩,
    ⟨cylOuter _ _, rfl⟩⟩

variable (hpos : 0 < (w j).length)
include hpos

/-- An actual two-edge apex excursion can be replaced by an actual path in the cylinder. -/
theorem exists_presCone_excursion_replacement
    (x y : RelatorCircle w j) :
    ∃ l : List _,
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l (iCirc w x.val) (iCirc w y.val) ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy _ (iCirc w x.val) (iCirc w y.val)
        [ordPos (relatorCirclePresInclusion_lt_apex w j x).le,
          ordNeg (relatorCirclePresInclusion_lt_apex w j y).le] l := by
  obtain ⟨l, hl⟩ := relatorCircle_isConnected w j hpos x y
  let I := orderCxMap _
    (relatorCirclePresInclusion_strictMono w j).monotone
  refine ⟨mapPath I l, isPath_mapPath I hl, relatorCirclePath_in_cylinder w j l, ?_⟩
  exact (htpy_path_through_upper_bound _
    _
    _
    (isPath_mapPath I hl) (relatorCirclePath_below_apex w j l)).symm

/-- Every genuine apex excursion, with arbitrary actual strict lower endpoints, has a cylinder replacement. -/
theorem exists_presCone_strict_excursion_replacement
    (x y : PresPos w) (hx : x < apexOf w j) (hy : y < apexOf w j) :
    ∃ l : List _,
      IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt l x y ∧
      PathIn (fun p => p ∈ coneAdjBaseSet (S := circSet w)) l ∧
      Htpy _ x y [ordPos hx.le, ordNeg hy.le] l := by
  obtain ⟨a, ha⟩ := relatorCircleToBelow_surjective w j ⟨x, hx⟩
  obtain ⟨b, hb⟩ := relatorCircleToBelow_surjective w j ⟨y, hy⟩
  have hax : iCirc w a.val = x := congrArg Subtype.val ha
  have hby : iCirc w b.val = y := congrArg Subtype.val hb
  subst x
  subst y
  apply exists_presCone_excursion_replacement <;> assumption

end FiniteChains.PresModel
