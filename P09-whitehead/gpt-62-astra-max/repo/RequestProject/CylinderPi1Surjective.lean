module

public import RequestProject.OrderConstructionPartialOrder
public import RequestProject.OrderReflexiveConjugation

@[expose] public section

namespace FiniteChains.Comb
universe u
variable {X S : Type u} [PartialOrder X] [PartialOrder S] (a : S →o X)

variable (x : X)

/-- Every actual based cylinder loop is homotopic to its retraction onto the base. -/
theorem cylinder_loop_retraction
    (p : List _)
    (hp : IsPath (orderCx (CylP a)).src (orderCx (CylP a)).tgt p (cylIn a x) (cylIn a x)) :
    Htpy _ (cylIn a x) (cylIn a x) p
      (mapPath (orderCxMap (cylIn a) (cylIn_monotone a))
        (mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p)) := by
  have h := htpy_loop_mapPath_le_fixed monotone_id (cylCollapse_monotone a)
    (le_cylIn_cylRetr a) rfl p hp
  have hid : mapPath (orderCxMap id monotone_id) p = p := by
    clear hp h
    induction p with
    | nil => rfl
    | cons e p ih =>
      exact congrArg _ ih
  simp_all [hid, mapPath, List.map_map, Function.comp_def, orderCxMap, cylCollapse, cylIn, cylRetr, id]

/-- The actual base inclusion surjects onto the cylinder fundamental group. -/
theorem cylinder_pi1_surjective :
    Function.Surjective (pi1Map (orderCxMap (cylIn a) (cylIn_monotone a)) x) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    refine ⟨Pi1.mk ⟨mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.val,
      isPath_mapPath (orderCxMap (cylRetr a) (cylRetr_monotone a)) p.property⟩,
      Quotient.sound ?_⟩
    exact (cylinder_loop_retraction a x p.val p.property).symm

end FiniteChains.Comb
