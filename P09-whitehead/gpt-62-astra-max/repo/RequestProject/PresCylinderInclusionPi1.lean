module

public import RequestProject.PresCylinderPi1Surjective
public import RequestProject.OrderIsoPi1Surjective
public import RequestProject.CylinderPi1Surjective

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The concrete cylinder inclusion surjects onto the presentation fundamental group. -/
theorem presCylinderInclusion_pi1_surjective (a : CylP (aHom w)) :
    Function.Surjective (pi1Map
      (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a) := by
  let e : coneAdjBaseSet (S := circSet w) ≃o CylP (aHom w) := coneAdjBaseOrderIso
  let b := e.symm a
  intro z
  obtain ⟨q, hq⟩ := presCylinder_pi1_surjective w hpos b z
  obtain ⟨p, hp⟩ := orderIso_pi1_surjective e.symm a q
  refine ⟨p, ?_⟩
  erw [← hp] at hq
  have hmap : pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) a p =
      pi1Map (subposetHom (coneAdjBaseSet (S := circSet w))) b
        (pi1Map (orderCxMap e.symm e.symm.monotone) a p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      have heq : mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h)) r.val =
          mapPath (subposetHom (coneAdjBaseSet (S := circSet w)))
            (mapPath (orderCxMap e.symm e.symm.monotone) r.val) := by
        simp only [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose]
        rfl
      simp_all
  exact hmap.trans hq

include hpos in
/-- Every actual presentation loop class comes from the actual rose. -/
theorem presRoseInclusion_pi1_surjective (x : Rose α) :
    Function.Surjective (pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x) := by
  intro z
  obtain ⟨q, hq⟩ := presCylinderInclusion_pi1_surjective w hpos (cylIn (aHom w) x) z
  obtain ⟨p, hp⟩ := cylinder_pi1_surjective (aHom w) x q
  refine ⟨p, ?_⟩
  erw [← hp] at hq
  have he : pi1Map (orderCxMap (iRose w)
      (iRose_monotone w)) x p =
      pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (fun _ _ h => h))
        (cylIn (aHom w) x)
        (pi1Map (orderCxMap (cylIn (aHom w)) (cylIn_monotone (aHom w))) x p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      simp [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose]
  exact he.trans hq

end FiniteChains.PresModel
