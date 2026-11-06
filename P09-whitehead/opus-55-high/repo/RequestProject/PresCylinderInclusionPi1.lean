import RequestProject.PresCylinderPi1Surjective
import RequestProject.OrderIsoPi1Surjective
import RequestProject.CylinderPi1Surjective
import RequestProject.Tac


bwd

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
  let b : coneAdjBaseSet (S := circSet w) := e.symm a
  intro z
  cases' presCylinder_pi1_surjective w hpos b z with q hq
  cases' orderIso_pi1_surjective e.symm a q with p hp
  refine ⟨p, ?_⟩
  rwd [← hp] at hq
  have hmap : pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (by tauto)) a p =
      pi1Map (subposetHom _) b
        (pi1Map (orderCxMap e.symm e.symm.monotone) a p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      have heq : mapPath (orderCxMap (ConeAdj.inc (S := circSet w)) (by tauto)) r.val =
          mapPath (subposetHom _)
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
  cases' presCylinderInclusion_pi1_surjective w hpos _ z with q hq
  cases' cylinder_pi1_surjective _ x q with p hp
  refine ⟨p, ?_⟩
  rwd [← hp] at hq
  have he : pi1Map (orderCxMap _
      (iRose_monotone w)) x p =
      pi1Map (orderCxMap (ConeAdj.inc (S := circSet w)) (by tauto))
        (cylIn (aHom w) x)
        (pi1Map (orderCxMap (cylIn _) (by grind)) x p) := by
    induction p using Quotient.inductionOn with
    | h r =>
      apply Quotient.sound
      simp [mapPath, List.map_map, Function.comp_def, orderCxMap, iRose]
  exact he.trans hq
