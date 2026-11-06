import RequestProject.PresStrictPathCylinderReduction
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)

include hpos in
/-- The actual cylinder inclusion is surjective on the actual presentation fundamental group. -/
theorem presCylinder_pi1_surjective
    (a : {p : PresPos w // p ∈ coneAdjBaseSet (S := circSet w)}) :
    Function.Surjective (pi1Map (subposetHom (coneAdjBaseSet (S := circSet w))) a) := by
  intro z
  induction z using Quotient.inductionOn with
  | h p =>
    obtain ⟨q, hq, hqc, hh⟩ := exists_presPath_cylinder_reduction w hpos p.val a.val a.val
      a.property a.property p.property
    let r := liftPathIn q hqc
    have hr :=
      isPath_liftPathIn q hqc a.property a.property hq
    refine ⟨Pi1.mk ⟨r, hr⟩, Quotient.sound ?_⟩
    change Htpy _ a.val a.val
      (mapPath (subposetHom _) (liftPathIn q hqc)) p.val
    rwd [mapPath_liftPathIn]
    exact hh.symm
