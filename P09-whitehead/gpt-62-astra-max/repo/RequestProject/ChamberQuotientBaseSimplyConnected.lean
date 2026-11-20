module

public import RequestProject.ChamberQuotientBaseCover
public import RequestProject.OrderUniversalPosetConnected

@[expose] public section

/-! Each actual lifted base component is simply connected, proved from the
genuine covering and the proved injection of the base fundamental group. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

variable (a : Qpos A X att) (hc : IsConnected (orderCx (Qpos A X att)))
include hc

omit [Fintype V] in
theorem qBaseCover_path_projection
    (l : List _) :
    mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
      (mapPath (orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono) l) =
    mapPath (orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone)
      (mapPath (orderCxMap Subtype.val
        (fun _ _ h => h)) l) := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [mapPath, List.map_cons] at ih ⊢
    congr 1
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (qBaseCoverEnd_spec a e.1.1.1) (qBaseCoverEnd_spec a e.1.1.2)
    · rfl

/-- All edge loops of the actual full lifted base are null-homotopic. Its
different components are not identified with one another. -/
theorem qLiftedBase_simplyConnected :
    SimplyConnected (orderCx (QLiftedBase a)) := by
  let beta := orderCxMap _ (qBaseCoverEnd_isPosetCover a hc).mono
  let incl := orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
    (fun _ _ h => h)
  intro b p hp
  have hi := uOrder_complex_simplyConnected
    b.1 _ (isPath_mapPath incl hp)
  have hnull := mapPath_htpy (orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone) hi
  have hq : Htpy _ (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
        (mapPath beta p)) [] := by
    erw [qBaseCover_path_projection a hc, qBaseCoverEnd_spec]
    exact hnull
  have hcl : Pi1.mk (⟨mapPath beta p, isPath_mapPath beta hp⟩) = 1 := by
    apply pi1Map_qNew_injective (att := att) _
    exact Quotient.sound hq
  obtain ⟨m, _, hmap, hpm⟩ := lift_htpy (isCovering_orderCxMap (qBaseCoverEnd_isPosetCover a hc)).lifts hp (Quotient.exact hcl)
  have hm := List.map_eq_nil_iff.mp hmap
  simp_all

end FiniteChains.Davis
