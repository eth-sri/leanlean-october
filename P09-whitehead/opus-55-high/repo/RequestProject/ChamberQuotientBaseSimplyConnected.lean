import RequestProject.ChamberQuotientBaseCover
import RequestProject.OrderUniversalPosetConnected
import RequestProject.Tac


/-! Each actual lifted base component is simply connected, proved from the
genuine covering and the proved injection of the base fundamental group. -/
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

omit [Fintype V] in
theorem qBaseCover_path_projection (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att)))
    (l : List ((orderCx (QLiftedBase a)).E × Bool)) :
    mapPath (orderCxMap (qNew (A := A) (X := X) (att := att)) qNew_monotone)
      (mapPath (orderCxMap (qBaseCoverEnd a) (qBaseCoverEnd_isPosetCover a hc).mono) l) =
    mapPath (orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone)
      (mapPath (orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
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
theorem qLiftedBase_simplyConnected (a : Qpos A X att)
    (hc : IsConnected (orderCx (Qpos A X att))) :
    SimplyConnected (orderCx (QLiftedBase a)) := by
  let beta := orderCxMap _ (qBaseCoverEnd_isPosetCover a hc).mono
  have hcov := isCovering_orderCxMap (qBaseCoverEnd_isPosetCover a hc)
  let incl := orderCxMap (Subtype.val : QLiftedBase a → UOrder (Qpos A X att) a)
    (by tauto)
  let proj := orderCxMap (uOrderEnd (P := Qpos A X att) (a := a)) uOrderEnd_monotone
  intro b p hp
  have hi := uOrder_complex_simplyConnected (P := Qpos A X att) (a := a)
    b.1 _ (isPath_mapPath incl hp)
  have hnull := mapPath_htpy proj hi
  have hq : Htpy (orderCx (Qpos A X att)) (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (qNew (A := A) (att := att) (qBaseCoverEnd (X := X) a b))
      (mapPath (orderCxMap _ qNew_monotone)
        (mapPath beta p)) [] := by
    rwd [qBaseCover_path_projection a hc, qBaseCoverEnd_spec]
    exact hnull
  let l : Loop (orderCx X) (qBaseCoverEnd (X := X) a b) := ⟨mapPath beta p, isPath_mapPath beta hp⟩
  have hcl : Pi1.mk l = 1 := by
    apply pi1Map_qNew_injective (A := A) (att := att) _
    exact Quotient.sound hq
  have hl := Quotient.exact hcl
  obtain ⟨m, _, hmap, hpm⟩ := lift_htpy hcov hp hl
  have hm := List.map_eq_nil_iff.mp hmap
  simp_all
