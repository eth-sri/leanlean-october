import RequestProject.CombUniversalCover
import RequestProject.Tac


/-! Path-class identities for comparing covers with chosen reference paths. -/
bwd

namespace FiniteChains.Comb
universe u
variable {X : Complex2.{u}} {o a b : X.V}

/-- Path extension commutes with every actual deck transformation. -/
theorem extendList_deckV g p (v : UV X o) :
    extendList p (deckV g v) = deckV g (extendList p v) := by
  induction p generalizing v with
  | nil => rfl
  | cons e p ih => rw [extendList_cons, extend_deckV, ih, extendList_cons]

/-- A loop acting on the base cover vertex is its actual lifted endpoint. -/
theorem deckV_loop_base l :
    deckV (Pi1.mk l) (UV.base X o) = extendList l.1 (UV.base X o) := by
  let r : PathFrom X o := ⟨l.1, by grind [endpt_eq_of_isPath l.2]⟩
  have h : extendList l.1 (UV.base X o) = UV.mk r :=
    extendList_mk (p := ⟨[], rfl⟩) (r := r) l.2 rfl
  rw [h]
  apply Quotient.sound
  change Htpy X o (endpt X o (l.1 ++ [])) (l.1 ++ []) l.1
  simp [List.append_nil]
  exact Htpy.refl _

/-- The endpoint after a path is the translated reference endpoint at its target. -/
theorem extendList_reference_gauge
    (hr : IsPathX X r o a) (hp : IsPathX X p a b)
    hs :
    extendList p (extendList r (UV.base X o)) =
      deckV (Pi1.mk ⟨r ++ p ++ revPath s, (hr.append hp).append (isPath_revPath hs)⟩)
        (extendList s (UV.base X o)) := by
  rw [← extendList_deckV, deckV_loop_base, ← extendList_append, ← extendList_append]
  have h : Htpy X o b (r ++ p) ((r ++ p ++ revPath s) ++ s) := by
    have hc := Htpy.append_congr (hr.append hp)
      ((isPath_revPath hs).append hs) (by tauto) (htpy_revPath_append hs)
    simpa [List.append_nil, List.append_assoc] using hc.symm
  exact extendList_htpy (hr.append hp) h
