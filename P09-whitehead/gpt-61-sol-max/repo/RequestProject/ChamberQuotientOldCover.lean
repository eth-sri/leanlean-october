import Mathlib.Tactic

import RequestProject.BlockSpinePres
import RequestProject.ChamberQuotientOldStar
import RequestProject.ChamberQuotientEquivariantGeneration
import RequestProject.ChamberZConnected

/-! The old-block part of the actual quotient universal cover is an actual poset cover. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type u} [DecidableEq V] {A : CommRel V}
  {X : Type u} [PartialOrder X] {att : NeSpx A →o X}

def qOldPartOrderIso : {p : Qpos A X att // InQOld p} ≃o QOld A where
  toFun p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | inl c => exact c
    | inr x => exact False.elim hp
  invFun c := ⟨Sum.inl c, trivial⟩
  left_inv p := by
    classical
    rcases p with ⟨p, hp⟩
    cases p <;> aesop
  right_inv c := rfl
  map_rel_iff' := by
    rintro ⟨p, hp⟩ ⟨r, hr⟩
    cases p with
    | inr x => exact False.elim hp
    | inl c =>
      cases r with
      | inr x => exact False.elim hr
      | inl d => rfl

variable (a : Qpos A X att)
abbrev QLiftedOld  :=
  {p : UOrder (Qpos A X att) a // InQOld (uOrderEnd p)}

def qOldCoverEnd  (p : QLiftedOld a)  :=
  qOldPartOrderIso ⟨uOrderEnd p.1, p.2⟩

abbrev qOldCoverEnd_spec  (p : QLiftedOld a)  :=
  congrArg Subtype.val (qOldPartOrderIso.symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

variable [Fintype V]

theorem qOldCoverEnd_isPosetCover (x : X) (hx : IsConnected (orderCx X)) :
    IsPosetCover (qOldCoverEnd (qNew (A := A) (att := att) x)) := by
  letI : Nonempty X := ⟨x⟩
  have hc : IsConnected (orderCx (Qpos A X att)) :=
    qpos_isConnected_of_zpos (zpos_isConnected hx)
  have hf := IsPosetCover.restriction
    (uOrderEnd (P := Qpos A X att) (a := qNew x)) {p | InQOld p}
    (uOrderEnd_isPosetCover hc)
  exact hf.postcompose_orderIso qOldPartOrderIso

end FiniteChains.Davis
