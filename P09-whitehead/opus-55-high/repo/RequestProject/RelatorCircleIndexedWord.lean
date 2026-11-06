import RequestProject.RelatorCircleBoundaryHomeomorph
import RequestProject.PresPosetAlpha
import Mathlib.Data.List.OfFn
import RequestProject.Tac


/-! Exact enumeration of the actual circle edges as the four edges of each
successive letter. This is a list identity, including the final closing
edge, not merely an equality of free-group elements. Pending verification. -/

noncomputable section
bwd

namespace FiniteChains.PresModel
open Comb
open scoped Classical

variable {A J : Type} (w : J → List (A × Bool)) (j : J)

def circleSegmentGerm (k : Fin (w j).length) (t : Fin 4) :=
  ![ordPos (TCirc.cor_le_cedgL w k.isLt),
    ordNeg (TCirc.cmid_le_cedgL w k.isLt),
    ordPos (TCirc.cmid_le_cedgR w k.isLt),
    ordNeg (TCirc.cor_csucc_le_cedgR w k.isLt)] t

def circleIndexedGerm (i : Fin ((w j).length * 4)) :=
  circleSegmentGerm w j (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

@[simp] theorem circleIndexedGerm_pair k t :
    circleIndexedGerm w j (finProdFinEquiv (k, t)) = circleSegmentGerm w j k t := by
  simp [circleIndexedGerm, Equiv.symm_apply_apply]

theorem circleIndexedGerm_src i :
    gSrcX (orderCx (TCirc w)) (circleIndexedGerm w j i) =
      ((relatorCircleIndexEquiv w j).symm i).val := by
  obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [circleIndexedGerm_pair, relatorCircleIndex_symm_pair]
  fin_cases t <;> rfl

theorem circleIndexedGerm_tgt hn i :
    gTgtX (orderCx (TCirc w)) (circleIndexedGerm w j i) =
      (relatorCircleSuccessor w j hn ((relatorCircleIndexEquiv w j).symm i)).val := by
  obtain ⟨⟨k, t⟩, rfl⟩ := finProdFinEquiv.surjective i
  rw [circleIndexedGerm_pair, relatorCircleIndex_symm_pair]
  fin_cases t <;> rfl

theorem circleSegmentGerm_ofFn k :
    List.ofFn (circleSegmentGerm w j k) = segAt w j k.val := by
  rw [segAt, dif_pos k.isLt]
  rfl

theorem circleSegments_flatten m :
    (List.ofFn (fun k : Fin m => segAt w j k.val)).flatten = circPath w j m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    aesop

theorem circleIndexedGerm_ofFn : List.ofFn (circleIndexedGerm w j) = circLoop w j := by
  rw [List.ofFn_mul]
  have hblock (k : Fin (w j).length) :
      List.ofFn (fun t : Fin 4 => circleIndexedGerm w j
        ⟨k.val * 4 + t.val, by omega⟩) = segAt w j k.val := by
    have he (t : Fin 4) :
        ⟨k.val * 4 + t.val, by omega⟩ =
          finProdFinEquiv (k, t) := by
      apply Fin.ext
      change k.val * 4 + t.val = t.val + 4 * k.val
      omega
    simp_rw [he, circleIndexedGerm_pair]
    exact circleSegmentGerm_ofFn w j k
  simp_rw [hblock]
  exact circleSegments_flatten w j _
