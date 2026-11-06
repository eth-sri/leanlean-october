import RequestProject.RoseStrictEdges
import RequestProject.RelatorCircleEdges


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- The actual attaching map preserves strict comparability on each valid relator circle. -/
theorem relatorCircleAttaching_strictMono :
    StrictMono (fun x : RelatorCircle w j => aFun w x.val) := by
  have he : ∀ e : StrictOrdEdge (RelatorCircle w j),
      aFun w e.val.1.val < aFun w e.val.2.val := by
    intro e
    cases' relatorCircle_edge_cases w j e with k he
    cases' exists_get_of_lt w k.isLt with a ha
    rcases he with rfl | rfl | rfl | rfl
    · change aFun w (TCirc.pt w j k.val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cor, aFun_pt_cedgL_of_get w ha]
      tauto
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgL)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgL_of_get w ha]
      tauto
    · change aFun w (TCirc.pt w j k.val CPos.cmid) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cmid_of_get w ha, aFun_pt_cedgR_of_get w ha]
      tauto
    · change aFun w (TCirc.pt w j (relatorCircleNext w j k).val CPos.cor) <
        aFun w (TCirc.pt w j k.val CPos.cedgR)
      rw [aFun_pt_cor, aFun_pt_cedgR_of_get w ha]
      tauto
  intro x y h
  exact he ⟨(x, y), h⟩
