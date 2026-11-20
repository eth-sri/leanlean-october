module

public import QPBT.Games.StrategyClasses
public import QPBT.Games.DistanceTheorems.Support

/-! Player exchange for symmetric games and their strategies. -/

@[expose] public section

namespace MIPStarRE.QPBT

open MIPStarRE.LDT DistanceCalculus
open scoped BigOperators

/-- Exchange the two players in a symmetric game, including their tensor factors. -/
noncomputable def SymmetricGame.swapStrategy (G : SymmetricGame) (S : Strategy G.toGame) :
    Strategy G.toGame where
  ιA := S.ιB
  ιB := S.ιA
  ψ := reindexState (Equiv.prodComm _ _) S.ψ
  ψ_norm := (reindexState_norm_eq _ _).trans S.ψ_norm
  A := S.B
  B := S.A

@[simp] theorem SymmetricGame.outcomeWeight_swapStrategy (G : SymmetricGame)
    (S : Strategy G.toGame) (x y : G.Question) (a b : G.Answer) :
    outcomeWeight (G.swapStrategy S) x y a b = outcomeWeight S y x b a := by
  change stateQForm (reindexState (Equiv.prodComm _ _) S.ψ)
    (heteroKron ((S.B x).effect a) ((S.A y).effect b)) = _
  rw [stateQForm_reindexState, reindexOp_prodComm_heteroKron]
  rfl

/-- Exchanging players preserves the value of a strategy in a symmetric game. -/
@[simp] theorem SymmetricGame.swapStrategy_value (G : SymmetricGame) (S : Strategy G.toGame) :
    (G.swapStrategy S).value = S.value := by
  classical
  change avgOver G.μ (fun x => ∑ a : G.Answer, ∑ b : G.Answer,
      if G.decide x.1 x.2 a b then outcomeWeight (G.swapStrategy S) x.1 x.2 a b else 0) =
    avgOver G.μ (fun x => ∑ a : G.Answer, ∑ b : G.Answer,
      if G.decide x.1 x.2 a b then outcomeWeight S x.1 x.2 a b else 0)
  simp only [avgOver_eq_sum_univ, outcomeWeight_swapStrategy]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun ⟨x, y⟩ => ?_
  dsimp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
  rw [G.μ_symm x y, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [G.decide_symm x y a b]
  rfl

end MIPStarRE.QPBT
