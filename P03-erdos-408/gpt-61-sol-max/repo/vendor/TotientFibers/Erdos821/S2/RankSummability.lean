module
public import Mathlib.Tactic

public import Erdos821.S2.HighRankTask

/-! Every equality-rank expression at a finite cutoff is genuinely summable. -/

@[expose] public section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Erdos821.S2Core

open Erdos821.Blueprint.Graph

variable {F : FixedData} {P : PrimeGroups} {J m : ℕ}

theorem rankHistory_hasFiniteSupport {β : Type*} [Zero β]
    (A : Model F P J m) (n B : ℕ)
    (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))))
    (f : MemoryHistory A n → β) :
    Function.HasFiniteSupport (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        f H else 0) := by
  have hf : Set.Finite {H : MemoryHistory A n | H.Truncated B} :=
    @Set.toFinite (MemoryHistory A n) {H | H.Truncated B}
      (truncated_history_finite A n B)
  apply hf.subset
  simp_all

section
variable (A : Model F P J m) (n B : ℕ) (rho theta : ℝ) (pi : Finset (Finset (Fin (Fintype.card (BirthAddress P (J + F.ell) n B)))))

theorem highRankHistoryExpression_summable    
     
      :
    Summable (fun H : MemoryHistory A n =>
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        ‖H.Weight rho theta‖ else 0) :=
  summable_of_hasFiniteSupport (Erdos821.S2Core.rankHistory_hasFiniteSupport A n B pi fun H => ‖H.Weight rho theta‖)

theorem lowRankHistoryExpression_norm_le    
     
      :
    ‖lowRankHistoryExpression A n B rho theta pi‖ ≤
      highRankHistoryExpression A n B rho theta pi := by
  let f (H : MemoryHistory A n) : ℂ :=
    if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
      H.Weight rho theta else 0
  have he (H : MemoryHistory A n) : ‖f H‖ =
      if H.Valid ∧ H.Truncated B ∧ birthEvent (H.performedFin B) (H.valueFin B) pi then
        ‖H.Weight rho theta‖ else 0 := by
    simp only [f, apply_ite norm, norm_zero]
  have hs : Summable (fun H => ‖f H‖) := by
    simp_all [highRankHistoryExpression_summable]
  simpa only [lowRankHistoryExpression, highRankHistoryExpression, he] using
    norm_tsum_le_tsum_norm hs

end

end Erdos821.S2Core
