module

public import RequestProject.PresConeExcursionReplacement

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- Actual relator apices are maximal vertices in the actual presentation poset. -/
theorem presCone_apex_maximal (p : PresPos w) (h : apexOf w j ≤ p) : p = apexOf w j := by
  cases p with
  | inl p => exact h.elim
  | inr k => exact congrArg Sum.inr h.symm

/-- A strict actual incidence cannot have an apex as its lower endpoint. -/
theorem presCone_strictEdge_source_ne_apex (e : StrictOrdEdge (PresPos w)) :
    e.val.1 ≠ apexOf w j := by
  intro h
  have ht := presCone_apex_maximal w j e.val.2 (h ▸ e.property.le)
  grind

variable (e : (strictOrderCx (PresPos w)).E × Bool)

/-- Every actual strict germ leaving an apex is a reversed incoming incidence. -/
theorem presCone_strictGerm_from_apex
    (h : germSrc (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e = apexOf w j) :
    e.2 = false ∧ e.1.val.2 = apexOf w j := by
  rcases e with ⟨e, b⟩
  cases b with
  | false => solve_by_elim
  | true => solve_by_elim [presCone_strictEdge_source_ne_apex]

/-- Every actual strict germ entering an apex is a positive incoming incidence. -/
theorem presCone_strictGerm_to_apex
    (h : germTgt (strictOrderCx (PresPos w)).src (strictOrderCx (PresPos w)).tgt e = apexOf w j) :
    e.2 = true ∧ e.1.val.2 = apexOf w j := by
  rcases e with ⟨e, b⟩
  cases b with
  | false => solve_by_elim [presCone_strictEdge_source_ne_apex]
  | true => solve_by_elim

end FiniteChains.PresModel
