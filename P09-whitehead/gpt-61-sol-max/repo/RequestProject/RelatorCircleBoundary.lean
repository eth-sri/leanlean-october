import Mathlib.Tactic

import RequestProject.RelatorCircleEdges

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

variable (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
variable (k : Fin (w j).length)
include k in
theorem relatorCircle_boundary_left
      :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgL) =
        c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

include k in
theorem relatorCircle_boundary_mid
      :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cmid) =
        -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

include k in
theorem relatorCircle_boundary_right
      :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgR) =
        c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    grind

theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l he
  have he' := congrArg Fin.val he
  change (k.val + 1) % (w j).length = (l.val + 1) % (w j).length at he'
  
  
  apply Fin.ext
  by_cases hks : k.val + 1 < (w j).length <;>
    by_cases hls : l.val + 1 < (w j).length
  · classical simp_all [Nat.mod_eq_of_lt]
  · classical grind [Nat.mod_eq_of_lt, Nat.mod_self]
  · classical grind [Nat.mod_self, Nat.mod_eq_of_lt]
  · omega

include k in
theorem relatorCircle_boundary_corner
      :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
        -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) -
          c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, Finsupp.add_apply, hc, hd]; ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    classical grind [FiniteChains.PresModel.relatorCircleNext_injective]

variable (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
include hc in
theorem relatorCircle_cycle_coefficients
    
    
    (k : Fin (w j).length) :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  have hl := relatorCircle_boundary_left w j c k
  have hm := relatorCircle_boundary_mid w j c k
  have hr := relatorCircle_boundary_right w j c k
  have hk := relatorCircle_boundary_corner w j c k
  rw [hc, Finsupp.zero_apply] at hl hm hr hk
  omega

theorem relatorCircle_successor_invariant_constant
    (a : Fin (w j).length → ℤ)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    a k = a ⟨0, hpos⟩ := by
  have hi : ∀ n (hn : n < (w j).length), a ⟨n, hn⟩ = a ⟨0, hpos⟩ := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hp : n < (w j).length := by omega
      have hs : relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      rw [← hs, ha]
      exact ih hp
  exact hi k.val k.isLt

include hc in
abbrev relatorCircle_cycle_coefficient_constant
    
    
    (hpos : 0 < (w j).length) (k : Fin (w j).length)  :=
  FiniteChains.PresModel.relatorCircle_successor_invariant_constant w j
    (fun (l : Fin (w j).length) => c (FiniteChains.PresModel.relatorCircleEdge0 w j l))
    (fun (l : Fin (w j).length) => (FiniteChains.PresModel.relatorCircle_cycle_coefficients w j c hc l).right.right.right)
    hpos k

include hc in
theorem relatorCircle_cycle_all_coefficients
    
    
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  simp_all [relatorCircle_cycle_coefficients, relatorCircle_cycle_coefficient_constant]

/-- Agreement at one genuine circle edge determines an entire one-cycle. -/
theorem relatorCircle_cycle_ext
    (c d : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) d = 0)
    (hpos : 0 < (w j).length)
    (he : c (relatorCircleEdge0 w j ⟨0, hpos⟩) =
      d (relatorCircleEdge0 w j ⟨0, hpos⟩)) : c = d := by
  ext e
  obtain ⟨k, hk⟩ := relatorCircle_edge_cases w j e
  aesop (add simp [relatorCircle_cycle_all_coefficients])

end FiniteChains.PresModel
