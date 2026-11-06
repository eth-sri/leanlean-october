import RequestProject.RelatorCircleEdges
import RequestProject.Tac


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem relatorCircle_boundary_left
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) k :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgL) =
        c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k) := by
  classical
  lin_ind c with c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd]; ring
  | e n =>
    cases' relatorCircle_edge_cases w j e with l he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_mid
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) k :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cmid) =
        -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k) := by
  classical
  lin_ind c with c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd]; ring
  | e n =>
    cases' relatorCircle_edge_cases w j e with l he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]

theorem relatorCircle_boundary_right
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) k :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j k CPos.cedgR) =
        c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k) := by
  classical
  lin_ind c with c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd]; ring
  | e n =>
    cases' relatorCircle_edge_cases w j e with l he
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
  · simp_all [Nat.mod_eq_of_lt hks, Nat.mod_eq_of_lt hls]
  · have hs : l.val + 1 = (w j).length := by omega
    simp_all [Nat.mod_eq_of_lt hks, hs, Nat.mod_self]
  · have hs : k.val + 1 = (w j).length := by omega
    simp_all [hs, Nat.mod_self, Nat.mod_eq_of_lt hls]
  · omega

theorem relatorCircle_boundary_corner
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) k :
    (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c)
      (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
        -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) -
          c (relatorCircleEdge3 w j k) := by
  classical
  lin_ind c with c d hc hd => simp [map_add, Finsupp.add_apply, hc, hd]; ring
  | e n =>
    cases' relatorCircle_edge_cases w j e with l he
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
    by_cases h : l = k
    · subst l
      simp
    · have hn : (relatorCircleNext w j l).val ≠ (relatorCircleNext w j k).val := by
        intro he
        exact h (relatorCircleNext_injective w j (Fin.ext he))
      omega

theorem relatorCircle_cycle_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    k :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  have hl := relatorCircle_boundary_left w j c k
  have hm := relatorCircle_boundary_mid w j c k
  have hr := relatorCircle_boundary_right w j c k
  have hk := relatorCircle_boundary_corner w j c k
  grind

theorem relatorCircle_successor_invariant_constant
    (a : Fin (w j).length → ℤ)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    hpos k :
    a k = a ⟨0, hpos⟩ := by
  have hi : ∀ n hn, a ⟨n, hn⟩ = a ⟨0, hpos⟩ := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      have hp : n < (w j).length := by omega
      have hs : relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      grind
  simp_all

theorem relatorCircle_cycle_coefficient_constant
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    hpos k :
    c (relatorCircleEdge0 w j k) = c (relatorCircleEdge0 w j ⟨0, hpos⟩) := by
  apply relatorCircle_successor_invariant_constant w j
    (fun l => c (relatorCircleEdge0 w j l)) _ hpos k
  intro l
  exact (relatorCircle_cycle_coefficients w j c hc l).2.2.2

theorem relatorCircle_cycle_all_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    hpos k :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  dsimp
  have h := relatorCircle_cycle_coefficients w j c hc k
  have h0 := relatorCircle_cycle_coefficient_constant w j c hc hpos k
  omega

/-- Agreement at one genuine circle edge determines an entire one-cycle. -/
theorem relatorCircle_cycle_ext
    (c d : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) d = 0)
    hpos
    (he : c (relatorCircleEdge0 w j ⟨0, hpos⟩) =
      d (relatorCircleEdge0 w j ⟨0, hpos⟩)) : c = d := by
  ext e
  cases' relatorCircle_edge_cases w j e with k hk
  have hck := relatorCircle_cycle_all_coefficients w j c hc hpos k
  have hdk := relatorCircle_cycle_all_coefficients w j d hd hpos k
  grind
