module

public import RequestProject.RelatorCircleEdges

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l he
  have he' := congrArg Fin.val he
  change (k.val + 1) % (w j).length = (l.val + 1) % (w j).length at he'
  have hk := k.isLt
  have hl := l.isLt
  apply Fin.ext
  by_cases hks : k.val + 1 < (w j).length <;>
    by_cases hls : l.val + 1 < (w j).length
  · simp_all [Nat.mod_eq_of_lt]
  · have hs : l.val + 1 = (w j).length := by omega
    simp_all [Nat.mod_eq_of_lt]
  · have hs : k.val + 1 = (w j).length := by omega
    simp_all [Nat.mod_eq_of_lt]
  · omega

variable (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)

/-- The four boundary coefficients of one subdivided letter, with the corner
read at the start of the next letter. -/
theorem relatorCircle_boundary (k : Fin (w j).length) (s : CPos) :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c
      (relatorCirclePoint w j (if s = .cor then relatorCircleNext w j k else k) s) =
    match s with
    | .cedgL => c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k)
    | .cmid => -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k)
    | .cedgR => c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k)
    | .cor => -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) - c (relatorCircleEdge3 w j k) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => aesop
  | add c d hc hd => rw [map_add, Finsupp.add_apply, hc, hd]; cases s <;> simp <;> ring
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    have hnext : (relatorCircleNext w j l).val = (relatorCircleNext w j k).val ↔ l.val = k.val := by
      simp [Fin.val_inj, (relatorCircleNext_injective w j).eq_iff]
    cases s <;> rcases he with rfl | rfl | rfl | rfl <;>
      simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc, hnext]

theorem relatorCircle_cycle_coefficients
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (k : Fin (w j).length) :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  let circleboundary := relatorCircle_boundary w j c k
  have hL := circleboundary .cedgL
  have hM := circleboundary .cmid
  have hR := circleboundary .cedgR
  have hC := circleboundary .cor
  grind

theorem relatorCircle_successor_invariant_constant
    (a : Fin (w j).length → ℤ)
    (ha : ∀ k, a (relatorCircleNext w j k) = a k)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    a k = a ⟨0, hpos⟩ := by
  have hi : ∀ n (hn : n < (w j).length), a ⟨n, hn⟩ = a ⟨0, hpos⟩ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have hp : n < (w j).length := by omega
      have hs : relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        exact Nat.mod_eq_of_lt hn
      grind
  exact hi k.val k.isLt

section

variable (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length)
    (k : Fin (w j).length)
include hc

theorem relatorCircle_cycle_coefficient_constant :
    c (relatorCircleEdge0 w j k) = c (relatorCircleEdge0 w j ⟨0, hpos⟩) := by
  apply relatorCircle_successor_invariant_constant w j
    (fun l => c (relatorCircleEdge0 w j l)) _ hpos k
  simp_all [relatorCircle_cycle_coefficients]

theorem relatorCircle_cycle_all_coefficients :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  simp_all [relatorCircle_cycle_coefficients, relatorCircle_cycle_coefficient_constant]

end

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
  have hck := relatorCircle_cycle_all_coefficients w j c hc hpos k
  have hdk := relatorCircle_cycle_all_coefficients w j d hd hpos k
  grind

end FiniteChains.PresModel
