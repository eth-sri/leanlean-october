module

public import RequestProject.RelatorCircleEdges

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

private theorem relatorCircle_boundary_values
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) (k : Fin (w j).length) :
    let d := bdry1 (strictOrderCx (RelatorCircle w j)) c
    d (relatorCirclePoint w j k CPos.cedgL) = c (relatorCircleEdge0 w j k) + c (relatorCircleEdge1 w j k) ∧
    d (relatorCirclePoint w j k CPos.cmid) = -c (relatorCircleEdge1 w j k) - c (relatorCircleEdge2 w j k) ∧
    d (relatorCirclePoint w j k CPos.cedgR) = c (relatorCircleEdge2 w j k) + c (relatorCircleEdge3 w j k) ∧
    d (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) =
      -c (relatorCircleEdge0 w j (relatorCircleNext w j k)) - c (relatorCircleEdge3 w j k) := by
  classical
  dsimp only
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hc
    obtain ⟨g₁, g₂, g₃, g₄⟩ := hd
    simp only [map_add, Finsupp.add_apply, h₁, h₂, h₃, h₄, g₁, g₂, g₃, g₄]
    grind
  | single e n =>
    obtain ⟨l, he⟩ := relatorCircle_edge_cases w j e
    have hnext : (relatorCircleNext w j l).val = (relatorCircleNext w j k).val ↔ l = k :=
      ⟨fun h => relatorCircleNext_injective w j (Fin.ext h), fun h => h ▸ rfl⟩
    rcases he with rfl | rfl | rfl | rfl <;>
      simp [bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
        relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
        Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc, hnext] <;> grind

theorem relatorCircle_cycle_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (k : Fin (w j).length) :
    c (relatorCircleEdge1 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge2 w j k) = c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge3 w j k) = -c (relatorCircleEdge0 w j k) ∧
    c (relatorCircleEdge0 w j (relatorCircleNext w j k)) =
      c (relatorCircleEdge0 w j k) := by
  obtain ⟨hl, hm, hr, hk⟩ := relatorCircle_boundary_values w j c k
  rw [hc, Finsupp.zero_apply] at hl hm hr hk
  omega

theorem relatorCircle_cycle_coefficient_constant
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    c (relatorCircleEdge0 w j k) = c (relatorCircleEdge0 w j ⟨0, hpos⟩) := by
  apply relatorCircle_successor_invariant_constant w j
    (fun l => c (relatorCircleEdge0 w j l)) _ hpos k
  intro l
  exact (relatorCircle_cycle_coefficients w j c hc l).2.2.2

theorem relatorCircle_cycle_all_coefficients
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) (k : Fin (w j).length) :
    let a := c (relatorCircleEdge0 w j ⟨0, hpos⟩)
    c (relatorCircleEdge0 w j k) = a ∧
    c (relatorCircleEdge1 w j k) = -a ∧
    c (relatorCircleEdge2 w j k) = a ∧
    c (relatorCircleEdge3 w j k) = -a := by
  dsimp only
  have h := relatorCircle_cycle_coefficients w j c hc k
  have h0 := relatorCircle_cycle_coefficient_constant w j c hc hpos k
  simp_all

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
