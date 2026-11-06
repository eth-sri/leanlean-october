import RequestProject.RelatorCircleBoundary
import RequestProject.Tac
noncomputable section


bwd

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

/-- The four signed actual incidence edges for one letter of the attaching circle. -/
def relatorCircleLetterChain (k : Fin (w j).length) :
    StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  Finsupp.single (relatorCircleEdge0 w j k) 1 -
    Finsupp.single (relatorCircleEdge1 w j k) 1 +
    Finsupp.single (relatorCircleEdge2 w j k) 1 -
    Finsupp.single (relatorCircleEdge3 w j k) 1

theorem relatorCircleLetterChain_boundary k :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleLetterChain w j k) =
      Finsupp.single (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) 1 -
      Finsupp.single (relatorCirclePoint w j k CPos.cor) 1 := by
  classical
  simp [relatorCircleLetterChain, map_add, map_sub, Comb.bdry1_single (X := strictOrderCx (RelatorCircle w j)), one_smul]
  simp [strictOrderCx,
    relatorCircleEdge0, relatorCircleEdge1, relatorCircleEdge2, relatorCircleEdge3]

/-- The genuine finite attaching-circle fundamental chain. -/
def relatorCircleFundamentalChain :=
  ∑ k : Fin (w j).length, relatorCircleLetterChain w j k

theorem relatorCircleLetterChain_edge0 l k :
    relatorCircleLetterChain w j l (relatorCircleEdge0 w j k) = if l = k then 1 else 0 := by
  classical
  by_cases h : l = k
  · subst l
    simp [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1,
      relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
      RelatorCircle, StrictOrdEdge, TCirc]
  · have hv : l.val ≠ k.val := by omega
    simp [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1,
      relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
      RelatorCircle, StrictOrdEdge, TCirc, hv, h]

theorem relatorCircleFundamentalChain_cycle :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleFundamentalChain w j) = 0 := by
  classical
  rw [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_boundary]
  let e : Fin (w j).length ≃ Fin (w j).length := Equiv.ofBijective
    (relatorCircleNext w j) ⟨relatorCircleNext_injective w j,
      Finite.surjective_of_injective (relatorCircleNext_injective w j)⟩
  have he := e.sum_comp (fun k =>
    Finsupp.single (relatorCirclePoint w j k CPos.cor) (1 : ℤ))
  aesop

theorem relatorCircleFundamentalChain_edge0 k :
    relatorCircleFundamentalChain w j (relatorCircleEdge0 w j k) = 1 := by
  classical
  simp [relatorCircleFundamentalChain, relatorCircleLetterChain_edge0]

/-- Every actual attaching-circle cycle is the corresponding integer multiple of
its genuine fundamental chain. -/
theorem relatorCircle_cycle_eq_smul_fundamental
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    hpos :
    c = c (relatorCircleEdge0 w j ⟨0, hpos⟩) • relatorCircleFundamentalChain w j := by
  refine relatorCircle_cycle_ext w j c _ hc ?_ hpos ?_
  · rw [map_smul, relatorCircleFundamentalChain_cycle, smul_zero]
  · simp [relatorCircleFundamentalChain_edge0]
