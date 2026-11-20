module

public import RequestProject.RelatorCircleBoundary

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

variable (k : Fin (w j).length)

/-- The four signed actual incidence edges for one letter of the attaching circle. -/
noncomputable def relatorCircleLetterChain :
    StrictOrdEdge (RelatorCircle w j) →₀ ℤ :=
  Finsupp.single (relatorCircleEdge0 w j k) 1 -
    Finsupp.single (relatorCircleEdge1 w j k) 1 +
    Finsupp.single (relatorCircleEdge2 w j k) 1 -
    Finsupp.single (relatorCircleEdge3 w j k) 1

theorem relatorCircleLetterChain_boundary :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleLetterChain w j k) =
      Finsupp.single (relatorCirclePoint w j (relatorCircleNext w j k) CPos.cor) 1 -
      Finsupp.single (relatorCirclePoint w j k CPos.cor) 1 := by
  classical
  simp only [relatorCircleLetterChain, map_add, map_sub, Comb.bdry1_single (X := strictOrderCx (RelatorCircle w j)), one_smul]
  simp [strictOrderCx,
    relatorCircleEdge0, relatorCircleEdge1, relatorCircleEdge2, relatorCircleEdge3]

/-- The genuine finite attaching-circle fundamental chain. -/
noncomputable def relatorCircleFundamentalChain :=
  ∑ k : Fin _, relatorCircleLetterChain w j k

theorem relatorCircleLetterChain_edge0 (l k : Fin _) :
    relatorCircleLetterChain w j l (relatorCircleEdge0 w j k) = if l = k then 1 else 0 := by
  classical
  by_cases h : l = k
  · simp_all [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1, relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt, RelatorCircle, StrictOrdEdge, TCirc]
  · have hv : l.val ≠ k.val := fun he => h (Fin.ext he)
    simp [relatorCircleLetterChain, relatorCircleEdge0, relatorCircleEdge1,
      relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
      RelatorCircle, StrictOrdEdge, TCirc, hv, h]

theorem relatorCircleFundamentalChain_cycle :
    Comb.bdry1 (strictOrderCx (RelatorCircle w j)) (relatorCircleFundamentalChain w j) = 0 := by
  classical
  rw [relatorCircleFundamentalChain, map_sum]
  simp_rw [relatorCircleLetterChain_boundary]
  let e := Equiv.ofBijective
    _ ⟨relatorCircleNext_injective w j,
      Finite.surjective_of_injective (relatorCircleNext_injective w j)⟩
  have he := e.sum_comp (fun k =>
    Finsupp.single (relatorCirclePoint w j k CPos.cor) (1 : ℤ))
  aesop

theorem relatorCircleFundamentalChain_edge0 (k : Fin _) :
    relatorCircleFundamentalChain w j (relatorCircleEdge0 w j k) = 1 := by
  simp [relatorCircleFundamentalChain, relatorCircleLetterChain_edge0]

/-- Every actual attaching-circle cycle is the corresponding integer multiple of
its genuine fundamental chain. -/
theorem relatorCircle_cycle_eq_smul_fundamental
    (c : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hpos : 0 < (w j).length) :
    c = c (relatorCircleEdge0 w j ⟨0, hpos⟩) • relatorCircleFundamentalChain w j := by
  refine relatorCircle_cycle_ext w j c _ hc ?_ hpos ?_
  · rw [map_smul, relatorCircleFundamentalChain_cycle, smul_zero]
  · simp [relatorCircleFundamentalChain_edge0]

end FiniteChains.PresModel
