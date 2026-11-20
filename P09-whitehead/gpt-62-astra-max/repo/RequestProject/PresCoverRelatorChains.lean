module

public import RequestProject.PresCoverCycleCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J P : Type u} [PartialOrder P] (w : J → List (α × Bool))
  (f : P → PresPos w) (hf : IsPosetCover f) (hpos : ∀ j, 0 < (w j).length)

/-- Actual lifted relator apices, with their actual relator label. -/
def PresCoverRelator := {p : P × J // f p.1 = apexOf w p.2}

/-- The distinguished actual cone triangle over the first left attaching-circle incidence. -/
def presCoverRelatorTriangle (p : PresCoverRelator w f) :=
  strictConeTriangle p.1.1
    ((strictOrderEdgeEquiv
      (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)).symm
      (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))

theorem presCoverRelatorTriangle_injective :
    Function.Injective (presCoverRelatorTriangle w f hf hpos) := by
  intro p q he
  have hv := congrArg (fun t : StrictOrdTri P => t.1.2.2) he
  have hj : p.1.2 = q.1.2 := by
    apply Sum.inr_injective
    exact p.2.symm.trans ((congrArg f hv).trans q.2)
  apply Subtype.ext
  exact Prod.ext hv hj

/-- A genuine finite triangle chain yields a genuine finitely supported relator chain. -/
def presCoverRelatorChain :
    (StrictOrdTri P →₀ ℤ) →ₗ[ℤ] (PresCoverRelator w f →₀ ℤ) :=
  (Finsupp.comapDomain.addMonoidHom
    (presCoverRelatorTriangle_injective w f hf hpos)).toIntLinearMap

variable (c : StrictOrdTri P →₀ ℤ) (p : PresCoverRelator w f)

theorem presCoverRelatorChain_apply :
    presCoverRelatorChain w f hf hpos c p = c (presCoverRelatorTriangle w f hf hpos p) := rfl

theorem presCoverRelatorChain_circle :
    presCoverRelatorChain w f hf hpos c p =
      presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
        (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩) := by
  let e := strictOrderEdgeEquiv (presCoverConeCircleOrderIso w f hf p.1.1 p.1.2 p.2)
  have he := presCoverConeCircleChain_apply w f hf p.1.1 p.1.2 p.2 c
    (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))
  change _ = c (presCoverRelatorTriangle w f hf hpos p) at he
  rw [presCoverRelatorChain_apply]
  rw [← he]
  change presCoverConeCircleChain w f hf p.1.1 p.1.2 p.2 c
    (e (e.symm (relatorCircleEdge0 w p.1.2 ⟨0, hpos p.1.2⟩))) = _
  simp

/-- The genuine strict two-cycle module embeds linearly in actual lifted-relator chains. -/
def presCoverCycleRelatorLinear :=
  (presCoverRelatorChain w f hf hpos).comp
    (LinearMap.ker (Comb.bdry2 (strictOrderCx P))).subtype

end FiniteChains.PresModel
