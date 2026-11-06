import RequestProject.PresIdentityCoverChains
import RequestProject.RelatorCircleExponentChain
import RequestProject.ExponentCorrection
import RequestProject.OrderStrictAcyclicityComparison
import RequestProject.OrderNerveDimension
import RequestProject.PresPosetConnected
import RequestProject.Tac


/-! Actual singular acyclicity of a presentation realization forces its
finitely supported exponent matrix to be bijective. The alphabets and relator
sets are arbitrary; finiteness is used only in individual chain supports. -/
bwd

namespace FiniteChains.PresModel.IdentityChains
open Comb Comb.StrictNormalized
universe u
variable {α J : Type u} (w : J → List (α × Bool))

theorem roseProjection_relatorBoundary p :
    roseProjection w (presCoverCylinderRelatorBoundary w id (cover w) p) =
      roseIntegerRealize (FiniteChains.expVec (FreeGroup.mk (w p.1.2))) := by
  change mapOne (cylRetr _) _ (baseProjection w _) = _
  rwd [baseProjection_relatorBoundary]
  unfold cylinderBoundary
  rwd [mapOne_comp]
  exact relatorCircleFundamentalChain_exponent w p.1.2

/-- With the actual identity-cover labels, the actual attaching differential
is the original exponent matrix, realized by genuine rose cycles. -/
theorem roseProjection_relatorBoundaryChain c :
    roseProjection w (presCoverCylinderRelatorBoundaryChain w id (cover w) c) =
      roseIntegerRealize (expMatrix (fun j => FreeGroup.mk (w j))
        (Finsupp.mapDomain (·.1.2) c)) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero =>
      rfl
  | add c d hc hd => simp only [map_add, Finsupp.mapDomain_add, hc, hd]
  | single p n =>
    simp [presCoverCylinderRelatorBoundaryChain, Finsupp.linearCombination_single, map_smul, roseProjection_relatorBoundary, Finsupp.mapDomain_single, expMatrix]

theorem roseProjection_relative_boundary hpos
    (c : StrictOrdTri (PresPos w) →₀ ℤ) (b : StrictOrdEdge (Base w) →₀ ℤ)
    (hb : Comb.bdry2 (strictOrderCx (PresPos w)) c =
      chain1 (strictSubposetIncl (coneAdjBaseSet (S := circSet w))) b) :
    roseProjection w b =
      roseIntegerRealize (expMatrix (fun j => FreeGroup.mk (w j))
        (Finsupp.mapDomain (·.1.2)
          (presCoverRelatorChain w id (cover w) hpos c))) := by
  have h := congrArg (roseProjection w)
    (presCover_relative_collapsed_boundary w id (cover w) hpos c b hb)
  grind [roseProjection_collapse, roseProjection_relatorBoundaryChain]

/-- Vanishing actual H₂ rules out every exponent-matrix kernel vector.
The proof realizes the vector by actual cone fans and an actual cylinder
prism before applying H₂. -/
theorem expMatrix_injective_of_strict_h2 (hpos : ∀ j, 0 < (w j).length)
    (h2 : Function.Injective (Comb.bdry2 (strictOrderCx (PresPos w)))) :
    Function.Injective (expMatrix (fun j => FreeGroup.mk (w j))) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  let d := Finsupp.mapDomain (relatorEquiv w) c
  have hd : Finsupp.mapDomain (·.1.2) d = c := by
    rwd [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  have hb : roseProjection w (presCoverCylinderRelatorBoundaryChain w id (cover w) d) = 0 := by
    rwd [roseProjection_relatorBoundaryChain, hd, hc, map_zero]
  obtain ⟨z, hz, hcoord⟩ := exists_presCover_cycle_of_collapsed_relator_boundary
    w id _ hpos d
    (collapsed_eq_zero_of_roseProjection_eq_zero w _ hb)
  have hd0 : d = 0 := by simp_all
  simp_all

/-- Vanishing actual H₁ supplies every exponent vector: realize it on the
rose, fill it in the original strict complex, and extract the actual apex
coefficients of that filling. -/
theorem expMatrix_surjective_of_strict_h1 (hpos : ∀ j, 0 < (w j).length)
    (h1 : ∀ c : StrictOrdEdge (PresPos w) →₀ ℤ,
      Comb.bdry1 (strictOrderCx (PresPos w)) c = 0 →
        ∃ d : StrictOrdTri (PresPos w) →₀ ℤ,
          Comb.bdry2 (strictOrderCx (PresPos w)) d = c) :
    Function.Surjective (expMatrix (fun j => FreeGroup.mk (w j))) := by
  intro v
  let b := roseInclusion w (roseIntegerRealize v)
  let I := strictSubposetIncl (coneAdjBaseSet (S := circSet w))
  have hb : Comb.bdry1 (strictOrderCx (Base w)) b = 0 := by
    change Comb.bdry1 _ (chain1 (strictOrderCxMap _
      (roseIntoBase_strictMono w)) (roseIntegerRealize v)) = 0
    simp [bdry1_chain1, roseIntegerRealize_cycle, map_zero]
  have hz : Comb.bdry1 _ (chain1 I b) = 0 := by
    erw [bdry1_chain1 I b, hb, map_zero]
  cases' h1 _ hz with d hd
  refine ⟨Finsupp.mapDomain (·.1.2)
    (presCoverRelatorChain w id (cover w) hpos d), ?_⟩
  apply roseIntegerRealize_injective
  have h := roseProjection_relative_boundary w hpos d b hd
  simp_all [show b = roseInclusion w (roseIntegerRealize v) from rfl, roseProjection_inclusion]

end FiniteChains.PresModel.IdentityChains

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u}

/-- An acyclic actual strict presentation complex has a bijective exponent
matrix, without finiteness assumptions on either cell-index type. -/
theorem expMatrix_bijective_of_strict_pres_acyclic
    ρ (w : J → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)
    (h : IsAcyclic (strictOrderCx (PresPos w))) : Function.Bijective (expMatrix ρ) := by
  have he := funext hw
  rwd [← he]
  exact ⟨IdentityChains.expMatrix_injective_of_strict_h2 w hpos h.h2,
    IdentityChains.expMatrix_surjective_of_strict_h1 w hpos h.h1⟩

end FiniteChains.PresModel

namespace FiniteChains.PresModel
open Comb CategoryTheory
variable {α J : Type}

/-- The actual singular acyclicity hypothesis discharges the algebraic matrix
hypothesis used by the arbitrary-cell initial construction. -/
theorem expMatrix_bijective_of_presRealization_acyclic
    ρ (w : J → List (α × Bool))
    (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)
    (h : Whitehead.Acyclic (orderNerveRealization (PresPos w))) :
    Function.Bijective (expMatrix ρ) := by
  letI : Nonempty (PresPos w) := ⟨ptBase w⟩
  letI : (nerve (PresPos w)).HasDimensionLE 2 :=
    orderNerve_hasDimensionLE _ (presPosDimension_strictMono w) 2
      (presPosDimension_le_two w)
  exact expMatrix_bijective_of_strict_pres_acyclic ρ w hw hpos
    ((orderRealization_acyclic_iff_strict_isAcyclic _
      (presPos_isConnected w (by grind))).mp h)
