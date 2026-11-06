import Mathlib.Tactic

import RequestProject.PresWordEmbeddingRelators
import RequestProject.PresWordEmbeddingCocycle
import RequestProject.PresUniversalRelatorGroupCoordinates
import RequestProject.PresUniversalRelatorDeck
import RequestProject.PresPosetCoverDimension
import RequestProject.OrderUniversalMap
import RequestProject.UnivCoverIncl

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v)

/-- The actual functorial lift to the two path-class universal covers. -/
noncomputable def universalMap : UOrder (PresPos w) (ptBase w) →o UOrder (PresPos v) (ptBase v) :=
  uOrderMap h.posMap h.posMap.monotone (ptBase w)

abbrev universalMap_end (p : UOrder (PresPos w) (ptBase w))  :=
  uOrderMap_end h.posMap h.posMap.monotone (ptBase w) p

/-- Comparable distinct vertices remain distinct, even when the lift identifies
different vertices over the same source base vertex. -/
theorem universalMap_strictMono : StrictMono h.universalMap := by
  intro p q hpq
  apply lt_of_le_of_ne (h.universalMap.monotone hpq.le)
  intro he
  have hh  :=
    (h.universalMap_end p).symm.trans ((congrArg uOrderEnd he).trans (h.universalMap_end q))
  exact (ne_of_lt (uOrderEnd_strictMono hpq)) (h.posMap.injective hh)

noncomputable def universalRelatorMap  :=
  h.coverRelatorMap uOrderEnd uOrderEnd h.universalMap h.universalMap_end

theorem universalRelatorChain_map (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presCoverRelatorChain v uOrderEnd (presUniversalEnd_isPosetCover v hv) hv
      (chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c) =
        Finsupp.mapDomain h.universalRelatorMap
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hw) hw c) :=
  h.coverRelatorChain_map hw hv uOrderEnd (presUniversalEnd_isPosetCover w hw)
    uOrderEnd (presUniversalEnd_isPosetCover v hv) h.universalMap
    h.universalMap_strictMono h.universalMap_end c

variable (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hv : ∀ j, FreeGroup.mk (v j) = σ j)

include hw hv in
theorem relator_compat (j : J) : σ (h.cell j) = FreeGroup.map h.gen (ρ j) := by
  rw [← hv (h.cell j), h.word]
  change FreeGroup.map h.gen (FreeGroup.mk (w j)) = FreeGroup.map h.gen (ρ j)
  rw [hw]

/-- The actual induced homomorphism of presented groups. -/
def groupHom  :=
  presInclGroupHom h.gen ρ σ h.cell (h.relator_compat ρ σ hw hv)



/-- The lifted path class has the actual induced group coordinate. -/
abbrev universal_reading_map (p : UOrder (PresPos w) (ptBase w))  :=
  h.readVertex_map (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ))
    (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup σ)) (h.groupHom ρ σ hw hv)
    (fun _ => rfl) (presGroup_wordVal_eq_one ρ w hw) (presGroup_wordVal_eq_one σ v hv)
    (ptBase w) p

variable (hwp : ∀ j, 0 < (w j).length)
variable (hvp : ∀ j, 0 < (v j).length)
theorem universalRelatorGroupEquiv_map 
    
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w))) :
    presUniversalRelatorGroupEquiv σ v hv hvp (h.universalRelatorMap p) =
      Prod.map (h.groupHom ρ σ hw hv) h.cell (presUniversalRelatorGroupEquiv ρ w hw hwp p) := by
  apply Prod.ext
  · exact h.universal_reading_map ρ σ hw hv p.val.1
  · rfl

/-- The full finite relator-coordinate chains commute with the actual lift,
including summation over group elements identified by the induced homomorphism. -/
theorem universalRelatorGroupChainEquiv_map 
    
    (c : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv σ v hv hvp (Finsupp.mapDomain h.universalRelatorMap c) =
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hw hv) h.cell)
        (presUniversalRelatorGroupChainEquiv ρ w hw hwp c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all [Finsupp.mapDomain_add]
  | single p n =>
    classical simp_all [FiniteChains.relSub_normal, FiniteChains.PresModel.PresWordEmbedding.universalRelatorGroupEquiv_map, presUniversalRelatorGroupChainEquiv]

theorem universalRelatorChain_group_map 
    
    (c : StrictOrdTri (UOrder (PresPos w) (ptBase w)) →₀ ℤ) :
    presUniversalRelatorGroupChainEquiv σ v hv hvp
      (presCoverRelatorChain v uOrderEnd (presUniversalEnd_isPosetCover v hvp) hvp
        (chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c)) =
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hw hv) h.cell)
        (presUniversalRelatorGroupChainEquiv ρ w hw hwp
          (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hwp) hwp c)) := by
  rw [h.universalRelatorChain_map, h.universalRelatorGroupChainEquiv_map]

end FiniteChains.PresModel.PresWordEmbedding
