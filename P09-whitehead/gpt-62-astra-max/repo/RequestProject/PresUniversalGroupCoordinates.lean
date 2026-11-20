module

public import RequestProject.PresPosetGroupEquiv
public import RequestProject.OrderUniversalCocycleReading
public import RequestProject.PresPosetConnected

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- Evaluating a word in the presentation group is its actual quotient image. -/
theorem presGroup_wordVal (l : List _) :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) l =
      QuotientGroup.mk (FreeGroup.mk l) := by
  have h : (FreeGroup.lift fun i : α =>
      (QuotientGroup.mk (FreeGroup.of i))) = QuotientGroup.mk' (relSub ρ) := by
    apply FreeGroup.ext_hom
    simp
  exact DFunLike.congr_fun h _

include hw in
/-- The relator words evaluate to one in their actual presentation group. -/
theorem presGroup_wordVal_eq_one (j : J) :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) (w j) = 1 := by
  have hlift : (FreeGroup.lift fun i : α =>
      (QuotientGroup.mk (FreeGroup.of i))) = QuotientGroup.mk' (relSub ρ) := by
    apply FreeGroup.ext_hom
    simp
  change FreeGroup.lift _ (FreeGroup.mk _) = 1
  rw [hlift, hw j]
  exact (QuotientGroup.eq_one_iff _).2
    (Subgroup.subset_normalClosure (Set.mem_range.2 ⟨j, rfl⟩))

/-- The genuine presentation cocycle with values in its actual presentation group. -/
def presGroupCocycle :=
  presCoc w _ (presGroup_wordVal_eq_one ρ w hw)

@[simp] theorem presGroupCocycle_monodromy :
    (presGroupCocycle ρ w hw).monodromy _ = readingPresW ρ w hw := rfl

variable (hpos : ∀ j, 0 < (w j).length)
include hpos

/-- The actual universal-cover reading separates vertices in every endpoint fibre. -/
theorem presUniversal_reading_injective
    (p q : UV _ _) (he : endV p = endV q)
    (hr : (presGroupCocycle ρ w hw).readVertex _ p =
      (presGroupCocycle ρ w hw).readVertex (ptBase w) q) : p = q :=
  (presGroupCocycle ρ w hw).readVertex_fibre_injective _
    (readingPresW_injective w ρ hw hpos) p q he hr

/-- Reading gives genuine group coordinates on every actual endpoint fibre of the universal cover. -/
noncomputable def presUniversalFibreGroupEquiv
    (v : PresPos w) :
    {p : UV (orderCx (PresPos w)) (ptBase w) // endV p = v} ≃ PresGroup ρ :=
  Equiv.ofBijective (fun p => (presGroupCocycle ρ w hw).readVertex (ptBase w) p.val) ⟨by
    intro p q h
    grind [presUniversal_reading_injective], by
    intro z
    obtain ⟨p, hp⟩ := endV_surjective
      (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j))) v
    obtain ⟨q, hq, hz⟩ := (presGroupCocycle ρ w hw).readVertex_fibre_surjective
      (ptBase w) (readingPresW_surjective ρ w hw) p z
    exact ⟨⟨q, hq.trans hp⟩, hz⟩⟩

end FiniteChains.PresModel
