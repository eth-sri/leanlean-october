import RequestProject.PresPosetGroupEquiv
import RequestProject.OrderUniversalCocycleReading
import RequestProject.PresPosetConnected


namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j)

/-- Evaluating a word in the presentation group is its actual quotient image. -/
theorem presGroup_wordVal l :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) l =
      QuotientGroup.mk (FreeGroup.mk l) := by
  have h : (FreeGroup.lift fun i =>
      (QuotientGroup.mk (FreeGroup.of i))) = QuotientGroup.mk' (relSub ρ) := by
    aesop
  exact DFunLike.congr_fun h _

include hw in
/-- The relator words evaluate to one in their actual presentation group. -/
theorem presGroup_wordVal_eq_one (j : J) :
    wordVal (fun i => (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) (w j) = 1 := by
  have hlift : (FreeGroup.lift fun i =>
      (QuotientGroup.mk (FreeGroup.of i) : PresGroup ρ)) = QuotientGroup.mk' _ := by
    aesop
  change FreeGroup.lift _ (FreeGroup.mk (w j)) = 1
  rw [hlift, hw j]
  exact (QuotientGroup.eq_one_iff _).2
    (Subgroup.subset_normalClosure (by simp))

/-- The genuine presentation cocycle with values in its actual presentation group. -/
def presGroupCocycle : OrdCocycle (PresPos w) (PresGroup ρ) :=
  presCoc w _ (presGroup_wordVal_eq_one ρ w hw)

@[simp] theorem presGroupCocycle_monodromy :
    (presGroupCocycle ρ w hw).monodromy (ptBase w) = readingPresW ρ w hw := rfl

/-- The actual universal-cover reading separates vertices in every endpoint fibre. -/
theorem presUniversal_reading_injective (hpos : ∀ j, 0 < (w j).length)
    p q (he : endV p = endV q)
    (hr : (presGroupCocycle ρ w hw).readVertex (ptBase w) p =
      (presGroupCocycle ρ w hw).readVertex (ptBase w) q) : p = q :=
  (presGroupCocycle ρ w hw).readVertex_fibre_injective _
    (readingPresW_injective w ρ hw hpos) p q he hr

/-- Reading gives genuine group coordinates on every actual endpoint fibre of the universal cover. -/
noncomputable def presUniversalFibreGroupEquiv (hpos : ∀ j, 0 < (w j).length)
    (v : PresPos w) :
    {p : UV (orderCx (PresPos w)) (ptBase w) // endV p = v} ≃ PresGroup ρ :=
  Equiv.ofBijective ((presGroupCocycle ρ w hw).readVertex _ ·.val) ⟨by
    intro p q h
    apply Subtype.ext
    exact presUniversal_reading_injective ρ w hw hpos p.val q.val
      (p.property.trans q.property.symm) h, by
    intro z
    obtain ⟨p, hp⟩ := endV_surjective
      (presPos_isConnected w (by grind)) v
    obtain ⟨q, hq, hz⟩ := (presGroupCocycle ρ w hw).readVertex_fibre_surjective
      _ (readingPresW_surjective ρ w hw) p z
    aesop⟩
