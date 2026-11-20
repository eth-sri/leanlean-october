module

public import RequestProject.GenusQuotientRelativeSupport
public import RequestProject.GenusOldCoverSpineFaithfulness
public import RequestProject.ChamberQuotientOldCover
public import RequestProject.StrictOrderPullbackHom
public import RequestProject.OrderCxRestriction
public import RequestProject.UniversalCoverPi1Injection

@[expose] public section

/-! The received spine is mapped into the genuine pulled-back old-cover spine.

-/

namespace FiniteChains.Comb
theorem uOrderHomInv_projection_square {P : Type} [PartialOrder P] (a : P) :
    (orderCxMap uOrderEnd (uOrderEnd_monotone (P := P) (a := a))).comp uOrderHomInv =
      univProj (orderCx P) a := by
  apply Hom.ext_orderCx
  funext x
  change uOrderEnd (uOrderHomInv.onV x) = endV x
  erw [uOrderHomInv_vertex]
  rfl

theorem deckV_injective_in_group {X : Complex2} (a : X.V) (v : UV X a) :
    Function.Injective (fun g : Pi1 X a => deckV g v) := by
  intro g h he
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive
    v (deckV g v) (endV_deckV g v).symm
  exact (hu g rfl).trans (hu h he.symm).symm

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}
  {X : Type} [PartialOrder X] {att : NeSpx A →o X}

theorem qOldCover_projection_square (a : Qpos A X att)
    (hf : Monotone (qOldCoverEnd a)) :
    (orderCxMap (qOldIncl (att := att)) qOldIncl_monotone).comp
      (orderCxMap (qOldCoverEnd a) hf) =
      (orderCxMap uOrderEnd uOrderEnd_monotone).comp
        (orderCxMap (Subtype.val : QLiftedOld a → UOrder (Qpos A X att) a)
          (fun _ _ h => h)) := by
  exact Hom.ext_orderCx (funext (qOldCoverEnd_spec a))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

noncomputable abbrev namedOldCover := QLiftedOld (namedQuotientBase ρ q u)

noncomputable def namedOldCoverProjection :
    namedOldCover q ρ u → QOld (cmpRel (GenusVertex q)) :=
  qOldCoverEnd (namedQuotientBase ρ q u)

theorem namedOldCoverProjection_isPosetCover : IsPosetCover (namedOldCoverProjection q ρ u) :=
  qOldCoverEnd_isPosetCover (namedAtt ρ q u (gBase q)) (namedBasePos_isConnected ρ q u)

variable {P : Type} [PartialOrder P] (f : P → QOld (cmpRel (GenusVertex q)))

/-- The fibre product over the surviving spine is precisely the old-cover
spine used by the proved chain-faithfulness theorem. -/
def spinePullbackOldCoverOrderIso :
    PosetCoverPullback f (genusSpineCellToOld q) ≃o OldCoveredSpine q f where
  toFun x := ⟨⟨(x.1.1, x.1.2.1), x.2⟩, x.1.2.2⟩
  invFun x := ⟨(x.1.1.1, ⟨x.1.1.2, x.2⟩), x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

end FiniteChains.Davis.Genus

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : IsSpineRelator ρ q u)

noncomputable def coveredSpineToStrictSpine :
    Hom (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u)))
      (strictOrderCx (GenusSpineCell q)) :=
  (strictPullbackProjection (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm
        (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm.strictMono)

end FiniteChains.Davis.Genus
