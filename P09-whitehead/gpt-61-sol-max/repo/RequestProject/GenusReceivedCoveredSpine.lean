import Mathlib.Tactic

import RequestProject.GenusQuotientRelativeSupport
import RequestProject.GenusOldCoverSpineFaithfulness
import RequestProject.ChamberQuotientOldCover
import RequestProject.StrictOrderPullbackHom
import RequestProject.OrderCxRestriction
import RequestProject.UniversalCoverPi1Injection

/-! The received spine is mapped into the genuine pulled-back old-cover spine.

-/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem Hom.comp_left_cancel_of_injective (f : Hom Y Z)
    (hv : Function.Injective f.onV) (he : Function.Injective f.onE)
    (hf : Function.Injective f.onF) (r s : Hom K Y)
    (h : f.comp r = f.comp s) : r = s := by
  apply Hom.ext'
  · funext a
    exact hv (congrArg (fun k : Hom K Z => k.onV a) h)
  · funext e
    exact he (congrArg (fun k : Hom K Z => k.onE e) h)
  · funext t
    exact hf (congrArg (fun k : Hom K Z => k.onF t) h)

theorem uOrderHomInv_projection_square {P : Type} [PartialOrder P] (a : P) :
    (orderCxMap uOrderEnd (uOrderEnd_monotone (P := P) (a := a))).comp uOrderHomInv =
      univProj (orderCx P) a := by
  apply Hom.ext'
  · funext x
    change uOrderEnd (uOrderHomInv.onV x) = endV x
    rw  [uOrderHomInv_vertex]
    rfl
  · funext e
    exact uOrderHomInv_edge_projection e
  · funext t
    exact uOrderHomInv_face_projection t

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
          (fun _ _ h => h)) := by apply Hom.ext' <;> funext x <;> solve_by_elim (maxDepth := 10) [Subtype.ext, Prod.ext, qOldCoverEnd_spec]

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve

variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable abbrev namedOldCover := QLiftedOld (namedQuotientBase ρ q u)

noncomputable def namedOldCoverProjection  :=
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

variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

noncomputable def coveredSpineToStrictSpine  :=
  (strictPullbackProjection (namedOldCoverProjection q ρ u)
    (namedOldCoverProjection_isPosetCover q ρ u) (genusSpineCellToOld q)
    (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm
        (spinePullbackOldCoverOrderIso q (namedOldCoverProjection q ρ u)).symm.strictMono)

end FiniteChains.Davis.Genus
