import RequestProject.GenusQuotientRelativeSupport
import RequestProject.GenusOldCoverSpineFaithfulness
import RequestProject.ChamberQuotientOldCover
import RequestProject.StrictOrderPullbackHom
import RequestProject.OrderCxRestriction
import RequestProject.UniversalCoverPi1Injection
import RequestProject.Tac
noncomputable section


/-! The received spine is mapped into the genuine pulled-back old-cover spine.

-/
bwd

namespace FiniteChains.Comb
variable {K Y Z : Complex2}

theorem Hom.comp_left_cancel_of_injective (f : Hom Y Z)
    (hv : Function.Injective f.onV) (he : Function.Injective f.onE)
    (hf : Function.Injective f.onF) (r s : Hom K Y)
    (h : f.comp r = f.comp s) : r = s := by
  apply Hom.ext'
  · funext a
    exact hv (congrArg (·.onV a) h)
  · funext e
    exact he (congrArg (·.onE e) h)
  · funext t
    exact hf (congrArg (·.onF t) h)

theorem uOrderHomInv_projection_square {P : Type} [PartialOrder P] a :
    (orderCxMap uOrderEnd (uOrderEnd_monotone (P := P) (a := a))).comp uOrderHomInv =
      univProj (orderCx P) a := by
  apply Hom.ext'
  · funext x
    change uOrderEnd (uOrderHomInv.onV x) = endV x
    rwd [uOrderHomInv_vertex]
    rfl
  · funext e
    exact uOrderHomInv_edge_projection e
  · funext t
    exact uOrderHomInv_face_projection t

theorem deckV_injective_in_group a v :
    Function.Injective (fun g : Pi1 X a => deckV g v) := by
  intro g h he
  obtain ⟨d, _, hu⟩ := (isRegular_univProj (X := X) (x₀ := a)).simply_transitive
    v _ (endV_deckV g v).symm
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
  apply Hom.ext'
  · funext p
    exact qOldCoverEnd_spec a p
  · funext e
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a e.1.1) (qOldCoverEnd_spec a e.1.2)
  · funext t
    apply Subtype.ext
    exact Prod.ext (qOldCoverEnd_spec a t.1.1)
      (Prod.ext (qOldCoverEnd_spec a t.1.2.1) (qOldCoverEnd_spec a t.1.2.2))

end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily Nerve
open scoped Classical
variable (q : ℕ) [NeZero q] {α Jr : Type}
  (ρ : Jr ⊕ PUnit.{1} → FreeGroup α) (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

abbrev namedOldCover := QLiftedOld (namedQuotientBase ρ q u)

def namedOldCoverProjection :
    namedOldCover q ρ u → QOld (cmpRel (GenusVertex q)) :=
  qOldCoverEnd _

theorem namedOldCoverProjection_isPosetCover : IsPosetCover (namedOldCoverProjection q ρ u) :=
  qOldCoverEnd_isPosetCover _ (namedBasePos_isConnected ρ q u)

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
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))

def coveredSpineToStrictSpine :
    Hom (strictOrderCx (OldCoveredSpine q (namedOldCoverProjection q ρ u)))
      (strictOrderCx (GenusSpineCell q)) :=
  (strictPullbackProjection _
    (namedOldCoverProjection_isPosetCover q ρ u) _
    (genusSpineCellToOld_monotone q)).comp
      (strictOrderCxMap (spinePullbackOldCoverOrderIso q _).symm
        (by tauto))
