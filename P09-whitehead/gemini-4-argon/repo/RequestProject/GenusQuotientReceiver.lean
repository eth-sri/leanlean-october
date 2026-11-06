module

public import RequestProject.ChamberQuotientCocycleGluing
public import RequestProject.GenusReceivedSpineCover
public import RequestProject.PresUniversalGroupCoordinates
public import RequestProject.GenusNonemptyMarkedReading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Comb.OrdCocycle
open SpanningTree
open scoped Classical
universe u v
variable {P : Type u} [Preorder P] {G : Type v} [Group G]
  (T : SpanningTree (orderCx P)) (φ : PresGroup (treeRel T) →* G)

def fromTreeReceiver (T : SpanningTree (orderCx P)) (φ : PresGroup (treeRel T) →* G) :
    OrdCocycle P G where
  val a b := if hab : a ≤ b then φ (wordClass T [ordPos hab]) else 1
  comp hab hbc := by
    simp only [dif_pos hab, dif_pos hbc, dif_pos (hab.trans hbc), ← map_mul, ← wordClass_append]
    exact congrArg φ (wordClass_htpy T (htpy_orderCx_tri hab hbc))

theorem exists_of_monodromy (hP : IsConnected (orderCx P)) (x : P)
    (ψ : Pi1 (orderCx P) x →* G) :
    ∃ c : OrdCocycle P G, ∀ p : Loop (orderCx P) x,
      c.readPath p.1 = ψ (Pi1.mk p) := by
  obtain ⟨T, rfl⟩ := SpanningTree.exists_of_isConnected hP x
  let φ := ψ.comp (SpanningTree.presToPi1 T)
  have hread (p : List ((orderCx P).E × Bool)) :
      (fromTreeReceiver T φ).readPath p = φ (wordClass T p) := by
    induction p with
    | nil => simp [wordClass, pathWord_nil]
    | cons e p ih =>
        have hg : (fromTreeReceiver T φ).readGerm e = φ (wordClass T [e]) := by
          obtain ⟨⟨⟨a, b⟩, hab⟩, side⟩ := e
          cases side
          · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1)⁻¹ = φ (wordClass T [ordNeg hab])
            rw [dif_pos hab, ← map_inv]; congr 1
            change (QuotientGroup.mk (pathWord T [ordPos hab]))⁻¹ = QuotientGroup.mk (pathWord T [ordNeg hab])
            rw [← QuotientGroup.mk_inv, ← pathWord_revPath]; rfl
          · change (if h : a ≤ b then φ (wordClass T [ordPos h]) else 1) = _
            rw [dif_pos hab]; rfl
        rw [readPath_cons, hg, ih, ← map_mul, ← wordClass_append]; rfl
  refine ⟨fromTreeReceiver T φ, fun p => ?_⟩
  rw [hread]
  exact SpanningTree.presToPi1_pi1ToPres T (Pi1.mk p) ▸ rfl

end FiniteChains.Comb.OrdCocycle

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily
universe v
variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)
  (hrho : ρ (Sum.inr PUnit.unit) = commWord u (finitePairs q))
  {G : Type v} [Group G] (j : PresGroup ρ →* G)

def namedBaseReceiver : PresGroup (namedPres ρ q u) →* G :=
  j.comp (SurfaceWordExpansion.elimination ρ u (finitePairs q) hrho)

def namedBaseCocycle :
    OrdCocycle (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q)
      (namedB (α := α) q) q)) G :=
  (presGroupCocycle (namedPres ρ q u)
    (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
    (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u))).postcompose
      (namedBaseReceiver ρ q u hrho j)

abbrev namedQuotientPos :=
  Qpos (cmpRel (GenusVertex q))
    (PresPos (genusNonemptyW (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q))
    (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)

abbrev namedQuotientBase : namedQuotientPos ρ q u :=
  qNew (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
    (gBase q))

def namedSpineIntoQuotient :
    PresGroup (namedSpinePresentation q) →*
      Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) :=
  (quotientOldBasedInclusion (gBase q)).comp (namedSpineToOldEquiv q).toMonoidHom

theorem exists_namedQuotientReading
    (φ : PresGroup (namedSpinePresentation q) →* G)
    (hm : ∀ x : Fin q × Bool,
      φ (QuotientGroup.mk (FreeGroup.of (Sum.inr x))) = j (QuotientGroup.mk (u x))) :
    ∃ ψ : Pi1 (orderCx (namedQuotientPos ρ q u)) (namedQuotientBase ρ q u) →* G,
      ψ.comp (namedSpineIntoQuotient ρ q u) = φ ∧
      ψ.comp
        (pi1Map (orderCxMap (qNew (att := genusNonemptyAtt (namedPres ρ q u)
          (namedA (α := α) q) (namedB (α := α) q) q)) qNew_monotone)
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q))) =
        (namedBaseCocycle ρ q u hrho j).monodromy
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q
            (gBase q)) := by
  have : Nonempty (GenusVertex q) := ⟨cV (gc q) (cyc (8 * q) 0)⟩
  let oldRec : Pi1 (orderCx (QOld (cmpRel (GenusVertex q)))) (posQCube (gBase q)) →* G :=
    φ.comp (namedSpineToOldEquiv q).symm.toMonoidHom
  obtain ⟨old, hread⟩ := OrdCocycle.exists_of_monodromy isConnected_orderCx_qOld (posQCube (gBase q)) oldRec
  have hmark (x : Fin q × Bool) :
      old.readPath (mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2))) =
      (namedBaseCocycle ρ q u hrho j).readPath
        (mapPath (orderCxMap
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q)
          (genusNonemptyAtt (namedPres ρ q u) (namedA (α := α) q) (namedB (α := α) q) q).monotone)
          (gSig q (x.1.val, x.2))) := by
    rw [hread ⟨_, isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2))⟩]
    have hm' := namedSpineToOld_marked q x
    rw [spineMarkedLoop_toOld_class] at hm'
    have hold : oldRec (Pi1.mk ⟨mapPath (surfCx (cmpRel (GenusVertex q))) (gSig q (x.1.val, x.2)),
        isPath_mapPath (surfCx _) (isPath_gSig q (x.1.val, x.2))⟩) = j (QuotientGroup.mk (u x)) := by
      change φ ((namedSpineToOldEquiv q).symm _) = _
      rw [← hm', MulEquiv.symm_apply_apply, hm]
    rw [hold]
    let ep := namedPres ρ q u; let aa := namedA (α := α) q; let bb := namedB (α := α) q
    let w := genusNonemptyW ep aa bb q
    have hh := (namedBaseCocycle ρ q u hrho j).readPath_htpy
      (genusNonempty_hread ep aa bb q PUnit.unit.{1} (x.1.val, x.2))
    simp only [List.nil_append, revPath_nil, List.append_nil] at hh
    have hl : genusLw aa bb q PUnit.unit.{1} (x.1.val, x.2) = [(Sum.inr x, true)] :=
      namedLw_eq q PUnit.unit x
    rw [hh, hl]
    change _ = (namedBaseCocycle ρ q u hrho j).readPath (genLoop w (Sum.inr x))
    rw [namedBaseCocycle, OrdCocycle.postcompose_readPath]
    change _ = namedBaseReceiver ρ q u hrho j
      (reading w (fun a => (QuotientGroup.mk (FreeGroup.of a) : PresGroup ep))
        (presGroup_wordVal_eq_one ep w (mk_genusNonemptyW _ _ _ _ (namedPres_surface ρ q u)))
        (genClass w (Sum.inr x)))
    rw [reading_genClass]
    change _ = j (QuotientGroup.mk (SurfaceWordExpansion.foldNames u (FreeGroup.of (Sum.inr x))))
    simp [SurfaceWordExpansion.foldNames]
  obtain ⟨c, hcold, hcbase, hccyl⟩ := exists_quotientCocycle_of_marked q _ old
    (namedBaseCocycle ρ q u hrho j) hmark
  refine ⟨c.monodromy (namedQuotientBase ρ q u), ?_,
    monodromy_quotientBaseInclusion _ c (namedBaseCocycle ρ q u hrho j) hcbase⟩
  have h := monodromy_quotientOldBasedInclusion (gBase q) c oldRec hccyl fun p => by
    have he : c.comap (qOldIncl (att := _)) qOldIncl_monotone = old := OrdCocycle.eq_of_val_eq hcold
    rw [← OrdCocycle.comap_readPath, he]; exact hread p
  change ((c.monodromy (namedQuotientBase ρ q u)).comp
    (quotientOldBasedInclusion (gBase q))).comp (namedSpineToOldEquiv q).toMonoidHom = φ
  rw [h]
  exact MonoidHom.ext fun z => by
    change φ ((namedSpineToOldEquiv q).symm ((namedSpineToOldEquiv q) z)) = φ z
    rw [MulEquiv.symm_apply_apply]
