import Mathlib.Tactic

import RequestProject.GenusFaithfulComparison
import RequestProject.ChamberQuotientAttachingCover
import RequestProject.PosetCoverPullback
import RequestProject.PosetCoverComparableLifts
import RequestProject.OrderNormalizationNaturality
import RequestProject.GenusReceivedPolygonCoefficient
import RequestProject.NerveDegree

/-!
The genuine surface cover under the lifted attaching locus of the named
quotient. Since its attaching map is `gHom ∘ chainMax`, the surface cover is
an actual pullback of the quotient's universal order cover. A unique lower
interval lift gives the sheet-preserving map from the subdivided attaching
locus. Its normalized finite-chain map commutes with the boundary and
preserves the required support on the polygon marking.

Written proof terms; not compiled under the current workflow. This constructs
the forward chain transfer, not an unproved inverse subdivision equivalence.
-/

noncomputable section


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The normalized one-chain map of a monotone map between different posets. -/
def normalizedChain1To (f : P → Q) (hf : Monotone f)  :=
  normalizeOrdChain1.comp ((chain1 (orderCxMap f hf)).comp (chain1 (strictOrderIncl P)))

end FiniteChains.Comb

namespace FiniteChains.Davis
open RACG Mirror Comb

variable {P X : Type u} [PartialOrder P] [DecidableEq P]
  [PartialOrder X] (g : P →o X)
  (a : Qpos (cmpRel P) X (nerveAtt g))
  (hc : IsConnected (orderCx (Qpos (cmpRel P) X (nerveAtt g))))

/-- The cover of the original cell poset retains actual universal-cover sheets. -/
abbrev AttachingSurfaceCover := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun p : P => qNew (att := nerveAtt g) (g p))

abbrev attachingSurfaceProjection : AttachingSurfaceCover g a → P :=
  posetPullbackProjection _ _

include hc in
theorem attachingSurfaceProjection_isPosetCover :
    IsPosetCover (attachingSurfaceProjection g a) :=
  (uOrderEnd_isPosetCover hc).pullback _ (qNew_monotone.comp g.monotone)

theorem qAttachingCoverEnd_monotone :
    Monotone (qAttachingCoverEnd a) := by
  intro p r hpr
  
  exact qPositiveOldOrderIso.monotone
    (show (⟨uOrderEnd p.1, p.2⟩ : QPositiveOld) ≤ ⟨uOrderEnd r.1, r.2⟩ from
      uOrderEnd_monotone hpr)

variable (p : QLiftedAttaching a)
theorem qAttachingCoverEnd_oldPoint  :
    qOldIncl (att := nerveAtt g) (posQCube (qAttachingCoverEnd a p)) = uOrderEnd p.1 := congrArg Subtype.val
    (qPositiveOldOrderIso.symm_apply_apply ⟨uOrderEnd p.1, p.2⟩)

theorem attachingSurface_lower_comparison  :
    qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) ≤ uOrderEnd p.1 := by
  grind [FiniteChains.Davis.qAttachingCoverEnd_oldPoint, FiniteChains.Davis.qNew_att_le_qOldIncl]

/-- Move to the actual lower base lift in the same universal-cover sheet. -/
def attachingSurfaceLowerLift   :=
  (uOrderEnd_isPosetCover hc).lowerMapLift Subtype.val
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (attachingSurface_lower_comparison g a) p

theorem attachingSurfaceLowerLift_spec  :
    attachingSurfaceLowerLift g a hc p ≤ p.1 ∧
      uOrderEnd (attachingSurfaceLowerLift g a hc p) =
        qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)) :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_spec _ _ _ p

abbrev attachingSurfaceLowerLift_monotone  :=
  (uOrderEnd_isPosetCover hc).lowerMapLift_monotone
    (Subtype.val : QLiftedAttaching a → UOrder (Qpos (cmpRel P) X (nerveAtt g)) a)
    (fun p => qNew (att := nerveAtt g) (nerveAtt g (qAttachingCoverEnd a p)))
    (fun _ _ h => h)
    (qNew_monotone.comp ((nerveAtt g).monotone.comp (qAttachingCoverEnd_monotone g a)))
    (attachingSurface_lower_comparison g a)

/-- The actual lifted last-vertex map from the subdivided attaching locus. -/
def attachingToSurfaceCover  : AttachingSurfaceCover g a :=
  ⟨(attachingSurfaceLowerLift g a hc p, chainMax (qAttachingCoverEnd a p)),
    (attachingSurfaceLowerLift_spec g a hc p).2⟩

theorem attachingToSurfaceCover_monotone :
    Monotone (attachingToSurfaceCover g a hc) := by
  intro p r hpr
  exact ⟨attachingSurfaceLowerLift_monotone g a hc hpr,
    chainMax_monotone (qAttachingCoverEnd_monotone g a hpr)⟩

@[simp] theorem attachingToSurfaceCover_projection  :
    attachingSurfaceProjection g a (attachingToSurfaceCover g a hc p) =
      chainMax (qAttachingCoverEnd a p) := rfl

def attachingSurfaceChain1  :=
  normalizedChain1To (attachingToSurfaceCover g a hc)
    (attachingToSurfaceCover_monotone g a hc)

/-- The barycentric pullback cover, before applying its last-vertex map. -/
abbrev AttachingSurfaceSubdivision := PosetCoverPullback
  (uOrderEnd (P := Qpos (cmpRel P) X (nerveAtt g)) (a := a))
  (fun σ : NeSpx (cmpRel P) => qNew (att := nerveAtt g) (nerveAtt g σ))

def attachingToSurfaceSubdivision  :
    AttachingSurfaceSubdivision g a :=
  ⟨(attachingSurfaceLowerLift g a hc p, qAttachingCoverEnd a p),
    (attachingSurfaceLowerLift_spec g a hc p).2⟩

def surfaceSubdivisionLastVertex (p : AttachingSurfaceSubdivision g a) :
    AttachingSurfaceCover g a := ⟨(p.1.1, chainMax p.1.2), p.2⟩

@[simp] theorem surfaceSubdivisionLastVertex_attaching  :
    surfaceSubdivisionLastVertex g a (attachingToSurfaceSubdivision g a hc p) =
      attachingToSurfaceCover g a hc p := rfl

theorem surfaceSubdivision_upper_comparison (p : AttachingSurfaceSubdivision g a) :
    uOrderEnd p.1.1 ≤ qOldIncl (att := nerveAtt g) (posQCube p.1.2) := by
  grind [FiniteChains.Davis.qNew_att_le_qOldIncl]

/-- The inverse cover comparison is an actual upper interval lift in the
same sheet, rather than a selected homotopy equivalence of presentations. -/
def surfaceSubdivisionUpperLift (p : AttachingSurfaceSubdivision g a)  :=
  (uOrderEnd_isPosetCover hc).upperMapLift (fun p => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p

theorem surfaceSubdivisionUpperLift_spec (p : AttachingSurfaceSubdivision g a) :
    p.1.1 ≤ surfaceSubdivisionUpperLift g a hc p ∧
      uOrderEnd (surfaceSubdivisionUpperLift g a hc p) =
        qOldIncl (att := nerveAtt g) (posQCube p.1.2) :=
  (uOrderEnd_isPosetCover hc).upperMapLift_spec
    (fun p : AttachingSurfaceSubdivision g a => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    (surfaceSubdivision_upper_comparison g a) p

theorem surfaceSubdivisionUpperLift_monotone :
    Monotone (surfaceSubdivisionUpperLift g a hc) := by
  apply (uOrderEnd_isPosetCover hc).upperMapLift_monotone
    (fun p : AttachingSurfaceSubdivision g a => p.1.1)
    (fun p => qOldIncl (att := nerveAtt g) (posQCube p.1.2))
    ?_ ?_ (surfaceSubdivision_upper_comparison g a)
  · exact fun _ _ h => h.1
  · intro p r hpr
    exact qOldIncl_monotone (show posQCube p.1.2 ≤ posQCube r.1.2 from
      ⟨hpr.2, fun _ _ => rfl⟩)

def surfaceSubdivisionToAttaching (p : AttachingSurfaceSubdivision g a) :
    QLiftedAttaching a :=
  ⟨surfaceSubdivisionUpperLift g a hc p, by
    rw (config := { transparency := .default }) [(surfaceSubdivisionUpperLift_spec g a hc p).2]
    exact ⟨trivial, rfl⟩⟩

abbrev surfaceSubdivisionToAttaching_monotone  :=
  FiniteChains.Davis.surfaceSubdivisionUpperLift_monotone g a hc



end FiniteChains.Davis

namespace FiniteChains.Davis.Genus
open RACG Mirror Comb PresModel BlockFamily

variable {α Jr : Type} (ρ : Jr ⊕ PUnit.{1} → FreeGroup α)
  (q : ℕ) [NeZero q] (u : Fin q × Bool → FreeGroup α)

def namedSurfaceLabel  :=
  gHom (w := genusNonemptyW (namedPres ρ q u)
      (namedA (α := α) q) (namedB (α := α) q) q) (j₀ := Sum.inr PUnit.unit)
    (genus_hM (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_hvlab (namedA (α := α) q) (namedB (α := α) q) q)
    (genus_helb (namedA (α := α) q) (namedB (α := α) q) q) (gc q)



theorem namedQuotientPos_isConnected : IsConnected (orderCx (namedQuotientPos ρ q u)) := by
  letI : Nonempty (namedBasePos ρ q u) := ⟨namedAtt ρ q u (gBase q)⟩
  exact qpos_isConnected_of_zpos (zpos_isConnected (namedBasePos_isConnected ρ q u))

abbrev NamedSurfaceCover :=
  AttachingSurfaceCover (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

abbrev namedSurfaceProjection  :=
  attachingSurfaceProjection (namedSurfaceLabel ρ q u) (namedQuotientBase ρ q u)

theorem namedSurfaceProjection_isPosetCover : IsPosetCover (namedSurfaceProjection ρ q u) :=
  attachingSurfaceProjection_isPosetCover (namedSurfaceLabel ρ q u)
    (namedQuotientBase ρ q u) (namedQuotientPos_isConnected ρ q u)

end FiniteChains.Davis.Genus
