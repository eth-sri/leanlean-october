module

public import RequestProject.BlockSpinePres
public import RequestProject.SubstOneWayQuotientW

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FiniteChains.Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] {A : CommRel V}
variable {α J : Type u} (w : J → List (α × Bool)) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))

abbrev qInclCxW : Hom (orderCx (PresPos w)) (orderCx (Qpos A (PresPos w) att)) :=
  orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone

abbrev qBasePtW : (orderCx (Qpos A (PresPos w) att)).V :=
  qNew (A := A) (att := att) (ptBase w)

abbrev surfQW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qOldIncl (X := PresPos w) (att := att) (posQCube σ)

abbrev surfBaseW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qNew (att σ)

def cylPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  mapPath (qInclCxW w att) cb ++ [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)]

theorem isPath_cylPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (cylPathW w att σ₀ cb) (qBasePtW w att) (surfQW w att σ₀) :=
  isPath_append_iff.mpr ⟨_, isPath_mapPath (qInclCxW w att) hcb, isPath_ordPos _⟩

def rootPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  cylPathW w att σ₀ cb ++
    revPath (mapPath (blockCx A (PresPos w) att) (T.treePath (posQCube σ₀)))

theorem isPath_rootPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (rootPathW w att σ₀ cb T) (qBasePtW w att)
      (qOldIncl (X := PresPos w) (att := att) T.root) :=
  (isPath_cylPathW w att σ₀ cb hcb).append
    (isPath_revPath (isPath_mapPath _ (T.treePath_isPath (posQCube σ₀))))

def blockToQW (hcb : IsPath (orderCx (PresPos w)).src
    (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀)) :
    Pi1 (orderCx (QOld A)) T.root →*
      Pi1 (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) :=
  (pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)).comp
    (pi1Map (blockCx A (PresPos w) att) T.root)

theorem blockToQW_surfLoop
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Map (qInclCxW w att) (ptBase w)
          (pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p,
            isPath_mapPath _ hp⟩)) := by
  classical
  have htp := T.treePath_isPath (posQCube σ₀)
  have hmtp := isPath_mapPath (blockCx A (PresPos w) att) htp
  have hcyl := isPath_cylPathW w att σ₀ cb hcb
  set X : Pi1 (orderCx (QOld A)) (posQCube σ₀) :=
    Pi1.mk ⟨mapPath (surfCx A) p, isPath_mapPath (surfCx A) hp⟩
  set Y : Pi1 (orderCx (PresPos w)) (att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p, isPath_mapPath _ hp⟩
  set Z : Pi1 (orderCx (Qpos A (PresPos w) att)) (surfBaseW w att σ₀) :=
    Pi1.mk ⟨mapPath (orderCxMap (surfBaseW w att) (qNew_monotone.comp att.monotone)) p,
      isPath_mapPath _ hp⟩
  have hcancel : Htpy (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) (surfQW w att σ₀)
      (rootPathW w att σ₀ cb T ++ mapPath (blockCx A (PresPos w) att)
        (T.treePath (posQCube σ₀))) (cylPathW w att σ₀ cb) := by
    simpa [rootPathW, List.append_assoc] using
      (htpy_revPath_append hmtp).congr_append hcyl (isPath_nil' (surfQW w att σ₀))
  have hback : Htpy (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) (surfBaseW w att σ₀)
      (cylPathW w att σ₀ cb ++ [ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)])
      (mapPath (qInclCxW w att) cb) := by
    simpa [cylPathW, List.append_assoc] using
      (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)).congr_append
        (isPath_mapPath (qInclCxW w att) hcb) (isPath_nil' (surfBaseW w att σ₀))
  have hE : pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X
      = pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)) Z := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (PresPos w) att)) (surfQW w att σ₀) (surfQW w att σ₀)
      (mapPath (blockCx A (PresPos w) att) (mapPath (surfCx A) p)) _
    rw [show mapPath (blockCx A (PresPos w) att) (mapPath (surfCx A) p) =
      mapPath (orderCxMap (surfQW w att) (qOldIncl_monotone.comp posQCube_monotone)) p by
        simp [mapPath, blockCx, surfCx, orderCxMap, Function.comp_def]]
    exact htpy_loop_mapPath_le (qNew_monotone.comp att.monotone)
      (qOldIncl_monotone.comp posQCube_monotone)
      (fun σ => qNew_att_le_qOldIncl (att := att) σ) hp
  have hH : Z = pi1Map (qInclCxW w att) (att σ₀) Y := by
    refine Quotient.sound ?_
    show Htpy (orderCx (Qpos A (PresPos w) att)) (surfBaseW w att σ₀) (surfBaseW w att σ₀)
      (mapPath (orderCxMap (surfBaseW w att) (qNew_monotone.comp att.monotone)) p)
      (mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p))
    rw [show mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p) =
      mapPath (orderCxMap (surfBaseW w att) (qNew_monotone.comp att.monotone)) p by
        simp [mapPath, orderCxMap, Function.comp_def]]
  calc blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)
          (pi1Conj hmtp (pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X)) :=
        congrArg (pi1Conj (isPath_rootPathW w att σ₀ cb T hcb))
          (pi1Map_pi1Conj (blockCx A (PresPos w) att) htp X)
    _ = pi1Conj hcyl (pi1Map (blockCx A (PresPos w) att) (posQCube σ₀) X) :=
        (pi1Conj_pi1Conj _ hmtp _).trans (pi1Conj_congr _ hcyl hcancel _)
    _ = pi1Conj (isPath_mapPath (qInclCxW w att) hcb) Z :=
        (congrArg _ hE).trans ((pi1Conj_pi1Conj _ _ _).trans
          (pi1Conj_congr _ (isPath_mapPath (qInclCxW w att) hcb) hback _))
    _ = pi1Map (qInclCxW w att) (ptBase w) (pi1Conj hcb Y) :=
        (congrArg _ hH).trans (pi1Map_pi1Conj (qInclCxW w att) hcb Y).symm
