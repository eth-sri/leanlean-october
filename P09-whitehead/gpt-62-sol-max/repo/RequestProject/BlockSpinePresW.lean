module

public import RequestProject.BlockSpinePres
public import RequestProject.SubstOneWayQuotientW

@[expose] public section

/-!
# The block over a model built on prescribed relator words

This file repeats the construction of `RequestProject/BlockSpinePres.lean` — the geometric loops
of the block, the cylinder computation and the marked homomorphism of the block into the
fundamental group of the quotient — over the poset model `PresPos w` of the presentation complex
built on a **prescribed** family of relator words `w` with `FreeGroup.mk (w j) = ρ j`.

The spine of the block, its internal generators `FiniteChains.Davis.spineGens` and its relators
`FiniteChains.Davis.spineBeta` do not involve the base at all and are reused unchanged.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V]  {A : CommRel V}

section SpineW

variable {α J : Type u} (w : J → List (α × Bool)) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))

/-- The cellular map of the inclusion of the base copy in the quotient. -/
noncomputable abbrev qInclCxW : Hom (orderCx (PresPos w)) (orderCx (Qpos A (PresPos w) att)) :=
  orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone

/-- The base point of the quotient. -/
noncomputable abbrev qBasePtW : (orderCx (Qpos A (PresPos w) att)).V :=
  qNew (A := A) (att := att) (ptBase w)

/-- The cut surface, mapped into the quotient through the block. -/
noncomputable abbrev surfQW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qOldIncl (X := PresPos w) (att := att) (posQCube σ)


theorem surfQW_monotone : Monotone (surfQW w att) :=
  qOldIncl_monotone.comp posQCube_monotone

/-- The cut surface, mapped into the quotient through the copy of the base. -/
noncomputable abbrev surfBaseW : (NeSpx A) → Qpos A (PresPos w) att :=
  fun σ => qNew (att σ)


theorem surfBaseW_monotone : Monotone (surfBaseW w att) :=
  qNew_monotone.comp att.monotone

/-- The path from the base point of the copy of the base to the block. -/
noncomputable def cylPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  mapPath (qInclCxW w att) cb ++ [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)]


theorem isPath_cylPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (cylPathW w att σ₀ cb) (qBasePtW w att) (surfQW w att σ₀) :=
  isPath_append_iff.mpr ⟨_, isPath_mapPath (qInclCxW w att) hcb, isPath_ordPos _⟩

/-- The path from the base point of the copy of the base to the root of the spanning tree. -/
noncomputable def rootPathW : List ((orderCx (Qpos A (PresPos w) att)).E × Bool) :=
  cylPathW w att σ₀ cb ++
    revPath (mapPath (blockCx A (PresPos w) att) (T.treePath (posQCube σ₀)))


theorem isPath_rootPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (rootPathW w att σ₀ cb T) (qBasePtW w att)
      (qOldIncl (X := PresPos w) (att := att) T.root) :=
  (isPath_cylPathW w att σ₀ cb hcb).append
    (isPath_revPath (isPath_mapPath _ (T.treePath_isPath (posQCube σ₀))))

/-- **The geometric loops of the block.** -/
noncomputable def blockToQW (hcb : IsPath (orderCx (PresPos w)).src
    (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀)) :
    Pi1 (orderCx (QOld A)) T.root →*
      Pi1 (orderCx (Qpos A (PresPos w) att)) (qBasePtW w att) :=
  (pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)).comp
    (pi1Map (blockCx A (PresPos w) att) T.root)


/-- **The cylinder computation.** -/
theorem blockToQW_surfLoop
    (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
    {p : List ((orderCx (NeSpx A)).E × Bool)}
    (hp : IsPath (orderCx (NeSpx A)).src (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Map (qInclCxW w att) (ptBase w)
          (pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p,
            isPath_mapPath _ hp⟩)) := by
  let b := blockCx A (PresPos w) att
  let i := qInclCxW w att
  let a := orderCxMap att att.monotone
  let z := Pi1.mk ⟨p, hp⟩
  have ht := T.treePath_isPath (posQCube σ₀)
  have hcyl := isPath_cylPathW w att σ₀ cb hcb
  have hroot := isPath_rootPathW w att σ₀ cb T hcb
  have hle := qNew_att_le_qOldIncl (att := att)
  have hcancel : Htpy _ (qBasePtW w att) (surfQW w att σ₀) (rootPathW w att σ₀ cb T ++ mapPath b (T.treePath (posQCube σ₀)))
      (cylPathW w att σ₀ cb) := by
    have h := (htpy_revPath_append (isPath_mapPath b ht)).congr_append hcyl
      (isPath_nil' (surfQW w att σ₀))
    simpa [rootPathW, List.append_assoc] using h
  have hback : Htpy _ (qBasePtW w att) (surfBaseW w att σ₀) (cylPathW w att σ₀ cb ++ [ordNeg (hle σ₀)]) (mapPath i cb) := by
    have h := (htpy_ordPos_ordNeg (hle σ₀)).congr_append
      (isPath_mapPath i hcb) (isPath_nil' (surfBaseW w att σ₀))
    simpa [cylPathW, List.append_assoc, i, qBasePtW] using h
  have hmap : pi1Map b (posQCube σ₀) (pi1Map (surfCx A) σ₀ z) =
      pi1Conj (isPath_ordNeg (hle σ₀)) (pi1Map i (att σ₀) (pi1Map a σ₀ z)) := by
    exact (pi1Map_comp_apply (surfCx A) b σ₀ z).symm.trans
      ((pi1Map_orderCx_le (surfBaseW_monotone w att) (surfQW_monotone w att) hle z).trans
        (congrArg _ (pi1Map_comp_apply a i σ₀ z)))
  change pi1Conj hroot (pi1Map b T.root (pi1Conj ht (pi1Map (surfCx A) σ₀ z))) =
    pi1Map i (ptBase w) (pi1Conj hcb (pi1Map a σ₀ z))
  erw [pi1Map_pi1Conj b ht, pi1Conj_pi1Conj, pi1Conj_congr _ hcyl hcancel,
    hmap, pi1Conj_pi1Conj, pi1Conj_congr _ (isPath_mapPath i hcb) hback, pi1Map_pi1Conj]

end SpineW












end Davis
end FiniteChains
