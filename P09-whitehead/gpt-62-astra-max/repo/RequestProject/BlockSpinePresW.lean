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

noncomputable section

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel BlockFamily

universe u

variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}

section SpineW

variable {α J : Type u} (w : J → List (α × Bool)) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))

/-- The cellular map of the inclusion of the base copy in the quotient. -/
abbrev qInclCxW :=
  orderCxMap (qNew (A := A) (X := PresPos w) (att := att)) qNew_monotone

/-- The base point of the quotient. -/
abbrev qBasePtW : (orderCx (Qpos A _ att)).V :=
  qNew (att := att) (ptBase w)

/-- The cut surface, mapped into the quotient through the block. -/
abbrev surfQW : (NeSpx A) → Qpos A _ att :=
  fun σ => qOldIncl (posQCube σ)

omit [Fintype V] in
theorem surfQW_monotone : Monotone (surfQW w att) :=
  qOldIncl_monotone.comp posQCube_monotone

/-- The cut surface, mapped into the quotient through the copy of the base. -/
abbrev surfBaseW : (NeSpx A) → Qpos A _ att :=
  fun σ => qNew (att σ)

omit [Fintype V] in
theorem surfBaseW_monotone : Monotone (surfBaseW w att) :=
  qNew_monotone.comp att.monotone

/-- The path from the base point of the copy of the base to the block. -/
def cylPathW :=
  mapPath (qInclCxW w att) cb ++ [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)]

omit [Fintype V] in
theorem isPath_cylPathW (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt
    cb (ptBase w) (att σ₀)) :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (cylPathW w att σ₀ cb) (qBasePtW w att) (surfQW w att σ₀) :=
  isPath_append_iff.mpr ⟨_, isPath_mapPath (qInclCxW w att) hcb, isPath_ordPos _⟩

/-- The path from the base point of the copy of the base to the root of the spanning tree. -/
def rootPathW :=
  cylPathW w att σ₀ cb ++
    revPath (mapPath (blockCx A (PresPos w) att) (T.treePath (posQCube σ₀)))

variable (hcb : IsPath (orderCx (PresPos w)).src (orderCx (PresPos w)).tgt cb (ptBase w) (att σ₀))
include hcb

omit [Fintype V] in
theorem isPath_rootPathW :
    IsPath (orderCx (Qpos A (PresPos w) att)).src (orderCx (Qpos A (PresPos w) att)).tgt
      (rootPathW w att σ₀ cb T) (qBasePtW w att)
      (qOldIncl (X := PresPos w) (att := att) T.root) :=
  (isPath_cylPathW w att σ₀ cb hcb).append
    (isPath_revPath (isPath_mapPath _ (T.treePath_isPath (posQCube σ₀))))

/-- **The geometric loops of the block.** -/
def blockToQW :=
  (pi1Conj (isPath_rootPathW w att σ₀ cb T hcb)).comp
    (pi1Map (blockCx A (PresPos w) att) T.root)

omit [Fintype V] in
/-- **The cylinder computation.** -/
theorem blockToQW_surfLoop
    {p : List _}
    (hp : IsPath _ (orderCx (NeSpx A)).tgt p σ₀ σ₀) :
    blockToQW w att σ₀ cb T hcb (SpanningTree.loopOf T (isPath_mapPath (surfCx A) hp))
      = pi1Map (qInclCxW w att) _
          (pi1Conj hcb (Pi1.mk ⟨mapPath (orderCxMap att att.monotone) p,
            isPath_mapPath _ hp⟩)) := by
  classical
  have htp : IsPath _ _ _
      T.root (posQCube σ₀) := T.treePath_isPath _
  have hmtp := isPath_mapPath (blockCx A (PresPos w) att) htp
  have hcyl := isPath_cylPathW w att σ₀ cb hcb
  set X : Pi1 _ _ :=
    Pi1.mk ⟨mapPath (surfCx A) p, isPath_mapPath (surfCx A) hp⟩ with hX
  set Y : Pi1 _ _ :=
    Pi1.mk _ with hY
  set Z : Pi1 _ _ :=
    Pi1.mk ⟨mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p,
      isPath_mapPath _ hp⟩ with hZ
  have hcancel : Htpy _ (qBasePtW w att) (surfQW w att σ₀)
      (rootPathW w att σ₀ cb T ++ mapPath (blockCx A (PresPos w) att)
        (T.treePath (posQCube σ₀))) (cylPathW w att σ₀ cb) := by
    have h := (htpy_revPath_append hmtp).congr_append hcyl (isPath_nil' (surfQW w att σ₀))
    simp_all [rootPathW, List.append_assoc]
  have hback : Htpy _ (qBasePtW w att) (surfBaseW w att σ₀)
      (cylPathW w att σ₀ cb ++ [ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)])
      (mapPath (qInclCxW w att) cb) := by
    have h := (htpy_ordPos_ordNeg (qNew_att_le_qOldIncl σ₀)).congr_append
      (isPath_mapPath (qInclCxW w att) hcb) (isPath_nil' (surfBaseW w att σ₀))
    simp_all [cylPathW, List.append_assoc]
  have hnat := htpy_loop_mapPath_le (surfBaseW_monotone w att) (surfQW_monotone w att)
    (fun σ => qNew_att_le_qOldIncl (att := att) σ) hp
  have hE : pi1Map (blockCx A (PresPos w) att) _ X
      = pi1Conj (isPath_ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)) Z := by
    refine Quotient.sound ?_
    show Htpy _ (surfQW w att σ₀) (surfQW w att σ₀)
      _
      ([ordNeg (qNew_att_le_qOldIncl (att := att) σ₀)] ++
        mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p ++
        [ordPos (qNew_att_le_qOldIncl (att := att) σ₀)])
    have hlist : mapPath (blockCx A (PresPos w) att) (mapPath (surfCx A) p)
        = mapPath (orderCxMap (surfQW w att) (surfQW_monotone w att)) p := by
      simp [mapPath, blockCx, surfCx, orderCxMap, List.map_map, Function.comp_def]
    simp_all
  have hH : Z = pi1Map (qInclCxW w att) _ Y := by
    refine Quotient.sound ?_
    show Htpy _ _ _
      _
      (mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p))
    have hlist : mapPath (qInclCxW w att) (mapPath (orderCxMap att att.monotone) p)
        = mapPath (orderCxMap (surfBaseW w att) (surfBaseW_monotone w att)) p := by
      simp [mapPath, orderCxMap, List.map_map, Function.comp_def]
    rw [hlist]
    exact Htpy.refl _
  calc blockToQW w att σ₀ cb T hcb _
      = pi1Conj _
          _ := rfl
    _ = pi1Conj _
          _ :=
        congrArg _ (pi1Map_pi1Conj (blockCx A (PresPos w) att) htp X)
    _ = pi1Conj _
          _ :=
        pi1Conj_pi1Conj _ hmtp _
    _ = pi1Conj hcyl _ :=
        pi1Conj_congr _ hcyl hcancel _
    _ = pi1Conj hcyl _ :=
        congrArg _ hE
    _ = pi1Conj _ Z :=
        pi1Conj_pi1Conj _ _ _
    _ = pi1Conj _ Z :=
        pi1Conj_congr _ _ hback _
    _ = pi1Conj _
          _ := congrArg _ hH
    _ = pi1Map (qInclCxW w att) _ _ :=
        (pi1Map_pi1Conj _ hcb Y).symm

end SpineW

section ApplicationW

variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (att : NeSpx A →o PresPos w) (σ₀ : NeSpx A)
  (cb : List ((orderCx (PresPos w)).E × Bool)) (T : SpanningTree (orderCx (QOld A)))
  {Su : Type u}

include hw

end ApplicationW

end Davis
end FiniteChains
