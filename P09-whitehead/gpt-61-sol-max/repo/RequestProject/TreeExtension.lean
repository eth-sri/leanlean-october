import Mathlib.Tactic

import RequestProject.TreePresentation

/-!
# Extending a spanning tree along a subcomplex inclusion

Condition (1) of Theorem A speaks of a chain `K = X₀ ⊂ X₁ ⊂ ⋯ ⊂ Xₙ` of two-complexes, whereas
Section 2 of the paper works with presentation complexes.  `RequestProject/SpanningTree.lean`
and `RequestProject/TreePresentation.lean` collapse a *single* complex to a presentation; to do
the same to a whole chain one has to collapse the stages *compatibly*, that is, to extend a
spanning tree of a subcomplex to a spanning tree of the ambient complex.  This file does that
and reads off the resulting inclusion of presentations.

* `FiniteChains.Comb.SpanningTree.exists_extension` — **a spanning tree of a subcomplex extends
  to a spanning tree of the ambient connected complex**, with the same root and meeting the
  subcomplex exactly in the given tree.  Only injectivity on vertices and edges is used; no
  finiteness.
* `FiniteChains.Comb.SpanningTree.nonTreeIncl` — the induced injection of generators
  `E(X) ∖ T ↪ E(Y) ∖ T'`;
* `FiniteChains.Comb.SpanningTree.pathWord_mapPath` and
  `FiniteChains.Comb.SpanningTree.treeRel_onF` — the words spelled by an edge path and the
  relators of the two-cells are transported by that injection, so the two collapsed
  presentations form an inclusion of presentations
  `⟨E(X) ∖ T | r⟩ ⊂ ⟨E(Y) ∖ T' | r'⟩` in the sense used by `FiniteChains.PresChain`.

The extension is built exactly as in `FiniteChains.Comb.SpanningTree.exists_of_isConnected`, but
with the distance to the *image of `X`* in place of the distance to the root: a vertex outside
the image gets as tree edge the first edge of a shortest path towards the image, and its height
is defined by recursion along that edge, while a vertex `h a` of the image keeps the tree edge
and the height it has in `X`.  A tree edge of `Y` at a vertex outside the image cannot be an
edge of `X`, because both endpoints of such an edge lie in the image; this is what makes the
new tree meet `X` exactly in `T`.
-/

namespace FiniteChains.Comb.SpanningTree




variable {X Y : Complex2.{u}}

/-! ### Distance to the image of a subcomplex -/

section

/-- The lengths of the edge paths from `a` to the image of `X`. -/
def imReach (h : Hom X Y) (a : Y.V)  :=
  {n | ∃ p : List (Y.E × Bool), p.length = n ∧ ∃ x : X.V, IsPath Y.src Y.tgt p a (h.onV x)}

/-- The distance from a vertex of `Y` to the image of `X`. -/
noncomputable def imDist (h : Hom X Y) (a : Y.V)  := sInf (imReach h a)

variable (h : Hom X Y) (hconn : IsConnected Y) (x₀ : X.V)

include hconn x₀ in
theorem imReach_nonempty (a : Y.V) : (imReach h a).Nonempty := by
  obtain ⟨p, hp⟩ := hconn a (h.onV x₀)
  exact ⟨p.length, p, rfl, x₀, hp⟩

include hconn x₀ in
theorem imDist_mem (a : Y.V) : imDist h a ∈ imReach h a :=
  Nat.sInf_mem (imReach_nonempty h hconn x₀ a)

theorem imDist_le {a : Y.V} {p : List (Y.E × Bool)} {x : X.V}
    (hp : IsPath Y.src Y.tgt p a (h.onV x)) : imDist h a ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, x, hp⟩

theorem imDist_image (x : X.V) : imDist h (h.onV x) = 0 :=
  Nat.le_zero.1 (imDist_le h (p := []) (x := x) rfl)

include hconn x₀ in
theorem exists_pre {a : Y.V} (hz : imDist h a = 0) : ∃ x : X.V, a = h.onV x := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  rw [hz, List.length_eq_zero_iff] at hlen
  subst hlen
  exact ⟨x, hp⟩

/-- A choice of preimage of a vertex at distance zero from the image. -/
noncomputable def imPre {a : Y.V} (hz : imDist h a = 0)  :=
  Classical.choose (exists_pre h hconn x₀ hz)

theorem imPre_spec {a : Y.V} (hz : imDist h a = 0) :
    a = h.onV (imPre h hconn x₀ hz) :=
  Classical.choose_spec (exists_pre h hconn x₀ hz)

include hconn x₀ in
/-- A vertex not in the image has a neighbour one step closer to the image. -/
theorem imDist_step {a : Y.V} (ha : imDist h a ≠ 0) :
    ∃ g : Y.E × Bool, germSrc Y.src Y.tgt g = a ∧
      imDist h (germTgt Y.src Y.tgt g) + 1 = imDist h a := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  have hne : p ≠ [] := by
    aesop
  obtain ⟨g, q, rfl⟩ : ∃ (g : Y.E × Bool) (q : List (Y.E × Bool)), p = g :: q := by
    cases p <;> simp_all
  obtain ⟨hgs, hq⟩ := hp
  refine ⟨g, hgs.symm, ?_⟩
  have h1  := imDist_le h hq
  have h2 : imDist h a ≤ imDist h (germTgt Y.src Y.tgt g) + 1 := by
    obtain ⟨q', hlen', x', hq'⟩ := imDist_mem h hconn x₀ (germTgt Y.src Y.tgt g)
    have hpath : IsPath Y.src Y.tgt (g :: q') a (h.onV x') := ⟨hgs, hq'⟩
    have := imDist_le h hpath
    simpa [hlen'] using this
  have h3 : q.length + 1 = imDist h a := by
    simp only [List.length_cons] at hlen
    omega
  omega

/-- The edge towards the image chosen at a vertex outside the image. -/
noncomputable def upChoice {a : Y.V} (ha : imDist h a ≠ 0)  :=
  Classical.choose (imDist_step h hconn x₀ ha)

theorem upChoice_src {a : Y.V} (ha : imDist h a ≠ 0) :
    germSrc Y.src Y.tgt (upChoice h hconn x₀ ha) = a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).1

theorem upChoice_dist {a : Y.V} (ha : imDist h a ≠ 0) :
    imDist h (germTgt Y.src Y.tgt (upChoice h hconn x₀ ha)) + 1 = imDist h a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).2

/-! ### The extended height and the extended tree edges -/

variable (T : SpanningTree X)

/-- The height function of the extended tree: the old height on the image, and one more than
the height of the next vertex towards the image elsewhere. -/
noncomputable def extHt (a : Y.V)  :=
  if hz : imDist h a = 0 then T.ht (imPre h hconn x₀ hz)
  else extHt (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1
  termination_by imDist h a
  decreasing_by
    have := upChoice_dist h hconn x₀ hz
    omega

theorem extHt_of_zero {a : Y.V} (hz : imDist h a = 0) :
    extHt h hconn x₀ T a = T.ht (imPre h hconn x₀ hz) := by
  rw [extHt, dif_pos hz]

theorem extHt_of_ne {a : Y.V} (hz : imDist h a ≠ 0) :
    extHt h hconn x₀ T a =
      extHt h hconn x₀ T (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1 := by
  rw [extHt]
  exact dif_neg hz

variable (hV : Function.Injective h.onV)
include hV in
include hconn x₀ in
theorem extHt_image  (x : X.V) :
    extHt h hconn x₀ T (h.onV x) = T.ht x := by
  grind [imDist, imDist_image, extHt_of_zero, imPre_spec]

theorem imPre_ne_root {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    imPre h hconn x₀ hz ≠ T.root := fun hr =>
  ha ((imPre_spec h hconn x₀ hz).trans (congrArg h.onV hr))

/-- The tree edge of the extended tree. -/
noncomputable def extUp (a : Y.V) (ha : a ≠ h.onV T.root)  :=
  if hz : imDist h a = 0 then
    (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
      (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).2)
  else upChoice h hconn x₀ hz

theorem extUp_of_zero {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    extUp h hconn x₀ T a ha =
      (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
        (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).2) := by
  rw [extUp, dif_pos hz]

theorem extUp_of_ne {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a ≠ 0) :
    extUp h hconn x₀ T a ha = upChoice h hconn x₀ hz := by
  rw [extUp]
  exact dif_neg hz

include hV in
/-- The extension of a spanning tree of a subcomplex to the ambient complex. -/
noncomputable def extend  : SpanningTree Y where
  root := h.onV T.root
  ht := extHt h hconn x₀ T
  isTree := fun e => ∃ (a : Y.V) (ha : a ≠ h.onV T.root), (extUp h hconn x₀ T a ha).1 = e
  up := extUp h hconn x₀ T
  ht_root := by rw [extHt_image h hconn x₀ T hV, T.ht_root]
  ht_eq_zero := by
    classical grind [FiniteChains.Comb.SpanningTree.imPre_spec, FiniteChains.Comb.SpanningTree.ht_eq_zero, FiniteChains.Comb.SpanningTree.extHt_of_zero, FiniteChains.Comb.SpanningTree.extHt_of_ne, imDist]
  up_src := by
    classical grind [FiniteChains.Comb.SpanningTree.imPre_ne_root, FiniteChains.Comb.SpanningTree.extUp_of_zero, FiniteChains.Comb.germSrc_onE, FiniteChains.Comb.SpanningTree.up_src, FiniteChains.Comb.SpanningTree.imPre_spec, FiniteChains.Comb.SpanningTree.extUp_of_ne, FiniteChains.Comb.SpanningTree.upChoice_src, imDist]
  up_ht := by
    classical grind [FiniteChains.Comb.SpanningTree.imPre_ne_root, FiniteChains.Comb.SpanningTree.extUp_of_zero, FiniteChains.Comb.germTgt_onE, FiniteChains.Comb.SpanningTree.extHt_image, FiniteChains.Comb.SpanningTree.extHt_of_zero, FiniteChains.Comb.SpanningTree.up_ht, FiniteChains.Comb.SpanningTree.extUp_of_ne, FiniteChains.Comb.SpanningTree.extHt_of_ne, imDist]
  isTree_iff := fun _ => Iff.rfl

include hV in
include hconn x₀ in
/-- **A spanning tree of a subcomplex extends to a spanning tree of the ambient complex.**
The extension has the image of the old root as root, and an edge of the subcomplex is an edge
of the extension exactly when it was an edge of the old tree. -/
theorem exists_extension  (hE : Function.Injective h.onE) :
    ∃ T' : SpanningTree Y, T'.root = h.onV T.root ∧
      ∀ e : X.E, (T'.isTree (h.onE e) ↔ T.isTree e) := by
  refine ⟨extend h hconn x₀ T hV, rfl, ?_⟩
  intro e
  constructor
  · rintro ⟨a, ha, hae⟩
    by_cases hz : imDist h a = 0
    · classical aesop (add simp [FiniteChains.Comb.SpanningTree.isTree_iff, FiniteChains.Comb.SpanningTree.imPre_ne_root, FiniteChains.Comb.SpanningTree.extUp_of_zero])
    · exfalso
      apply hz
      rw [extUp_of_ne h hconn x₀ T ha hz] at hae
      have hsrc := upChoice_src h hconn x₀ hz
      revert hae hsrc
      generalize upChoice h hconn x₀ hz = g
      obtain ⟨e', b⟩ := g
      intro hae hsrc
      simp only at hae
      subst hae
      rw [← hsrc, germSrc_onE h (e, b)]
      exact imDist_image h _
  · intro he
    obtain ⟨x, hx, hxe⟩ := (T.isTree_iff e).1 he
    have hne  := fun hc => hx (hV hc)
    refine ⟨h.onV x, hne, ?_⟩
    grind [imDist_image, extUp_of_zero, imPre_spec]

end

/-! ### The induced inclusion of the collapsed presentations -/

section

variable {h : Hom X Y} {T : SpanningTree X} {T' : SpanningTree Y}
  (hiff : ∀ e : X.E, T'.isTree (h.onE e) ↔ T.isTree e)

/-- The generators of the collapse of `X` are generators of the collapse of `Y`, as soon as the
spanning tree of `Y` meets `X` exactly in the spanning tree of `X`. -/
def nonTreeIncl (e : NonTree T) : NonTree T' :=
  ⟨h.onE e.1, fun hc => e.2 ((hiff e.1).1 hc)⟩



theorem nonTreeIncl_injective (hE : Function.Injective h.onE) :
    Function.Injective (nonTreeIncl hiff) := by
  intro a b hab
  exact Subtype.ext (hE (congrArg Subtype.val hab))

/-- The letter spelled by an oriented edge is transported by the inclusion of generators. -/
theorem germWord_onE (g : X.E × Bool) :
    germWord T' (h.onE g.1, g.2) = FreeGroup.map (nonTreeIncl hiff) (germWord T g) := by
  aesop (add simp [germWord])

/-- **The word spelled by an edge path is transported by the inclusion of generators.** -/
theorem pathWord_mapPath (l : List (X.E × Bool)) :
    pathWord T' (mapPath h l) = FreeGroup.map (nonTreeIncl hiff) (pathWord T l) := by
  induction l with
  | nil => simp [mapPath]
  | cons g l ih =>
      classical grind [mapPath, pathWord_cons, germWord_onE]

/-- **The relators of the collapse of `X` are relators of the collapse of `Y`.**  Together with
`FiniteChains.Comb.SpanningTree.nonTreeIncl_injective` this exhibits the collapse of `X` as a
subpresentation of the collapse of `Y`, in the sense used by `FiniteChains.PresChain`. -/
theorem treeRel_onF (f : X.F) :
    treeRel T' (h.onF f) = FreeGroup.map (nonTreeIncl hiff) (treeRel T f) := by
  have hatt : Y.att (h.onF f) = mapPath h (X.att f) := h.att_onF f
  rw [treeRel, hatt, pathWord_mapPath hiff, treeRel]

end

end FiniteChains.Comb.SpanningTree


