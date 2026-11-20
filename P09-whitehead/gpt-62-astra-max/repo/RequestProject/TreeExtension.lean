module

public import RequestProject.TreePresentation

@[expose] public section

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

noncomputable section

namespace FiniteChains
namespace Comb
namespace SpanningTree

universe u

variable {X Y : Complex2.{u}}

/-! ### Distance to the image of a subcomplex -/

section Extension

variable (h : Hom X Y) (a : Y.V)

/-- The lengths of the edge paths from `a` to the image of `X`. -/
def imReach :=
  {n | ∃ p : List _, p.length = n ∧ ∃ x : X.V, IsPath Y.src Y.tgt p a (h.onV x)}

/-- The distance from a vertex of `Y` to the image of `X`. -/
def imDist := sInf (imReach h a)

variable (h : Hom X Y) (hconn : IsConnected Y) (x₀ : X.V)

variable (a : Y.V)

include hconn x₀ in
theorem imReach_nonempty : (imReach h a).Nonempty := by
  obtain ⟨p, hp⟩ := hconn a _
  exact ⟨p.length, p, rfl, x₀, hp⟩

include hconn x₀ in
theorem imDist_mem : imDist h a ∈ imReach h a :=
  Nat.sInf_mem (imReach_nonempty h hconn x₀ a)

theorem imDist_le {a : Y.V} {p : List _} {x : X.V}
    (hp : IsPath Y.src Y.tgt p a (h.onV x)) : imDist h a ≤ p.length :=
  Nat.sInf_le ⟨p, rfl, x, hp⟩

theorem imDist_image (x : X.V) : imDist h (h.onV x) = 0 :=
  Nat.le_zero.1 (imDist_le h (p := []) (x := x) rfl)

variable {a : Y.V}

section

variable (hz : imDist h a = 0)
include hz

include hconn x₀ in
theorem exists_pre : ∃ x : X.V, a = h.onV x := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a <;> simp_all

/-- A choice of preimage of a vertex at distance zero from the image. -/
def imPre :=
  Classical.choose (exists_pre h hconn x₀ hz)

theorem imPre_spec :
    a = h.onV (imPre h hconn x₀ hz) :=
  Classical.choose_spec (exists_pre h hconn x₀ hz)

end

section

variable (ha : imDist h a ≠ 0)
include ha

include hconn x₀ in
/-- A vertex not in the image has a neighbour one step closer to the image. -/
theorem imDist_step :
    ∃ g : Y.E × Bool, germSrc Y.src Y.tgt g = a ∧
      imDist h (germTgt Y.src Y.tgt g) + 1 = imDist h a := by
  obtain ⟨p, hlen, x, hp⟩ := imDist_mem h hconn x₀ a
  have hne : p ≠ [] := by
    intro hp0
    simp_all
  obtain ⟨g, q, rfl⟩ : ∃ (g : Y.E × Bool) (q : List _), p = g :: q := by
    cases p with
    | nil => exact absurd rfl hne
    | cons g q => simp
  obtain ⟨hgs, hq⟩ := hp
  have h1 := imDist_le h hq
  have h2 : imDist h a ≤ imDist h (germTgt Y.src Y.tgt g) + 1 := by
    obtain ⟨q', hlen', x', hq'⟩ := imDist_mem h hconn x₀ _
    have hpath : IsPath Y.src Y.tgt (g :: q') a _ := ⟨hgs, hq'⟩
    have := imDist_le h hpath
    simp_all
  grind

/-- The edge towards the image chosen at a vertex outside the image. -/
def upChoice :=
  Classical.choose (imDist_step h hconn x₀ ha)

theorem upChoice_src :
    germSrc Y.src Y.tgt (upChoice h hconn x₀ ha) = a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).1

theorem upChoice_dist :
    imDist h (germTgt Y.src Y.tgt (upChoice h hconn x₀ ha)) + 1 = imDist h a :=
  (Classical.choose_spec (imDist_step h hconn x₀ ha)).2

end

/-! ### The extended height and the extended tree edges -/

variable (T : SpanningTree X)

/-- The height function of the extended tree: the old height on the image, and one more than
the height of the next vertex towards the image elsewhere. -/
def extHt (a : Y.V) :=
  if hz : imDist h a = 0 then T.ht (imPre h hconn x₀ hz)
  else extHt (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1
  termination_by imDist h a
  decreasing_by
    have := upChoice_dist h hconn x₀ hz
    omega

variable {a : Y.V}

theorem extHt_of_zero (hz : imDist h a = 0) :
    extHt h hconn x₀ T a = T.ht (imPre h hconn x₀ hz) := by
  simp_all [extHt, dif_pos]

theorem extHt_of_ne (hz : imDist h a ≠ 0) :
    extHt h hconn x₀ T a =
      extHt h hconn x₀ T (germTgt Y.src Y.tgt (upChoice h hconn x₀ hz)) + 1 := by
  rw [extHt]
  exact dif_neg hz

include hconn x₀ in
theorem extHt_image (hV : Function.Injective h.onV) (x : X.V) :
    extHt h hconn x₀ T (h.onV x) = T.ht x := by
  grind [imDist_image, extHt_of_zero, imPre_spec]

theorem imPre_ne_root {a : Y.V} (ha : a ≠ h.onV T.root) (hz : imDist h a = 0) :
    imPre h hconn x₀ hz ≠ T.root := by grind [imPre]

/-- The tree edge of the extended tree. -/
def extUp (a : Y.V) (ha : a ≠ h.onV T.root) :=
  if hz : imDist h a = 0 then
    (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
      (T.up _ (imPre_ne_root h hconn x₀ T ha hz)).2)
  else upChoice h hconn x₀ hz

variable {a : Y.V} (ha : a ≠ h.onV T.root)

theorem extUp_of_zero (hz : imDist h a = 0) :
    extUp h hconn x₀ T a ha =
      (h.onE (T.up (imPre h hconn x₀ hz) (imPre_ne_root h hconn x₀ T ha hz)).1,
        (T.up _ (imPre_ne_root h hconn x₀ T ha hz)).2) := by
  simp_all [extUp, dif_pos]

theorem extUp_of_ne (hz : imDist h a ≠ 0) :
    extUp h hconn x₀ T a ha = upChoice h hconn x₀ hz := by
  apply dif_neg

variable (hV : Function.Injective h.onV)
include hV

/-- The extension of a spanning tree of a subcomplex to the ambient complex. -/
def extend : SpanningTree Y where
  root := h.onV T.root
  ht := extHt h hconn x₀ T
  isTree := fun e => ∃ (a : Y.V) (ha : a ≠ h.onV T.root), (extUp h hconn x₀ T a ha).1 = e
  up := extUp h hconn x₀ T
  ht_root := by simp_all [extHt_image, T.ht_root]
  ht_eq_zero := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extHt_of_zero h hconn x₀ T hz] at ha
      exact (imPre_spec h hconn x₀ hz).trans (congrArg h.onV (T.ht_eq_zero _ ha))
    · simp_all [extHt_of_ne]
  up_src := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz, germSrc_onE h, T.up_src]
      grind [imPre_spec]
    · simp_all [extUp_of_ne, upChoice_src]
  up_ht := by
    intro a ha
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz, germTgt_onE h,
        extHt_image h hconn x₀ T hV, extHt_of_zero h hconn x₀ T hz]
      exact T.up_ht _ _
    · simp_all [extUp_of_ne, extHt_of_ne]
  isTree_iff := fun _ => Iff.rfl

include hconn x₀ in
/-- **A spanning tree of a subcomplex extends to a spanning tree of the ambient complex.**
The extension has the image of the old root as root, and an edge of the subcomplex is an edge
of the extension exactly when it was an edge of the old tree. -/
theorem exists_extension (hE : Function.Injective h.onE) :
    ∃ T' : SpanningTree Y, T'.root = h.onV T.root ∧
      ∀ e : X.E, (T'.isTree (h.onE e) ↔ T.isTree e) := by
  refine ⟨extend h hconn x₀ T hV, rfl, ?_⟩
  intro e
  constructor
  · rintro ⟨a, ha, hae⟩
    by_cases hz : imDist h a = 0
    · rw [extUp_of_zero h hconn x₀ T ha hz] at hae
      exact (T.isTree_iff e).2 ⟨_, imPre_ne_root h hconn x₀ T ha hz, hE hae⟩
    · exfalso
      apply hz
      rw [extUp_of_ne h hconn x₀ T ha hz] at hae
      have hsrc := upChoice_src h hconn x₀ hz
      revert hae hsrc
      generalize upChoice h hconn x₀ hz = g
      obtain ⟨e', b⟩ := g
      intro hae hsrc
      subst hae
      rw [← hsrc, germSrc_onE h (e, b)]
      exact imDist_image h _
  · intro he
    obtain ⟨x, hx, hxe⟩ := (T.isTree_iff e).1 he
    refine ⟨h.onV x, (fun hc => hx (hV hc)), ?_⟩
    grind [imDist_image, extUp_of_zero, imPre_spec]

end Extension

/-! ### The induced inclusion of the collapsed presentations -/

section Presentation

variable {h : Hom X Y} {T : SpanningTree X} {T' : SpanningTree Y}
  (hiff : ∀ e : X.E, T'.isTree (h.onE e) ↔ T.isTree e)

variable (e : NonTree T)

/-- The generators of the collapse of `X` are generators of the collapse of `Y`, as soon as the
spanning tree of `Y` meets `X` exactly in the spanning tree of `X`. -/
def nonTreeIncl : NonTree T' :=
  ⟨h.onE e.1, fun hc => e.2 ((hiff e.1).1 hc)⟩

@[simp] theorem nonTreeIncl_coe : (nonTreeIncl hiff e) = h.onE e.1 := rfl

theorem nonTreeIncl_injective (hE : Function.Injective h.onE) :
    Function.Injective (nonTreeIncl hiff) := by
  intro a b hab
  exact Subtype.ext (hE (congrArg Subtype.val hab))

/-- The letter spelled by an oriented edge is transported by the inclusion of generators. -/
theorem germWord_onE (g : X.E × Bool) :
    germWord T' (h.onE g.1, g.2) = FreeGroup.map (nonTreeIncl hiff) (germWord T g) := by
  classical
  obtain ⟨e, b⟩ := g
  by_cases hT : T.isTree e
  · simp [germWord, hT, ((hiff e).2 hT)]
  · have hT' : ¬ T'.isTree _ := fun hc => hT ((hiff e).1 hc)
    cases b <;> simp [germWord, hT, hT', nonTreeIncl]

/-- **The word spelled by an edge path is transported by the inclusion of generators.** -/
theorem pathWord_mapPath (l : List _) :
    pathWord T' (mapPath h l) = FreeGroup.map (nonTreeIncl hiff) (pathWord T l) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
      have hcons : mapPath h (g :: l) = (h.onE g.1, g.2) :: mapPath h l := rfl
      grind [pathWord_cons, germWord_onE]

/-- **The relators of the collapse of `X` are relators of the collapse of `Y`.**  Together with
`FiniteChains.Comb.SpanningTree.nonTreeIncl_injective` this exhibits the collapse of `X` as a
subpresentation of the collapse of `Y`, in the sense used by `FiniteChains.PresChain`. -/
theorem treeRel_onF (f : X.F) :
    treeRel T' (h.onF f) = FreeGroup.map (nonTreeIncl hiff) (treeRel T f) := by
  have hatt : Y.att _ = mapPath h _ := h.att_onF f
  rw [treeRel, hatt, pathWord_mapPath hiff, treeRel]

end Presentation

end SpanningTree
end Comb
end FiniteChains
