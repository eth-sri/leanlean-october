module

public import RequestProject.OrderComplexRetraction

@[expose] public section

/-!
# Transferring path statements along monotone maps and order isomorphisms

Auxiliary material for turning the injectivity statements of
`RequestProject/OrderComplexRetraction.lean` — which are formulated inside one ambient order
complex — into statements about the map of fundamental groups induced by a monotone map.

* `FiniteChains.Comb.htpyIn_true_iff` — a homotopy inside the whole poset is just a homotopy;
* `FiniteChains.Comb.mapPath_comp_eq_self` — a monotone map composed with a monotone left
  inverse returns an edge path unchanged;
* `FiniteChains.Comb.simplyConnected_orderCx_of_orderIso`,
  `FiniteChains.Comb.isConnected_orderCx_of_orderIso` — transfer of connectivity and simple
  connectedness along an order isomorphism;
* `FiniteChains.Comb.htpy_nil_of_injIn` and `FiniteChains.Comb.pi1Map_injective_of_injIn` —
  if the image subposet of a monotone embedding with a monotone retraction is injective on path
  classes inside the whole poset, then the induced map of fundamental groups is injective.
-/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains
namespace Comb

universe u

variable {P Q R : Type u} [Preorder P] [Preorder Q] [Preorder R]

/-- A homotopy inside the whole poset is an ordinary homotopy. -/
theorem htpyIn_true_iff {a b : P} {p q : List _} :
    HtpyIn (fun _ : P => True) a b p q ↔ Htpy _ a b p q := by
  constructor
  · exact HtpyIn.htpy
  · intro h
    refine Relation.ReflTransGen.mono (fun x y hs => ?_) _ _ h
    exact hs.imp (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)
      (fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => ⟨trivial, trivial⟩⟩)

/-- A monotone map followed by a monotone left inverse returns an edge path unchanged. -/
theorem mapPath_comp_eq_self {f : Q → P} (hf : Monotone f) {g : P → Q} (hg : Monotone g)
    (hgf : ∀ y, g (f y) = y) :
    ∀ l : List _,
      mapPath (orderCxMap g hg) (mapPath (orderCxMap f hf) l) = l
  | [] => rfl
  | e :: t => by
      simp only [mapPath, List.map_cons, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf _
        · exact hgf _
      · simpa [mapPath] using mapPath_comp_eq_self hf hg hgf t

section

variable (e : P ≃o Q)
include e

/-- Simple connectedness transfers along an order isomorphism. -/
theorem simplyConnected_orderCx_of_orderIso (h : SimplyConnected (orderCx Q)) :
    SimplyConnected (orderCx P) := by
  intro a p hp
  have hmono : Monotone e := fun _ _ hxy => e.monotone hxy
  have himg := h _ _
    (isPath_mapPath (orderCxMap e hmono) hp)
  have hpush := mapPath_htpy (orderCxMap e.symm (fun _ _ hxy => e.symm.monotone hxy)) himg
  simp_all [mapPath_comp_eq_self]

/-- Connectivity transfers along an order isomorphism. -/
theorem isConnected_orderCx_of_orderIso (h : IsConnected (orderCx Q)) :
    IsConnected (orderCx P) := by
  intro a b
  have hmono' : Monotone e.symm := fun _ _ hxy => e.symm.monotone hxy
  obtain ⟨l, hl⟩ := h (e a) (e b)
  refine ⟨mapPath (orderCxMap e.symm hmono') l, ?_⟩
  have := isPath_mapPath (orderCxMap e.symm hmono') hl
  simp_all

end

variable {Bp : P → Prop}

/-- The lift of the image of an edge path, pushed back by a monotone retraction, is the original
path. -/
theorem mapPath_liftPathIn_mapPath {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp _) {g : {z : P // Bp z} → Q} (hg : Monotone g)
    (hgf : ∀ y, g ⟨f y, hfB y⟩ = y) :
    ∀ (l : List _) (hl : PathIn Bp _),
      mapPath (orderCxMap g hg) (liftPathIn (mapPath (orderCxMap f hf) l) hl) = l
  | [], _ => rfl
  | e :: t, hl => by
      simp only [mapPath, List.map_cons, liftPathIn, List.cons.injEq]
      refine ⟨?_, ?_⟩
      · refine Prod.ext ?_ rfl
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact hgf _
        · exact hgf _
      · simpa [mapPath] using (mapPath_liftPathIn_mapPath hf hfB hg hgf t (pathIn_of_cons hl).2)

/-- The image of an edge path under a monotone map with values in `Bp` lies inside `Bp`. -/
theorem pathIn_mapPath_of_image {f : Q → P} (hf : Monotone f)
    (hfB : ∀ y, Bp (f y)) (l : List _) :
    PathIn Bp (mapPath (orderCxMap f hf) l) := by
  intro e he
  simp only [mapPath, List.mem_map] at he
  obtain ⟨x, -, rfl⟩ := he <;> aesop

variable (hinj : InjIn (fun _ : P => True) Bp)
    {f : Q → P}
    (hf : Monotone f)
    (hfB : ∀ y, Bp (f y))
    {g : {z : P // Bp z} → Q}
    (hg : Monotone g)
    (hgf : ∀ y, g ⟨f y, hfB y⟩ = y)
include hinj hfB g hg hgf

/-- **From injectivity on path classes to injectivity on loops.**  If the image of a monotone map
`f` with a monotone retraction `g` is injective on path classes inside the whole poset, then a
loop of the source which becomes null-homotopic in the target is null-homotopic. -/
theorem htpy_nil_of_injIn
    {y : Q} {p : List _}
    (hp : IsPath (orderCx Q).src (orderCx Q).tgt p y y)
    (h : Htpy _ (f y) (f y) (mapPath (orderCxMap f hf) p) []) :
    Htpy _ y y p [] := by
  have hpB := pathIn_mapPath_of_image hf hfB p
  have hIn :=
    hinj _ _ (hfB y) (isPath_mapPath (orderCxMap f hf) hp) hpB (htpyIn_true_iff.mpr h)
  have hpush := mapPath_htpy (orderCxMap g hg) (htpy_lift_of_htpyIn hIn (hfB y) (hfB y) hpB (pathIn_nil Bp))
  rw [mapPath_liftPathIn_mapPath hf hfB hg hgf p hpB] at hpush <;> aesop

/-- **Injectivity of the induced map of fundamental groups.** -/
theorem pi1Map_injective_of_injIn (y : Q) :
    Function.Injective (Comb.pi1Map (orderCxMap f hf) y) := by
  refine (injective_iff_map_eq_one _).mpr ?_
  intro c hc
  induction c using Quotient.inductionOn with
  | h p =>
      exact Quotient.sound (htpy_nil_of_injIn hinj hf hfB hg hgf p.2 (Quotient.exact hc))

end Comb
end FiniteChains
