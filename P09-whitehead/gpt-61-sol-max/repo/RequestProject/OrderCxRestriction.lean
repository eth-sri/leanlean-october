import Mathlib.Tactic

import RequestProject.OrderComplexGluing
import RequestProject.ComponentComplex

/-! Corestrict an actual cellular map to an induced subposet using only its
vertex support. The other face vertices are recovered from the attaching path.

-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {K : Complex2.{u}} {P : Type u} [Preorder P]
  (k : Hom K (orderCx P)) (S : P → Prop) (hk : ∀ v, S (k.onV v))

include hk in
theorem orderCxRestrict_edge_support (e : K.E) :
    S (k.onE e).1.1 ∧ S (k.onE e).1.2 := by
  classical grind [FiniteChains.Comb.Hom.src_onE, FiniteChains.Comb.Hom.tgt_onE, orderCx]

include hk in
/-- The middle and final vertices of the image triangle occur as targets of
its attaching edges, so vertex support suffices even for a general two-complex. -/
theorem orderCxRestrict_face_support (t : K.F) :
    S (k.onF t).1.1 ∧ S (k.onF t).1.2.1 ∧ S (k.onF t).1.2.2 := by
  have he : ∀ e : OrdEdge P, (e, true) ∈ (orderCx P).att (k.onF t) → S e.1.2 := by
    classical simp_all [FiniteChains.Comb.Hom.att_onF, FiniteChains.Comb.orderCxRestrict_edge_support, OrdEdge]
  refine ⟨?_, ?_, ?_⟩
  · classical grind [FiniteChains.Comb.Hom.base_onF, orderCx]
  · simp_all [orderCx]
  · simp_all [orderCx]

def orderCxRestrictEdge (e : K.E) : OrdEdge {p : P // S p} :=
  ⟨(⟨(k.onE e).1.1, (orderCxRestrict_edge_support k S hk e).1⟩,
    ⟨(k.onE e).1.2, (orderCxRestrict_edge_support k S hk e).2⟩), (k.onE e).2⟩

def orderCxRestrictFace (t : K.F) : OrdTri {p : P // S p} :=
  ⟨(⟨(k.onF t).1.1, (orderCxRestrict_face_support k S hk t).1⟩,
    ⟨(k.onF t).1.2.1, (orderCxRestrict_face_support k S hk t).2.1⟩,
    ⟨(k.onF t).1.2.2, (orderCxRestrict_face_support k S hk t).2.2⟩), (k.onF t).2⟩

theorem orderCxRestrict_germ_injective :
    Function.Injective (fun eb : (orderCx {p : P // S p}).E × Bool =>
      ((subposetHom S).onE eb.1, eb.2)) := by
  intro x y h
  refine Prod.ext ?_ (congrArg (fun e : OrdEdge P × Bool => e.2) h)
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun e : OrdEdge P × Bool => e.1.1.1) h
  · apply Subtype.ext
    exact congrArg (fun e : OrdEdge P × Bool => e.1.1.2) h

/-- The actual codomain restriction; no edge or face support premise is added. -/
def orderCxRestrict : Hom K (orderCx {p : P // S p}) where
  onV v := ⟨k.onV v, hk v⟩
  onE := orderCxRestrictEdge k S hk
  onF := orderCxRestrictFace k S hk
  src_onE e := Subtype.ext (k.src_onE e)
  tgt_onE e := Subtype.ext (k.tgt_onE e)
  base_onF t := Subtype.ext (k.base_onF t)
  att_onF t := by
    apply List.map_injective_iff.mpr (orderCxRestrict_germ_injective S)
    rw [← (subposetHom S).att_onF]
    change (orderCx P).att (k.onF t) =
      ((K.att t).map (fun eb => (orderCxRestrictEdge k S hk eb.1, eb.2))).map
        (fun eb => ((subposetHom S).onE eb.1, eb.2))
    rw [List.map_map, k.att_onF]
    congr 1





end FiniteChains.Comb
