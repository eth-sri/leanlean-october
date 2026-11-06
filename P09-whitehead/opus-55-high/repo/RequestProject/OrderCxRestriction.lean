import RequestProject.OrderComplexGluing
import RequestProject.ComponentComplex
import RequestProject.Tac


/-! Corestrict an actual cellular map to an induced subposet using only its
vertex support. The other face vertices are recovered from the attaching path.

-/

bwd

namespace FiniteChains.Comb
universe u
variable {K : Complex2.{u}} {P : Type u} [Preorder P]
  (k : Hom K (orderCx P)) (S : P → Prop) (hk : ∀ v, S (k.onV v))

include hk in
theorem orderCxRestrict_edge_support (e : K.E) :
    S (k.onE e).1.1 ∧ S (k.onE e).1.2 := by
  constructor
  · change S ((orderCx P).src (k.onE e))
    simp_all [k.src_onE]
  · change S ((orderCx P).tgt (k.onE e))
    simp_all [k.tgt_onE]

include hk in
/-- The middle and final vertices of the image triangle occur as targets of
its attaching edges, so vertex support suffices even for a general two-complex. -/
theorem orderCxRestrict_face_support (t : K.F) :
    S (k.onF t).1.1 ∧ S (k.onF t).1.2.1 ∧ S (k.onF t).1.2.2 := by
  have he : ∀ e : OrdEdge P, (e, true) ∈ (orderCx P).att (k.onF t) → S e.1.2 := by
    intro e he
    rw [k.att_onF] at he
    obtain ⟨eb, _, heb⟩ := List.mem_map.mp he
    have ht := congrArg (·.1.1.2) heb
    rw [← ht]
    exact (orderCxRestrict_edge_support k S hk eb.1).2
  refine ⟨?_, ?_, ?_⟩
  · change S ((orderCx P).base (k.onF t))
    simp_all [k.base_onF]
  · exact he ⟨((k.onF t).1.1, (k.onF t).1.2.1), (k.onF t).2.1⟩
      (by tauto)
  · exact he ⟨((k.onF t).1.2.1, (k.onF t).1.2.2), (k.onF t).2.2⟩
      (by tauto)

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
  refine Prod.ext ?_ (by simp_all)
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (·.1.1.1) h
  · apply Subtype.ext
    exact congrArg (·.1.1.2) h

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
    change (orderCx P).att (k.onF t) =
      ((K.att t).map (fun eb => (orderCxRestrictEdge k S hk eb.1, eb.2))).map
        (fun eb => ((subposetHom S).onE eb.1, eb.2))
    rw [List.map_map, k.att_onF]
    congr 1


/-- Forgetting the support proofs recovers the original cellular map on every cell. -/
theorem orderCxRestrict_projects :
    (orderCxMap Subtype.val (fun _ _ h => h)).comp (orderCxRestrict k S hk) = k := by
  rfl
