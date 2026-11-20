module
public import GS.Topology.Germs
public import GS.CompactFibres
public import Mathlib.Topology.Maps.Proper.Basic
@[expose] public section

/-! Only a compact piece of a pointed chart is needed in the quotient argument. -/
noncomputable section
open Set Filter
open scoped Topology
namespace GS.Spectral
variable {E X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [NormedAddCommGroup E] [ProperSpace E]
structure Patch (E X : Type*) [NormedAddCommGroup E] [TopologicalSpace X] (x : X) where
  K : Set E
  compact : IsCompact K
  around : K ∈ 𝓝 0
  map : K → X
  cont : Continuous map
  inj : Function.Injective map
  point : map ⟨0,mem_of_mem_nhds around⟩ = x
  covers : range map ∈ 𝓝 x

/-- Pull a small compact ball back along the zero section of a submersion chart. -/
lemma level_patch {G : Type*} [TopologicalSpace G] [Zero Y] (c : OpenPartialHomeomorph X (Y × G))
    {P : X → Prop} (x : Subtype P) (hx : x.val ∈ c.source) (k : G ≃ₜ E) (h₀ : k (c x.val).2 = 0)
    (level : ∀ y ∈ c.source, P y ↔ (c y).1 = 0) : Nonempty (Patch E (Subtype P) x) := by
  let f (v : E) : Y × G := (0,k.symm v)
  have hf : Continuous f := continuous_const.prodMk k.symm.continuous
  have eq (a : Subtype P) (h : a.val ∈ c.source) : f (k (c a.val).2) = c a.val :=
    Prod.ext ((level _ h).mp a.property).symm (k.symm_apply_apply _)
  have h0 : f 0 = c x.val := h₀ ▸ eq x hx
  obtain ⟨r,hr,sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hf.continuousAt.preimage_mem_nhds (c.open_target.mem_nhds (h0 ▸ c.map_source hx)))
  let K := Metric.closedBall (0:E) r
  let a (y : K) : Subtype P := ⟨_,(level _ (c.map_target (sub y.property))).2 (congrArg Prod.fst (c.right_inv (sub y.property)))⟩
  have hK : K ∈ 𝓝 (0:E) := Metric.closedBall_mem_nhds _ hr
  refine ⟨⟨K,isCompact_closedBall _ _,hK,a,(c.continuousOn_symm.comp_continuous (hf.comp continuous_subtype_val) (fun y => sub y.property)).subtype_mk _,?_,?_,?_⟩⟩
  · intro u v h; exact Subtype.ext (k.symm.injective (congrArg Prod.snd (c.symm.injOn (sub u.property) (sub v.property) (congrArg Subtype.val h))))
  · exact Subtype.ext (by change c.symm (f 0) = _; rw [h0,c.left_inv hx])
  · have h := ((k.continuous.continuousAt.comp (c.continuousAt hx).snd).comp continuous_subtype_val.continuousAt).preimage_mem_nhds (h₀ ▸ hK : K ∈ 𝓝 (k (c x.val).2))
    filter_upwards [h,(c.open_source.preimage continuous_subtype_val).mem_nhds hx] with y hy hs
    exact ⟨⟨_,hy⟩,Subtype.ext (by change c.symm (f (k (c y.val).2)) = _; rw [eq y hs,c.left_inv hs])⟩
end GS.Spectral
