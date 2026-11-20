module

public import RequestProject.OrderComplexGluing

@[expose] public section

namespace FiniteChains.Comb

theorem chainCx_att_injective {P : Type*} {r : P → P → Prop} {hr : IsTrans P r} :
    Function.Injective (chainCx r hr).att := by
  rintro ⟨⟨a, b, c⟩, hab, hbc⟩ ⟨⟨x, y, z⟩, hxy, hyz⟩ h
  simp_all

/-- The endpoints specify each edge, and the attaching list specifies each triangle.
Consequently a map into an order complex is determined on vertices. -/
theorem Hom.ext_chainCx {X : Complex2} {P : Type*} {r : P → P → Prop} {hr : IsTrans P r}
    {f g : Hom X (chainCx r hr)} (hv : f.onV = g.onV) : f = g := by
  have he : f.onE = g.onE := funext fun e => Subtype.ext (Prod.ext
    (((f.src_onE e).trans (congrFun hv _)).trans (g.src_onE e).symm)
    (((f.tgt_onE e).trans (congrFun hv _)).trans (g.tgt_onE e).symm))
  have hf : f.onF = g.onF := funext fun t => chainCx_att_injective (by rw [f.att_onF, g.att_onF, he])
  cases f; aesop

theorem Hom.ext_orderCx {X : Complex2} {P : Type*} [Preorder P] {f g : Hom X (orderCx P)}
    (hv : f.onV = g.onV) : f = g :=
  @Hom.ext_chainCx X P (· ≤ ·) ⟨fun _ _ _ => le_trans⟩ f g hv

section Injective
universe u
variable {P : Type u} {r : P → P → Prop} {hr : IsTrans P r} {Y : Complex2.{u}}
  (f : Hom (chainCx r hr) Y) (hi : Function.Injective f.onV)
include hi

/-- A map out of a chain complex which embeds the vertices also embeds the cells. -/
theorem Hom.injective_chainCx_onE : Function.Injective f.onE := by
  intro e d h
  exact Subtype.ext (Prod.ext (hi (by rw [← f.src_onE, ← f.src_onE, h]))
    (hi (by rw [← f.tgt_onE, ← f.tgt_onE, h])))

theorem Hom.injective_chainCx_onF : Function.Injective f.onF := by
  intro t s h
  apply chainCx_att_injective
  apply mapPath_injective_of_onE (f := f) (f.injective_chainCx_onE hi)
  unfold mapPath
  rw [← f.att_onF, ← f.att_onF, h]

end Injective

/-- Left cancellation into a complex whose vertices distinguish the intermediate vertices. -/
theorem Hom.comp_left_cancel_orderCx {Y Z : Complex2} {P : Type} [Preorder P]
    {j : Hom (orderCx P) Z} (hi : Function.Injective j.onV)
    {r s : Hom Y (orderCx P)} (h : j.comp r = j.comp s) : r = s :=
  Hom.ext_orderCx (funext fun a => hi (congrArg (·.onV a) h))

end FiniteChains.Comb
