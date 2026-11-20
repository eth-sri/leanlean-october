module

public import RequestProject.OrderUniversalCocycleReading
public import RequestProject.OrderUniversalPosetCover
public import RequestProject.LocalSystemPosetCover

@[expose] public section

/-! A concrete ordered cover from a nonabelian cocycle, and its exact
realization in a universal order cover. Pending final Lean verification. -/

namespace FiniteChains.Comb.OrdCocycle
open CategoryTheory
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- The local system with right multiplication as transport. -/
abbrev transport : P ⥤ Type u where
  obj _ := G
  map {p q} _ := TypeCat.ofHom (fun g => g * c.val p q)
  map_id p := by ext g; change g * c.val p p = g; simp
  map_comp {p q r} h k := by
    ext g
    change g * c.val p r = (g * c.val p q) * c.val q r
    rw [mul_assoc, c.comp (leOfHom h) (leOfHom k)]

abbrev Cover := LocalSystem.Cover c.transport

theorem coverProjection_isPosetCover : IsPosetCover (LocalSystem.projection c.transport) :=
  LocalSystem.projection_isPosetCover c.transport
    (fun {p q} _ => (Equiv.mulRight (c.val p q)).bijective) (fun _ => ⟨1⟩)

/-- Left translation changes the sheet and preserves every incidence. -/
def coverDeck (g : G) : c.Cover ≃o c.Cover where
  toFun x := ⟨x.1, g * x.2⟩
  invFun x := ⟨x.1, g⁻¹ * x.2⟩
  left_inv x := by cases x <;> simp [transport] <;> rfl
  right_inv x := by cases x <;> simp [transport] <;> rfl
  map_rel_iff' := by
    intro x y
    change (∃ _ : x.1 ≤ y.1, (g * x.2) * c.val x.1 y.1 = g * y.2) ↔
      (∃ _ : x.1 ≤ y.1, x.2 * c.val x.1 y.1 = y.2)
    simp only [mul_assoc, mul_left_cancel_iff]

variable (a : P) (hc : IsConnected (orderCx P))
  (hm : Function.Bijective (c.monodromy a))

include hc in
theorem exists_point_reading (hs : Function.Surjective (c.monodromy a)) (p : P) (g : G) :
    ∃ v : UOrder P a, uOrderEnd v = p ∧ c.readVertex a v = g := by
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover hc).surj p
  obtain ⟨w, hw, hread⟩ := c.readVertex_fibre_surjective a hs v g
  exact ⟨w, hw.trans hv, hread⟩

/-- Actual path class with the specified endpoint and full group reading. -/
noncomputable def pointReading (p : P) (g : G) : UOrder P a :=
  Classical.choose (c.exists_point_reading a hc hm.2 p g)

theorem pointReading_end (p : P) (g : G) :
    uOrderEnd (c.pointReading a hc hm p g) = p :=
  (Classical.choose_spec (c.exists_point_reading a hc hm.2 p g)).1

theorem pointReading_read (p : P) (g : G) :
    c.readVertex a (c.pointReading a hc hm p g) = g :=
  (Classical.choose_spec (c.exists_point_reading a hc hm.2 p g)).2

/-- Comparable endpoint/read pairs lift to actual comparable vertices. -/
theorem pointReading_le {p r : P} {g h : G} (hpr : p ≤ r)
    (hgh : g * c.val p r = h) :
    c.pointReading a hc hm p g ≤ c.pointReading a hc hm r h := by
  let v := c.pointReading a hc hm p g
  have hv  := c.pointReading_end a hc hm p g
  have hvp : uOrderEnd v ≤ r := by rw [hv]; exact hpr
  let w := uOrderStep v r hvp
  have hw : uOrderEnd w = r := uOrderStep_end v r _
  have hr : c.readVertex a w = h := by
    change c.readVertex a (extend (ordPos hvp) v) = h
    rw [c.readVertex_extend a _ v rfl, c.pointReading_read,
      readGerm_ordPos, hv, hgh]
  have he  :=
    c.readVertex_fibre_injective a hm.1 w _
      (hw.trans (c.pointReading_end a hc hm r h).symm)
      (hr.trans (c.pointReading_read a hc hm r h).symm)
  rw [← he]
  exact uOrderStep_le v r _

end FiniteChains.Comb.OrdCocycle
