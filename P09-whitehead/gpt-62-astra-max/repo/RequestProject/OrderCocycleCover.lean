module

public import RequestProject.OrderUniversalCocycleReading
public import RequestProject.OrderUniversalPosetCover

@[expose] public section

/-! A concrete ordered cover from a nonabelian cocycle, and its exact
realization in a universal order cover. Pending final Lean verification. -/

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

/-- The sheet is multiplied on the right when a comparability is traversed. -/
structure Cover (c : OrdCocycle P G) where
  point : P
  sheet : G

instance coverPartialOrder : PartialOrder c.Cover where
  le a b := a.point ≤ b.point ∧ a.sheet * c.val a.point b.point = b.sheet
  le_refl a := ⟨le_rfl, by simp⟩
  le_trans a b d hab hbd := ⟨hab.1.trans hbd.1, by
    grind [c.comp, mul_assoc, hab.2, hbd.2]⟩
  le_antisymm a b hab hba := by
    have hp := le_antisymm hab.1 hba.1
    cases a with
    | mk ap ag =>
      simp_all

theorem coverProjection_isPosetCover : IsPosetCover (Cover.point (c := c)) := by
  refine ⟨fun _ _ h => h.1, fun p => ⟨⟨p, 1⟩, rfl⟩, ?_, ?_⟩
  · intro a p hp
    refine ⟨⟨p, a.sheet * c.val a.point p⟩, ⟨⟨hp, rfl⟩, rfl⟩, ?_⟩
    rintro ⟨b, g⟩ ⟨h, hb⟩
    have hg := h.2
    simp_all

  · intro a p hp
    refine ⟨⟨p, a.sheet * (c.val p a.point)⁻¹⟩,
      ⟨⟨hp, by simp⟩, rfl⟩, ?_⟩
    rintro ⟨b, g⟩ ⟨h, hb⟩
    change b = p at hb
    subst b
    have hg : g = a.sheet * (c.val p a.point)⁻¹ := by
      rw [← h.2]
      group
    simp_all

/-- Left translation changes the sheet and preserves every incidence. -/
def coverDeck (g : G) : c.Cover ≃o c.Cover where
  toFun x := ⟨x.point, g * x.sheet⟩
  invFun x := ⟨x.point, g⁻¹ * x.sheet⟩
  left_inv x := by simp
  right_inv x := by simp
  map_rel_iff' := by
    intro x y
    change (x.point ≤ y.point ∧ (g * x.sheet) * c.val x.point y.point = g * y.sheet) ↔
      (x.point ≤ y.point ∧ x.sheet * c.val x.point y.point = y.sheet)
    simp [mul_assoc, mul_left_cancel_iff]

variable (a : P) (hc : IsConnected (orderCx P))
  (hm : Function.Bijective (c.monodromy a))

variable (p : P) (g : G)

include hc hm in
theorem exists_point_reading :
    ∃ v : UOrder P a, uOrderEnd v = p ∧ c.readVertex a v = g := by
  obtain ⟨v, hv⟩ := (uOrderEnd_isPosetCover hc).surj p
  obtain ⟨w, hw, hread⟩ := c.readVertex_fibre_surjective a hm.2 v g <;> aesop

/-- Actual path class with the specified endpoint and full group reading. -/
noncomputable def pointReading :=
  Classical.choose (c.exists_point_reading a hc hm p g)

theorem pointReading_end :
    uOrderEnd (c.pointReading a hc hm p g) = p :=
  (Classical.choose_spec (c.exists_point_reading a hc hm p g)).1

theorem pointReading_read :
    c.readVertex a (c.pointReading a hc hm p g) = g :=
  (Classical.choose_spec (c.exists_point_reading a hc hm p g)).2

/-- Comparable endpoint/read pairs lift to actual comparable vertices. -/
theorem pointReading_le {p r : P} {g h : G} (hpr : p ≤ r)
    (hgh : g * c.val p r = h) :
    c.pointReading a hc hm p g ≤ c.pointReading a hc hm r h := by
  let v := c.pointReading a hc hm p g
  have hv := c.pointReading_end a hc hm p g
  have hvp : uOrderEnd v ≤ r := by rw [hv]; exact hpr
  let w := uOrderStep v r hvp
  have hr : c.readVertex a w = h := by
    change c.readVertex a (extend (ordPos hvp) v) = h
    rw [c.readVertex_extend a _ v rfl, c.pointReading_read,
      readGerm_ordPos, hv, hgh]
  have he :=
    c.readVertex_fibre_injective a hm.1 w _
      ((uOrderStep_end v r _).trans (c.pointReading_end a hc hm r h).symm)
      (hr.trans (c.pointReading_read a hc hm r h).symm)
  grind [uOrderStep_le]

end FiniteChains.Comb.OrdCocycle
