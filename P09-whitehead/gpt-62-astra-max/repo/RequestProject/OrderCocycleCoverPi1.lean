module

public import RequestProject.OrderCocycleCoverCoordinates
public import RequestProject.CombPerfectOneFillings
public import RequestProject.StrictNormalizedOneMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
universe u
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

def coverBase (a : P) : c.Cover := ⟨a, 1⟩
def coverHom :=
  orderCxMap Cover.point c.coverProjection_isPosetCover.mono

theorem coverGerm_sheet (e : (orderCx c.Cover).E × Bool) :
    (germSrc (orderCx c.Cover).src (orderCx c.Cover).tgt e).sheet *
        c.readGerm ((c.coverHom).onE e.1, e.2) =
      (germTgt (orderCx c.Cover).src (orderCx c.Cover).tgt e).sheet := by
  obtain ⟨e, b⟩ := e
  cases b with
  | true => exact e.property.2
  | false =>
    change e.val.2.sheet * (c.val e.val.1.point e.val.2.point)⁻¹ = e.val.1.sheet
    rw [← e.property.2] <;> simp_all

theorem coverPath_sheet {a b : c.Cover} {p : List _}
    (hp : IsPath (orderCx c.Cover).src (orderCx c.Cover).tgt p a b) :
    a.sheet * c.readPath (mapPath c.coverHom p) = b.sheet := by
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih =>
    obtain ⟨ha, hp⟩ := hp
    change a.sheet * c.readPath (((c.coverHom).onE e.1, e.2) :: mapPath c.coverHom p) = _
    rw [readPath_cons, ← mul_assoc, ha, c.coverGerm_sheet] <;> simp_all

variable (a : P)

theorem coverPi1_reading (g : Pi1 (orderCx c.Cover) _) :
    c.monodromy a (pi1Map c.coverHom (c.coverBase a) g) = 1 := by
  induction g using Quotient.inductionOn with
  | h p =>
    have h := c.coverPath_sheet p.property
    aesop

/-- The fundamental group of the honest cocycle cover maps to the monodromy kernel. -/
def coverPi1KernelHom :
    Pi1 (orderCx c.Cover) (c.coverBase a) →* (c.monodromy a).ker :=
  (pi1Map c.coverHom _).codRestrict _ (c.coverPi1_reading a)

theorem coverPi1KernelHom_injective :
    Function.Injective (c.coverPi1KernelHom a) := by
  intro g h he
  exact pi1Map_injective_of_isCovering
    (isCovering_orderCxMap c.coverProjection_isPosetCover) _
      (congrArg Subtype.val he)

/-- Every kernel class lifts to an actual closed path, since its sheet reading is one. -/
theorem coverPi1KernelHom_surjective :
    Function.Surjective (c.coverPi1KernelHom a) := by
  intro g
  obtain ⟨p, hp⟩ := Quotient.exists_rep g.val
  change Pi1.mk p = g.val at hp
  have hread : c.readPath p.val = 1 := by
    aesop
  obtain ⟨m, b, hm, he⟩ := exists_liftPathAt
    (isCovering_orderCxMap c.coverProjection_isPosetCover).lifts
    p.val (c.coverBase a) a p.property
  change mapPath c.coverHom m = p.val at he
  have hbpoint :=
    isPath_endpoint_eq (isPath_mapPath c.coverHom hm) (he.symm ▸ p.property)
  have hbsheet : b.sheet = 1 := by
    have h := c.coverPath_sheet hm
    simp_all [he, hread, coverBase, one_mul]
  have hb : b = c.coverBase a := by
    cases b with
    | mk bp bg => aesop
  refine ⟨Pi1.mk ⟨m, hb ▸ hm⟩, ?_⟩
  apply Subtype.ext
  change Pi1.mk _ = g.val
  simp_all

noncomputable def coverPi1KernelEquiv :=
  MulEquiv.ofBijective _
    ⟨c.coverPi1KernelHom_injective a, c.coverPi1KernelHom_surjective a⟩

end FiniteChains.Comb.OrdCocycle
