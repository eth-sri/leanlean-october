import RequestProject.OrderCocycleCoverCoordinates
import RequestProject.CombCoveringLift
import RequestProject.CombPerfectOneFillings
import RequestProject.StrictNormalizedOneMaps


set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb.OrdCocycle
variable {P G : Type u} [PartialOrder P] [Group G] (c : OrdCocycle P G)

def coverBase (a : P) : c.Cover := ⟨a, 1⟩
def coverHom :=
  orderCxMap Cover.point c.coverProjection_isPosetCover.mono

theorem coverGerm_sheet e :
    (gSrcX (orderCx c.Cover) e).sheet *
        c.readGerm ((c.coverHom).onE e.1, e.2) =
      (gTgtX (orderCx c.Cover) e).sheet := by
  cases' e with e b
  cases b with
  | true => exact e.property.2
  | false =>
    change e.val.2.sheet * (c.val e.val.1.point e.val.2.point)⁻¹ = e.val.1.sheet
    rw [← e.property.2]
    simp

theorem coverPath_sheet {a b : c.Cover} {p}
    (hp : IsPathX (orderCx c.Cover) p a b) :
    a.sheet * c.readPath (mapPath c.coverHom p) = b.sheet := by
  induction p generalizing a with
  | nil => simp_all
  | cons e p ih =>
    cases' hp with ha hp
    change a.sheet * c.readPath ((c.coverHom.onE e.1, e.2) :: mapPath c.coverHom p) = _
    simp_all [readPath_cons, ← mul_assoc, ha, c.coverGerm_sheet]

theorem coverPi1_reading a g :
    c.monodromy a (pi1Map c.coverHom (c.coverBase a) g) = 1 := by
  induction g using Quotient.inductionOn with
  | h p =>
    have h := c.coverPath_sheet p.property
    aesop

/-- The fundamental group of the honest cocycle cover maps to the monodromy kernel. -/
def coverPi1KernelHom a :
    Pi1 (orderCx c.Cover) (c.coverBase a) →* (c.monodromy a).ker :=
  (pi1Map c.coverHom _).codRestrict _ (c.coverPi1_reading a)

theorem coverPi1KernelHom_injective a :
    Function.Injective (c.coverPi1KernelHom a) := by
  intro g h he
  exact pi1Map_injective_of_isCovering
    (isCovering_orderCxMap c.coverProjection_isPosetCover) _
      (congrArg Subtype.val he)

/-- Every kernel class lifts to an actual closed path, since its sheet reading is one. -/
theorem coverPi1KernelHom_surjective a :
    Function.Surjective (c.coverPi1KernelHom a) := by
  intro g
  cases' Quotient.exists_rep g.val with p hp
  change Pi1.mk p = g.val at hp
  have hread : c.readPath p.val = 1 := by
    aesop
  obtain ⟨m, b, hm, he⟩ := exists_liftPathAt
    (isCovering_orderCxMap c.coverProjection_isPosetCover)
    p.val (c.coverBase a) a p.property
  change mapPath c.coverHom m = p.val at he
  have hbpoint :=
    isPath_endpoint_eq (isPath_mapPath c.coverHom hm) (he.symm ▸ p.property)
  have hbsheet : b.sheet = 1 := by
    have h := c.coverPath_sheet hm
    simp_all [he, hread, coverBase, one_mul]
  have hb : b = c.coverBase a := by
    cases b <;> aesop
  refine ⟨Pi1.mk ⟨m, hb ▸ hm⟩, ?_⟩
  apply Subtype.ext
  change Pi1.mk ⟨mapPath c.coverHom m, _⟩ = g.val
  simp_all

noncomputable def coverPi1KernelEquiv a :=
  MulEquiv.ofBijective _
    ⟨c.coverPi1KernelHom_injective a, c.coverPi1KernelHom_surjective a⟩
