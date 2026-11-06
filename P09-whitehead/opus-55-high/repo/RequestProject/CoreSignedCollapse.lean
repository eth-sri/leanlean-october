import RequestProject.CoreCollapse
import RequestProject.FoxCoordinateSubstitution
import RequestProject.Tac


/-! The actual core-collapse map, including reversed orientations of surviving cells.
The only input describing the quotient is an equality of free-group words.  The
group map, signed cellular map and Hurewicz reflection are constructed below.
Written proof terms; not compiled in the current proof-first workflow. -/

noncomputable section
open scoped Classical

bwd

namespace FiniteChains.CoreSignedCollapse

variable {A B M J : Type}

/-- Collapse the core generators and retain each extra generator. -/
def dropCore : FreeGroup (A ⊕ B) →* FreeGroup B :=
  FreeGroup.lift (Sum.elim (fun _ => 1) FreeGroup.of)

@[simp] theorem dropCore_of_inl (a : A) :
    dropCore (B := B) (FreeGroup.of (Sum.inl a)) = 1 := by
  rfl

@[simp] theorem dropCore_of_inr (b : B) :
    dropCore (A := A) (FreeGroup.of (Sum.inr b)) = FreeGroup.of b := by
  rfl

@[simp] theorem dropCore_map_inl (w : FreeGroup A) :
    dropCore (B := B) (FreeGroup.map Sum.inl w) = 1 := by
  have h : (dropCore (A := A) (B := B)).comp (FreeGroup.map Sum.inl) = 1 := by
    apply FreeGroup.ext_hom
    intro a
    simp
  exact DFunLike.congr_fun h w


variable (core : M → FreeGroup A) (extra : J → FreeGroup (A ⊕ B))
  (target : J → FreeGroup B) (rev : J → Bool)
  (hword : ∀ j, dropCore (extra j) = if rev j then (target j)⁻¹ else target j)

/-- The collapse descends because every collapsed attaching word is a target
relator or its inverse. -/
def groupMap : PresGroup (corePres core extra) →* PresGroup target :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' _).comp dropCore) (by
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨m | j, rfl⟩
      · change (QuotientGroup.mk' _)
          (dropCore (FreeGroup.map Sum.inl (core m))) = 1
        simp
      · change (QuotientGroup.mk' _) (dropCore (extra j)) = 1
        have ht : (QuotientGroup.mk (target j) : PresGroup target) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr
            (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        aesop)

def coefficientMap :=
  MonoidAlgebra.mapDomainRingHom ℤ (groupMap core extra target rev hword)

theorem coefficientMap_quot (x : FreeGroupRing (A ⊕ B)) :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) x) =
    quotRingHom ℤ (relSub target)
      (MonoidAlgebra.mapDomainRingHom ℤ dropCore x) := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | single g n =>
      change MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n)) =
        MonoidAlgebra.mapDomain _ (MonoidAlgebra.mapDomain _ (MonoidAlgebra.single g n))
      aesop

variable [DecidableEq A] [DecidableEq B]

theorem coefficientMap_fox b w :
    coefficientMap core extra target rev hword
      (quotRingHom ℤ (relSub (corePres core extra)) (fox (Sum.inr b) w)) =
    quotRingHom ℤ (relSub target) (fox b (dropCore w)) := by
  rw [coefficientMap_quot]
  congr 1
  symm
  apply fox_subst_coordinate
  simp

theorem quotientFox_inv_relator b j :
    quotRingHom ℤ (relSub target) (fox b (target j)⁻¹) =
      -foxMatrixPres target b j := by
  have ht : (QuotientGroup.mk ((target j)⁻¹) : PresGroup target) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact inv_mem (Subgroup.subset_normalClosure ⟨j, rfl⟩)
  have hg : quotRingHom ℤ (relSub target) (grp (target j)⁻¹) = 1 := by
    change quotRingHom ℤ _ (MonoidAlgebra.single _ 1) = _
    rw [quotRingHom_single, ht]
    rfl
  rw [fox_inv, map_neg, map_mul, hg, one_mul]
  rfl

theorem matrix_core b m :
    foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inl m) = 0 := by
  change quotRingHom ℤ _ (fox (Sum.inr b) (FreeGroup.map Sum.inl (core m))) = 0
  rw [fox_map_of_not_mem_range Sum.inl (by simp), map_zero]

theorem matrix_extra b j :
    coefficientMap core extra target rev hword
      (foxMatrixPres (corePres core extra) (Sum.inr b) (Sum.inr j)) =
      if rev j then -foxMatrixPres target b j else foxMatrixPres target b j := by
  change coefficientMap core extra target rev hword
    (quotRingHom ℤ _ (fox (Sum.inr b) (extra j))) = _
  rw [coefficientMap_fox, hword j]
  cases h : rev j
  · rfl
  · exact quotientFox_inv_relator target b j

variable [Fintype M] [Fintype J]
