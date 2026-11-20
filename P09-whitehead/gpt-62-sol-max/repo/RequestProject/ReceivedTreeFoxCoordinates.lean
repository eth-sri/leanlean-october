module

public import RequestProject.ReceivedTreeCover
public import RequestProject.FinsuppBasis
public import RequestProject.FoxWordBoundary

public import RequestProject.GroupCellChainCoordinates
public import RequestProject.FoxVoltage
public import RequestProject.MonoidAlgebraMapDomain

@[expose] public section

/-! Fox coordinates of the actual cover over the receiving group. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.ReceivedTree
open SpanningTree
open scoped Classical
universe u
variable {G : Type u}

/-- Read one cell coordinate while retaining its full group-ring coefficient. -/
noncomputable def cellCoefficient {E : Type u} (e : E) :
    ((G × E) →₀ ℤ) →ₗ[ℤ] MonoidAlgebra ℤ G :=
  (Finsupp.lapply e).comp groupCellChainEquiv.toLinearMap

theorem cellCoefficient_single {E : Type u} (e : E) (g : G) (j : E) (n : ℤ) :
    cellCoefficient e (Finsupp.single (g, j) n) =
      if j = e then MonoidAlgebra.single g n else 0 := by
  change groupCellChainEquiv (Finsupp.single (g, j) n) e = _
  rw [groupCellChainEquiv_single, Finsupp.single_apply]

theorem cellCoefficient_apply {E : Type u} (e : E) (c : (G × E) →₀ ℤ) (g : G) :
    (cellCoefficient e c).coeff g = c (g, e) := groupCellChainEquiv_apply c e g

/-- Assemble arbitrary group-ring coefficients into the actual finite cell chain. -/
noncomputable def cellCoordinates (E : Type u) [Fintype E] :
    ((G × E) →₀ ℤ) ≃ₗ[ℤ] (E → MonoidAlgebra ℤ G) :=
  groupCellChainEquiv.trans (Finsupp.linearEquivFunOnFinite _ _ _)

theorem cellCoordinates_apply (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) (g : G) :
    (cellCoordinates E c e).coeff g = c (g, e) := groupCellChainEquiv_apply c e g

theorem cellCoefficient_eq_coordinates (E : Type u) [Fintype E]
    (c : (G × E) →₀ ℤ) (e : E) :
    cellCoefficient e c = cellCoordinates E c e := rfl

theorem cellCoefficient_coordinates_symm (E : Type u) [Fintype E]
    (v : E → MonoidAlgebra ℤ G) (e : E) :
    cellCoefficient e ((cellCoordinates E).symm v) = v e := by
  rw [cellCoefficient_eq_coordinates, LinearEquiv.apply_symm_apply]

variable [Group G]

variable {K : Complex2.{u}} (T : SpanningTree K)
  (φ : PresGroup (treeRel T) →* G)

noncomputable def coefficientMap : FreeGroupRing (NonTree T) →+* MonoidAlgebra ℤ G :=
  (MonoidAlgebra.mapDomainRingHom ℤ φ).comp (quotRingHom ℤ (relSub (treeRel T)))

theorem coefficientMap_grp (w : FreeGroup (NonTree T)) :
    coefficientMap T φ (grp w) = MonoidAlgebra.single (φ (QuotientGroup.mk w)) 1 := by
  change MonoidAlgebra.mapDomain φ
    (quotRingHom ℤ (relSub (treeRel T)) (MonoidAlgebra.single w 1)) = _
  rw [quotRingHom_single, MonoidAlgebra.mapDomain_single]

variable [DecidableEq (NonTree T)]

/-- The signed contribution of one genuinely lifted oriented edge. -/
theorem cellCoefficient_liftGerm (i : NonTree T) (g : G) (e : K.E × Bool) :
    cellCoefficient (G := G) i.1 (pathChain [liftGerm T φ g e]) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (germWord T e)) := by
  classical
  obtain ⟨e, b⟩ := e
  by_cases ht : T.isTree e
  · have hne : e ≠ i.1 := fun h => i.2 (h ▸ ht)
    cases b <;>
      simp [PathVoltage.liftGerm, germWord, ht, pathChain, cellCoefficient_single, hne]
  · by_cases hi : e = i.1
    · subst e
      cases b <;>
        simp [PathVoltage.liftGerm, TreeVoltage.germ, freeReceiver, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, coefficientMap_grp, MonoidAlgebra.single_mul_single]
    · have hni : i ≠ (⟨e, ht⟩ : NonTree T) := fun h => hi (congrArg Subtype.val h).symm
      cases b <;>
        simp [PathVoltage.liftGerm, germWord, ht, pathChain, cellCoefficient_single,
          fox_inv, hni, hi]

/-- The whole lifted marked path has the translated Fox coefficient of its
actual tree word. No quotient of G or augmentation is taken. -/
theorem cellCoefficient_liftPath (i : NonTree T) (g : G) (p : List (K.E × Bool)) :
    cellCoefficient (G := G) i.1 (pathChain (liftPath T φ p g)) =
      MonoidAlgebra.single g 1 * coefficientMap T φ (fox i (pathWord T p)) := by
  have hc (x : FreeGroupRing (NonTree T)) : coefficientMap T φ x =
      MonoidAlgebra.mapDomainRingHom ℤ (freeReceiver T φ) x :=
    MonoidAlgebra.mapDomainRingHom_apply_comp _ _ _
  rw [hc]
  exact PathVoltage.liftPath_fox (freeReceiver T φ) (germWord T)
    (cellCoefficient i.1) i (fun g e => by rw [← hc]; exact cellCoefficient_liftGerm T φ i g e) p g

variable [Fintype K.F]

/-- The actual cellular two-boundary has exactly the received Fox coordinates. -/
theorem cellCoefficient_bdry2 (i : NonTree T) (c : (G × K.F) →₀ ℤ) :
    cellCoefficient (G := G) i.1 (bdry2 (cover T φ) c) =
      ∑ t : K.F, cellCoefficient t c * coefficientMap T φ (fox i (treeRel T t)) := by
  classical
  finsupp_basis c
  intro x
  obtain ⟨g, t⟩ := x
  rw [bdry2_single, map_smul]
  change 1 • cellCoefficient (G := G) i.1 (pathChain (liftPath T φ (K.att t) g)) = _
  rw [cellCoefficient_liftPath]
  rw [← smul_mul_assoc, MonoidAlgebra.smul_single]
  simp [cellCoefficient_single, treeRel]

end FiniteChains.Comb.ReceivedTree
