module

public import RequestProject.FoxCoordinateSubstitution

@[expose] public section

/-! Internal Fox coordinates of the actual simultaneous word substitution. -/
namespace FiniteChains.BlockFamily
universe u
variable {A Jr S : Type u} {I Z M : S → Type u}
  (ρ : Jr ⊕ S → FreeGroup A) (u : ∀ s, I s → FreeGroup A)
  (β : ∀ s, M s → FreeGroup (I s ⊕ Z s))

variable (s : S)

/-- The actual homomorphism from a marked block presentation to the substituted
group, obtained by substituting its markings and including its own generators. -/
def markedBlockHom : PresGroup (β s) →*
    PresGroup (substPresF ρ (fun s m => blockSubst u s (β s m))) :=
  QuotientGroup.lift _
    ((QuotientGroup.mk' (relSub (substPresF ρ (fun s m => blockSubst u s (β s m))))).comp
      ((FreeGroup.map (genEmb s)).comp (blockSubst u s))) (by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨m, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr
      (Subgroup.subset_normalClosure ⟨Sum.inr ⟨s, m⟩, rfl⟩))

@[simp] theorem markedBlockHom_mk (w : FreeGroup _) :
    markedBlockHom ρ u β s (QuotientGroup.mk w) =
      QuotientGroup.mk (FreeGroup.map (genEmb s) (blockSubst u s w)) := rfl

theorem markedBlockHom_coeff (x : FreeGroupRing _) :
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (quotRingHom ℤ (relSub (β s)) x) =
    quotRingHom ℤ (relSub _)
      (freeRingMap (genEmb s) (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x)) := by
  change MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub (β s))) x) =
    MonoidAlgebra.mapDomainRingHom ℤ
      (QuotientGroup.mk' _)
      (MonoidAlgebra.mapDomainRingHom ℤ (FreeGroup.map (genEmb s))
        (MonoidAlgebra.mapDomainRingHom ℤ (blockSubst u s) x))
  simp only [BlockMor.mapDomainRingHom_comp']
  rfl

variable [DecidableEq A] [DecidableEq S]
  [∀ s, DecidableEq (I s)] [∀ s, DecidableEq (Z s)]

/-- The internal column of the substituted presentation is precisely the block
column with its coefficients sent through the constructed block homomorphism. -/
theorem foxMatrix_markedBlock_internal (s : S) (z : Z s) (m : M s) :
    foxMatrixPres (substPresF ρ _)
      (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
    MonoidAlgebra.mapDomainRingHom ℤ (markedBlockHom ρ u β s)
      (foxMatrixPres (β s) (Sum.inr z) m) := by
  rw [foxMatrixPres, foxMatrixPres, markedBlockHom_coeff, substPresF_inr]
  change quotRingHom ℤ _
      (fox (genEmb s (Sum.inr z)) _) = _
  rw [fox_map (genEmb s) (genEmb_injective s), fox_blockSubst_internal]

end FiniteChains.BlockFamily
