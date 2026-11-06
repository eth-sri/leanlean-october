module

public import RequestProject.BlockFamilyB1Finsupp
public import RequestProject.CrowellFinsupp
public import RequestProject.GenusSpineFactorComparison
public import RequestProject.GenusSpineSubstitutedBoundary
public import RequestProject.PrincipalCycleBaseChange
public import RequestProject.GenusNormalizedSpineReference

@[expose] public section

noncomputable section
open scoped Classical

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains

theorem fox_filling_wordHom {A B J : Type*} [Fintype A] [DecidableEq A]
    [DecidableEq B] [Fintype J] (σ : J → FreeGroup A)
    (N : Subgroup (FreeGroup B)) [N.Normal]
    (φ : FreeGroup A →* FreeGroup B) (ψ : PresGroup σ →* (FreeGroup B ⧸ N))
    (hψ : ∀ w, ψ (QuotientGroup.mk w) = QuotientGroup.mk (φ w))
    (c : J → MonoidAlgebra ℤ (PresGroup σ)) (w : FreeGroup A)
    (hc : ∀ i, ∑ j, c j * foxMatrixPres σ i j =
      quotRingHom ℤ (relSub σ) (fox i w)) (b : B) :
    (∑ j, MonoidAlgebra.mapDomainRingHom ℤ ψ (c j) *
      quotRingHom ℤ N (fox b (φ (σ j)))) = quotRingHom ℤ N (fox b (φ w)) := by
  let C := MonoidAlgebra.mapDomainRingHom ℤ ψ
  have hchain (u : FreeGroup A) : fox b (φ u) = ∑ i : A,
      MonoidAlgebra.mapDomainRingHom ℤ φ (fox i u) * fox b (φ (FreeGroup.of i)) := by
    induction u using FreeGroup.induction_on with
    | one => simp
    | of j => simp [fox_of]
    | inv_of j ih =>
        rw [map_inv, fox_inv, ih]
        simp only [fox_inv, map_neg, map_mul, groupRingMap_grp, Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [map_inv]; simp only [neg_mul, mul_assoc]
    | mul v w hv hw =>
        rw [map_mul, fox_mul, hv, hw]
        simp only [fox_mul, map_add, map_mul, groupRingMap_grp, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
        exact congrArg (_ + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
  have hfox (v : FreeGroup A) : quotRingHom ℤ N (fox b (φ v)) =
      ∑ i : A, C (quotRingHom ℤ (relSub σ) (fox i v)) *
        quotRingHom ℤ N (fox b (φ (FreeGroup.of i))) := by
    rw [hchain, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul]
    congr 1
    change (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' N)
      (MonoidAlgebra.mapDomainRingHom ℤ φ (fox i v))) =
      MonoidAlgebra.mapDomainRingHom ℤ ψ
        (MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' (relSub σ)) (fox i v))
    have hh : ψ.comp (QuotientGroup.mk' (relSub σ)) = (QuotientGroup.mk' N).comp φ := MonoidHom.ext hψ
    rw [BlockMor.mapDomainRingHom_comp', BlockMor.mapDomainRingHom_comp', hh]
  rw [hfox w]
  simp_rw [hfox (σ _), Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  simpa only [map_mul, map_sum, MonoidHom.comp_apply, C, foxMatrixPres] using congrArg C (hc i)

end FiniteChains

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel BlockFamily

def markedSpineSurfaceWord (n : ℕ) [NeZero n] : FreeGroup (MarkedSpineGen n) :=
  commWord (fun x : Fin n × Bool => FreeGroup.of (Sum.inl x)) (finitePairs n)

def markedSpineFilling (n : ℕ) [NeZero n] :
    NamedSpineRel n →₀ MonoidAlgebra ℤ (PresGroup (markedSpineBeta n)) :=
  normalizedMarkedSpineFilling n (normalizedSpineReference n)

@[simp] theorem markedSpineFilling_named_coeff (n : ℕ) [NeZero n] (m : NamedSpineRel n) :
    markedSpineFilling n m =
      MonoidAlgebra.mapDomainRingHom ℤ (spineReorderHom n)
        (normalizedNamedSpineVector n (normalizedSpineReference n) m) :=
  normalizedMarkedSpineFilling_apply n (normalizedSpineReference n) m

variable {α Jr Sx : Type} (ρ : Jr ⊕ Sx → FreeGroup α)
  (q : Sx → ℕ) [∀ s, NeZero (q s)]
  (u : ∀ s, Fin (q s) × Bool → FreeGroup α)
  (hrho : ∀ s, ρ (Sum.inr s) = commWord (u s) (finitePairs (q s)))

def finiteSpineIndividualMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      IndividualGroup ρ (familyFiniteSpineWordBlock q u) s :=
  markedBlockHom (oneRel ρ s) (fun _ : PUnit.{1} => u s)
    (fun _ : PUnit.{1} => markedSpineBeta (q s)) PUnit.unit

def finiteSpineFamilyMarkedHom (s : Sx) :
    PresGroup (markedSpineBeta (q s)) →*
      PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u)) :=
  markedBlockHom ρ u (fun s => markedSpineBeta (q s)) s

def finiteSpineIndividualFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s))
    (map_zero _)

def finiteSpineFamilyFilling (s : Sx) : NamedSpineRel (q s) →₀
    MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))) :=
  (markedSpineFilling (q s)).mapRange
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s))
    (map_zero _)

include hrho in
theorem finiteSpineFamilyFilling_isFilling :
    IsFillingFS ρ (familyFiniteSpineWordBlock q u)
      (familyFiniteSpineWordBlock_filled ρ q u hrho)
      (finiteSpineFamilyFilling ρ q u) := by
  have hsurf (s : Sx) :
      FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)
        (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s
          (markedSpineSurfaceWord (q s))) =
      FreeGroup.map (Sum.inl (β := Σ s, SpinePresentationGen (q s))) (ρ (Sum.inr s)) := by
    have hm : (FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
        (FreeGroup.map (Sum.inl (β := SpinePresentationGen (q s)))) =
        FreeGroup.map (Sum.inl (α := α) (β := Σ s, SpinePresentationGen (q s))) :=
      FreeGroup.ext_hom _ _ (by simp)
    rw [markedSpineSurfaceWord, map_commWord, map_commWord]
    simp only [blockSubst_of_inl]
    simp_rw [← MonoidHom.comp_apply, hm]
    rw [← map_commWord, hrho s]
  have hboundary (s : Sx) (i : α ⊕ (Σ s, SpinePresentationGen (q s))) :=
    fox_filling_wordHom (markedSpineBeta (q s))
      (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      ((FreeGroup.map (genEmb (Zt := fun s => SpinePresentationGen (q s)) s)).comp
        (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s))
      (finiteSpineFamilyMarkedHom ρ q u s) (fun _ => rfl)
      (markedSpineFilling (q s)) (markedSpineSurfaceWord (q s))
      (normalizedMarkedSpineFilling_boundary (q s) (normalizedSpineReference (q s))
        (normalizedSpineReference_boundary (q s))) i
  refine isFillingFS_of_finite_blocks _ _ _ _ (fun s i => ?_) (fun s z => ?_)
  · have h := hboundary s (Sum.inl i)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inl i) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inl i)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rwa [hsurf s, fox_map Sum.inl Sum.inl_injective, ← coeffF_quotRingHom ρ
      (familyFiniteSpineWordBlock q u) (familyFiniteSpineWordBlock_filled ρ q u hrho)] at h
  · have h := hboundary s (Sum.inr ⟨s, z⟩)
    change (∑ m, finiteSpineFamilyFilling ρ q u s m *
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩)) =
      quotRingHom ℤ _ (fox (Sum.inr ⟨s, z⟩)
        (FreeGroup.map (genEmb s) (blockSubst u s (markedSpineSurfaceWord (q s))))) at h
    rwa [hsurf s, fox_map_of_not_mem_range Sum.inl (fun _ => Sum.inr_ne_inl), map_zero] at h

def FiniteSpineIndividualB2 : Prop :=
  ∀ (s : Sx) (v : NamedSpineRel (q s) →
    MonoidAlgebra ℤ (IndividualGroup ρ (familyFiniteSpineWordBlock q u) s)),
    (∀ z : SpinePresentationGen (q s), ∑ m, v m *
      foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) = 0) →
    ∃ r, ∀ m, v m = r * finiteSpineIndividualFilling ρ q u s m

include hrho in
theorem finiteSpineFamily_fsGenerates (hB2 : FiniteSpineIndividualB2 ρ q u)
    (x : (Jr ⊕ (Σ s, NamedSpineRel (q s))) →₀
      MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
    (hx : coverSecondBoundary (relSub (substPresF ρ (familyFiniteSpineWordBlock q u)))
      (substPresF ρ (familyFiniteSpineWordBlock q u)) x = 0) :
    x ∈ Submodule.span
      (MonoidAlgebra ℤ (PresGroup (substPresF ρ (familyFiniteSpineWordBlock q u))))
      {v | ∃ y : (Jr ⊕ Sx) →₀ MonoidAlgebra ℤ (PresGroup ρ),
        coverSecondBoundary (relSub ρ) ρ y = 0 ∧
        v = fsCellsF ρ (familyFiniteSpineWordBlock q u)
          (familyFiniteSpineWordBlock_filled ρ q u hrho)
          (finiteSpineFamilyFilling ρ q u) y} := by
  have hmarked (s : Sx) : (finiteSpineFactorToFamily ρ q u hrho s).comp
      (finiteSpineIndividualMarkedHom ρ q u s) = finiteSpineFamilyMarkedHom ρ q u s := by
    apply MonoidHom.ext; intro y
    induction y using QuotientGroup.induction_on with | _ w =>
    change QuotientGroup.mk (FreeGroup.map
      (individualGenEmb (α := α) (Zt := fun s => SpinePresentationGen (q s)) s)
      (FreeGroup.map (genEmb (Zt := fun _ : PUnit.{1} => SpinePresentationGen (q s))
        PUnit.unit) (blockSubst (Zt := fun s => SpinePresentationGen (q s)) u s w))) = _
    rw [individualGenEmb_block]; rfl
  refine fsGenerates_familySubst ρ (familyFiniteSpineWordBlock q u)
    (familyFiniteSpineWordBlock_filled ρ q u hrho) (finiteSpineFamilyFilling ρ q u)
    (finiteSpineFamilyFilling_isFilling ρ q u hrho)
    (blockSurfaceGeneratesFS_of_finite_blocks _ _ _ fun s v hv => ?_)
    (familyFiniteSpineWordBlock_injective ρ q u hrho) x hx
  have hint (z : SpinePresentationGen (q s)) (m : NamedSpineRel (q s)) :
      foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
      finiteSpineFactorRingHom ρ q u hrho s
        (foxMatrixPres (substPresF (oneRel ρ s)
          (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
          (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩)) := by
    have hf : foxMatrixPres (substPresF ρ (familyFiniteSpineWordBlock q u))
        (Sum.inr ⟨s, z⟩) (Sum.inr ⟨s, m⟩) =
        MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFamilyMarkedHom ρ q u s)
          (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
      convert foxMatrix_markedBlock_internal ρ u (fun t => markedSpineBeta (q t)) s z m using 1 <;> rfl
    have hi : foxMatrixPres (substPresF (oneRel ρ s)
        (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
        (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩) =
        MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
          (foxMatrixPres (markedSpineBeta (q s)) (Sum.inr z) m) := by
      convert foxMatrix_markedBlock_internal (oneRel ρ s)
          (fun _ : PUnit.{1} => u s) (fun _ : PUnit.{1} => markedSpineBeta (q s))
          PUnit.unit z m using 1 <;> rfl
    rw [hf, hi]
    change _ = MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
      (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s) _)
    rw [BlockMor.mapDomainRingHom_comp', hmarked]
  obtain ⟨r, hr⟩ := principal_cycles_baseChange
    (finiteSpineFactorToFamily ρ q u hrho s)
    (finiteSpineFactorToFamily_injective ρ q u hrho s)
    (fun z m => foxMatrixPres (substPresF (oneRel ρ s)
      (fun _ : PUnit.{1} => familyFiniteSpineWordBlock q u s))
      (Sum.inr ⟨PUnit.unit, z⟩) (Sum.inr ⟨PUnit.unit, m⟩))
    (finiteSpineIndividualFilling ρ q u s) (hB2 s) v
    (fun z => by simpa only [hint, finiteSpineFactorRingHom] using hv z)
  refine ⟨r, fun m => (hr m).trans ?_⟩
  congr 1
  change MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineFactorToFamily ρ q u hrho s)
    (MonoidAlgebra.mapDomainRingHom ℤ (finiteSpineIndividualMarkedHom ρ q u s)
      (markedSpineFilling (q s) m)) = _
  rw [BlockMor.mapDomainRingHom_comp', hmarked]; rfl
