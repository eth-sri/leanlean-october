module

public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticRayClassFieldReciprocity
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldContainment
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FullConductorRayClassField
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayFrobeniusRigidity
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassPrimeIdele
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassSubgroupPrimeArtin
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsRayCongruent
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsAbelianConductor
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.NarrowRayClassModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayPrincipalIdealSubgroup
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassGroup
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.IsUnramifiedOutsideModulus
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassSubgroupRealization
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.MathlibFrobeniusHilbertComparison
public import Mathlib.Data.Finsupp.Order

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Conductors and ray class fields implementation

This module supplies the implementation proofs for the compact conductor and
ray-class-field statements in the parent `Theorems` directory.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory.GlobalClassFieldComparison

universe u

/-- Interpret a public ray modulus in the existing idèle-theoretic ray-class
library, preserving both its finite exponents and selected real places. -/
def rayClassModulusToOriginal
    (K : Type u) [Field K] [NumberField K]
    (m : RayClassModulus K) : RayClass.Modulus K where
  finitePart := m.finitePart
  infinitePart := m.infinitePart

/-- At a real place, positivity of a principal idele component is exactly
positivity of its field generator under the corresponding real embedding. -/
private theorem principalIdele_mem_infinitePositiveSubgroup_iff
    (K : Type u) [Field K] [NumberField K] (x : Kˣ)
    (v : {v : InfinitePlace K // v.IsReal}) :
    IdeleGroup.infiniteComponent v.1 (IdeleGroup.principalIdele K x) ∈
        RayClass.infinitePositiveSubgroup v.1 ↔
      0 < v.1.embedding_of_isReal v.2 (x : K) := by
  rw [RayClass.mem_infinitePositiveSubgroup_iff]
  have hcoe (hv : v.1.IsReal) :
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
          ((IdeleGroup.infiniteComponent v.1
              (IdeleGroup.principalIdele K x) : v.1.Completionˣ) :
            v.1.Completion) =
        v.1.embedding_of_isReal hv (x : K) := by
    rw [IdeleGroup.infiniteComponent_principalIdele,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
    rfl
  constructor
  · intro h
    simpa only [hcoe] using h v.2
  · intro h hv
    simpa only [hcoe] using h

section

variable (K : Type u) [Field K] [NumberField K] (m : RayClassModulus K)

/-- A principal idèle satisfies the existing prime-to-modulus condition
exactly when its generator satisfies the public ray congruence. -/
theorem principalIdele_mem_primeTo_iff_isRayCongruent (x : Kˣ) :
    IdeleGroup.principalIdele K x ∈
        RayClass.idelePrimeToModulusSubgroup
          (rayClassModulusToOriginal K m) ↔
      IsRayCongruent m x := by
  have hinfinite :
      (IdeleGroup.principalIdele K x).1 ∈
          (rayClassModulusToOriginal K m).infiniteCongruenceSubgroup ↔
        ∀ v : RayClassRealPlace K, v ∈ m.infinitePart →
          0 < v.1.embedding_of_isReal v.2 (x : K) := by
    rw [RayClass.Modulus.mem_infiniteCongruenceSubgroup_iff]
    exact ⟨fun h v hv =>
      (principalIdele_mem_infinitePositiveSubgroup_iff K x v).mp (h v hv),
      fun h v hv =>
        (principalIdele_mem_infinitePositiveSubgroup_iff K x v).mpr (h v hv)⟩
  have hfinite :
      (IdeleGroup.principalIdele K x).2 ∈
          RayClass.finitePrimeToModulusSubgroup
            (rayClassModulusToOriginal K m) ↔
        ∀ v, v ∈ m.finitePart.support →
          finitePlaceUnitEmbedding v x ∈
            rayLocalHigherUnitGroup v (m.finitePart v) := by
    constructor
    · intro h v hv
      have h' := h v hv
      change finitePlaceUnitEmbedding v x ∈
        rayLocalHigherUnitGroup v (m.finitePart v) at h'
      exact h'
    · intro h v hv
      have h' := h v hv
      change (IdeleGroup.principalIdele K x).2 v ∈
        RayClass.localHigherUnitGroup v (m.finitePart v) at h'
      exact h'
  exact ⟨fun h => ⟨hfinite.mp h.2, hinfinite.mp h.1⟩,
    fun h => ⟨hinfinite.mpr h.2, hfinite.mpr h.1⟩⟩

/-- The public ray-principal subgroup equals the existing ideal-theoretic
ray-principal subgroup for every finite and infinite modulus. -/
theorem rayPrincipalIdealSubgroup_eq :
    rayPrincipalIdealSubgroupInPrimeTo m =
      RayClass.principalRayIdealSubgroup
        (rayClassModulusToOriginal K m) := by
  classical
  let m' := rayClassModulusToOriginal K m
  let P := rayClassPrimeToIdeals m
  let T :=
    Subgroup.map P.subtype (RayClass.principalRayIdealSubgroup m')
  have hCarrier :
      {I : NumberFieldFractionalIdealGroup K |
        ∃ x : Kˣ,
          IsRayCongruent m x ∧
            toPrincipalIdeal (𝓞 K) K x = I} = T := by
    ext I
    constructor
    · rintro ⟨x, hx, hIx⟩
      have hi :=
        (principalIdele_mem_primeTo_iff_isRayCongruent K m x).2 hx
      have hI : I ∈ P := by
        rw [← hIx, ← IdeleGroup.fractionalIdeal_principalIdele]
        exact RayClass.fractionalIdeal_mem_primeToModulusIdeals
          m' (IdeleGroup.principalIdele K x) hi
      let J : P := ⟨I, hI⟩
      exact ⟨J, ((RayClass.mem_principalRayIdealSubgroup_iff m' J).2
        ⟨x, hi, hIx⟩), rfl⟩
    · rintro ⟨J, hJ, hIJ⟩
      obtain ⟨x, hx, hEq⟩ :=
        (RayClass.mem_principalRayIdealSubgroup_iff m' J).1 hJ
      exact ⟨x,
        (principalIdele_mem_primeTo_iff_isRayCongruent K m x).1 hx,
        hEq.trans hIJ⟩
  have hUnrestricted : rayPrincipalIdealSubgroup m = T := by
    unfold rayPrincipalIdealSubgroup
    rw [hCarrier, Subgroup.closure_eq]
  apply Subgroup.ext
  intro I
  change (I : NumberFieldFractionalIdealGroup K) ∈
      rayPrincipalIdealSubgroup m ↔
    I ∈ RayClass.principalRayIdealSubgroup m'
  rw [hUnrestricted]
  constructor
  · rintro ⟨J, hJ, hIJ⟩
    exact (Subtype.ext hIJ) ▸ hJ
  · intro hI
    exact ⟨I, hI, rfl⟩

/-- The public ideal-theoretic ray class group is the existing ideal ray
class group for the same modulus. -/
noncomputable def rayClassGroupEquivOriginal :
    RayClassGroup m ≃*
      RayClass.IdealRayClassGroup (rayClassModulusToOriginal K m) := by
  let G := RayClass.primeToModulusIdeals (rayClassModulusToOriginal K m)
  let M := rayPrincipalIdealSubgroupInPrimeTo m
  let N :=
    RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m)
  let hComm : IsMulCommutative G :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (mul_comm a.1 b.1))
  exact @QuotientGroup.quotientMulEquivOfEq G _ M N (@Subgroup.normal_of_isMulCommutative G _ hComm M) (@Subgroup.normal_of_isMulCommutative G _ hComm N) (rayPrincipalIdealSubgroup_eq K m)

/-- The comparison preserves the class of each prime away from the
modulus. -/
theorem rayClassGroupEquivOriginal_prime
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv) =
      QuotientGroup.mk'
        (RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m))
        (RayClass.primeToModulusIdeal
          (rayClassModulusToOriginal K m) v hv) := by
  let G := RayClass.primeToModulusIdeals (rayClassModulusToOriginal K m)
  let M := rayPrincipalIdealSubgroupInPrimeTo m
  let N :=
    RayClass.principalRayIdealSubgroup (rayClassModulusToOriginal K m)
  let hComm : IsMulCommutative G :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (mul_comm a.1 b.1))
  rfl

/-- Compare the public ideal ray class group directly with the original
idèle-class ray class group.  This is the composite of the ideal comparison
above and the original idelic-to-ideal equivalence. -/
noncomputable def rayClassGroupEquivOriginalIdele :
    RayClassGroup m ≃*
      RayClass.RayClassGroup (rayClassModulusToOriginal K m) :=
  (rayClassGroupEquivOriginal K m).trans
    (RayClass.rayClassGroupEquivIdealRayClassGroup
      (rayClassModulusToOriginal K m)).symm

/-- A public prime ray class corresponds to the original normalized prime
idèle class, with the same finite and infinite modulus. -/
theorem rayClassGroupEquivOriginalIdele_prime
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    rayClassGroupEquivOriginalIdele K m (rayClassOfFinitePrime m v hv) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup (rayClassModulusToOriginal K m))
        (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
          (IdeleGroup.finitePrimeIdele v)) := by
  let m' := rayClassModulusToOriginal K m
  have hv' := hv
  let a : RayClass.idelePrimeToModulusSubgroup m' :=
    ⟨IdeleGroup.finitePrimeIdele v,
      GlobalClassFieldTheory.GlobalClassFields.finitePrimeIdele_mem_idelePrimeToModulusSubgroup
        m' v hv'⟩
  let e := RayClass.rayClassGroupEquivIdealRayClassGroup m'
  apply e.injective
  calc
    _ =
        rayClassGroupEquivOriginal K m (rayClassOfFinitePrime m v hv) := by
      exact e.apply_symm_apply _
    _ = QuotientGroup.mk'
          (RayClass.principalRayIdealSubgroup m')
          (RayClass.primeToModulusIdeal m' v hv) :=
      rayClassGroupEquivOriginal_prime K m v hv
    _ = RayClass.idealRayProjection m' a := by
      exact (GlobalClassFieldTheory.GlobalClassFields.idealRayProjection_finitePrimeIdele
        m' v hv').symm
    _ = e (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m')
          (QuotientGroup.mk' (IdeleGroup.principalSubgroup K) a)) := (GlobalClassFieldTheory.GlobalClassFields.rayClassGroupEquivIdealRayClassGroup_mk_primeTo
        m' a).symm

end

/-- Any finite abelian extension whose norm group contains the ray
congruence subgroup is unramified outside that modulus. -/
theorem unramifiedOutsideModulus_of_definingModulus
    (K E : Type) [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E]
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (m : RayClassModulus K)
    (hm : RayClass.Modulus.congruenceSubgroup
        (rayClassModulusToOriginal K m) ≤
          (_root_.ideleClassNorm K E).range) :
    IsUnramifiedOutsideModulus K E m := by
  classical
  let m' := rayClassModulusToOriginal K m
  let H :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
      (K := K) (L := E)
  have hDefining : GlobalClassFieldTheory.GlobalClassFields.IsDefiningModulus H.1 m' := by
    change m'.congruenceSubgroup ≤ (_root_.ideleClassNorm K E).range
    exact hm
  have hfinite := H.narrowFiniteConductor_le hDefining
  have hinfinite := H.fullConductorInfinitePart_subset_of_isDefiningModulus hDefining
  have hfiniteSupport :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_narrowFiniteConductor_support_eq_ramifiedBaseFinitePlaces
      (K := K) (L := E)
  have hinfiniteSupport :=
    GlobalClassFieldTheory.GlobalClassFields.ideleClassNormFullConductor_infinitePart_eq_realRamificationLocus
      (K := K) (L := E)
  constructor
  · intro v hv Q hQ hlie
    by_contra hram
    have hQne : Q ≠ ⊥ := by
      intro hbot
      have hunder := hlie.over
      rw [hbot, Ideal.under_bot] at hunder
      exact v.ne_bot hunder
    let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQ, hQne⟩
    have hvram : v ∈ _root_.ramifiedBaseFinitePlaces (K := K) (L := E) := by
      rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
      exact ⟨w, hlie, hram⟩
    have hvcond : v ∈
        (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormNarrowFiniteConductor
          (K := K) (L := E)).support := by
      rw [hfiniteSupport]
      exact hvram
    apply hv
    change v ∈ m'.finitePart.support
    exact (Finsupp.support_mono hfinite) hvcond
  · intro v hv hnot
    by_contra hram
    have hvcond : (⟨v, hv⟩ : RayClass.RealPlace K) ∈
        H.fullConductorInfinitePart := by
      change (⟨v, hv⟩ : RayClass.RealPlace K) ∈ H.fullConductor.infinitePart
      rw [hinfiniteSupport]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hram⟩
    exact hnot (hinfinite hvcond)

/-- Build the public Frobenius-normalized realization attached to a ray-class subgroup. -/
theorem rayClassSubgroup_existence
    (K : Type) [Field K] [NumberField K]
    (m : RayClassModulus K) (H : Subgroup (RayClassGroup m)) :
    Nonempty (RayClassSubgroupRealization K m H) := by
  let m' := rayClassModulusToOriginal K m
  let e := rayClassGroupEquivOriginalIdele K m
  let H' := H.map e.toMonoidHom
  let E :=
    GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubextension
       m' H'
  let artin :=
    (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
       m' H').comp e.toMonoidHom
  let hram :=
    unramifiedOutsideModulus_of_definingModulus K E m
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupSubextension_norm_range
         m' H')
  refine ⟨{
    extension := E
    unramifiedOutsideModulus := hram
    artin := artin
    artin_surjective := ?_
    artin_ker := ?_
    artin_frobenius := ?_
  }⟩
  · exact
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_surjective
         m' H').comp e.surjective
  · ext x
    change e x ∈
      (GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
         m' H').ker ↔ x ∈ H
    rw [GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_ker]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact (e.injective hxy) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  · intro v hv w hw
    calc
      _ =
          GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
             m' H'
            (QuotientGroup.mk' m'.congruenceSubgroup
              (QuotientGroup.mk' (IdeleGroup.principalSubgroup K)
                (IdeleGroup.finitePrimeIdele v))) := by
        change GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin
           m' H'
          (e (rayClassOfFinitePrime m v hv)) = _
        rw [rayClassGroupEquivOriginalIdele_prime K m v hv]
      _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
              v :=
        GlobalClassFieldTheory.GlobalClassFields.rayClassSubgroupArtin_finitePrimeIdele
           m' H' v
      _ = arithmeticFrobeniusAt w :=
        arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
            v w hw (hram.1 v hv w.asIdeal inferInstance hw)

end ClassFieldTheory.GlobalClassFieldComparison

namespace ClassFieldTheory

/-- The concrete full norm conductor is the least public modulus whose ray
class field contains the finite abelian extension. This implementation theorem
uses the original idelic full conductor in its statement. -/
theorem normFullConductor_isAbelianConductor
    (K : Type) [Field K] [NumberField K]
    (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsAbelianGalois K L] :
    IsAbelianConductor K L
      { finitePart :=
          (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
            (K := K) (L := L)).fullConductor.finitePart
        infinitePart :=
          (GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
            (K := K) (L := L)).fullConductor.infinitePart } := by
  let H := GlobalClassFieldTheory.GlobalClassFields.ideleClassNormConductorialSubgroup
    (K := K) (L := L)
  intro m
  let m' := GlobalClassFieldComparison.rayClassModulusToOriginal K m
  have hnorm (R : RayClassFieldRealization K m) :
      (_root_.ideleClassNorm K R.extension).range = m'.congruenceSubgroup := by
    let E := R.extension
    let e :=
      (GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm.trans R.artinEquiv
    apply GlobalClassFieldTheory.GlobalClassFields.rayModulus_normSubgroup_eq_of_arithmeticPrimeArtinEquiv
      m' e
    intro v hv
    have hvm := hv
    let w₀ := _root_.chosenFinitePlaceExtension (L := E) v
    let w := _root_.finitePlaceExtensionCentre v w₀
    have hw :=
      _root_.finitePlaceExtensionCentre_liesOver v w₀
    calc
      _ =
          R.artinEquiv (rayClassOfFinitePrime m v hvm) := by
        rw [← GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele_prime K m v hvm]
        exact congrArg R.artinEquiv
          ((GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele K m).symm_apply_apply _)
      _ = arithmeticFrobeniusAt w :=
        R.artin_frobenius v hvm w hw
      _ = GlobalClassFieldTheory.GlobalClassFields.arithmeticFinitePlacePrimeArtin
              v :=
        (GlobalClassFieldComparison.arithmeticPrimeArtin_eq_arithmeticFrobeniusAt
            v w hw ((R.unramifiedOutsideModulus.1 v hvm) w.asIdeal inferInstance hw)).symm
  constructor
  · rintro ⟨R, ⟨f⟩⟩
    have hdef : m'.congruenceSubgroup ≤
        (_root_.ideleClassNorm K L).range := by
      rw [← (hnorm R)]
      exact (GlobalClassFieldTheory.GlobalClassFields.ideleClassNorm_range_le_of_algHom
        L R.extension f)
    have hc : H.fullConductor ≤ m' :=
      (H.isDefiningModulus_iff_fullConductor_le m').mp hdef
    exact hc
  · intro hc
    obtain ⟨S⟩ := GlobalClassFieldComparison.rayClassSubgroup_existence K m ⊥
    let R : RayClassFieldRealization K m :=
      { extension := S.extension
        unramifiedOutsideModulus := S.unramifiedOutsideModulus
        artinEquiv := (MulEquiv.ofBijective S.artin ⟨((MonoidHom.ker_eq_bot_iff S.artin).mp S.artin_ker), S.artin_surjective⟩)
        artin_frobenius := fun v hv w hlie => S.artin_frobenius v hv w hlie}
    refine ⟨R,
      GlobalClassFieldTheory.GlobalClassFields.finiteAbelianExtension_nonempty_algHom_of_normRange_le
         L R.extension ?_⟩
    rw [(hnorm R)]
    exact ((H.isDefiningModulus_iff_fullConductor_le m').mpr hc)

end ClassFieldTheory

end
