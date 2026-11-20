module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalIdealComplexLattice
public import DedekindZetaZeroFree.Arithmetic.Units.IdealCuspRatios
public import DedekindZetaZeroFree.Arithmetic.Ideals.IdealCuspTranslations

@[expose] public section

noncomputable section
open scoped Matrix Pointwise
namespace DedekindZetaZeroFree.KPCuspFiniteArithmetic

section

variable (F : Type*) [Field F]

theorem rationalUnits_of_pow_mem [NumberField F]
    (u : Fˣ) (n : ℕ) (hn : 0 < n)
    (hu : u ^ n ∈ KPCuspArithmetic.rationalUnits F) :
    u ∈ KPCuspArithmetic.rationalUnits F := by
  let algebraMap₀ := algebraMap (NumberField.RingOfIntegers F) F
  change ∃ v : (NumberField.RingOfIntegers F)ˣ,
    Units.map (algebraMap₀).toMonoidHom v = u ^ n at hu
  obtain ⟨v, hv⟩ := hu
  have hvval : algebraMap₀ (v : NumberField.RingOfIntegers F) =
      (u : F) ^ n := by
    exact congrArg Units.val hv
  have hvival : algebraMap₀
      ((v⁻¹ : (NumberField.RingOfIntegers F)ˣ) : NumberField.RingOfIntegers F) =
      ((u⁻¹ : Fˣ) : F) ^ n := by
    have h : Units.map (algebraMap₀).toMonoidHom v⁻¹ =
        (u⁻¹ : Fˣ) ^ n := by rw [map_inv, hv, inv_pow]
    exact congrArg Units.val h
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (hvval ▸ isIntegral_algebraMap)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (hvival ▸ isIntegral_algebraMap)
  have hxy : x * y = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := by simpa only [mul_comm] using hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  apply Units.ext
  exact hx

theorem integral_ratio_of_commensurable [NumberField F]
    (E : Subgroup Fˣ) (hE : E.Commensurable (KPCuspArithmetic.rationalUnits F)) :
    E ≤ KPCuspArithmetic.rationalUnits F ∧
      (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex := by
  constructor
  · intro u hu
    obtain ⟨n, hn, _, hpow⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
      hE.2.relIndex_ne_zero hu
    exact rationalUnits_of_pow_mem F u n hn hpow.1
  · exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hE.1

theorem conjugatedStabilizer_commensurable
    (Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)) (h : Γ.Commensurable Δ)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) :
    (KPCuspArithmetic.conjugatedStabilizer F Γ q σ).Commensurable
      (KPCuspArithmetic.conjugatedStabilizer F Δ q σ) := by
  let stabilizer₀ := MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q
  have hq : (Γ ⊓ stabilizer₀).Commensurable
      (Δ ⊓ stabilizer₀) := by
    simpa using
      (h.comap (stabilizer₀).subtype).map
        (stabilizer₀).subtype
  exact hq.map (MulAut.conj σ⁻¹).toMonoidHom

end

alias conjugatedStabilizer_upper := DedekindZetaZeroFree.KPCuspArithmetic.PGL2CuspParabolicStabilizers.conjugated_upper

alias isZLattice_of_commensurable := DedekindZetaZeroFree.KPCuspParabolicLattices.PGL2CuspParabolicStabilizers.isZLattice_of_commensurable

 alias diagonal_ne_zero := DedekindZetaZeroFree.KPCuspParabolicLattices.diagonal_ne_zero
private theorem ratio_eq {F : Type*} [Field F]
    (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    A 0 0 / A 1 1 = B 0 0 / B 1 1 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  simp
  rw [mul_div_mul_right _ _ (Units.ne_zero u)]
 def representative {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :=
  Classical.choose (hS g g.property)
private theorem representative_mk {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :
    Matrix.ProjGenLinGroup.mk (representative S hS g) = g :=
  (Classical.choose_spec (hS g g.property)).1
 section

variable {F : Type*} [Field F] (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)

theorem representative_upper (g : S) :
    representative S hS g 1 0 = 0 :=
  (Classical.choose_spec (hS g g.property)).2
 def ratioValue (g : S) : F :=
  representative S hS g 0 0 / representative S hS g 1 1

end
private theorem ratioValue_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g) :
    ratioValue S hS g = A 0 0 / A 1 1 :=
  ratio_eq _ _ ((representative_mk S hS g).trans hA.symm)
 section

variable {F : Type*} [Field F] (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)

theorem ratioValue_one :
    ratioValue S hS 1 = 1 := by
  rw [ratioValue_formula S hS 1 1 (by simp)]
  simp
 theorem ratioValue_mul (g h : S) :
    ratioValue S hS (g*h) = ratioValue S hS g * ratioValue S hS h := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.ratioValue_mul <;> assumption

def upperRatio : S →* Fˣ where
  toFun g := Units.mk0 (ratioValue S hS g) (by
    exact div_ne_zero (diagonal_ne_zero _ (representative_upper S hS g)).1
      (diagonal_ne_zero _ (representative_upper S hS g)).2)
  map_one' := by apply Units.ext; exact ratioValue_one S hS
  map_mul' g h := by apply Units.ext; exact ratioValue_mul S hS g h

end

theorem upperRatio_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g)
    (hu : A 1 0 = 0) : A 0 0 = (upperRatio S hS g : F) * A 1 1 := by
  change A 0 0 = ratioValue S hS g * A 1 1
  rw [ratioValue_formula S hS g A hA]
  exact (div_mul_cancel₀ _ (diagonal_ne_zero A hu).2).symm

theorem upperRatio_agree {F : Type*} [Field F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (s : S) (t : T) (hst : (s : KPCuspArithmetic.PGL2 F) = t) :
    upperRatio S hS s = upperRatio T hT t := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits.StabilizerUnitRatios.upperRatio_agree <;> assumption

theorem ranges_commensurable_of_agree {G H : Type*} [Group G] [Group H]
    (S T : Subgroup G) (h : S.Commensurable T)
    (f : S →* H) (g : T →* H)
    (hfg : ∀ (s : S) (t : T), (s : G) = t → f s = g t) :
    f.range.Commensurable g.range := by
  have hs : (T.subgroupOf S).Commensurable (⊤ : Subgroup S) := by
    simpa using h.symm.comap S.subtype
  have ht : (S.subgroupOf T).Commensurable (⊤ : Subgroup T) := by
    simpa using h.comap T.subtype
  have heq : (T.subgroupOf S).map f = (S.subgroupOf T).map g := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      let t : T := ⟨s, hs⟩
      exact ⟨t, s.property, (hfg s t rfl).symm⟩
    · rintro ⟨t, ht, rfl⟩
      let s : S := ⟨t, ht⟩
      exact ⟨s, t.property, hfg s t rfl⟩
  have hs' : ((T.subgroupOf S).map f).Commensurable f.range := by
    simpa only [MonoidHom.range_eq_map] using hs.map f
  have ht' : ((S.subgroupOf T).map g).Commensurable g.range := by
    simpa only [MonoidHom.range_eq_map] using ht.map g
  exact hs'.symm.trans (heq ▸ ht')

section

variable {F : Type*} [Field F]

theorem upperRatio_ranges_commensurable
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (h : S.Commensurable T) :
    (upperRatio S hS).range.Commensurable (upperRatio T hT).range :=
  ranges_commensurable_of_agree S T h _ _ (upperRatio_agree S T hS hT)

def cuspTranslationMatrix (x : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])
 theorem translationMatrix_mul (x y : F) :
    cuspTranslationMatrix (x+y) = cuspTranslationMatrix x * cuspTranslationMatrix y := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.translationMatrix_mul <;> assumption

def cuspTranslation : Multiplicative F →* KPCuspArithmetic.PGL2 F where
  toFun x := Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix x.toAdd)
  map_one' := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix 0) = 1
    have h : cuspTranslationMatrix (0 : F) = 1 := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [cuspTranslationMatrix]
    rw [h, map_one]
  map_mul' x y := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix (x.toAdd+y.toAdd)) = _
    rw [translationMatrix_mul, map_mul]

end

theorem cuspTranslation_injective {F : Type*} [Field F] :
    Function.Injective (cuspTranslation (F := F)) := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.ParabolicStabilizers.cuspTranslation_injective <;> assumption

def cuspTranslationLattice {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : AddSubgroup F :=
  (S.comap cuspTranslation).toAddSubgroup

theorem cuspTranslationLattice_commensurable {F : Type*} [Field F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F)) (h : S.Commensurable T) :
    (cuspTranslationLattice S).Commensurable (cuspTranslationLattice T) := by
  have hc := h.comap cuspTranslation
  exact ⟨⟨hc.1.relIndex_ne_zero⟩, ⟨hc.2.relIndex_ne_zero⟩⟩

def cuspTranslationInclusion {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) :
    Multiplicative (cuspTranslationLattice S) →* S where
  toFun x := ⟨cuspTranslation (Multiplicative.ofAdd (x.toAdd : F)), x.toAdd.property⟩
  map_one' := by apply Subtype.ext; exact map_one cuspTranslation
  map_mul' x y := by apply Subtype.ext; exact map_mul cuspTranslation _ _
theorem cuspTranslationInclusion_injective {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) :
    Function.Injective (cuspTranslationInclusion S) := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.ParabolicStabilizers.cuspTranslationInclusion_injective <;> assumption

theorem cuspTranslationInclusion_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (x : cuspTranslationLattice S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = cuspTranslationInclusion S (Multiplicative.ofAdd x)) :
    A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0 := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h.symm
  change cuspTranslationMatrix (x : F) * Matrix.GeneralLinearGroup.scalar (Fin 2) u = A at hu
  rw [← hu]
  simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
private theorem ratio_one_translation {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (g : S) (hg : upperRatio S hS g = 1) :
    ∃ x : F, cuspTranslation (Multiplicative.ofAdd x) = g := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.ParabolicStabilizers.ratio_one_translation <;> assumption

theorem cuspTranslationInclusion_range {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) :
    (cuspTranslationInclusion S).range = (upperRatio S hS).ker := by apply @DedekindZetaZeroFree.KPCuspParabolicLattices.ParabolicStabilizers.cuspTranslationInclusion_range <;> assumption

def extensionDataOfRatio {F : Type*} [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hE : (upperRatio S hS).range.Commensurable (KPCuspArithmetic.rationalUnits F)) :
    KPCuspChart.ExtensionData F S where
  L := cuspTranslationLattice S
  E := (upperRatio S hS).range
  inclusion := cuspTranslationInclusion S
  ratio := (upperRatio S hS).rangeRestrict
  integralUnits := (integral_ratio_of_commensurable F _ hE).1
  unitIndex := (integral_ratio_of_commensurable F _ hE).2
  surjective := (upperRatio S hS).rangeRestrict_surjective
  exact := by
    rw [cuspTranslationInclusion_range S hS]
    ext g
    simp
  upper := hS
  unipotentFormula := cuspTranslationInclusion_formula S
  ratioFormula := upperRatio_formula S hS

theorem extension_lattice_of_parabolic_commensurable
    {F : Type*} [Field F] [NumberField F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (h : S.Commensurable T)
    (hE : (upperRatio T hT).range.Commensurable (KPCuspArithmetic.rationalUnits F))
    (hdisc : DiscreteTopology (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule)
    (hz : letI := hdisc; IsZLattice ℝ
      (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule) :
    ∃ D : KPCuspChart.ExtensionData F S,
      ∃ hd : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hd; IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  refine ⟨extensionDataOfRatio S hS ((upperRatio_ranges_commensurable S T hS hT h).trans hE), ?_⟩
  letI := hdisc
  letI := hz
  have hc := cuspTranslationLattice_commensurable S T h
  exact isZLattice_of_commensurable
    (KPCuspChart.translationLattice F (cuspTranslationLattice S))
    (KPCuspChart.translationLattice F (cuspTranslationLattice T))
    ⟨hc.1.map (KPCuspChart.embedding F), hc.2.map (KPCuspChart.embedding F)⟩

def idealArithmeticModule (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Submodule (NumberField.RingOfIntegers F) (Fin 2 → F) :=
  ((1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) : Submodule _ F).comap (LinearMap.proj 0) ⊓
  (I : Submodule _ F).comap (LinearMap.proj 1)
private theorem idealArithmeticModule_mem (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (v : Fin 2 → F) :
    v ∈ idealArithmeticModule F I ↔ (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I := by
  simp [idealArithmeticModule, FractionalIdeal.mem_one_iff]
 def pairVec (F : Type*) [Field F] [NumberField F] :
    (F × F) ≃ₗ[NumberField.RingOfIntegers F] (Fin 2 → F) where
  toFun x := ![x.1,x.2]
  invFun x := (x 0,x 1)
  left_inv x := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl
theorem idealArithmeticModule_full (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (hI : I ≠ 0) :
    KPCuspArithmetic.IsRankTwoLattice F (idealArithmeticModule F I) := by apply @DedekindZetaZeroFree.FiniteAdelicParabolicExtension.IdealCuspRatios.ratioIdealModule_full <;> assumption
private theorem ideal_stabilizer_iff (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F) (KPFiniteAdelicLatticeStabilizers.idealVectors F I) ↔
    ∀ v : Fin 2 → F, v ∈ idealArithmeticModule F I ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ idealArithmeticModule F I := by apply @DedekindZetaZeroFree.FiniteAdelicParabolicExtension.IdealCuspRatios.ideal_stabilizer_iff <;> assumption
theorem idealProjectiveAut_eq_arithmeticAutomorphisms (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I = KPCuspArithmetic.projectiveAutomorphisms F (idealArithmeticModule F I) := by apply @DedekindZetaZeroFree.FiniteAdelicParabolicExtension.IdealCuspRatios.ratioIdealAut_eq <;> assumption

theorem extension_lattice_of_ideal_commensurable
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (hI : I ≠ 0) (a : KPFiniteAdelicLatticeStabilizers.RationalPG F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hcomm : Γ.Commensurable
      ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map (MulAut.conj a).toMonoidHom))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ D : KPCuspChart.ExtensionData F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ),
      ∃ hdisc : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  let Δ := (KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
    (MulAut.conj a).toMonoidHom
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  let T := KPCuspArithmetic.conjugatedStabilizer F Δ q σ
  have hT :=
    conjugatedStabilizer_upper F Δ q σ hσ
  obtain ⟨J, hJ, htranslation⟩ :=
    FiniteAdelicParabolicExtension.ideal_cusp_translation_fractionalIdeal
      F I hI a q σ hσ
  have hL : cuspTranslationLattice T =
      (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup := by
    ext x
    exact htranslation x
  obtain ⟨hd, hz⟩ :=
    FiniteAdelicParabolicExtension.fractionalIdeal_complexPlace_lattice F hF J hJ
  have hlattice : ∃ hd' : DiscreteTopology
      (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule,
      letI := hd'; IsZLattice ℝ
        (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule := by
    rw [hL]
    exact ⟨hd, hz⟩
  obtain ⟨hd', hz'⟩ := hlattice
  exact extension_lattice_of_parabolic_commensurable S T (conjugatedStabilizer_upper F Γ q σ hσ) hT (conjugatedStabilizer_commensurable F Γ Δ hcomm q σ) (FiniteAdelicParabolicExtension.ideal_cusp_ratio_commensurable
    F I hI a q σ hσ (upperRatio T hT) (upperRatio_formula T hT)) hd' hz'

theorem finite_adelic_parabolic_extension_lattice
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteAdelicLatticeStabilizers.AdelicPG F))
    (hcompact : letI := KPFiniteAdelicLatticeStabilizers.projectiveTopology F;
      IsCompact (U : Set (KPFiniteAdelicLatticeStabilizers.AdelicPG F)))
    (hopen : letI := KPFiniteAdelicLatticeStabilizers.projectiveTopology F;
      IsOpen (U : Set (KPFiniteAdelicLatticeStabilizers.AdelicPG F)))
    (g : KPFiniteAdelicLatticeStabilizers.AdelicPG F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ D : KPCuspChart.ExtensionData F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPFiniteAdelicLatticeStabilizers.levelStabilizer F U g) q σ),
      ∃ hdisc : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  obtain ⟨I, a, hI, hstandard⟩ :=
    KPFiniteAdelicLatticeStabilizers.standard_stabilizer_class_obstruction F g
  obtain ⟨hlevel, _⟩ :=
    KPFiniteAdelicLatticeStabilizers.level_stabilizers_commensurable_standard F U hcompact hopen g
  exact extension_lattice_of_ideal_commensurable F hF I hI a
    (KPFiniteAdelicLatticeStabilizers.levelStabilizer F U g) (hlevel.trans hstandard) q σ hσ

end DedekindZetaZeroFree.KPCuspFiniteArithmetic

end
