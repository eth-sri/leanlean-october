module

public import DedekindZetaZeroFree.Adeles.Approximation.UpperRoots.ConjugatedLevelReduction

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

section

variable (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)

def finiteParameter :
    KPMsClearedTruncationL2.Additive F := (0,z)

theorem finite_root_mem :
    KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z) ∈
      KPFiniteCuspAtlas.FiniteCover F ζ hζ := by
  rw [MonoidHom.mem_ker]
  unfold KPGlobalTorusFunctionData.N KPAdelicCoverRestrictedProduct.scalarQuotient
    KPCuspGenuineMonodromy.archProjection
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.lift_mk']
  simp only [MonoidHom.comp_apply, KPAdelicCoverRestrictedProduct.projection_amalgamation]
  funext w
  simp [finiteParameter, KPAdelicCoverRestrictedProduct.adeleEval,
    KPStandardLocalRootLifts.N, KPLocalCover.sectionMap, KPLocalCover.projection,
    KubotaRankTwo.n, RingHom.fst]
  have he : Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w)))
      (by simp [Matrix.det_fin_two]) = 1 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  change Matrix.GeneralLinearGroup.mkOfDetNeZero
      (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F (Sum.inl w))) _ ∈ _
  exact he.symm ▸ Subgroup.one_mem _

def finiteRoot :
    KPFiniteCuspAtlas.FiniteCover F ζ hζ :=
  ⟨KPGlobalTorusFunctionData.N F ζ hζ (finiteParameter F z), finite_root_mem F ζ hζ z⟩

end

@[simp] theorem finiteRoot_zero : finiteRoot F ζ hζ 0 = 1 := by
  apply Subtype.ext
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPRationalAdelicSplitting.N F ζ hζ 0) = 1
  rw [KPRationalAdelicSplitting.N_zero, map_one]

open KPAdelicCoverRestrictedProduct
attribute [local instance] localTopology

private alias finiteRoot_integral_iff := DedekindZetaZeroFree.KPRationalAdelicSplitting.integral_iff

private alias finiteRoot_good := DedekindZetaZeroFree.KPRationalAdelicSplitting.AdelicRationalSplitting.good_N

 def finiteRootTupleHom :
    Multiplicative (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) →*
      RestrictedCover F ζ hζ where
  toFun z := KPGlobalTorusFunctionData.rootTuple F ζ hζ (finiteParameter F z.toAdd)
  map_one' := by
    apply Subtype.ext
    funext v
    change KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v 0) = 1
    rw [map_zero, KPStandardLocalRootLifts.N_zero]
  map_mul' z w := by
    apply Subtype.ext
    funext v
    change KPStandardLocalRootLifts.N F ζ hζ v
      (adeleEval F v (finiteParameter F (z.toAdd + w.toAdd))) =
        KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v (finiteParameter F z.toAdd)) *
        KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v (finiteParameter F w.toAdd))
    have he : finiteParameter F (z.toAdd + w.toAdd) =
        finiteParameter F z.toAdd + finiteParameter F w.toAdd := by
      apply Prod.ext
      · exact (add_zero 0).symm
      · rfl
    rw [he, map_add, KPStandardLocalRootLifts.N_add]

private theorem finiteRootTupleHom_continuous : Continuous (finiteRootTupleHom F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
    intro v
    cases v with
    | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
    | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
        (depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v, IsOpen (compact F ζ hζ v : Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨compact_open F ζ hζ⟩
  apply continuous_of_continuousAt_one (finiteRootTupleHom F ζ hζ)
  let U : Set (Multiplicative (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) :=
    {z | ∀ q, ¬ Bad F q → z.toAdd q ∈ q.adicCompletionIntegers F}
  have hO : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      IsOpen (q.adicCompletionIntegers F : Set (q.adicCompletion F)) := by
    intro q
    exact Valued.isOpen_valuationSubring _
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem hO).preimage continuous_id
  have h1 : (1 : Multiplicative (IsDedekindDomain.FiniteAdeleRing
      (NumberField.RingOfIntegers F) F)) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) := {v | match v with | .inl _ => True | .inr q => ¬Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    constructor
    · exact Set.toFinite _
    · simpa [S] using bad_finite F
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (compact F ζ hζ v : Set _)) (Filter.principal S) :=
    fun z => ⟨(finiteRootTupleHom F ζ hζ z.val).val, by
      intro v hv
      cases v with
      | inl w => exact Subgroup.mem_top _
      | inr q => exact finiteRoot_good F ζ hζ q hv ⟨z.val.toAdd q, (finiteRoot_integral_iff F q _).mpr (z.property q hv)⟩⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr (by
    apply continuous_pi
    intro v
    cases v with
    | inl w =>
      change Continuous (fun z : U => KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) 0)
      exact continuous_const
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (depth_admissible F ζ hζ q)).comp
          ((RestrictedProduct.continuous_eval q).comp continuous_subtype_val))
  have hr : Continuous (U.domRestrict (finiteRootTupleHom F ζ hζ)) :=
    (RestrictedProduct.continuous_inclusion hS).comp hf
  exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h1)

theorem finiteRoot_continuous : Continuous (finiteRoot F ζ hζ) := by
  apply Continuous.subtype_mk
  exact QuotientGroup.continuous_mk.comp (QuotientGroup.continuous_mk.comp (finiteRootTupleHom_continuous F ζ hζ))

theorem canonical_finite_root_reduction
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (σ c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (z : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) :
    ∃ b : F, c⁻¹ * σ *
      finiteRoot F ζ hζ (z - algebraMap F
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) b) *
      σ⁻¹ * c ∈ U.toOpenSubgroup := finite_root_reduction U σ c (finiteRoot F ζ hζ)
    (finiteRoot_continuous F ζ hζ) (finiteRoot_zero F ζ hζ) z

end DedekindZetaZeroFree.KPMsResidualTailRestoration.SharpConstantTerm.FiberStability

end
