module

public import Mathlib

public import DedekindZetaZeroFree.Metaplectic.Kubota.CentralScalarSplitting
public import DedekindZetaZeroFree.Metaplectic.Kubota.LocalRootLifts
public import DedekindZetaZeroFree.Metaplectic.Kubota.TameCompact.IntegralCompactSplitting

@[expose] public section


open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPPGLLocalCover

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : KPHilbert.Place F)

def scalarSubgroup  :=
  (KPScalarSplitCentral.scalarMatrix F v).range

theorem scalarSubgroup_le_center :
    scalarSubgroup F v ≤ Subgroup.center (KPLocalCover.LocalGL2 F v) := by
    rintro x ⟨z, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun g =>
      (Matrix.GeneralLinearGroup.scalar_commute z g).symm)

instance scalarSubgroup_normal : (scalarSubgroup F v).Normal :=
  Subgroup.normal_of_le_center (scalarSubgroup_le_center F v)

abbrev LocalPGL2 := KPLocalCover.LocalGL2 F v ⧸ scalarSubgroup F v

def splitScalarSubgroup  :=
  (KPScalarSplitCentral.scalarHom F ζ hζ v).range

instance splitScalarSubgroup_normal : (splitScalarSubgroup F ζ hζ v).Normal :=
  Subgroup.normal_of_le_center (KPScalarSplitCentral.scalarHom_range_le_center F ζ hζ v)

abbrev CubicPGL2 := KPLocalCover.CubicGL2Raw F ζ hζ v ⧸ splitScalarSubgroup F ζ hζ v

def baseQuotient : KPLocalCover.LocalGL2 F v →* LocalPGL2 F v :=
  QuotientGroup.mk' (scalarSubgroup F v)

def coverQuotient : KPLocalCover.CubicGL2Raw F ζ hζ v →* CubicPGL2 F ζ hζ v :=
  QuotientGroup.mk' (splitScalarSubgroup F ζ hζ v)

theorem splitScalarSubgroup_le_ker :
    splitScalarSubgroup F ζ hζ v ≤
      ((baseQuotient F v).comp (KPLocalCover.projection F ζ hζ v)).ker := by
    rintro x ⟨z, rfl⟩
    change baseQuotient F v
      (KPLocalCover.projection F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v z)) = 1
    rw [KPScalarSplitCentral.projection_scalarHom]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩

def projection : CubicPGL2 F ζ hζ v →* LocalPGL2 F v :=
  QuotientGroup.lift (splitScalarSubgroup F ζ hζ v)
    ((baseQuotient F v).comp (KPLocalCover.projection F ζ hζ v))
    (splitScalarSubgroup_le_ker F ζ hζ v)


local notation:max "current_coverQuotient" => coverQuotient F ζ hζ


local notation:max "current_projectionLocal" => projection F ζ hζ

def centralInjection  :=
  (current_coverQuotient v).comp (KPLocalCover.centralInjection F ζ hζ v)

@[simp] theorem projection_coverQuotient (g : KPLocalCover.CubicGL2Raw F ζ hζ v) :
    current_projectionLocal v (current_coverQuotient v g) =
      baseQuotient F v (KPLocalCover.projection F ζ hζ v g) := rfl

theorem splitScalar_inf_kernel :
    splitScalarSubgroup F ζ hζ v ⊓ (KPLocalCover.projection F ζ hζ v).ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨z, hz⟩ := hx.1
    have he : KPScalarSplitCentral.scalarMatrix F v z = 1 := by
      rw [← KPScalarSplitCentral.projection_scalarHom F ζ hζ v z, hz]
      exact hx.2
    have hz1 : z = 1 := by
      apply_fun (fun g : KPLocalCover.LocalGL2 F v => (g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) at he
      simpa [KPScalarSplitCentral.scalarMatrix, Matrix.GeneralLinearGroup.coe_scalar] using he
    rw [← hz, hz1, map_one]
    exact Subgroup.one_mem _

theorem centralInjection_injective : Function.Injective (centralInjection F ζ hζ v) := by
  apply (injective_iff_map_eq_one (centralInjection F ζ hζ v)).mpr
  intro e he
  have hs : KPLocalCover.centralInjection F ζ hζ v e ∈ splitScalarSubgroup F ζ hζ v :=
    (QuotientGroup.eq_one_iff _).mp he
  have hk : KPLocalCover.centralInjection F ζ hζ v e ∈
      (KPLocalCover.projection F ζ hζ v).ker := rfl
  have h1 : KPLocalCover.centralInjection F ζ hζ v e = 1 := by
    have hmem : KPLocalCover.centralInjection F ζ hζ v e ∈
        splitScalarSubgroup F ζ hζ v ⊓ (KPLocalCover.projection F ζ hζ v).ker := ⟨hs, hk⟩
    rw [splitScalar_inf_kernel] at hmem
    exact hmem
  exact (map_eq_one_iff _ (KPLocalCover.centralInjection_injective F ζ hζ v)).mp h1

theorem projection_surjective : Function.Surjective (current_projectionLocal v) := by
    intro x
    induction x using QuotientGroup.induction_on with | _ g =>
      obtain ⟨h, rfl⟩ := KPLocalCover.projection_surjective F ζ hζ v g
      exact ⟨coverQuotient F ζ hζ v h, projection_coverQuotient F ζ hζ v h⟩

theorem range_centralInjection_eq_ker_projection :
    (centralInjection F ζ hζ v).range = (current_projectionLocal v).ker := by
  ext x
  induction x using QuotientGroup.induction_on with | _ g =>
    constructor
    · rintro ⟨e, he⟩
      rw [← he]
      change baseQuotient F v (KPLocalCover.projection F ζ hζ v
        (KPLocalCover.centralInjection F ζ hζ v e)) = 1
      exact map_one _
    · intro hx
      change baseQuotient F v (KPLocalCover.projection F ζ hζ v g) = 1 at hx
      obtain ⟨z, hz⟩ := (QuotientGroup.eq_one_iff _).mp hx
      have he : KPScalarSplitCentral.scalarHom F ζ hζ v z *
          KPLocalCover.centralInjection F ζ hζ v g.epsilon = g := by
        cases g with | mk a e =>
          change KPScalarSplitCentral.scalarMatrix F v z = a at hz
          change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
          simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
            KPLocalCover.sectionMap, hz]
      refine ⟨g.epsilon, ?_⟩
      change current_coverQuotient v (KPLocalCover.centralInjection F ζ hζ v g.epsilon) = _
      calc
        current_coverQuotient v (KPLocalCover.centralInjection F ζ hζ v g.epsilon) =
            1 * current_coverQuotient v (KPLocalCover.centralInjection F ζ hζ v g.epsilon) :=
          (one_mul _).symm
        _ = current_coverQuotient v (KPScalarSplitCentral.scalarHom F ζ hζ v z) *
            current_coverQuotient v (KPLocalCover.centralInjection F ζ hζ v g.epsilon) := by
          have hs : current_coverQuotient v (KPScalarSplitCentral.scalarHom F ζ hζ v z) = 1 :=
            (QuotientGroup.eq_one_iff _).mpr ⟨z, rfl⟩
          rw [hs]
        _ = current_coverQuotient v g := by rw [← map_mul, he]

theorem centralInjection_range_le_center :
    (centralInjection F ζ hζ v).range ≤ Subgroup.center (CubicPGL2 F ζ hζ v) := by
    rintro x ⟨e, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with | _ g =>
      exact congrArg (current_coverQuotient v)
        ((Subgroup.mem_center_iff.mp
          (KPLocalCover.centralInjection_range_le_center F ζ hζ v
            ⟨e, rfl⟩)) g)

def finiteTopology (w : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    TopologicalSpace (CubicPGL2 F ζ hζ (Sum.inr w)) :=
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  inferInstance






theorem finiteTopology_independent (w : HeightOneSpectrum (𝓞 F)) (m n : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
    (hn : KPLocalChartTopology.MatrixChartDepth F w n) :
    finiteTopology F ζ hζ w m = finiteTopology F ζ hζ w n := by
    unfold finiteTopology
    rw [KPLocalChartTopology.translatedTopology_independent F ζ hζ w m n hm hn]

 def kernelEquiv : rootsOfUnity 3 F ≃ (current_projectionLocal v).ker :=
  Equiv.ofBijective
    (fun ε => ⟨centralInjection F ζ hζ v ε, by
      rw [← range_centralInjection_eq_ker_projection]
      exact ⟨ε, rfl⟩⟩)
    ⟨fun _ _ h => centralInjection_injective F ζ hζ v (congrArg Subtype.val h), by
      intro x
      have hx := x.property
      have hx : x.val ∈ (centralInjection F ζ hζ v).range := by
        simpa only [range_centralInjection_eq_ker_projection] using hx
      obtain ⟨ε, hε⟩ := hx
      exact ⟨ε, Subtype.ext hε⟩⟩

private def kernel_finite  :=
  Finite.of_equiv (rootsOfUnity 3 F) (kernelEquiv F ζ hζ v)

private theorem fiber_card (g : LocalPGL2 F v) :
    Nat.card {x : CubicPGL2 F ζ hζ v | current_projectionLocal v x = g} = 3 := by
  obtain ⟨a, ha⟩ := projection_surjective F ζ hζ v g
  let e : (current_projectionLocal v).ker ≃
      {x : CubicPGL2 F ζ hζ v | current_projectionLocal v x = g} := {
    toFun x := ⟨x.val * a, by
      change current_projectionLocal v (x.val * a) = g
      rw [map_mul, show current_projectionLocal v x.val = 1 from x.property, one_mul, ha]⟩
    invFun x := ⟨x.val * a⁻¹, by
      change current_projectionLocal v (x.val * a⁻¹) = 1
      rw [map_mul, map_inv, show current_projectionLocal v x.val = g from x.property, ha,
        mul_inv_cancel]⟩
    left_inv x := Subtype.ext (by simp)
    right_inv x := Subtype.ext (by simp)
  }
  exact (Nat.card_congr e.symm).trans ((Nat.card_congr (kernelEquiv F ζ hζ v).symm).trans
    (KPHilbert.primitive_three F ζ hζ).card_rootsOfUnity)

private theorem quotient_cover
    [IsTopologicalGroup (KPLocalCover.LocalGL2 F v)]
    [TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v)]
    [T2Space (KPLocalCover.CubicGL2Raw F ζ hζ v)]
    [LocallyCompactSpace (KPLocalCover.CubicGL2Raw F ζ hζ v)]
    [IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v)]
    (hs : IsClosed (Set.range (KPScalarSplitCentral.scalarHom F ζ hζ v)))
    (hp : IsLocalHomeomorph (KPLocalCover.projection F ζ hζ v)) :
    T2Space (CubicPGL2 F ζ hζ v) ∧
      LocallyCompactSpace (CubicPGL2 F ζ hζ v) ∧
      IsTopologicalGroup (CubicPGL2 F ζ hζ v) ∧
      IsLocalHomeomorph (current_projectionLocal v) ∧
      ∀ g : LocalPGL2 F v,
        Nat.card {x : CubicPGL2 F ζ hζ v | current_projectionLocal v x = g} = 3 := by
  letI : IsClosed (splitScalarSubgroup F ζ hζ v :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ v)) := hs
  haveI : T2Space (CubicPGL2 F ζ hζ v) := inferInstance
  haveI  := kernel_finite F ζ hζ v
  haveI : DiscreteTopology (current_projectionLocal v).ker := inferInstance
  have hc : Continuous (current_projectionLocal v) :=
    (QuotientGroup.isQuotientMap_mk (splitScalarSubgroup F ζ hζ v)).continuous_iff.mpr
      (QuotientGroup.continuous_mk.comp hp.continuous)
  have ho : IsOpenMap (current_projectionLocal v) :=
    IsOpenMap.of_comp QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ v))
      (QuotientGroup.isOpenMap_coe.comp hp.isOpenMap)
  have hq := ho.isQuotientMap hc (projection_surjective F ζ hζ v)
  exact ⟨inferInstance, inferInstance, inferInstance,
    (hq.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
      (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).isLocalHomeomorph,
    fiber_card F ζ hζ v⟩

section
variable (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m)
include w m hm
theorem finite_topological_cover   :
    letI := finiteTopology F ζ hζ w m
    T2Space (CubicPGL2 F ζ hζ (Sum.inr w)) ∧
      LocallyCompactSpace (CubicPGL2 F ζ hζ (Sum.inr w)) ∧
      IsTopologicalGroup (CubicPGL2 F ζ hζ (Sum.inr w)) ∧
      IsLocalHomeomorph (projection F ζ hζ (Sum.inr w)) ∧
      ∀ g : LocalPGL2 F (Sum.inr w),
        Nat.card {x : CubicPGL2 F ζ hζ (Sum.inr w) | projection F ζ hζ (Sum.inr w) x = g} = 3 := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  obtain ⟨ht, hl, hg⟩ := KPLocalChartTopology.finite_topological_group F ζ hζ w m hm
  letI := ht
  letI := hl
  letI := hg
  exact quotient_cover F ζ hζ (Sum.inr w)
    (KPScalarSplitCentral.finite_continuous_closed F ζ hζ w m hm).2
    (KPLocalChartTopology.finite_projection F ζ hζ w m hm).1

















theorem finite_discrete_kernel   :
    letI := finiteTopology F ζ hζ w m
    letI : Group (LocalPGL2 F (Sum.inr w)) :=
      @QuotientGroup.Quotient.group _ _ (scalarSubgroup F (Sum.inr w))
        (scalarSubgroup_normal F (Sum.inr w))
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    DiscreteTopology (projection F ζ hζ (Sum.inr w)).ker ∧
      ∃ e : rootsOfUnity 3 F ≃ₜ (projection F ζ hζ (Sum.inr w)).ker,
        ∀ ε, (e ε).val = centralInjection F ζ hζ (Sum.inr w) ε := by
  letI := finiteTopology F ζ hζ w m
  letI : Group (LocalPGL2 F (Sum.inr w)) :=
    @QuotientGroup.Quotient.group _ _ (scalarSubgroup F (Sum.inr w))
      (scalarSubgroup_normal F (Sum.inr w))
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  letI := (finite_topological_cover F ζ hζ w m hm).1
  letI := kernel_finite F ζ hζ (Sum.inr w)
  haveI : DiscreteTopology (projection F ζ hζ (Sum.inr w)).ker := inferInstance
  exact ⟨inferInstance,
    ⟨{ kernelEquiv F ζ hζ (Sum.inr w) with
        continuous_toFun := continuous_of_discreteTopology
        continuous_invFun := continuous_of_discreteTopology }, fun _ => rfl⟩⟩
end


def N (t : KPHilbert.Completion F v)  :=
  current_coverQuotient v (KPStandardLocalRootLifts.N F ζ hζ v t)

def LowerN (t : KPHilbert.Completion F v)  :=
  current_coverQuotient v (KPStandardLocalRootLifts.LowerN F ζ hζ v t)

def A (y : (KPHilbert.Completion F v)ˣ)  :=
  current_coverQuotient v (KPStandardLocalRootLifts.A F ζ hζ v y)

def W  :=
  current_coverQuotient v (KPStandardLocalRootLifts.W F ζ hζ v)

def signedW  :=
  current_coverQuotient v (KPStandardLocalRootLifts.signedW F ζ hζ v)

theorem N_add (t u : KPHilbert.Completion F v) :
    N F ζ hζ v (t + u) = N F ζ hζ v t * N F ζ hζ v u := by
    change current_coverQuotient v (KPStandardLocalRootLifts.N F ζ hζ v (t + u)) = _
    rw [KPStandardLocalRootLifts.N_add, map_mul]
    rfl

theorem LowerN_add (t u : KPHilbert.Completion F v) :
    LowerN F ζ hζ v (t + u) = LowerN F ζ hζ v t * LowerN F ζ hζ v u := by
    change current_coverQuotient v (KPStandardLocalRootLifts.LowerN F ζ hζ v (t + u)) = _
    rw [KPStandardLocalRootLifts.LowerN_add, map_mul]
    rfl

theorem A_mul (x y : (KPHilbert.Completion F v)ˣ) :
    A F ζ hζ v x * A F ζ hζ v y =
      centralInjection F ζ hζ v (KPHilbert.B3 F ζ hζ v x y ^ 2) * A F ζ hζ v (x * y) := by
    change current_coverQuotient v (KPStandardLocalRootLifts.A F ζ hζ v x) *
      current_coverQuotient v (KPStandardLocalRootLifts.A F ζ hζ v y) = _
    rw [← map_mul, KPStandardLocalRootLifts.A_mul, map_mul]
    rfl

theorem W_sq : W F ζ hζ v ^ 2 = 1 := by
    change (current_coverQuotient v (KPStandardLocalRootLifts.W F ζ hζ v)) ^ 2 = 1
    rw [← map_pow, KPStandardLocalRootLifts.W_sq, map_one]

theorem signedW_sq : signedW F ζ hζ v ^ 2 = 1 := by
    change (current_coverQuotient v (KPStandardLocalRootLifts.signedW F ζ hζ v)) ^ 2 = 1
    rw [← map_pow, KPStandardLocalRootLifts.signedW_sq]
    have h : KubotaRankTwo.d (KPHilbert.Completion F v) (-1) (-1) =
        KPScalarSplitCentral.scalarMatrix F v (-1) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.d, KPScalarSplitCentral.scalarMatrix,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.mkOfDetNeZero]
    rw [h]
    change current_coverQuotient v (KPScalarSplitCentral.scalarHom F ζ hζ v (-1)) = 1
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩

theorem finite_lifts_continuous (w : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteTopology F ζ hζ w m
    Continuous (N F ζ hζ (Sum.inr w)) ∧ Continuous (LowerN F ζ hζ (Sum.inr w)) ∧
      Continuous (A F ζ hζ (Sum.inr w)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  have hq : Continuous (current_coverQuotient (Sum.inr w)) := QuotientGroup.continuous_mk
  exact ⟨hq.comp (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ w m hm),
    hq.comp (KPStandardLocalRootLifts.finite_LowerN_continuous F ζ hζ w m hm),
    hq.comp (KPStandardLocalRootLifts.finite_A_continuous F ζ hζ w m hm)⟩

def compactScalarSubgroup (w : HeightOneSpectrum (𝓞 F))  :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : (KPTameCompact.O F w)ˣ →*
    KPTameCompact.K0 F w).range

theorem compactScalarSubgroup_normal (w : HeightOneSpectrum (𝓞 F)) :
    (compactScalarSubgroup F w).Normal := by
    apply Subgroup.normal_of_le_center
    rintro x ⟨u, rfl⟩
    exact Subgroup.mem_center_iff.mpr (fun g =>
      (Matrix.GeneralLinearGroup.scalar_commute u g).symm)

attribute [instance] compactScalarSubgroup_normal

abbrev CompactPGL2 (w : HeightOneSpectrum (𝓞 F)) :=
  KPTameCompact.K0 F w ⧸ compactScalarSubgroup F w

section
variable (w : HeightOneSpectrum (𝓞 F))
    (hw : ringChar (KPTameCompact.O F w ⧸ KPTameCompact.p F w) ≠ 3)
include w hw
theorem compactScalarSubgroup_le_ker   :
    compactScalarSubgroup F w ≤
      ((coverQuotient F ζ hζ (Sum.inr w)).comp
        (KPGoodCompactSplitting.kStar F ζ hζ w hw)).ker := by
    rintro x ⟨u, rfl⟩
    change coverQuotient F ζ hζ (Sum.inr w)
      (KPGoodCompactSplitting.kStar F ζ hζ w hw
        (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) = 1
    change coverQuotient F ζ hζ (Sum.inr w) (KPLocalCover.CubicGL2Raw.mk _ _) = 1
    rw [← KPScalarSplitCentral.good_compact_unit_scalar F ζ hζ w hw u]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩

def compactSplitting    :=
  QuotientGroup.lift (compactScalarSubgroup F w)
    ((coverQuotient F ζ hζ (Sum.inr w)).comp (KPGoodCompactSplitting.kStar F ζ hζ w hw))
    (compactScalarSubgroup_le_ker F ζ hζ w hw)

@[simp] theorem compactSplitting_mk  
    (g : KPTameCompact.K0 F w) :
    compactSplitting F ζ hζ w hw (QuotientGroup.mk g) =
      coverQuotient F ζ hζ (Sum.inr w) (KPGoodCompactSplitting.kStar F ζ hζ w hw g) := rfl

theorem compactSplitting_topology  
    (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteTopology F ζ hζ w m
    Continuous (compactSplitting F ζ hζ w hw) ∧
      IsCompact (Set.range (compactSplitting F ζ hζ w hw)) ∧
      IsOpen (Set.range (compactSplitting F ζ hζ w hw)) := by
  letI := KPLocalChartTopology.translatedTopology F ζ hζ w m
  letI := (KPLocalChartTopology.finite_topological_group F ζ hζ w m hm).2.2
  have hq : Continuous (coverQuotient F ζ hζ (Sum.inr w)) := QuotientGroup.continuous_mk
  have hr : Set.range (compactSplitting F ζ hζ w hw) =
      coverQuotient F ζ hζ (Sum.inr w) '' Set.range (KPGoodCompactSplitting.kStar F ζ hζ w hw) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      induction g using QuotientGroup.induction_on with | _ g =>
        exact ⟨_, ⟨g, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk g, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · apply (QuotientGroup.isQuotientMap_mk (compactScalarSubgroup F w)).continuous_iff.mpr
    exact hq.comp (KPGoodCompactSplitting.kStar_continuous F ζ hζ w hw m hm)
  · rw [hr]
    exact (KPGoodCompactSplitting.kStar_compact_image F ζ hζ w hw m hm).image hq
  · rw [hr]
    exact QuotientGroup.isOpenMap_coe _
      (KPGoodCompactSplitting.kStar_open_image F ζ hζ w hw m hm)
end


end
end DedekindZetaZeroFree.KPPGLLocalCover
