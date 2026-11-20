module
public import DedekindZetaZeroFree.Metaplectic.Torus.ClosednessAndNormChartFormula

public import DedekindZetaZeroFree.Metaplectic.Torus.PhaseTrivialFiniteLevels

@[expose] public section

open scoped NumberField Classical Topology
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def finiteTorusForClassLifts : Subgroup (KPGlobalTorusFunctionData.E F ζ hζ) :=
  (KPGlobalTorusFunctionData.finitePart F ζ hζ).comap
    (KPGlobalTorusFunctionData.torus F ζ hζ).subtype

def finiteTorusClassProjection : finiteTorusForClassLifts F ζ hζ →*
    KPGlobalCubicIdelePairing.D F :=
  (KPGlobalProductPolarizationCharacter.pD F ζ hζ).comp
    (finiteTorusForClassLifts F ζ hζ).subtype

section

variable (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F) (h10 : A 1 0 = 0) (h01 : A 0 1 = 0)

private lemma diag_inverse :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit⁻¹.val = A⁻¹ 0 0 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 0 0) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h10, mul_zero, add_zero, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit_spec
  change A⁻¹ 0 0 * A 0 0 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit
  have hu' : u = A 0 0 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 0 0 * A 0 0) := by rw [h]
    _ = A⁻¹ 0 0 := by rw [← hu']; simp [← mul_assoc, mul_comm]
private lemma diag_inverse11 :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit⁻¹.val = A⁻¹ 1 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 1 1) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h01, mul_zero, zero_add, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit_spec
  change A⁻¹ 1 1 * A 1 1 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit
  have hu' : u = A 1 1 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 1 1 * A 1 1) := by rw [h]
    _ = A⁻¹ 1 1 := by rw [← hu']; simp [← mul_assoc, mul_comm]

end
private lemma preimage_diag (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      KPGlobalTorusFunctionData.ordinaryTorus F) : A 1 0 = 0 ∧ A 0 1 = 0 := by
  obtain ⟨B, hB, h10, h01⟩ := hA
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  rw [← he]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
private lemma ratio_continuous : Continuous (KPGlobalTorusFunctionData.torusRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S := (KPGlobalTorusFunctionData.ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).1.unit
  let w (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).2.unit
  have hu : Continuous u := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (u A).val)
      have he : (fun A : q ⁻¹' S => (u A).val) = fun A => A.val 0 0 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (u A)⁻¹.val) = fun A => A.val⁻¹ 0 0 := by
        funext A; exact diag_inverse F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (u A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have hw : Continuous w := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (w A).val)
      have he : (fun A : q ⁻¹' S => (w A).val) = fun A => A.val 1 1 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (w A)⁻¹.val) = fun A => A.val⁻¹ 1 1 := by
        funext A; exact diag_inverse11 F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (w A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have he : (KPGlobalTorusFunctionData.torusRatio F) ∘ S.restrictPreimage q =
      fun A => u A * (w A)⁻¹ := by
    funext A
    apply Units.ext
    exact KPGlobalTorusFunctionData.ratio_formula F _ A.val rfl
      (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
  rw [he]
  exact hu.mul hw.inv

theorem finiteTorusClassProjection_continuous :
    Continuous (finiteTorusClassProjection F ζ hζ) := by
  change Continuous (fun x : finiteTorusForClassLifts F ζ hζ =>
    KPGlobalProductPolarizationCharacter.pD F ζ hζ x.val)
  apply Continuous.comp (g := (KPGlobalProductPolarizationCharacter.pD F ζ hζ))
    (f := Subtype.val) _ continuous_subtype_val
  apply QuotientGroup.continuous_mk.comp
  apply (ratio_continuous F).comp
  exact ((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
    continuous_subtype_val).subtype_mk (fun t => t.property)

private theorem class_totallyDisconnected :
    TotallyDisconnectedSpace (KPGlobalCubicIdelePairing.D F) := by
  letI : ∀ v, DiscreteTopology (KPGlobalCubicIdelePairing.LocalD F v) := (by
    apply @DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport.local_discrete <;> assumption)
  obtain ⟨e, he⟩ := KPGlobalCubicIdelePairing.restricted_cube_quotient F
  let f := fun x => e x
  refine ⟨isTotallyDisconnected_of_image (RestrictedProduct.continuous_coe.comp e.continuous).continuousOn ?_
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  intro x y h
  apply e.injective
  ext v
  exact congrFun h v

theorem compact_open_transverse_subgroup_in_nhds
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (N : Set (KPGlobalCubicIdelePairing.D F)) (hN : N ∈ nhds 1) :
    ∃ K : Subgroup (KPGlobalCubicIdelePairing.D F),
      K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P ∧
      IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ ∧
      (K : Set (KPGlobalCubicIdelePairing.D F)) ⊆ N := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := class_totallyDisconnected F
  letI := KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  let M := KPGlobalProductPolarizationCharacter.M F ζ hζ P
  letI : CompactSpace M := isCompact_iff_compactSpace.mp (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).1
  obtain ⟨O, hO, hOA⟩ := isOpen_induced_iff.mp
    (isOpen_discrete ({1} : Set (KPGlobalPrincipalCubicLagrangian.A F)))
  have h1O : (1 : KPGlobalCubicIdelePairing.D F) ∈ O := by
    have : (1 : KPGlobalPrincipalCubicLagrangian.A F) ∈ ({1} : Set (KPGlobalPrincipalCubicLagrangian.A F)) := by simp
    rw [← hOA] at this
    exact this
  obtain ⟨W, ⟨h1W, hW⟩, hWN⟩ := (nhds_basis_clopen (1 : M)).mem_iff.mp (continuous_subtype_val.continuousAt.preimage_mem_nhds (Filter.inter_mem hN (hO.mem_nhds h1O)))
  obtain ⟨H, hHW⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
  let K := H.toSubgroup.map M.subtype
  have hK : (K : Set (KPGlobalCubicIdelePairing.D F)) = Subtype.val '' (H : Set M) := rfl
  refine ⟨K, ?_, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_subtype_le _
  · rw [hK]
    exact H.isClosed.isCompact.image continuous_subtype_val
  · rw [hK]
    exact ((KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).2.isOpenEmbedding_subtypeVal).isOpenMap _ H.isOpen
  · apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx.1
    have hya : (⟨y.val, hx.2⟩ : KPGlobalPrincipalCubicLagrangian.A F) ∈ ({1} : Set _) := by
      rw [← hOA]
      exact ((hWN (hHW hy)).2)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Set.mem_singleton_iff.mp hya))
  · rintro x ⟨y, hy, rfl⟩
    exact (hWN (hHW hy)).1

theorem phase_trivial_class_lifts_of_open_projection
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (hπ : IsOpenMap (finiteTorusClassProjection F ζ hζ))
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    ∃ K : Subgroup (KPGlobalCubicIdelePairing.D F),
      K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P ∧
      IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ ∧
      ∀ d ∈ K, ∃ j : KPGlobalProductPolarizationCharacter.B F ζ hζ P,
        j.val ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype ∧
        KPGlobalProductPolarizationCharacter.pD F ζ hζ j.val = d ∧
        KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T j /
          KPGlobalCenterRationalCharacter.positiveComplex
            (KPGlobalCenterRationalCharacter.nu F ζ hζ j.val) = 1 := by
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  obtain ⟨V, hV⟩ := finite_level_with_trivial_phase F ζ hζ P T
    (KPGlobalProductPolarizationCharacter.M F ζ hζ P) le_rfl (KPGlobalProductPolarizationCharacter.M_compact_open F ζ hζ P).2
  let f : finiteTorusForClassLifts F ζ hζ →* KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let N :=
    ((U.toOpenSubgroup ⊓ V.toOpenSubgroup).toSubgroup).comap f
  obtain ⟨K, hKM, hKc, hKo, hKA, hK⟩ :=
    compact_open_transverse_subgroup_in_nhds F ζ hζ P
      ((finiteTorusClassProjection F ζ hζ) '' N)
      ((hπ _ ((U.toOpenSubgroup.isOpen.inter V.toOpenSubgroup.isOpen).preimage ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))).mem_nhds ⟨1, N.one_mem, map_one _⟩)
  refine ⟨K, hKM, hKc, hKo, hKA, ?_⟩
  intro d hd
  obtain ⟨x, hx, hxd⟩ := hK hd
  have hxV : x.val ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ V).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype :=
    ⟨f x, hx.2, rfl⟩
  let b : KPGlobalProductPolarizationCharacter.B F ζ hζ P := ⟨x.val, (hV x.val hxV).1⟩
  exact ⟨b, (⟨f x, hx.1, rfl⟩), hxd, (hV x.val hxV).2 b rfl⟩

private alias ordinary_torus_closed := DedekindZetaZeroFree.KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.ClosednessAndNormChartFormula.ordinarytorusclosed

alias FiniteClassProjection.ordinary_torus_closed := ordinary_torus_closed

theorem finiteTorusForClassLifts_locallyCompact : LocallyCompactSpace (finiteTorusForClassLifts F ζ hζ) := by
  letI : LocallyCompactSpace (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI : LocallyCompactSpace (KPGlobalTorusFunctionData.E F ζ hζ) := ((ordinary_torus_closed F).preimage (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous).locallyCompactSpace
  apply IsClosed.locallyCompactSpace
  have hf : IsClosed (KPGlobalTorusFunctionData.finitePart F ζ hζ : Set (KPGlobalTorusFunctionData.G F ζ hζ)) := by
    rw [finitePart_eq_closure F ζ hζ]
    exact Subgroup.isClosed_topologicalClosure _
  exact hf.preimage continuous_subtype_val

theorem finiteTorusClassProjection_open_of_surjective
    (hs : Function.Surjective (finiteTorusClassProjection F ζ hζ)) :
    IsOpenMap (finiteTorusClassProjection F ζ hζ) := by
  letI := finiteTorusForClassLifts_locallyCompact F ζ hζ
  letI : SecondCountableTopology (KPGlobalTorusFunctionData.G F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : SecondCountableTopology (KPGlobalTorusFunctionData.E F ζ hζ) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI : SecondCountableTopology (finiteTorusForClassLifts F ζ hζ) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  letI := KPGlobalCubicIdelePairing.hausdorff F
  letI := KPGlobalCubicIdelePairing.locally_compact F
  exact (finiteTorusClassProjection F ζ hζ).isOpenMap_of_sigmaCompact hs
    (finiteTorusClassProjection_continuous F ζ hζ)

 section

variable (y : KPGlobalCubicIdelePairing.Ideles F)

def finiteIdele : KPGlobalCubicIdelePairing.Ideles F :=
  { val := (1, y.val.2)
    inv := (1, y.inv.2)
    val_inv := by have h := congrArg Prod.snd y.val_inv; exact Prod.ext (one_mul 1) h
    inv_val := by have h := congrArg Prod.snd y.inv_val; exact Prod.ext (one_mul 1) h }
private lemma finiteIdele_infinite (w : InfinitePlace F) :
    KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w) (finiteIdele F y) = 1 := rfl
private lemma finiteIdele_class :
    QuotientGroup.mk' (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F)) (finiteIdele F y) =
    QuotientGroup.mk' _ y := by
  apply KPGlobalCubicIdelePairing.classComparison_injective F
  ext v
  cases v with
  | inl w => letI := KPGlobalCubicIdelePairing.local_complex_trivial F w; exact Subsingleton.elim _ _
  | inr q => rfl
private lemma diag_tuple_projection :
    KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y) =
      KPGlobalCubicIdelePairing.diagonalHom F y := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    have hh := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inl w) => A i j) (KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y) (Sum.inl w))
    change ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y)) i j).1 w =
      (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inl w))
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w) y) 1) i j at hh
    fin_cases i <;> fin_cases j
    all_goals simp [KubotaRankTwo.d] at hh
    all_goals convert hh using 1 <;> rfl
  · apply RestrictedProduct.ext
    intro q
    have hh := congrArg (fun A : KPLocalCover.LocalGL2 F (Sum.inr q) => A i j) (KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y) (Sum.inr q))
    change ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ y)) i j).2 q =
      (KubotaRankTwo.d (KPHilbert.Completion F (Sum.inr q))
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y) 1) i j at hh
    fin_cases i <;> fin_cases j
    all_goals simp [KubotaRankTwo.d] at hh
    all_goals convert hh using 1 <;> rfl

end

theorem finiteTorusClassProjection_surjective : Function.Surjective (finiteTorusClassProjection F ζ hζ) := by
  intro d
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (CubicCharacters.cubes (KPGlobalCubicIdelePairing.Ideles F)) d
  let u := finiteIdele F y
  let x := KPGlobalCenterRationalCharacter.diagonalTuple F ζ hζ u
  let g := KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ u
  have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ g =
      KPGlobalCubicIdelePairing.diagonalPGL F u := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x) = _
    rw [diag_tuple_projection F ζ hζ]
    rfl
  have ht : g ∈ KPGlobalTorusFunctionData.torus F ζ hζ := by
    refine ⟨KPGlobalCubicIdelePairing.diagonalHom F u, hproj.symm, ?_, ?_⟩
    all_goals simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
  let e : KPGlobalTorusFunctionData.E F ζ hζ := ⟨g, ht⟩
  have hf : e ∈ finiteTorusForClassLifts F ζ hζ := by
    refine ⟨x, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inl w) u) = 1
    rw [finiteIdele_infinite F y, KPStandardLocalRootLifts.A_one]
  have hp : KPGlobalTorusFunctionData.p F ζ hζ e = u := by
    apply Units.ext
    have h := KPGlobalTorusFunctionData.ratio_formula F
      ⟨_, ht⟩ (KPGlobalCubicIdelePairing.diagonalHom F u) hproj.symm
      (by simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix])
      (by simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix])
    let A := KPGlobalCubicIdelePairing.diagonalHom F u
    let h10 : A 1 0 = 0 := by simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
    let h01 : A 0 1 = 0 := by simp [A, KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix]
    let a := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit
    let b := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit
    have ha : a = u := by
      apply Units.ext
      exact (IsUnit.unit_spec _).trans (rfl)
    have hb : b = 1 := by
      apply Units.ext
      exact (IsUnit.unit_spec _).trans (rfl)
    change ↑((KPGlobalTorusFunctionData.p F ζ hζ) e) = a.val * b⁻¹.val at h
    rw [ha, hb] at h
    simpa using h
  refine ⟨⟨e, hf⟩, ?_⟩
  change QuotientGroup.mk' _ (KPGlobalTorusFunctionData.p F ζ hζ e) = _
  rw [hp]
  exact finiteIdele_class F y

theorem finite_torus_projection_and_phase_trivial_class_lifts
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P) :
    Continuous (finiteTorusClassProjection F ζ hζ) ∧
    IsOpenMap (finiteTorusClassProjection F ζ hζ) ∧
    Function.Surjective (finiteTorusClassProjection F ζ hζ) ∧
    ∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
    ∃ K : Subgroup (KPGlobalCubicIdelePairing.D F),
      K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P ∧
      IsCompact (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      IsOpen (K : Set (KPGlobalCubicIdelePairing.D F)) ∧
      K ⊓ KPGlobalPrincipalCubicLagrangian.A F = ⊥ ∧
      ∀ d ∈ K, ∃ j : KPGlobalProductPolarizationCharacter.B F ζ hζ P,
        j.val ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype ∧
        KPGlobalProductPolarizationCharacter.pD F ζ hζ j.val = d ∧
        KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T j /
          KPGlobalCenterRationalCharacter.positiveComplex
            (KPGlobalCenterRationalCharacter.nu F ζ hζ j.val) = 1 := by
  have hs := finiteTorusClassProjection_surjective F ζ hζ
  have ho := finiteTorusClassProjection_open_of_surjective F ζ hζ hs
  exact ⟨finiteTorusClassProjection_continuous F ζ hζ, ho, hs,
    phase_trivial_class_lifts_of_open_projection F ζ hζ P T ho⟩

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
