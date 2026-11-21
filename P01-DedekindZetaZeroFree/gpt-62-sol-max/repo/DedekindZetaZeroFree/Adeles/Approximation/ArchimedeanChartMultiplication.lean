module

public import DedekindZetaZeroFree.Metaplectic.Kubota.ArchimedeanChartMultiplication
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteLevelActionsAndDensity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology ContDiff Matrix
namespace DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ArchChartProduct
open KPGlobalResidualConstruction KPLiteralChamber NumberField
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalResidualConstruction.NativeChartProduct (product choose_domain product_smooth product_chart)
export KPGlobalResidualConstruction.NativeChartProduct (product_coordinate)

private theorem product_domain (y x : ArchCoordinates F) (hy : y ∈ archDomain F)
    (hx : x ∈ archDomain F) (hden : ∀w, 1+y w 2*x w 0 ≠ 0) :
    product F (y,x) ∈ archDomain F := by
  intro w
  exact div_ne_zero (mul_ne_zero (hy w) (hx w)) (pow_ne_zero _ (hden w))
private theorem finitePart_eq : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ := by
  unfold KPGlobalTorusFunctionData.finitePart PGLComplex.AdelicSlices.finiteSubgroup
  congr 1
  ext r
  simp [PGLComplex.AdelicSlices.finiteTuples]

 def matrixCoordinates (M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    ArchCoordinates F := fun w => rightCoordinates (M w).val
private theorem coordinates_continuousAt_one : ContinuousAt (matrixCoordinates F)
    (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) := by
  apply continuousAt_pi.mpr
  intro w
  apply continuousAt_pi.mpr
  intro i
  have he (j k : Fin 2) : ContinuousAt (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ =>
      (M w).val j k) 1 := by
    exact (continuous_apply k).continuousAt.comp
      ((continuous_apply j).continuousAt.comp
        ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) ℂ)).continuousAt.comp (continuous_apply w).continuousAt))
  have hd : ContinuousAt (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ => (M w).val.det) 1 := by
    simp only [Matrix.det_fin_two]
    exact ((he 0 0).mul (he 1 1)).sub ((he 0 1).mul (he 1 0))
  have hn : ((1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) w).val 1 1 ≠ 0 := by simp
  fin_cases i <;> simp [matrixCoordinates, rightCoordinates]
  · exact (he 0 1).div (he 1 1) hn
  · exact hd.div ((he 1 1).pow 2) (pow_ne_zero _ hn)
  · exact (he 1 0).div (he 1 1) hn
private theorem archImage_nhds (W : Set (ArchCoordinates F)) (hW : IsOpen W) (hb : archBase F ∈ W) :
    (fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W ∈
      nhds (1 : InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ) := by
  let Q : (InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) →
      (InfinitePlace F → Matrix.ProjGenLinGroup (Fin 2) ℂ) := Pi.map (fun _ => Matrix.ProjGenLinGroup.mk)
  have hQ : IsOpenMap Q := IsOpenMap.piMap
    (fun _ => QuotientGroup.isOpenMap_coe) (Filter.Eventually.of_forall (fun _ => Matrix.ProjGenLinGroup.mk_surjective))
  have hn : ∀ᶠ M in nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ),
      matrixCoordinates F M ∈ W := by
    have hbase : matrixCoordinates F (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) = archBase F := by
      funext w i; fin_cases i <;> simp [matrixCoordinates, rightCoordinates, archBase]
    exact (coordinates_continuousAt_one F) (hbase ▸ hW.mem_nhds hb)
  have hden : ∀ᶠ M in nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ),
      ∀w, (M w).val 1 1 ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro w
    have he : Continuous (fun M : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ => (M w).val 1 1) := by fun_prop
    exact he.continuousAt (isOpen_ne.mem_nhds (by simp))
  have hpre : Q ⁻¹' ((fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W) ∈
      nhds (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) := by
    filter_upwards [hn,hden] with M hM hD
    refine ⟨matrixCoordinates F M, hM, ?_⟩
    funext w
    exact rightCoordinates_reconstruct (M w) (hD w)
  have hnh := hQ.nhds_le (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ)
  have hone : Q (1 : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) = 1 := by funext w; simp [Q]
  rw [hone] at hnh
  exact hnh hpre
private theorem thickening_nhds (W : Set (ArchCoordinates F)) (hW : IsOpen W) (hb : archBase F ∈ W)
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    {g | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
      g = archChart F ζ hζ y * u} ∈ nhds (1 : G F ζ hζ) := by
  obtain ⟨e,he,hep⟩ := PGLComplex.AdelicSlices.actual_product_splitting F ζ hζ
  have hf := finitePart_eq F ζ hζ
  let E : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ := Homeomorph.setCongr (congrArg (fun S : Subgroup (G F ζ hζ) => (S : Set (G F ζ hζ))) hf)
  let L : Set (PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := E '' (U.toOpenSubgroup : Set _)
  have hL : L ∈ nhds (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := by
    have hopen : IsOpen L := E.isOpenMap _ U.toOpenSubgroup.isOpen
    have hmem : (1 : PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) ∈ L := by
      exact ⟨1,U.toOpenSubgroup.one_mem,Subtype.ext rfl⟩
    exact hopen.mem_nhds hmem
  have hA := archImage_nhds F W hW hb
  let A : Set (PGLComplex.AdelicSlices.ArchGroup F) :=
    (fun x w => Matrix.ProjGenLinGroup.mk (rightMatrix (x w))) '' W
  have hprod : A ×ˢ L ∈ nhds (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hA hL
  have himage : e '' (A ×ˢ L) ∈ nhds (1 : G F ζ hζ) := by
    have hh := e.toHomeomorph.isOpenMap.nhds_le (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ)
    have heone : e (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) = 1 := e.map_one
    change nhds (e (1 : PGLComplex.AdelicSlices.ArchGroup F ×
      PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ)) ≤ Filter.map e (nhds 1) at hh
    rw [heone] at hh
    have hpre : e ⁻¹' (e '' (A ×ˢ L)) ∈ nhds (1 : PGLComplex.AdelicSlices.ArchGroup F ×
        PGLComplex.AdelicSlices.finiteSubgroup F ζ hζ) :=
      Filter.mem_of_superset hprod (Set.subset_preimage_image e (A ×ˢ L))
    exact hh hpre
  apply Filter.mem_of_superset himage
  rintro g ⟨⟨a,u⟩,⟨⟨y,hy,rfl⟩,⟨v,hv,hu⟩⟩,rfl⟩
  refine ⟨y,hy,v.val,?_,?_⟩
  · exact ⟨v,hv,rfl⟩
  · rw [he, right_insertion]
    have hval : u.val = v.val := congrArg Subtype.val hu.symm
    rw [hval]
    rfl

theorem actual_archChart_product :
    ∃ V : Set (ArchCoordinates F), IsOpen V ∧ archBase F ∈ V ∧ V ⊆ archDomain F ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (product F) (V ×ˢ V) ∧ Set.MapsTo (product F) (V ×ˢ V) (archDomain F) ∧
      (∀ y ∈ V, ∀ x ∈ V, archChart F ζ hζ (product F (y,x)) =
        archChart F ζ hζ y * archChart F ζ hζ x) ∧
      (∀ W : Set (ArchCoordinates F), IsOpen W → archBase F ∈ W → W ⊆ V →
        ∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
          {g | ∃ y ∈ W, ∃ u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
            g = archChart F ζ hζ y * u} ∈ nhds (1 : G F ζ hζ)) ∧
      (∀ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ, ∀ u ∈
        KPGlobalTorusFunctionData.globalLevel F ζ hζ U, ∀ x : ArchCoordinates F,
          Commute (archChart F ζ hζ x) u) := by
  obtain ⟨V,hVo,hb,hVD,hden⟩ := choose_domain F
  refine ⟨V,hVo,hb,hVD,product_smooth F V hden,?_,?_,?_,?_⟩
  · rintro ⟨y,x⟩ ⟨hy,hx⟩
    exact product_domain F y x (hVD hy) (hVD hx) (hden y hy x hx)
  · intro y hy x hx
    exact product_chart F ζ hζ y x (hVD hy) (hVD hx) (hden y hy x hx)
  · intro W hW hbW hWV U
    exact thickening_nhds F ζ hζ W hW hbW U
  · intro U u hu x
    obtain ⟨v,hv,rfl⟩ := hu
    exact ActualFiniteTranslationEstimates.archChart_commutes_finite F ζ hζ x v

end DedekindZetaZeroFree.KPLiteralChamber.JointProfile.ArchChartProduct

end
