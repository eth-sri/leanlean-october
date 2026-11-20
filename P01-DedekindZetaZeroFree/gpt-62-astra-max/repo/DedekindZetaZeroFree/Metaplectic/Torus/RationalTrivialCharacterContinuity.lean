module
public import DedekindZetaZeroFree.Metaplectic.Torus.PrincipalCubicLagrangianPreimage

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterCharacterData

@[expose] public section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private alias diag_inverse := PrincipalCubicLagrangianPreimage.diag_inverse

private alias diag_inverse11 := PrincipalCubicLagrangianPreimage.diag_inverse11

private alias preimage_diag := PrincipalCubicLagrangianPreimage.preimage_diag

private alias ratio_continuous := PrincipalCubicLagrangianPreimage.ratio_continuous

private alias p_continuous := PrincipalCubicLagrangianPreimage.p_continuous

 alias rationalTrivialCharacterContinuity_diagonalPGL_torusRatio_eq := CubeDiagonalProduct.diagonalPGL_torusRatio

 def ordinaryTorusCoverToCubicPullback : E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (rationalTrivialCharacterContinuity_diagonalPGL_torusRatio_eq F ⟨_, e.property⟩).symm⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext rfl (map_one (KPGlobalTorusFunctionData.p F ζ hζ))
  map_mul' x y := by
    apply Subtype.ext
    exact Prod.ext rfl (map_mul (KPGlobalTorusFunctionData.p F ζ hζ) x y)

private theorem torusPullbackBridge_injective :
    Function.Injective (ordinaryTorusCoverToCubicPullback F ζ hζ) := by apply @PrincipalCubicLagrangianPreimage.torusPullbackBridge_injective <;> assumption

private theorem torusPullbackBridge_surjective :
    Function.Surjective (ordinaryTorusCoverToCubicPullback F ζ hζ) := by apply @PrincipalCubicLagrangianPreimage.torusPullbackBridge_surjective <;> assumption

private alias p_rational := PrincipalCubicLagrangianPreimage.p_rational

 def ordinaryTorusCoverRatioModuloCubes : E F ζ hζ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp (KPGlobalTorusFunctionData.p F ζ hζ)

 def rhoPrime : KPGlobalCubicIdelePairing.E F ζ hζ →* KPGlobalCubicIdelePairing.D F :=
  (QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
    (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)

private theorem rhoPrime_ker :
    (rhoPrime F ζ hζ).ker = Subgroup.comap (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)
      (CubicCharacters.cubes (Ideles F)) := by
  show ((QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
    (KPGlobalCubicIdelePairing.torusProjection F ζ hζ)).ker = _
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

private theorem center_eq_ker_pD : Z F ζ hζ = (ordinaryTorusCoverRatioModuloCubes F ζ hζ).ker := by apply @PrincipalCubicLagrangianPreimage.center_eq_pD_ker <;> assumption

private theorem pD_mem_A (g : E F ζ hζ) (hg : g ∈ rationalCenterSubgroup F ζ hζ) :
    ordinaryTorusCoverRatioModuloCubes F ζ hζ g ∈ KPGlobalPrincipalCubicLagrangian.A F := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  obtain ⟨a, rfl⟩ := hx
  have hy1 : ordinaryTorusCoverRatioModuloCubes F ζ hζ y = 1 := by
    refine MonoidHom.mem_ker.mp ?_
    rw [← center_eq_ker_pD F ζ hζ]; exact hy
  have hsa : ordinaryTorusCoverRatioModuloCubes F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) =
      KPGlobalPrincipalCubicLagrangian.principalClass F a := by
    rw [ordinaryTorusCoverRatioModuloCubes, MonoidHom.comp_apply, p_rational]
    rfl
  rw [← hxy, map_mul, hsa, hy1, mul_one]
  exact ⟨a, rfl⟩

theorem rational_extension_continuous (χ : Z F ζ hζ →ₜ* ℂˣ)
    (f : rationalCenterSubgroup F ζ hζ → ℂˣ)
    (hf : ∀ (g : rationalCenterSubgroup F ζ hζ) (a : Fˣ) (z : Z F ζ hζ),
      KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val → f g = χ z) :
    Continuous f := by
  classical
  have decomp : ∀ g : rationalCenterSubgroup F ζ hζ, ∃ a : Fˣ, ∃ z : Z F ζ hζ,
      KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val := by
    intro g
    have hg : g.val ∈ (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ := g.property
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    obtain ⟨a, rfl⟩ := hx
    exact ⟨a, ⟨y, hy⟩, hxy⟩
  have hf1 : f 1 = 1 := by
    have h := hf 1 1 1 (by simp)
    simpa using h
  have hfmul : ∀ g h : rationalCenterSubgroup F ζ hζ, f (g * h) = f g * f h := by
    intro g h
    obtain ⟨a₁, z₁, hz₁⟩ := decomp g
    obtain ⟨a₂, z₂, hz₂⟩ := decomp h
    have hc : Commute (KPGlobalTorusFunctionData.s F ζ hζ a₂) z₁.val :=
      Subgroup.mem_center_iff.mp z₁.property _
    have hgh : KPGlobalTorusFunctionData.s F ζ hζ (a₁ * a₂) * (z₁ * z₂).val = (g * h).val := by
      rw [map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      calc (KPGlobalTorusFunctionData.s F ζ hζ a₁ * KPGlobalTorusFunctionData.s F ζ hζ a₂) *
            (z₁.val * z₂.val)
          = (KPGlobalTorusFunctionData.s F ζ hζ a₁ * z₁.val) *
              (KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₂.val) :=
            hc.mul_mul_mul_comm _ _
        _ = g.val * h.val := by rw [hz₁, hz₂]
    have h1 := hf (g * h) (a₁ * a₂) (z₁ * z₂) hgh
    rw [h1, map_mul, hf g a₁ z₁ hz₁, hf h a₂ z₂ hz₂]
  let fM : rationalCenterSubgroup F ζ hζ →* ℂˣ :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul }
  have hZR : Z F ζ hζ ≤ rationalCenterSubgroup F ζ hζ :=
    fun z hz => Subgroup.mem_sup_right hz

  haveI : IsTopologicalGroup (KPAdelicCoverRestrictedProduct.CubicPGL2Adelic F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hpDcont : Continuous (ordinaryTorusCoverRatioModuloCubes F ζ hζ) :=
    (QuotientGroup.isOpenQuotientMap_mk).continuous.comp (p_continuous F ζ hζ)
  haveI : DiscreteTopology (KPGlobalPrincipalCubicLagrangian.A F) :=
    KPGlobalPrincipalCubicLagrangian.principal_discrete F ζ hζ
  have h1open : IsOpen ({1} : Set (KPGlobalPrincipalCubicLagrangian.A F)) :=
    discreteTopology_iff_isOpen_singleton_one.mp inferInstance
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp h1open
  have honeU : (1 : KPGlobalCubicIdelePairing.D F) ∈ U := by
    have h := (Set.ext_iff.mp hUeq (1 : KPGlobalPrincipalCubicLagrangian.A F))
    simpa using h.mpr rfl
  have hZopen : IsOpen {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} := by
    have hZeq : {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} =
        {g : rationalCenterSubgroup F ζ hζ | ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ U} := by
      ext g
      constructor
      · intro hg
        show ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ U
        have hmem : g.val ∈ (ordinaryTorusCoverRatioModuloCubes F ζ hζ).ker := by
          rw [← center_eq_ker_pD F ζ hζ]; exact hg
        rw [MonoidHom.mem_ker.mp hmem]; exact honeU
      · intro hg
        show g.val ∈ Z F ζ hζ
        have hA : ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val ∈ KPGlobalPrincipalCubicLagrangian.A F :=
          pD_mem_A F ζ hζ g.val g.property
        have haux : (⟨ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val, hA⟩ : KPGlobalPrincipalCubicLagrangian.A F) = 1 :=
          (Set.ext_iff.mp hUeq ⟨ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val, hA⟩).mp hg
        have : ordinaryTorusCoverRatioModuloCubes F ζ hζ g.val = 1 := congrArg Subtype.val haux
        rw [center_eq_ker_pD F ζ hζ]
        exact MonoidHom.mem_ker.mpr this
    rw [hZeq]
    exact (hpDcont.comp continuous_subtype_val).isOpen_preimage U hUopen

  have hfOnZ : (fM ∘ Subgroup.inclusion hZR) = fun z : Z F ζ hζ => χ z := by
    funext z
    change f ⟨(z : E F ζ hζ), hZR z.property⟩ = χ z
    exact hf _ 1 z (by simp)
  have hcont1 : ContinuousAt fM 1 := by
    have hiind : Topology.IsInducing (Subgroup.inclusion hZR) :=
      (Topology.IsEmbedding.inclusion hZR).isInducing
    have hrange : Set.range (Subgroup.inclusion hZR) =
        {g : rationalCenterSubgroup F ζ hζ | g.val ∈ Z F ζ hζ} := by
      ext g; constructor
      · rintro ⟨z, rfl⟩; exact z.property
      · intro hg; exact ⟨⟨g.val, hg⟩, Subtype.ext rfl⟩
    have hmem : Set.range (Subgroup.inclusion hZR) ∈ nhds (Subgroup.inclusion hZR 1) := by
      rw [hrange]
      exact hZopen.mem_nhds (by simp)
    have hc : Continuous (fM ∘ Subgroup.inclusion hZR) := by
      rw [hfOnZ]; exact χ.continuous
    have hcat := (hiind.continuousAt_iff' hmem).mp (hc.continuousAt (x := (1 : Z F ζ hζ)))
    simpa only [map_one] using hcat
  exact continuous_of_continuousAt_one fM hcont1

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
