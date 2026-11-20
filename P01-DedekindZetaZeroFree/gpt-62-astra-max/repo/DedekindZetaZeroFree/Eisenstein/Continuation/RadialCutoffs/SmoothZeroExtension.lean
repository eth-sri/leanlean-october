module
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSectors.CompactCutoffDifferentialBounds
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.CompactHeightSublevels

public import DedekindZetaZeroFree.Adeles.Quotients.CuspGeometry.BufferedCollars
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContActualRadialCutoff

open KPContActualSectorTestDifferentialDescent

section Helpers
open KPContActualCollarBuffer KPContActualSectorSmoothTestModules
open KPContActualCotangentCountableShrinking KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
 abbrev S := KPContSectorCoveredQuotientVocabulary.SymmetricSpace F
 def Q (i : Fin (H.atlas U).componentCount) (x : S (F := F)) : Base F ζ hζ U :=
 KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)
   (KPCuspSiegel.projection F _ x)
private theorem Q_cont (i : Fin (H.atlas U).componentCount) : Continuous (Q (H := H) i) :=
 continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
private theorem act_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : S (F := F) => γ • x) := by apply @DedekindZetaZeroFree.KPContSectorSmoothFramesSupport.SmoothSectionsAndSupport.rationalAction_smooth <;> assumption
section

variable (i : Fin (H.atlas U).componentCount)

private theorem Q_invariant
    (g : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : S (F := F)) : Q (H := H) i (g.val • x) = Q (H := H) i x := by
  apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i))
  apply Quotient.sound
  exact ⟨g,rfl⟩
private theorem component_injective :
    Function.Injective (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) := by
  intro x y he
  have hh : (H.atlas U).components ⟨i,x⟩ = (H.atlas U).components ⟨i,y⟩ := by
    simpa only [(H.atlas U).components_formula, Q, chartLift,
      KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection, Quotient.lift_mk] using he
  exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective hh)).2

end

 def localHeight (γ : KPCuspArithmetic.PGL2 F) (x : S (F := F)) : ℝ :=
  KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (γ • x)
private theorem localHeight_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (localHeight γ) := by apply @DedekindZetaZeroFree.KPCuspCutoffGraphApproximation.GenericZeroExtension.CompactHeightSublevels.localHeight_smooth <;> assumption

private theorem interior_height (A : ℝ)
    (buffer : CollarBuffer F ζ hζ U R P H A)
    (c : CuspIndex F ζ hζ U R P H) (x : S (F := F))
    (hx : Q (H := H) c.1 x ∈ endSet F ζ hζ U R P H buffer.τ c) :
    ∃ γ : KPCuspArithmetic.PGL2 F, (fun y => height F ζ hζ U R P H buffer.τ c (Q (H := H) c.1 y)) =ᶠ[𝓝 x]
        localHeight γ := by
  rw [← buffer.lift_range c] at hx
  obtain ⟨z,hz,he⟩ := hx
  have he' : KPCuspSiegel.projection F _
      (((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z) =
      KPCuspSiegel.projection F _ x :=
    component_injective (H := H) c.1 he
  obtain ⟨g,hg⟩ := Quotient.exact he'.symm
  change g.val • (((H.atlas U).cuspAtlas c.1).representative c.2 •
    KPCuspCharts.toArch F z) = x at hg
  let γ := (((H.atlas U).cuspAtlas c.1).representative c.2)⁻¹ * g.val⁻¹
  have ht : localHeight γ x = z.2 := by
    dsimp [localHeight, γ]
    rw [mul_smul, ← hg, inv_smul_smul, inv_smul_smul]
    exact KPCuspCharts.toArch_meanHeight F buffer.positive_dimension z
  refine ⟨γ, ?_⟩
  have hopen : IsOpen {y : S (F := F) | buffer.τ < localHeight γ y} :=
    isOpen_lt continuous_const (localHeight_smooth γ).continuous
  have htx : x ∈ {y : S (F := F) | buffer.τ < localHeight γ y} := by
    change buffer.τ < localHeight γ x
    rw [ht]; exact hz
  filter_upwards [hopen.mem_nhds htx] with y hy
  let w := (KPCuspCharts.toArchHomeomorph F buffer.positive_dimension).symm (γ • y)
  have hw : w.2 = localHeight γ y := rfl
  have hl : chartLift F ζ hζ U R P H c w = Q (H := H) c.1 y := by
    dsimp only [w, γ]
    rw [mul_smul]
    change Q c.1
      (((H.atlas U).cuspAtlas c.1).representative c.2 •
        (KPCuspCharts.toArchHomeomorph F buffer.positive_dimension)
          ((KPCuspCharts.toArchHomeomorph F buffer.positive_dimension).symm _)) = _
    rw [Homeomorph.apply_symm_apply, smul_inv_smul]
    simpa using Q_invariant c.1 g⁻¹ y
  rw [← hl, buffer.height_coordinates c w (hw ▸ hy), hw]
section

variable (A : ℝ) (buffer : CollarBuffer F ζ hζ U R P H A) (c : CuspIndex F ζ hζ U R P H)

private theorem zero_germ (φ : ℝ → ℝ)
    (hzero : ∀ t, t ≤ A → φ t = 0) (p : Base F ζ hζ U)
    (hp : p ∉ endSet F ζ hζ U R P H buffer.τ c) :
    KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buffer.τ c φ =ᶠ[𝓝 p] 0 := by
  by_cases hc : p ∈ closure (endSet F ζ hζ U R P H buffer.τ c)
  · have hf : p ∈ frontier (endSet F ζ hζ U R P H buffer.τ c) := by
      rw [frontier, (buffer.open_ends c).interior_eq]
      exact ⟨hc,hp⟩
    obtain ⟨V,hV,hpV,hbound⟩ := buffer.boundary_height_buffer c p hf
    filter_upwards [hV.mem_nhds hpV] with y hy
    by_cases he : y ∈ endSet F ζ hζ U R P H buffer.τ c
    · simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem he, Pi.zero_apply]
      exact hzero _ (le_of_lt (hbound y hy he))
    · simp [KPContActualCollarBuffer.zeroExtension, he]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
    have he : y ∉ endSet F ζ hζ U R P H buffer.τ c := fun he => hy (subset_closure he)
    simp [KPContActualCollarBuffer.zeroExtension, he]
private theorem upstairs_smooth (φ : ℝ → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hzero : ∀ t, t ≤ A → φ t = 0)
    (i : Fin (H.atlas U).componentCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : S (F := F) =>
      KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buffer.τ c φ
        (Q (H := H) i x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : Q (H := H) i x ∈ endSet F ζ hζ U R P H buffer.τ c
  · have hi : i = c.1 := by
      have hh := hx
      rw [← buffer.lift_range c] at hh
      obtain ⟨z,hz,he⟩ := hh
      have hh : (H.atlas U).components ⟨i, KPCuspSiegel.projection F _ x⟩ =
          (H.atlas U).components ⟨c.1, KPCuspSiegel.projection F _
            (((H.atlas U).cuspAtlas c.1).representative c.2 • KPCuspCharts.toArch F z)⟩ := by
        simpa only [(H.atlas U).components_formula, Q, chartLift,
          KPFiniteCuspAtlas.componentMap, KPCuspSiegel.projection, Quotient.lift_mk] using he.symm
      exact congrArg Sigma.fst ((H.atlas U).components.injective hh)
    subst i
    obtain ⟨γ, he⟩ := interior_height A buffer c x hx
    have hf : (fun y : S (F := F) =>
        KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buffer.τ c φ
          (Q (H := H) c.1 y)) =ᶠ[𝓝 x] (fun y => φ (localHeight γ y)) := by
      filter_upwards [he, ((buffer.open_ends c).preimage (Q_cont c.1)).mem_nhds hx] with y hy hmem
      change Q (H := H) c.1 y ∈ endSet F ζ hζ U R P H buffer.τ c at hmem
      simp only [KPContActualCollarBuffer.zeroExtension, Set.indicator_of_mem hmem, hy]
    exact ((hφ.comp (localHeight_smooth γ)).contDiffAt).congr_of_eventuallyEq hf
  · have he := (zero_germ A buffer c φ hzero (Q (H := H) i x) hx).comp_tendsto
      (Q_cont i).continuousAt
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq he

end
private theorem labeledA_smooth : ContDiff ℝ (⊤ : ℕ∞)
    (labeledA (placeEquiv F ζ hζ) : M F → S (F := F)) := by
  apply contDiff_pi.mpr
  intro k
  exact (contDiff_apply ℝ _ ((placeEquiv F ζ hζ).symm k)).comp
    (CotangentLogCoframe.A (KPContCotangentActualOverlap.d F)).contDiff
private alias continuous_iff_quotient := DedekindZetaZeroFree.KPContActualSectorMultiplier.CompactCutoffDifferentialBounds.continuous_iff_isQuotientMap
private theorem upstairs_continuous_descends (f : Base F ζ hζ U → ℝ)
    (hf : ∀ i, Continuous (fun x : S (F := F) => f (Q (H := H) i x))) : Continuous f := by
  obtain ⟨cover⟩ := (kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H).2
  refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
  · intro x
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (by rw [cover.covers]; trivial)
    exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
  · intro n
    let a := cover.chart n
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_iff_quotient
      (every_shrunkChart_properties F ζ hζ U R P H a).quotient _).mpr ((hf a.component).comp continuous_subtype_val)
end Helpers

theorem exists_smooth_zero_extension
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (A : ℝ) (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ U R P H A)
    (c : KPContActualCollarBuffer.CuspIndex F ζ hζ U R P H)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hzero : ∀ t, t ≤ A → φ t = 0) :
    ∃ η : RealSmoothCutoff F ζ hζ U R P H,
      η.val = KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buffer.τ c φ ∧
      Continuous η.val := by
  let val := KPContActualCollarBuffer.zeroExtension F ζ hζ U R P H buffer.τ c φ
  have hs := upstairs_smooth A buffer c φ hφ hzero
  refine ⟨⟨val, ?_⟩, rfl, upstairs_continuous_descends val (fun i => (hs i).continuous)⟩
  intro a
  refine ⟨fun x => val (KPContCotangentOverlapRationalBranches.q a x), ?_, fun _ => rfl⟩
  exact ((hs a.component).comp labeledA_smooth).contDiffOn

end DedekindZetaZeroFree.KPContActualRadialCutoff

end
