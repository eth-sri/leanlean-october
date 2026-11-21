module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.CodifferentialCovariance
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarDifferentialDescent

@[expose] public section

section

noncomputable section
open scoped Classical NumberField BigOperators
open Topology Filter

namespace DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentRealOrthogonalComplexification

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem phase_eventually_constant {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (x : M F) (hx : x ∈ e.domain) :
    e.phase =ᶠ[𝓝 x] fun _ => e.phase x := by
  have he := (unitary_phase e).1.eventually_eq ⟨x,hx⟩
  rw [← map_nhds_subtype_coe_eq_nhds hx (e.isOpen_domain.mem_nhds hx)]
  exact he
open KPCuspCutoffGraphApproximation (part codifferential_smul_const coframe_codifferential_of_push)

private theorem part_complexification (d : ℕ) (f : ℂ →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin d × Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 3))
    (v : EuclideanSpace ℂ (Fin d × Fin 3)) :
    part d f (operatorComplexification _ A v) = A (part d f v) := by
  have hre : (∑ j, (part d f v) j • EuclideanSpace.basisFun _ ℝ j) = part d f v :=
    (EuclideanSpace.basisFun _ ℝ).sum_repr _
  ext k
  rw [← hre, map_sum]
  simp only [part, WithLp.ofLp_toLp, operatorComplexification_apply, map_sum,
    WithLp.ofLp_sum, Finset.sum_apply, map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (((A (EuclideanSpace.basisFun _ ℝ j)) k : ℝ) : ℂ) * v j =
      ((A (EuclideanSpace.basisFun _ ℝ j)) k : ℝ) • v j by simp [Complex.real_smul]]
  rw [map_smul]
  simp only [smul_eq_mul]
  ring
set_option maxHeartbeats 1000000 in
private theorem untwisted_codifferential {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (V W : M F → E F) (x : M F) (hx : x ∈ e.domain)
    (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x) (hW : ContDiffAt ℝ (⊤ : ℕ∞) W (e.psi x))
    (hVW : (fun y => W (e.psi y)) =ᶠ[𝓝 x]
      (fun y => operatorComplexification _ (Q e y) (V y))) :
    HyperbolicChart.codifferential (d F) ((CotangentLogCoframe.j (d F)).symm ∘ W) (e.psi x) =
      HyperbolicChart.codifferential (d F) ((CotangentLogCoframe.j (d F)).symm ∘ V) x := by
  have hψ : ContDiffAt ℝ 2 e.psi x :=
    ((smooth_metric e).1.contDiffAt (e.isOpen_domain.mem_nhds hx)).of_le (by simp)
  have hm : ∀ᶠ y in 𝓝 x, ∀ u v : M F,
      HyperbolicChart.metric (d F) (e.psi y) (fderiv ℝ e.psi y u) (fderiv ℝ e.psi y v) =
        HyperbolicChart.metric (d F) y u v := by
    filter_upwards [e.isOpen_domain.mem_nhds hx] with y hy
    exact (smooth_metric e).2 y hy
  apply coframe_codifferential_of_push (d F) e.psi V W x hψ hV hW hm
  intro f
  filter_upwards [hVW] with y hy
  rw [hy, part_complexification]
  simp [Q, ContinuousLinearMap.comp_apply, CotangentLogCoframe.H]

set_option maxHeartbeats 1000000 in

theorem actual_codifferential_arrow {i : Fin (H.atlas U).componentCount}
    {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H) i}
    (e : Arrow a b) (V W : M F → E F) (x : M F) (hx : x ∈ e.domain)
    (hV : ContDiffAt ℝ (⊤ : ℕ∞) V x)
    (hW : ContDiffAt ℝ (⊤ : ℕ∞) W (e.psi x))
    (hVW : (fun y => W (e.psi y)) =ᶠ[𝓝 x]
      (fun y => twistedOperator e y (V y))) :
    HyperbolicChart.codifferential (d F) ((CotangentLogCoframe.j (d F)).symm ∘ W)
        (e.psi x) =
      e.phase x *
        HyperbolicChart.codifferential (d F) ((CotangentLogCoframe.j (d F)).symm ∘ V) x := by
  let c : ℂ := e.phase x
  have hc : c ≠ 0 := by
    have hn := (unitary_phase e).2.2.1 x hx
    intro h
    simp [c, show e.phase x = 0 from h] at hn
  let W' : M F → E F := fun y => c⁻¹ • W y
  have hW' : ContDiffAt ℝ (⊤ : ℕ∞) W' (e.psi x) := by
    exact (contDiffAt_const (c := c⁻¹)).smul hW
  have hp : (fun y => W' (e.psi y)) =ᶠ[𝓝 x]
      (fun y => operatorComplexification _ (Q e y) (V y)) := by
    filter_upwards [hVW, phase_eventually_constant e x hx] with y hy hphase
    dsimp only [W']
    rw [hy]
    simp only [twistedOperator, ContinuousLinearMap.smul_apply, hphase, smul_smul]
    change (c⁻¹ * c) • _ = _
    rw [inv_mul_cancel₀ hc, one_smul]
  have ht := untwisted_codifferential e V W' x hx hV hW' hp
  have hw : ((CotangentLogCoframe.j (d F)).symm ∘ W') =
      fun y => c⁻¹ • ((CotangentLogCoframe.j (d F)).symm ∘ W) y := by
    funext y
    exact map_smul _ _ _
  rw [hw, codifferential_smul_const] at ht
  · apply (mul_left_cancel₀ (inv_ne_zero hc))
    simpa [mul_assoc, c, hc] using ht
  · exact (((CotangentLogCoframe.j (d F)).symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).differentiableAt.comp _
      (hW.differentiableAt (by simp)))

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

end

end

section
noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

open KPContActualSectorSmoothTestModules KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

private theorem coordinateDerivative_congr {d : ℕ} {i : Fin d} {k : Fin 3}
    {f g : HyperbolicChart.Space d → ℂ} {p : HyperbolicChart.Space d}
    (h : f =ᶠ[nhds p] g) :
    HyperbolicChart.coordinateDerivative d i k f p =
      HyperbolicChart.coordinateDerivative d i k g p := by
  unfold HyperbolicChart.coordinateDerivative
  rw [h.fderiv_eq]

private theorem codifferential_congr {d : ℕ}
    {W W' : HyperbolicChart.Space d → HyperbolicChart.Cotangent d}
    {p : HyperbolicChart.Space d} (h : W =ᶠ[nhds p] W') :
    HyperbolicChart.codifferential d W p = HyperbolicChart.codifferential d W' p := by
  simp only [HyperbolicChart.codifferential]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : (fun q => W q i 0) =ᶠ[nhds p] (fun q => W' q i 0) := h.fun_comp (fun v => v i 0)
  have h1 : (fun q => W q i 1) =ᶠ[nhds p] (fun q => W' q i 1) := h.fun_comp (fun v => v i 1)
  have h2 : (fun q => W q i 2) =ᶠ[nhds p] (fun q => W' q i 2) := h.fun_comp (fun v => v i 2)
  rw [coordinateDerivative_congr (i := i) (k := 2) h0,
    coordinateDerivative_congr (i := i) (k := 0) h1,
    coordinateDerivative_congr (i := i) (k := 1) h2, h0.eq_of_nhds]

private theorem codifferential_zero {d : ℕ}
    {W : HyperbolicChart.Space d → HyperbolicChart.Cotangent d}
    {p : HyperbolicChart.Space d} (h : W =ᶠ[nhds p] 0) :
    HyperbolicChart.codifferential d W p = 0 := by
  rw [codifferential_congr h]
  simp [HyperbolicChart.codifferential, HyperbolicChart.coordinateDerivative]

theorem codifferential_support_subset (W : T_U F ζ hζ U R P H) :
    scalarSupport (fun a x => HyperbolicChart.codifferential (d F)
      (fun y => (CotangentLogCoframe.j (d F)).symm
        (if hy : y ∈ omega a then (coefficient W.val a) ⟨y, hy⟩ else 0)) x.val) ⊆
      cotangentSupport W.val := by
  apply closure_minimal _ isClosed_closure
  rintro x ⟨a, y₀, hq, hne⟩
  rw [← hq]
  set A : Set (M F) :=
    {z | ∃ (hz : z ∈ omega a), (coefficient W.val a) ⟨z, hz⟩ ≠ 0} with hAdef
  have hyA : y₀.val ∈ closure A := by
    by_contra hcon
    have hg : (fun y => (CotangentLogCoframe.j (d F)).symm
        (if hy : y ∈ omega a then (coefficient W.val a) ⟨y, hy⟩ else 0)) =ᶠ[nhds y₀.val] 0 := by
      refine Filter.eventually_of_mem
        ((isClosed_closure.isOpen_compl.inter (isOpen_omega a)).mem_nhds ⟨hcon, y₀.property⟩) ?_
      intro y hy
      have hyA' : y ∉ A := fun hmem => hy.1 (subset_closure hmem)
      change (CotangentLogCoframe.j (d F)).symm
        (if hy : y ∈ omega a then (coefficient W.val a) ⟨y, hy⟩ else 0) = 0
      rw [dif_pos hy.2]
      have hzero : (coefficient W.val a) ⟨y, hy.2⟩ = 0 := by
        by_contra hc
        exact hyA' ⟨hy.2, hc⟩
      rw [hzero, map_zero]
    exact hne (codifferential_zero hg)
  have himg : q a '' closure A ⊆ closure (q a '' A) :=
    image_closure_subset_closure_image (continuous_q a)
  have hsub : q a '' A ⊆ {x | ∃ (a' : ActualChart (U := U) (H := H)) (y : omega a'),
      q a' y.val = x ∧ coefficient W.val a' y ≠ 0} := by
    rintro x ⟨z, ⟨hz, hc⟩, rfl⟩
    exact ⟨a, ⟨z, hz⟩, rfl, hc⟩
  exact closure_mono hsub (himg (Set.mem_image_of_mem (q a) hyA))

private theorem smooth_codifferential {a : ActualChart (U := U) (H := H)}
    {W : omega a → E F} (hW : SmoothOnLift a W) :
    SmoothOnLift a (fun x => HyperbolicChart.codifferential (d F)
      (fun y => (CotangentLogCoframe.j (d F)).symm
        (if hy : y ∈ omega a then W ⟨y, hy⟩ else 0)) x.val) := by
  let Z : M F → HyperbolicChart.Cotangent (d F) := fun y =>
    (CotangentLogCoframe.j (d F)).symm
      (if hy : y ∈ omega a then W ⟨y, hy⟩ else 0)
  have hs (i : Fin (d F)) (k : Fin 3) :
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Z y i k) (omega a) := by
    obtain ⟨V, hV, he⟩ := hW
    have hcomp : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => V y (i, k)) (omega a) :=
      ((EuclideanSpace.proj (𝕜 := ℂ) (i, k)).restrictScalars ℝ).contDiff.comp_contDiffOn hV
    refine hcomp.congr ?_
    intro y hy
    simp only [Z, dif_pos hy]
    change W ⟨y, hy⟩ (i,k) = V y (i,k)
    rw [he ⟨y, hy⟩]
  have hcd (i : Fin (d F)) (k l : Fin 3) :
      ContDiffOn ℝ (⊤ : ℕ∞)
        (HyperbolicChart.coordinateDerivative (d F) i k (fun y => Z y i l)) (omega a) :=
    ((hs i l).fderiv_of_isOpen (isOpen_omega a) (m := (⊤ : ℕ∞)) (by simp)).clm_apply
      contDiffOn_const
  have hexp (i : Fin (d F)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : M F => (Real.exp (y (i, 2)) : ℂ)) (omega a) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).contDiff.exp.contDiffOn)
  refine ⟨fun y => HyperbolicChart.codifferential (d F) Z y, ?_, fun _ => rfl⟩
  apply ContDiffOn.sum
  intro i _
  exact ((((hcd i 2 0).neg.add (contDiffOn_const.mul (hs i 0))).sub
    ((hexp i).mul (hcd i 0 1))).sub ((hexp i).mul (hcd i 1 2)))

private theorem compact_cotangentSupport (W : T_U F ζ hζ U R P H) :
    IsCompact (cotangentSupport W.val) := by
  let g : KPFiniteCuspAtlas.rawXU F ζ hζ U → NNReal :=
    fun x => if x ∈ cotangentSupport W.val then normSquare W.val x else 0
  have hg : Measurable g := (measurable_normSquare W.val).piecewise
    isClosed_closure.measurableSet measurable_const
  have he : g = normSquare W.val :=
    (Classical.choose_spec (normSquare_descends W.val)).2 g ⟨hg, by
      intro a x
      by_cases hx : q a x.val ∈ cotangentSupport W.val
      · simp [g, hx, normSquare_chart]
      · have hz : coefficient W.val a x = 0 := by
          by_contra hn
          exact hx (subset_closure ⟨a, x, rfl, hn⟩)
        simp [g, hx, hz]⟩
  apply W.property.2.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro x ⟨a, y, hq, hn⟩
  rw [← hq, Function.mem_support, normSquare_chart]
  simpa using hn

 def tensorExtension (a : ActualChart (U := U) (H := H))
    (W : omega a → E F) : M F → E F :=
  fun y => if hy : y ∈ omega a then W ⟨y, hy⟩ else 0

 def positiveC (a : ActualChart (U := U) (H := H))
    (W : omega a → E F) : omega a → ℂ :=
  fun x => HyperbolicChart.codifferential (d F)
    ((CotangentLogCoframe.j (d F)).symm ∘ tensorExtension a W) x.val

private theorem smooth_tensorExtension {a : ActualChart (U := U) (H := H)}
    {W : omega a → E F} (hW : SmoothOnLift a W) (x : omega a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (tensorExtension a W) x.val := by
  obtain ⟨V, hV, he⟩ := hW
  have hmem := (isOpen_omega a).mem_nhds x.property
  have heq : tensorExtension a W =ᶠ[𝓝 x.val] V := by
    filter_upwards [hmem] with y hy
    simp only [tensorExtension, dif_pos hy]
    exact (he ⟨y, hy⟩).symm
  exact (hV.contDiffAt hmem).congr_of_eventuallyEq heq

private theorem codifferential_compatible (W : T_U F ζ hζ U R P H) :
    ScalarCompatible (fun a => positiveC a (coefficient W.val a)) := by
  refine ⟨?_, ?_⟩
  · intro a γ x hx
    exact actual_codifferential_arrow (isotropyArrow a γ)
      (tensorExtension a (coefficient W.val a)) (tensorExtension a (coefficient W.val a))
      x (omega_subset_larger a hx)
      (smooth_tensorExtension (W.property.1 a) ⟨x, hx⟩)
      (smooth_tensorExtension (W.property.1 a) ⟨_, isotropy_mem a γ x hx⟩)
      (by
        filter_upwards [(isOpen_omega a).mem_nhds hx] with y hy
        simp only [tensorExtension, dif_pos hy, dif_pos (isotropy_mem a γ y hy)]
        exact W.val.property.2.1 a γ y hy)
  · intro a b e x hx
    exact actual_codifferential_arrow e.arrow
      (tensorExtension a (coefficient W.val a)) (tensorExtension b (coefficient W.val b)) x hx
      (smooth_tensorExtension (W.property.1 a) ⟨x, e.source_shrinking hx⟩)
      (smooth_tensorExtension (W.property.1 b) ⟨_, e.target_shrinking hx⟩)
      (by
        filter_upwards [e.arrow.isOpen_domain.mem_nhds hx] with y hy
        simp only [tensorExtension, dif_pos (e.source_shrinking hy), dif_pos (e.target_shrinking hy)]
        exact W.val.property.2.2 a b e y hy)

theorem codifferential_closed (W : T_U F ζ hζ U R P H) :
    (fun a => positiveC a (coefficient W.val a)) ∈ scalarTests := by
  refine ⟨fun a => smooth_codifferential (W.property.1 a), codifferential_compatible W, ?_⟩
  exact (compact_cotangentSupport W).of_isClosed_subset isClosed_closure
    (codifferential_support_subset W)

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

end

end
