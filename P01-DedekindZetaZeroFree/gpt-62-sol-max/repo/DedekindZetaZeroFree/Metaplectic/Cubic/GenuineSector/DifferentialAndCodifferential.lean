module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.CoframeCalculus
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.MetricCodifferentialDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescent

open KPContActualSectorSmoothTestModules KPContActualCotangentCountableShrinking
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy
open KPContCotangentOverlapRationalBranches KPContActualCotangentMeasurableFamilies

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

def liftExtension {W : Type*} [Zero W] (a : ActualChart (U := U) (H := H))
    (f : omega a → W) (x : M F) : W :=
  if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

def chartDifferential (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ)
    (x : omega a) : E F :=
  CotangentLogCoframe.j (d F)
    (HyperbolicChart.differential (d F) (liftExtension a f) x.val)

def chartCodifferential (a : ActualChart (U := U) (H := H)) (W : omega a → E F)
    (x : omega a) : ℂ :=
  HyperbolicChart.codifferential (d F)
    (fun y => (CotangentLogCoframe.j (d F)).symm (liftExtension a W y)) x.val

 theorem differential_descent (f : S_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a => chartDifferential a (f.val a)) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a => chartDifferential a (f.val a)),
      (⟨fun a => chartDifferential a (f.val a), hv⟩ : Family (U := U) (H := H)) ∈
        cotangentTests ∧
      cotangentSupport ⟨fun a => chartDifferential a (f.val a), hv⟩ ⊆
        scalarSupport f.val := by
  exact KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.1 f

 theorem chart_differential_add (a : ActualChart (U := U) (H := H))
    (f g : omega a → ℂ) (hf : SmoothOnLift a f) (hg : SmoothOnLift a g) :
    chartDifferential a (f + g) = chartDifferential a f + chartDifferential a g := by
  exact KPContActualSectorTestDifferentialDescentCalculus.ZD_add a f g hf hg

 theorem chart_differential_smul (a : ActualChart (U := U) (H := H))
    (c : ℂ) (f : omega a → ℂ) (hf : SmoothOnLift a f) :
    chartDifferential a (c • f) = c • chartDifferential a f := by
  exact KPContActualSectorTestDifferentialDescentCalculus.ZD_smul a c f hf

def D_U : S_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun f := ⟨⟨fun a => chartDifferential a (f.val a), (differential_descent f).1⟩,
    ((differential_descent f).2 _).1⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact chart_differential_add a (f.val a) (g.val a) (f.property.1 a) (g.property.1 a)
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact chart_differential_smul a c (f.val a) (f.property.1 a)

 theorem codifferential_descent (W : T_U F ζ hζ U R P H) :
    (fun a => chartCodifferential a (coefficient W.val a)) ∈ scalarTests ∧
    scalarSupport (fun a => chartCodifferential a (coefficient W.val a)) ⊆
      cotangentSupport W.val := by
  exact ⟨KPContActualSectorTestDifferentialDescentCalculus.codifferential_closed W,
    KPContActualSectorTestDifferentialDescentCalculus.codifferential_support_subset W⟩

 theorem chart_codifferential_add (a : ActualChart (U := U) (H := H))
    (V W : omega a → E F) (hV : SmoothOnLift a V) (hW : SmoothOnLift a W) :
    chartCodifferential a (V + W) = chartCodifferential a V + chartCodifferential a W := by
  exact KPContActualSectorTestDifferentialDescentCalculus.ZC_add a V W hV hW

 theorem chart_codifferential_smul (a : ActualChart (U := U) (H := H))
    (c : ℂ) (W : omega a → E F) (hW : SmoothOnLift a W) :
    chartCodifferential a (c • W) = c • chartCodifferential a W := by
  exact KPContActualSectorTestDifferentialDescentCalculus.ZC_smul a c W hW

def δ_U : T_U F ζ hζ U R P H →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun W := ⟨fun a => chartCodifferential a (coefficient W.val a),
    (codifferential_descent W).1⟩
  map_add' V W := by
    apply Subtype.ext
    funext a
    exact chart_codifferential_add a (coefficient V.val a) (coefficient W.val a)
      (V.property.1 a) (W.property.1 a)
  map_smul' c W := by
    apply Subtype.ext
    funext a
    exact chart_codifferential_smul a c (coefficient W.val a) (W.property.1 a)

structure RealSmoothCutoff (F : Type) [Field F] [NumberField F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 12) (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) where
  val : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  smooth : ∀ a : ActualChart (U := U) (H := H),
    SmoothOnLift a (fun x => val (q a x.val))

theorem RealSmoothCutoff.continuous (η : RealSmoothCutoff F ζ hζ U R P H) : Continuous η.val := by
  apply KPContActualCotangentPieceHilbertSum.continuous_of_chart_lifts
  intro a
  obtain ⟨g, hg, he⟩ := η.smooth a
  convert hg.continuousOn.domRestrict using 1
  exact funext (fun y => (he y).symm)

def cutoffLift (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) : ℂ :=
  (η.val (q a x.val) : ℂ)

def cutoffDifferential (η : RealSmoothCutoff F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) : E F :=
  chartDifferential a (cutoffLift η a) x

 theorem cutoff_scalar_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    (fun a x => cutoffLift η a x * f.val a x) ∈ scalarTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).1 f

 theorem cutoff_tensor_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (W : T_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W.val a x) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a x => cutoffLift η a x • coefficient W.val a x),
      (⟨fun a x => cutoffLift η a x • coefficient W.val a x, hv⟩ :
        Family (U := U) (H := H)) ∈ cotangentTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).2.1 W

 theorem cutoff_gradient_mem (η : RealSmoothCutoff F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    IsMeasurableCotangentFamily (fun a x => f.val a x • cutoffDifferential η a x) ∧
    ∀ hv : IsMeasurableCotangentFamily (fun a x => f.val a x • cutoffDifferential η a x),
      (⟨fun a x => f.val a x • cutoffDifferential η a x, hv⟩ :
        Family (U := U) (H := H)) ∈ cotangentTests := by
  exact (KPContActualSectorTestDifferentialDescentCalculus.scalar_differential_descent.2
    η.val η.smooth).2.2 f

def scalarMultiply (η : RealSmoothCutoff F ζ hζ U R P H) :
    S_U F ζ hζ U R P H →ₗ[ℂ] S_U F ζ hζ U R P H where
  toFun f := ⟨fun a x => cutoffLift η a x * f.val a x, cutoff_scalar_mem η f⟩
  map_add' f g := by
    apply Subtype.ext
    funext a x
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext a x
    change cutoffLift η a x * (c * f.val a x) = c * (cutoffLift η a x * f.val a x)
    ring

def cotangentMultiply (η : RealSmoothCutoff F ζ hζ U R P H) :
    T_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun W := ⟨⟨fun a x => cutoffLift η a x • coefficient W.val a x,
    (cutoff_tensor_mem η W).1⟩, (cutoff_tensor_mem η W).2 _⟩
  map_add' V W := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact smul_add _ _ _
  map_smul' c W := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact smul_comm (cutoffLift η a x) c (coefficient W.val a x)

def cutoffGradientTimes (η : RealSmoothCutoff F ζ hζ U R P H) :
    S_U F ζ hζ U R P H →ₗ[ℂ] T_U F ζ hζ U R P H where
  toFun f := ⟨⟨fun a x => f.val a x • cutoffDifferential η a x,
    (cutoff_gradient_mem η f).1⟩, (cutoff_gradient_mem η f).2 _⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact add_smul _ _ _
  map_smul' c f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a x
    exact mul_smul _ _ _

theorem differential_chart (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    coefficient (D_U f).val a x = chartDifferential a (f.val a) x := rfl

theorem differential_support (f : S_U F ζ hζ U R P H) :
    cotangentSupport (D_U f).val ⊆ scalarSupport f.val :=
  ((differential_descent f).2 _).2

theorem codifferential_support (W : T_U F ζ hζ U R P H) :
    scalarSupport (δ_U W).val ⊆ cotangentSupport W.val :=
  (codifferential_descent W).2

theorem laplacian_chart (f : S_U F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    (δ_U (D_U f)).val a x =
      HyperbolicChart.laplacian (d F) (liftExtension a (f.val a)) x.val :=
  KPContActualSectorTestDifferentialDescentCalculus.ZC_ZD a (f.val a) (f.property.1 a) x

theorem differential_product (η : RealSmoothCutoff F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    D_U (scalarMultiply η f) = cotangentMultiply η (D_U f) + cutoffGradientTimes η f := by
  apply Subtype.ext
  apply Subtype.ext
  funext a x
  exact KPContActualSectorTestDifferentialDescentCalculus.ZD_mul
    a (fun y => η.val (q a y.val)) (f.val a) (η.smooth a) (f.property.1 a) x

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescent

end
