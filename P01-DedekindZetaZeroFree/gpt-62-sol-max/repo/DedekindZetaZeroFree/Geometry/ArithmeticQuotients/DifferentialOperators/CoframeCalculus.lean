module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.RadialGreenIdentity
public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.DifferentialOperators.ScalarDifferentialDescent

@[expose] public section

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

 def zext (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : M F → ℂ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

 def rext (a : ActualChart (U := U) (H := H)) (f : omega a → ℝ) : M F → ℝ :=
  fun x => if hx : x ∈ omega a then f ⟨x, hx⟩ else 0

private theorem contDiffAt_zext {a : ActualChart (U := U) (H := H)} {f : omega a → ℂ}
    (hf : SmoothOnLift a f) (x : omega a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (zext a f) x.val :=
  (smooth_zext hf).contDiffAt ((isOpen_omega a).mem_nhds x.property)

private theorem contDiffAt_rext {a : ActualChart (U := U) (H := H)} {f : omega a → ℝ}
    (hf : SmoothOnLift a f) (x : omega a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (rext a f) x.val := by
  obtain ⟨g, hg, hge⟩ := hf
  have hmem := (isOpen_omega a).mem_nhds x.2
  have heq : rext a f =ᶠ[𝓝 x.val] g := by
    filter_upwards [hmem] with y hy
    simp only [rext, dif_pos hy]
    simp_all
  exact (hg.contDiffAt hmem).congr_of_eventuallyEq heq

private lemma zext_add (a : ActualChart (U := U) (H := H)) (f g : omega a → ℂ) :
    zext a (f + g) = zext a f + zext a g := by
  funext y; by_cases hy : y ∈ omega a <;> simp [zext, hy]

private lemma zext_smul (a : ActualChart (U := U) (H := H)) (c : ℂ) (f : omega a → ℂ) :
    zext a (c • f) = c • zext a f := by
  funext y; by_cases hy : y ∈ omega a <;> simp [zext, hy]

private lemma zext_ofReal (a : ActualChart (U := U) (H := H)) (η : omega a → ℝ) :
    zext a (fun y => (η y : ℂ)) = fun y => ((rext a η) y : ℂ) := by
  funext y; by_cases hy : y ∈ omega a <;> simp [zext, rext, hy]

private lemma differential_add (d : ℕ) (φ ψ : HyperbolicChart.Space d → ℂ)
    (p : HyperbolicChart.Space d) (hφ : DifferentiableAt ℝ φ p) (hψ : DifferentiableAt ℝ ψ p) :
    HyperbolicChart.differential d (φ + ψ) p =
      HyperbolicChart.differential d φ p + HyperbolicChart.differential d ψ p := by
  funext i k
  have h1 : ∀ k, HyperbolicChart.coordinateDerivative d i k (φ + ψ) p =
      HyperbolicChart.coordinateDerivative d i k φ p +
        HyperbolicChart.coordinateDerivative d i k ψ p := by
    intro k
    simp only [HyperbolicChart.coordinateDerivative, fderiv_add hφ hψ,
      ContinuousLinearMap.add_apply]
  fin_cases k <;> simp [HyperbolicChart.differential, h1, mul_add]

private lemma differential_smul (d : ℕ) (c : ℂ) (φ : HyperbolicChart.Space d → ℂ)
    (p : HyperbolicChart.Space d) (hφ : DifferentiableAt ℝ φ p) :
    HyperbolicChart.differential d (c • φ) p = c • HyperbolicChart.differential d φ p := by
  funext i k
  have h1 : ∀ k, HyperbolicChart.coordinateDerivative d i k (c • φ) p =
      c * HyperbolicChart.coordinateDerivative d i k φ p := by
    intro k
    simp only [HyperbolicChart.coordinateDerivative, fderiv_const_smul hφ,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
  fin_cases k <;> simp [HyperbolicChart.differential, h1] <;> ring

private lemma differential_mul (d : ℕ) (φ ψ : HyperbolicChart.Space d → ℂ)
    (p : HyperbolicChart.Space d) (hφ : DifferentiableAt ℝ φ p) (hψ : DifferentiableAt ℝ ψ p) :
    HyperbolicChart.differential d (φ * ψ) p =
      φ p • HyperbolicChart.differential d ψ p + ψ p • HyperbolicChart.differential d φ p := by
  funext i k
  have h1 : ∀ k, HyperbolicChart.coordinateDerivative d i k (φ * ψ) p =
      φ p * HyperbolicChart.coordinateDerivative d i k ψ p +
        ψ p * HyperbolicChart.coordinateDerivative d i k φ p := by
    intro k
    simp only [HyperbolicChart.coordinateDerivative, fderiv_mul hφ hψ,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Pi.mul_apply, smul_eq_mul]
  fin_cases k <;> simp [HyperbolicChart.differential, h1] <;> ring_nf

 def zcot (a : ActualChart (U := U) (H := H)) (W : omega a → E F) :
    M F → HyperbolicChart.Cotangent (d F) :=
  fun y => (CotangentLogCoframe.j (d F)).symm (if hy : y ∈ omega a then W ⟨y, hy⟩ else 0)

 def ZD (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ) : omega a → E F :=
  fun x => CotangentLogCoframe.j (d F) (HyperbolicChart.differential (d F) (zext a f) x.val)

 def ZC (a : ActualChart (U := U) (H := H)) (W : omega a → E F) : omega a → ℂ :=
  fun x => HyperbolicChart.codifferential (d F) (zcot a W) x.val

private lemma zcot_apply_eq_zext (a : ActualChart (U := U) (H := H)) (W : omega a → E F)
    (i : Fin (d F)) (k : Fin 3) :
    (fun q => zcot a W q i k) = zext a (fun y => W y (i,k)) := by
  funext q; by_cases hq : q ∈ omega a
  · simp only [zcot, zext, dif_pos hq]; rfl
  · simp [zcot, zext, dif_neg hq]

private theorem smoothOnLift_component {a : ActualChart (U := U) (H := H)} {W : omega a → E F}
    (hW : SmoothOnLift a W) (i : Fin (d F)) (k : Fin 3) :
    SmoothOnLift a (fun y => W y (i,k)) := by
  obtain ⟨G, hG, hGe⟩ := hW
  refine ⟨fun y => G y (i,k), ?_, ?_⟩
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (i,k)).restrictScalars ℝ).contDiff.comp_contDiffOn hG
  · intro y; show (G y.val) (i,k) = (W y) (i,k); rw [hGe y]

private lemma codifferential_congr (d : ℕ)
    {W W' : HyperbolicChart.Space d → HyperbolicChart.Cotangent d}
    {p : HyperbolicChart.Space d} (h : W =ᶠ[𝓝 p] W') :
    HyperbolicChart.codifferential d W p = HyperbolicChart.codifferential d W' p := by
  simp only [HyperbolicChart.codifferential, HyperbolicChart.coordinateDerivative]
  apply Finset.sum_congr rfl
  intro i hi
  have h0 : (fun q => W q i 0) =ᶠ[𝓝 p] (fun q => W' q i 0) :=
    h.mono fun q hq => by show W q i 0 = W' q i 0; rw [hq]
  have h1 : (fun q => W q i 1) =ᶠ[𝓝 p] (fun q => W' q i 1) :=
    h.mono fun q hq => by show W q i 1 = W' q i 1; rw [hq]
  have h2 : (fun q => W q i 2) =ᶠ[𝓝 p] (fun q => W' q i 2) :=
    h.mono fun q hq => by show W q i 2 = W' q i 2; rw [hq]
  rw [h0.fderiv_eq, h1.fderiv_eq, h2.fderiv_eq, h.self_of_nhds]

private lemma coordinateDerivative_add (d : ℕ) (i : Fin d) (k : Fin 3)
    (f g : HyperbolicChart.Space d → ℂ) (p : HyperbolicChart.Space d)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    HyperbolicChart.coordinateDerivative d i k (f + g) p =
      HyperbolicChart.coordinateDerivative d i k f p +
        HyperbolicChart.coordinateDerivative d i k g p := by
  simp only [HyperbolicChart.coordinateDerivative, fderiv_add hf hg, ContinuousLinearMap.add_apply]

private lemma coordinateDerivative_smul (d : ℕ) (i : Fin d) (k : Fin 3) (c : ℂ)
    (f : HyperbolicChart.Space d → ℂ) (p : HyperbolicChart.Space d)
    (hf : DifferentiableAt ℝ f p) :
    HyperbolicChart.coordinateDerivative d i k (c • f) p =
      c * HyperbolicChart.coordinateDerivative d i k f p := by
  simp only [HyperbolicChart.coordinateDerivative, fderiv_const_smul hf,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma codifferential_add (d : ℕ)
    (A B : HyperbolicChart.Space d → HyperbolicChart.Cotangent d) (p : HyperbolicChart.Space d)
    (hA : ∀ i k, DifferentiableAt ℝ (fun q => A q i k) p)
    (hB : ∀ i k, DifferentiableAt ℝ (fun q => B q i k) p) :
    HyperbolicChart.codifferential d (A + B) p =
      HyperbolicChart.codifferential d A p + HyperbolicChart.codifferential d B p := by
  simp only [HyperbolicChart.codifferential]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : HyperbolicChart.coordinateDerivative d i 2 (fun q => (A + B) q i 0) p =
      HyperbolicChart.coordinateDerivative d i 2 (fun q => A q i 0) p +
        HyperbolicChart.coordinateDerivative d i 2 (fun q => B q i 0) p := by
    rw [show (fun q => (A + B) q i 0) = (fun q => A q i 0) + (fun q => B q i 0) from by
      funext q; rfl]
    exact coordinateDerivative_add d i 2 _ _ p (hA i 0) (hB i 0)
  have h1 : HyperbolicChart.coordinateDerivative d i 0 (fun q => (A + B) q i 1) p =
      HyperbolicChart.coordinateDerivative d i 0 (fun q => A q i 1) p +
        HyperbolicChart.coordinateDerivative d i 0 (fun q => B q i 1) p := by
    rw [show (fun q => (A + B) q i 1) = (fun q => A q i 1) + (fun q => B q i 1) from by
      funext q; rfl]
    exact coordinateDerivative_add d i 0 _ _ p (hA i 1) (hB i 1)
  have h2 : HyperbolicChart.coordinateDerivative d i 1 (fun q => (A + B) q i 2) p =
      HyperbolicChart.coordinateDerivative d i 1 (fun q => A q i 2) p +
        HyperbolicChart.coordinateDerivative d i 1 (fun q => B q i 2) p := by
    rw [show (fun q => (A + B) q i 2) = (fun q => A q i 2) + (fun q => B q i 2) from by
      funext q; rfl]
    exact coordinateDerivative_add d i 1 _ _ p (hA i 2) (hB i 2)
  have hmid : (A + B) p i 0 = A p i 0 + B p i 0 := rfl
  rw [h0, h1, h2, hmid]; ring

private lemma codifferential_smul (d : ℕ) (c : ℂ)
    (A : HyperbolicChart.Space d → HyperbolicChart.Cotangent d) (p : HyperbolicChart.Space d)
    (hA : ∀ i k, DifferentiableAt ℝ (fun q => A q i k) p) :
    HyperbolicChart.codifferential d (c • A) p = c * HyperbolicChart.codifferential d A p := by
  simp only [HyperbolicChart.codifferential]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : HyperbolicChart.coordinateDerivative d i 2 (fun q => (c • A) q i 0) p =
      c * HyperbolicChart.coordinateDerivative d i 2 (fun q => A q i 0) p := by
    rw [show (fun q => (c • A) q i 0) = c • (fun q => A q i 0) from by funext q; rfl]
    exact coordinateDerivative_smul d i 2 c _ p (hA i 0)
  have h1 : HyperbolicChart.coordinateDerivative d i 0 (fun q => (c • A) q i 1) p =
      c * HyperbolicChart.coordinateDerivative d i 0 (fun q => A q i 1) p := by
    rw [show (fun q => (c • A) q i 1) = c • (fun q => A q i 1) from by funext q; rfl]
    exact coordinateDerivative_smul d i 0 c _ p (hA i 1)
  have h2 : HyperbolicChart.coordinateDerivative d i 1 (fun q => (c • A) q i 2) p =
      c * HyperbolicChart.coordinateDerivative d i 1 (fun q => A q i 2) p := by
    rw [show (fun q => (c • A) q i 2) = c • (fun q => A q i 2) from by funext q; rfl]
    exact coordinateDerivative_smul d i 1 c _ p (hA i 2)
  have hmid : (c • A) p i 0 = c * (A p i 0) := rfl
  rw [h0, h1, h2, hmid]; ring

private lemma zcot_apply (a : ActualChart (U := U) (H := H)) (W : omega a → E F)
    (y : M F) (hy : y ∈ omega a) :
    zcot a W y = (CotangentLogCoframe.j (d F)).symm (W ⟨y, hy⟩) := by
  simp only [zcot, dif_pos hy]

theorem ZD_add (a : ActualChart (U := U) (H := H)) (f g : omega a → ℂ)
    (hf : SmoothOnLift a f) (hg : SmoothOnLift a g) :
    ZD a (f + g) = ZD a f + ZD a g := by
  funext x
  simp only [ZD, Pi.add_apply]
  rw [zext_add, differential_add (d F) (zext a f) (zext a g) x.val
      ((contDiffAt_zext hf x).differentiableAt (by simp))
      ((contDiffAt_zext hg x).differentiableAt (by simp)),
    map_add]

theorem ZD_smul (a : ActualChart (U := U) (H := H)) (c : ℂ) (f : omega a → ℂ)
    (hf : SmoothOnLift a f) :
    ZD a (c • f) = c • ZD a f := by
  funext x
  simp only [ZD, Pi.smul_apply]
  rw [zext_smul, differential_smul (d F) c (zext a f) x.val
      ((contDiffAt_zext hf x).differentiableAt (by simp)),
    map_smul]

theorem ZC_add (a : ActualChart (U := U) (H := H)) (V W : omega a → E F)
    (hV : SmoothOnLift a V) (hW : SmoothOnLift a W) :
    ZC a (V + W) = ZC a V + ZC a W := by
  have hzw : zcot a (V + W) = zcot a V + zcot a W := by
    funext y
    by_cases hy : y ∈ omega a
    · rw [Pi.add_apply, zcot_apply a (V + W) y hy, zcot_apply a V y hy,
        zcot_apply a W y hy,
        show (V + W) ⟨y, hy⟩ = V ⟨y, hy⟩ + W ⟨y, hy⟩ from rfl, map_add]
    · simp only [zcot, dif_neg hy, Pi.add_apply]; simp
  funext x
  simp only [ZC, Pi.add_apply]
  rw [hzw]
  exact codifferential_add (d F) (zcot a V) (zcot a W) x.val
    (fun i k => by
      rw [zcot_apply_eq_zext]
      exact (contDiffAt_zext (smoothOnLift_component hV i k) x).differentiableAt (by simp))
    (fun i k => by
      rw [zcot_apply_eq_zext]
      exact (contDiffAt_zext (smoothOnLift_component hW i k) x).differentiableAt (by simp))

theorem ZC_smul (a : ActualChart (U := U) (H := H)) (c : ℂ) (W : omega a → E F)
    (hW : SmoothOnLift a W) :
    ZC a (c • W) = c • ZC a W := by
  have hzw : zcot a (c • W) = c • zcot a W := by
    funext y
    by_cases hy : y ∈ omega a
    · rw [Pi.smul_apply, zcot_apply a (c • W) y hy, zcot_apply a W y hy,
        show (c • W) ⟨y, hy⟩ = c • W ⟨y, hy⟩ from rfl, map_smul]
    · simp only [zcot, dif_neg hy, Pi.smul_apply]; simp
  funext x
  simp only [ZC, Pi.smul_apply]
  rw [hzw]
  exact codifferential_smul (d F) c (zcot a W) x.val
    (fun i k => by
      rw [zcot_apply_eq_zext]
      exact (contDiffAt_zext (smoothOnLift_component hW i k) x).differentiableAt (by simp))

theorem ZC_ZD (a : ActualChart (U := U) (H := H)) (f : omega a → ℂ)
    (hf : SmoothOnLift a f) (x : omega a) :
    ZC a (ZD a f) x = HyperbolicChart.laplacian (d F) (zext a f) x.val := by
  have hmem : omega a ∈ 𝓝 x.val := (isOpen_omega a).mem_nhds x.2
  have hΨ : zcot a (ZD a f) = fun y : M F =>
      if hy : y ∈ omega a then HyperbolicChart.differential (d F) (zext a f) y else 0 := by
    funext y
    by_cases hy : y ∈ omega a
    · rw [zcot_apply a (ZD a f) y hy, ZD, LinearEquiv.symm_apply_apply, dif_pos hy]
    · simp [zcot, dif_neg hy]
  have heq : (fun y : M F => if hy : y ∈ omega a then
        HyperbolicChart.differential (d F) (zext a f) y else 0)
      =ᶠ[𝓝 x.val] HyperbolicChart.differential (d F) (zext a f) := by
    filter_upwards [hmem] with y hy
    exact dif_pos hy
  simp only [ZC, hΨ]
  rw [codifferential_congr (d F) heq]
  exact KPCompactGreen.GreenFlux.codifferential_differential_at (d F) (zext a f) x.val
    (contDiffAt_zext hf x)

theorem ZD_mul (a : ActualChart (U := U) (H := H)) (η : omega a → ℝ) (f : omega a → ℂ)
    (hη : SmoothOnLift a η) (hf : SmoothOnLift a f) (x : omega a) :
    ZD a (fun y => (η y : ℂ) * f y) x =
      (η x : ℂ) • ZD a f x + f x • ZD a (fun y => (η y : ℂ)) x := by
  have hdη : DifferentiableAt ℝ (rext a η) x.val := (contDiffAt_rext hη x).differentiableAt (by simp)
  have hdηc : DifferentiableAt ℝ (fun y => ((rext a η) y : ℂ)) x.val :=
    Complex.ofRealCLM.differentiableAt.comp x.val hdη
  have hdf : DifferentiableAt ℝ (zext a f) x.val := (contDiffAt_zext hf x).differentiableAt (by simp)
  have hze : zext a (fun y => (η y : ℂ) * f y) =
      (fun y => ((rext a η) y : ℂ)) * zext a f := by
    funext y; by_cases hy : y ∈ omega a <;> simp [zext, rext, hy]
  simp only [ZD]
  rw [hze, zext_ofReal,
    differential_mul (d F) (fun y => ((rext a η) y : ℂ)) (zext a f) x.val hdηc hdf,
    map_add, map_smul, map_smul]
  simp only [zext, rext, dif_pos x.2]

end DedekindZetaZeroFree.KPContActualSectorTestDifferentialDescentCalculus

end
