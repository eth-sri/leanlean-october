module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.LaplacianPairingInvariance

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSections.ChartEllipticity
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspDivergence.CutoffScalarFlux

public import DedekindZetaZeroFree.Geometry.Hyperbolic.Cotangent.DifferentialCoframe

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical Topology

namespace DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration
open KPMeanZeroWeightedEnergy HyperbolicChart

open _root_.DedekindZetaZeroFree.KPCompactGreenRadialIntegrability (laplacian_action_invariant)

theorem codifferential_star_mul (d : ℕ) (f : Space d → ℂ)
    (W : Space d → Cotangent d) (x : Space d)
    (hf : DifferentiableAt ℝ f x)
    (hW : ∀ i k, DifferentiableAt ℝ (fun q => W q i k) x) :
    codifferential d (fun q i k => star (f q) * W q i k) x =
      star (f x) * codifferential d W x - pairing d (differential d f x) (W x) := by
  have hm (i : Fin d) (j k : Fin 3) :
      coordinateDerivative d i j (fun q => star (f q) * W q i k) x =
        star (coordinateDerivative d i j f x) * W x i k +
          star (f x) * coordinateDerivative d i j (fun q => W q i k) x := by
    simpa [coordinateDerivative, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, Pi.mul_def, mul_comm, mul_left_comm, add_comm] using
      congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i j))
        ((hf.hasFDerivAt.star).mul (hW i k).hasFDerivAt).fderiv
  simp only [codifferential, pairing, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [hm, differential, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_def, Fin.succ_zero_eq_one, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

private theorem derivative_smoothAt (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) (i : Fin d) (k : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coordinateDerivative d i k g) x := (hg.fderiv_right (by simp)).clm_apply contDiffAt_const

private theorem exp_mul_derivative (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : DifferentiableAt ℝ g x) (i : Fin d) (k : Fin 3) (hk : k ≠ 2) :
    coordinateDerivative d i k (fun q => (Real.exp (q (i,2)) : ℂ) * g q) x =
      (Real.exp (x (i,2)) : ℂ) * coordinateDerivative d i k g x := by
  have he := Complex.ofRealCLM.hasFDerivAt.comp x
    ((EuclideanSpace.proj (𝕜 := ℝ) (i, (2 : Fin 3))).hasFDerivAt.exp)
  have hh := congrArg (fun A : Space d →L[ℝ] ℂ => A (coordinateVector d i k))
    (he.mul hg.hasFDerivAt).fderiv
  simpa [coordinateDerivative, coordinateVector, hk, Ne.symm hk, Pi.mul_def] using hh

theorem codifferential_differential_at (d : ℕ) (g : Space d → ℂ) (x : Space d)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    codifferential d (differential d g) x = laplacian d g x := by
  unfold codifferential laplacian
  apply Finset.sum_congr rfl
  intro i hi
  simp only [differential, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_def,
    Fin.succ_zero_eq_one]
  rw [exp_mul_derivative d _ x ((derivative_smoothAt d g x hg i 0).differentiableAt (by simp)) i 0 (by decide),
      exp_mul_derivative d _ x ((derivative_smoothAt d g x hg i 1).differentiableAt (by simp)) i 1 (by decide)]
  rw [show (Real.exp (2 * x (i, 2)) : ℂ) =
      (Real.exp (x (i, 2)) : ℂ) * (Real.exp (x (i, 2)) : ℂ) by
    rw [two_mul, Real.exp_add, Complex.ofReal_mul]]
  ring

open HyperbolicChart (differential_smoothAt)

open HyperbolicChart
private lemma differential_add (d : ℕ) (f g : Space d → ℂ) (x : Space d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    differential d (fun y => f y + g y) x = differential d f x + differential d g x := by
  have hfd : fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x + fderiv ℝ g x :=
    fderiv_add hf hg
  ext i k
  fin_cases k <;>
    (simp [differential, coordinateDerivative, hfd, Pi.add_apply, ContinuousLinearMap.add_apply]
     ; try ring)

private lemma two_mul_re_pairing (d : ℕ) (U W : Cotangent d) :
    2 * (pairing d U W).re =
      (∑ i, ∑ k, ‖(U + W) i k‖ ^ 2) - (∑ i, ∑ k, ‖U i k‖ ^ 2) -
        (∑ i, ∑ k, ‖W i k‖ ^ 2) := by
  have hterm : ∀ (i : Fin d) (k : Fin 3),
      2 * (star (U i k) * W i k).re =
        ‖(U + W) i k‖ ^ 2 - ‖U i k‖ ^ 2 - ‖W i k‖ ^ 2 := by
    intro i k
    have h1 : (star (U i k) * W i k).re =
        (U i k).re * (W i k).re + (U i k).im * (W i k).im := by
      simp [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have h2 : ‖(U + W) i k‖ ^ 2 =
        ‖U i k‖ ^ 2 + ‖W i k‖ ^ 2 +
          2 * ((U i k).re * (W i k).re + (U i k).im * (W i k).im) := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Pi.add_apply, Complex.add_re, Complex.add_im]
      ring
    rw [h1, h2]; ring
  have hre : (pairing d U W).re = ∑ i, ∑ k, (star (U i k) * W i k).re := by
    simp only [pairing]
    rw [← Complex.reCLM_apply]
    simp only [map_sum, Complex.reCLM_apply]
  calc 2 * (pairing d U W).re = 2 * (∑ i, ∑ k, (star (U i k) * W i k).re) := by rw [hre]
    _ = ∑ i, ∑ k, 2 * (star (U i k) * W i k).re := by
        simp only [Finset.mul_sum]
    _ = ∑ i, ∑ k, (‖(U + W) i k‖ ^ 2 - ‖U i k‖ ^ 2 - ‖W i k‖ ^ 2) := by
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro k _
        exact hterm i k
    _ = (∑ i, ∑ k, ‖(U + W) i k‖ ^ 2) - (∑ i, ∑ k, ‖U i k‖ ^ 2) -
          (∑ i, ∑ k, ‖W i k‖ ^ 2) := by
        simp only [Finset.sum_sub_distrib]

 def toCoord {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) : KPCuspCharts.Coordinates F :=
  (((fun i => (z i).1),
    ⟨KPCuspLogShape.shapeCoordinates (KPCuspLogShape.dimension F) z,
      KPCuspLogShape.shapeCoordinates_mem_hyperplane _
        (Nat.ne_of_gt hd) z⟩),
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z)

private theorem toArch_toCoord {F : Type} [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspCharts.toArch F (toCoord hd z) = z := by
  funext i
  simp [KPCuspCharts.toArch, toCoord, KPCuspLogShape.shapeCoordinates]

private theorem action_meanHeight
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (s : S) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) =
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z := by
  have hd := G.positive_dimension
  obtain ⟨A, hA, hA10⟩ := D.upper (s : KPCuspArithmetic.PGL2 F) s.2
  conv_lhs => rw [← toArch_toCoord hd z]
  rw [G.actual_action s A hA hA10 (toCoord hd z), KPCuspCharts.toArch_meanHeight F hd]
  rfl

private theorem u_action_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (s : S) (z : KPArch.Space (KPCuspLogShape.dimension F))
    (hz : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) :
    u (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) = u z := by
  have hd := G.positive_dimension
  set p' : {p : KPCuspCharts.Coordinates F // T < p.2} :=
    ⟨toCoord hd z, by
      change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z
      exact hz⟩ with hp'def
  have hsz : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z) := by
    rw [action_meanHeight G s z]; exact hz
  set q' : {p : KPCuspCharts.Coordinates F // T < p.2} :=
    ⟨toCoord hd (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z), by
      change T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z)
      exact hsz⟩ with hq'def
  have hrel : KPCuspCharts.highRelation F S T p' q' := by
    refine ⟨s⁻¹, ?_⟩
    show s⁻¹ • KPCuspCharts.toArch F q'.val = KPCuspCharts.toArch F p'.val
    rw [hq'def, hp'def]
    simp only [toArch_toCoord hd]
    change s⁻¹ • (s • z) = z
    rw [← mul_smul, inv_mul_cancel, one_smul]
  have hfin := hinv p' q' hrel
  simp only [hp'def, hq'def, toArch_toCoord hd] at hfin
  exact hfin.symm

private theorem pairing_re_invariant
    (d : ℕ) (g0 : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ)
    (Ac U : Space d → ℂ) (x : Space d)
    (hAcX : ContDiffAt ℝ (⊤ : ℕ∞) Ac x)
    (hAcY : ContDiffAt ℝ (⊤ : ℕ∞) Ac (real d (KPArch.productAction d g0 (arch d x))))
    (hUX : ContDiffAt ℝ (⊤ : ℕ∞) U x)
    (hUY : ContDiffAt ℝ (⊤ : ℕ∞) U (real d (KPArch.productAction d g0 (arch d x))))
    (hAceq : (Ac ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * Ac z)
    (hUeq : (U ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * U z) :
    (pairing d (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
        (differential d U (real d (KPArch.productAction d g0 (arch d x))))).re =
      (pairing d (differential d Ac x) (differential d U x)).re := by
  have hAUeq : ((fun z => Ac z + U z) ∘ fun z => real d (KPArch.productAction d g0 (arch d z)))
      =ᶠ[𝓝 x] fun z => (1 : ℂ) * (Ac z + U z) := by
    filter_upwards [hAceq, hUeq] with z h1 h2
    simp only [Function.comp_apply] at h1 h2 ⊢
    rw [h1, h2]; ring
  have hAUX : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Ac z + U z) x := hAcX.add hUX
  have hAUY : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => Ac z + U z)
      (real d (KPArch.productAction d g0 (arch d x))) := hAcY.add hUY
  have hSAU := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 (fun z => Ac z + U z) x 1
    (hAUX.differentiableAt (by simp)) (hAUY.differentiableAt (by simp)) hAUeq (by norm_num)
  have hSA := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 Ac x 1
    (hAcX.differentiableAt (by simp)) (hAcY.differentiableAt (by simp)) hAceq (by norm_num)
  have hSU := KPLocalizedFormGraph.ChartEnergyGeometry.differential_invariant d g0 U x 1
    (hUX.differentiableAt (by simp)) (hUY.differentiableAt (by simp)) hUeq (by norm_num)
  have hY := two_mul_re_pairing d
    (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
    (differential d U (real d (KPArch.productAction d g0 (arch d x))))
  have hXp := two_mul_re_pairing d (differential d Ac x) (differential d U x)
  have eY : differential d Ac (real d (KPArch.productAction d g0 (arch d x))) +
        differential d U (real d (KPArch.productAction d g0 (arch d x))) =
      differential d (fun z => Ac z + U z) (real d (KPArch.productAction d g0 (arch d x))) :=
    (differential_add d Ac U _ (hAcY.differentiableAt (by simp))
      (hUY.differentiableAt (by simp))).symm
  have eX : differential d Ac x + differential d U x =
      differential d (fun z => Ac z + U z) x :=
    (differential_add d Ac U _ (hAcX.differentiableAt (by simp))
      (hUX.differentiableAt (by simp))).symm
  rw [eY] at hY
  rw [eX] at hXp
  have h2 : 2 * (pairing d
        (differential d Ac (real d (KPArch.productAction d g0 (arch d x))))
        (differential d U (real d (KPArch.productAction d g0 (arch d x))))).re =
      2 * (pairing d (differential d Ac x) (differential d U x)).re := by
    have hSAU' : (∑ i, ∑ k, ‖differential d (fun z => Ac z + U z)
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d (fun z => Ac z + U z) x i k‖ ^ 2 := hSAU
    have hSA' : (∑ i, ∑ k, ‖differential d Ac
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d Ac x i k‖ ^ 2 := hSA
    have hSU' : (∑ i, ∑ k, ‖differential d U
          (real d (KPArch.productAction d g0 (arch d x))) i k‖ ^ 2) =
        ∑ i, ∑ k, ‖differential d U x i k‖ ^ 2 := hSU
    rw [hY, hXp, hSAU', hSA', hSU']
  exact mul_left_cancel₀ two_ne_zero h2

theorem cutoff_scalar_codifferential_high_orbit_invariant
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {T : ℝ} (u : KPArch.Space (KPCuspLogShape.dimension F) → ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u
      {z | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z})
    (hinv : ∀ p q : {p : KPCuspCharts.Coordinates F // T < p.2},
      KPCuspCharts.highRelation F S T p q →
      u (KPCuspCharts.toArch F p.val) = u (KPCuspCharts.toArch F q.val))
    (a : ℝ → ℝ) (ha : CompactRadialTest T a)
    (p q : {p : KPCuspCharts.Coordinates F // T < p.2})
    (hrel : KPCuspCharts.highRelation F S T p q) :
    (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val))).re =
    (codifferential (KPCuspLogShape.dimension F)
      (cutoffScalarFlux (KPCuspLogShape.dimension F) u a)
      (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val))).re := by
  have hd : 0 < KPCuspLogShape.dimension F := G.positive_dimension
  obtain ⟨s, hs⟩ := hrel
  obtain ⟨A, hA, _⟩ := D.upper (s : KPCuspArithmetic.PGL2 F) s.2
  let gC : Fin (KPCuspLogShape.dimension F) → Matrix.GeneralLinearGroup (Fin 2) ℂ :=
    fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A
  have hact : ∀ z, KPArch.productAction (KPCuspLogShape.dimension F) gC z =
      KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z := by
    intro z
    have h1 : KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) z =
        KPArch.productAction (KPCuspLogShape.dimension F) gC z := by
      rw [← hA, KPCuspSiegel.action_mk F A z]; rfl
    exact h1.symm
  set X : Space (KPCuspLogShape.dimension F) :=
    real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F q.val) with hXdef
  set Y : Space (KPCuspLogShape.dimension F) :=
    real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) X)) with hYdef
  have hs' : KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) (KPCuspCharts.toArch F q.val) =
      KPCuspCharts.toArch F p.val := hs
  have hYX : Y = real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p.val) := by
    rw [hYdef, hXdef, KPMeanZeroWeightedEnergy.arch_real_eq, hact, hs']
  have harchX : arch (KPCuspLogShape.dimension F) X = KPCuspCharts.toArch F q.val := by
    rw [hXdef, KPMeanZeroWeightedEnergy.arch_real_eq]
  have harchY : arch (KPCuspLogShape.dimension F) Y = KPCuspCharts.toArch F p.val := by
    rw [hYX, KPMeanZeroWeightedEnergy.arch_real_eq]
  rw [← hYX]
  let U : Space (KPCuspLogShape.dimension F) → ℂ :=
    fun z => (u (arch (KPCuspLogShape.dimension F) z) : ℂ)
  let Ac : Space (KPCuspLogShape.dimension F) → ℂ :=
    fun z => (a (KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z)) : ℂ)
  have hflux : cutoffScalarFlux (KPCuspLogShape.dimension F) u a =
      fun q i k => star (Ac q) * differential (KPCuspLogShape.dimension F) U q i k := by
    funext q i k
    simp only [cutoffScalarFlux, scalarDifferential, U, Ac, Complex.star_def,
      Complex.conj_ofReal]
  have hXh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) X) := by
    rw [harchX, KPCuspCharts.toArch_meanHeight F hd]; exact q.2
  have hYh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) Y) := by
    rw [harchY, KPCuspCharts.toArch_meanHeight F hd]; exact p.2
  have hmeanOpen : IsOpen {z : Space (KPCuspLogShape.dimension F) |
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
        (arch (KPCuspLogShape.dimension F) z)} :=
    isOpen_lt continuous_const ((KPMeanZeroWeightedEnergy.meanHeight_contDiff _).continuous.comp (KPMeanZeroWeightedEnergy.arch_contDiff _).continuous)
  have hN : ∀ᶠ z in 𝓝 X, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z) := hmeanOpen.mem_nhds hXh
  have hU_at : ∀ z, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (arch (KPCuspLogShape.dimension F) z) → ContDiffAt ℝ (⊤ : ℕ∞) U z := fun z hz => by
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((hu.contDiffAt ((isOpen_lt continuous_const (KPMeanZeroWeightedEnergy.meanHeight_contDiff _).continuous).mem_nhds
        hz)).comp z (KPMeanZeroWeightedEnergy.arch_contDiff _).contDiffAt)
  have hAc_at : ∀ z, ContDiffAt ℝ (⊤ : ℕ∞) Ac z := fun z =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((ha.1.comp ((KPMeanZeroWeightedEnergy.meanHeight_contDiff _).comp (KPMeanZeroWeightedEnergy.arch_contDiff _))).contDiffAt)
  have hUX := hU_at X hXh
  have hUY := hU_at Y hYh
  have hAcX := hAc_at X
  have hAcY := hAc_at Y
  have hAceq : (Ac ∘ fun z => real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) z)))
      =ᶠ[𝓝 X] fun z => (1 : ℂ) * Ac z := by
    filter_upwards with z
    dsimp only [Function.comp_apply, Ac]
    rw [one_mul, KPMeanZeroWeightedEnergy.arch_real_eq, hact, action_meanHeight G s]
  have hUeq : (U ∘ fun z => real (KPCuspLogShape.dimension F)
      (KPArch.productAction (KPCuspLogShape.dimension F) gC
        (arch (KPCuspLogShape.dimension F) z)))
      =ᶠ[𝓝 X] fun z => (1 : ℂ) * U z := by
    filter_upwards [hN] with z hz
    dsimp only [Function.comp_apply, U]
    rw [one_mul, KPMeanZeroWeightedEnergy.arch_real_eq, hact]
    exact congrArg (fun r : ℝ => (r : ℂ)) (u_action_invariant G u hinv s
      (arch (KPCuspLogShape.dimension F) z) hz)
  have hAcYX : Ac Y = Ac X := by
    rw [hYdef]
    dsimp only [Ac]
    rw [KPMeanZeroWeightedEnergy.arch_real_eq, hact, action_meanHeight G s]
  have hlap : laplacian (KPCuspLogShape.dimension F) U Y =
      laplacian (KPCuspLogShape.dimension F) U X := by
    have h := laplacian_action_invariant (KPCuspLogShape.dimension F) gC U X 1 hUeq hUX hUY
    rw [← hYdef] at h
    simpa using h
  have hpair := pairing_re_invariant (KPCuspLogShape.dimension F) gC Ac U X
    hAcX hAcY hUX hUY hAceq hUeq
  have hcod (z : Space (KPCuspLogShape.dimension F))
      (hAc : ContDiffAt ℝ (⊤ : ℕ∞) Ac z) (hUz : ContDiffAt ℝ (⊤ : ℕ∞) U z) :
      (codifferential (KPCuspLogShape.dimension F)
        (cutoffScalarFlux (KPCuspLogShape.dimension F) u a) z).re =
        (star (Ac z) * laplacian (KPCuspLogShape.dimension F) U z -
          pairing (KPCuspLogShape.dimension F)
            (differential (KPCuspLogShape.dimension F) Ac z)
            (differential (KPCuspLogShape.dimension F) U z)).re := by
    rw [hflux, codifferential_star_mul _ Ac (differential _ U) z
      (hAc.differentiableAt (by simp))
      (fun i k => (differential_smoothAt _ U z hUz i k).differentiableAt (by simp)),
      codifferential_differential_at _ U z hUz]
  rw [hcod Y hAcY hUY, hcod X hAcX hUX, hAcYX, hlap, Complex.sub_re, Complex.sub_re, hpair]

end DedekindZetaZeroFree.KPCompactGreen.ScalarFluxDisintegration

end
