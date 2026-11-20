module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Iwasawa.FieldJets
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.IsometryNaturality

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped Matrix.Norms.Operator Classical
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric
open KPSmoothActualFlowData
open KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.NormalCoefficient (matrix_path_components normSq_hasDerivAt)
open _root_.DedekindZetaZeroFree.KPMsGreenFlux.FramedConormal.NativeShellStokes.IwasawaFieldJets (horizontalNumerator_hasDerivAt bottomDenominator_hasDerivAt)

 abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ
 def curve (i : Fin 6) (t : ℝ) : Mat := NormedSpace.exp ((t : ℂ) • basisMatrix i)

private theorem curve_entries (i : Fin 6) (r s : Fin 2) :
    HasDerivAt (fun t : ℝ => curve i t r s) (basisMatrix i r s) 0 := by
  simpa [curve] using matrix_path_components (1 : Mat) (basisMatrix i) r s

section

variable (i j : Fin 6)

private theorem curve_mul_entries (r s : Fin 2) :
    HasDerivAt (fun t : ℝ => (curve i t * basisMatrix j) r s)
      ((basisMatrix i * basisMatrix j) r s) 0 := by
  convert ((curve_entries i r 0).mul_const (basisMatrix j 0 s)).add
      ((curve_entries i r 1).mul_const (basisMatrix j 1 s)) using 1 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.add_apply] <;> rfl

 def numeratorSecond : ℂ :=
  (basisMatrix j 0 0) * star (basisMatrix i 1 0) +
    (basisMatrix i 0 0) * star (basisMatrix j 1 0) +
    star ((basisMatrix i * basisMatrix j) 1 0) +
    (basisMatrix i * basisMatrix j) 0 1 +
    basisMatrix j 0 1 * star (basisMatrix i 1 1) +
    basisMatrix i 0 1 * star (basisMatrix j 1 1)

private theorem numerator_second :
    HasDerivAt (fun t => horizontalNumeratorJet (curve i t) j)
      (numeratorSecond i j) 0 := by
  have h := curve_entries i
  have k := curve_mul_entries i j
  convert ((((k 0 0).mul (h 1 0).star).add ((h 0 0).mul (k 1 0).star)).add
    (((k 0 1).mul (h 1 1).star).add ((h 0 1).mul (k 1 1).star))) using 1
  · rfl
  · simp [numeratorSecond, curve, Matrix.one_apply]; ring

 def denominatorSecond : ℝ :=
  ![-4 * (basisMatrix i 1 1).re, 0,
    2 * (basisMatrix i 1 0).re, -2 * (basisMatrix i 1 0).im,
    2 * (basisMatrix i 1 0).re, 2 * (basisMatrix i 1 0).im] j

private theorem denominator_second :
    HasDerivAt (fun t => bottomDenominatorJet (curve i t) j)
      (denominatorSecond i j) 0 := by
  have h := curve_entries i
  have hp := (h 1 0).mul (h 1 1).star
  have hr := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hp).const_mul 2
  have hi := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hp).const_mul 2
  fin_cases j
  · convert (((normSq_hasDerivAt (h 1 0)).sub (normSq_hasDerivAt (h 1 1))).const_mul 2) using 1 <;> simp [bottomDenominatorJet, denominatorSecond, curve, Matrix.one_apply] <;> ring
  · simpa [bottomDenominatorJet, denominatorSecond] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  · simpa [bottomDenominatorJet, denominatorSecond, curve, Matrix.one_apply] using hr
  · convert hi.neg using 1 <;> simp [bottomDenominatorJet, denominatorSecond, curve, Matrix.one_apply, Pi.neg_apply] <;> rfl
  · simpa [bottomDenominatorJet, denominatorSecond, curve, Matrix.one_apply] using hr
  · simpa [bottomDenominatorJet, denominatorSecond, curve, Matrix.one_apply] using hi

 def horizontalSecond : ℂ :=
  numeratorSecond i j - horizontalNumeratorJet (1 : Mat) i * (bottomDenominatorJet (1 : Mat) j : ℂ)
    - horizontalNumeratorJet (1 : Mat) j * (bottomDenominatorJet (1 : Mat) i : ℂ)

 def verticalSecond : ℝ :=
  -denominatorSecond i j + bottomDenominatorJet (1 : Mat) j * bottomDenominatorJet (1 : Mat) i

private theorem horizontal_second :
    HasDerivAt (fun t => horizontalFieldJet (curve i t) j) (horizontalSecond i j) 0 := by
  have hN : HasDerivAt (fun t => horizontalNumerator (curve i t))
      (horizontalNumeratorJet (1 : Mat) i) 0 := by
    simpa [curve] using horizontalNumerator_hasDerivAt (1 : Mat) i
  have hD : HasDerivAt (fun t => (bottomDenominator (curve i t) : ℂ))
      (bottomDenominatorJet (1 : Mat) i : ℂ) 0 := by
    simpa [curve] using (bottomDenominator_hasDerivAt (1 : Mat) i).ofReal_comp
  convert ((((numerator_second i j).mul hD).sub (hN.mul ((denominator_second i j).ofReal_comp))).div (hD.pow 2)
    (by norm_num [curve, bottomDenominator])) using 1
  · rfl
  · simp [horizontalSecond, curve, bottomDenominator, horizontalNumerator]; ring

end

 def tangent (i : Fin 6) : KPArch.H3 :=
  (horizontalFieldJet (1 : Mat) i, verticalFieldJet (1 : Mat) i)

 def acceleration (i j : Fin 6) : KPArch.H3 :=
  (horizontalSecond i j, verticalSecond i j)

def localD (i : Fin 6) (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) : ℂ :=
  deriv (fun t : ℝ => f (g * matrixExponential ((t : ℂ) • basisMatrix i))) 0

 section

variable (φ : KPArch.H3 → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)

include hφ in
theorem localD_first
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) (i : Fin 6) :
    localD i (fun a => φ (KPArch.action a (0,0))) g =
      fderiv ℝ φ (KPArch.action g (0,0)) (horizontalFieldJet g i, verticalFieldJet g i) := by
  have hz : g * matrixExponential (((0 : ℝ) : ℂ) • basisMatrix i) = g := by
    apply Units.ext
    simp [matrixExponential]
  have hd := (show HasFDerivAt φ (fderiv ℝ φ (KPArch.action g (0,0)))
      (KPArch.action (g * matrixExponential (((0 : ℝ) : ℂ) • basisMatrix i)) (0,0)) by
        simpa only [hz] using (((hφ.differentiable (by simp)) (KPArch.action g (0,0))).hasFDerivAt)).comp_hasDerivAt 0 (actual_six_field_hasDerivAt g i)
  simpa only [localD, Function.comp_def, hz] using hd.deriv

include hφ in
private theorem localD_second
    (i j : Fin 6) :
    localD i (localD j (fun a => φ (KPArch.action a (0,0)))) 1 =
      fderiv ℝ (fderiv ℝ φ) (0,0) (tangent i) (tangent j) +
        fderiv ℝ φ (0,0) (acceleration i j) := by
  rw [(funext (fun a => localD_first φ hφ a j))]
  have hb := actual_six_field_hasDerivAt (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ) i
  have hfd :=
    (hφ.fderiv_right (by simp) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ)).differentiable (by simp)
  have hz : KPArch.action (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ) (0,0) = (0,0) :=
    (KPArch.action_laws 1 1 (0,0)).1
  have h0 : matrixExponential (((0 : ℝ) : ℂ) • basisMatrix i) = 1 := by
    apply Units.ext
    simp [matrixExponential]
  simp only [one_mul] at hb
  have hfd0 : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (0,0))
      (KPArch.action (matrixExponential (((0 : ℝ) : ℂ) • basisMatrix i)) (0,0)) := by
    rw [h0, hz]
    exact (hfd (0,0)).hasFDerivAt
  have hdf := hfd0.comp_hasDerivAt 0 hb
  have hv : HasDerivAt (fun t : ℝ =>
      (horizontalFieldJet (matrixExponential ((t : ℂ) • basisMatrix i)) j,
       verticalFieldJet (matrixExponential ((t : ℂ) • basisMatrix i)) j))
      (acceleration i j) 0 := by
    exact (horizontal_second i j).prodMk (by
      convert ((denominator_second i j).neg.div (by
        simpa [curve] using bottomDenominator_hasDerivAt (1 : Mat) i) (by norm_num [curve, bottomDenominator])) using 1
      · rfl
      · simp [verticalSecond, curve, bottomDenominator])
  have hd := hdf.clm_apply hv
  have h0 : matrixExponential (((0 : ℝ) : ℂ) • basisMatrix i) = 1 := by
    apply Units.ext
    simp [matrixExponential]
  simpa only [localD, one_mul, Function.comp_def, h0, hz, tangent, acceleration, add_comm, Units.val_one] using hd.deriv

end

 theorem basepoint_casimir (φ : KPArch.H3 → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    -((1 : ℂ) / 4) *
      (localD 0 (localD 0 (fun a => φ (KPArch.action a (0,0)))) 1 -
       localD 1 (localD 1 (fun a => φ (KPArch.action a (0,0)))) 1 +
       2 * (localD 2 (localD 4 (fun a => φ (KPArch.action a (0,0)))) 1 +
         localD 4 (localD 2 (fun a => φ (KPArch.action a (0,0)))) 1 -
         localD 3 (localD 5 (fun a => φ (KPArch.action a (0,0)))) 1 -
         localD 5 (localD 3 (fun a => φ (KPArch.action a (0,0)))) 1)) =
      -fderiv ℝ (fderiv ℝ φ) (0,0) (0,1) (0,1) -
        fderiv ℝ (fderiv ℝ φ) (0,0) (1,0) (1,0) -
        fderiv ℝ (fderiv ℝ φ) (0,0) (Complex.I,0) (Complex.I,0) +
        2 * fderiv ℝ φ (0,0) (0,1) := by
  simp_rw [localD_second φ hφ]
  have h2 : ((0,2) : KPArch.H3) = (2 : ℝ) • (0,1) := by ext <;> norm_num
  have hn2 : ((0,-2) : KPArch.H3) = (-2 : ℝ) • (0,1) := by ext <;> norm_num
  have hi : ((-Complex.I,0) : KPArch.H3) = -(Complex.I,0) := by ext <;> simp
  norm_num [tangent, acceleration, horizontalSecond, verticalSecond, numeratorSecond,
    denominatorSecond, horizontalFieldJet, verticalFieldJet, horizontalNumeratorJet,
    horizontalNumerator, bottomDenominatorJet, bottomDenominator, basisMatrix, sl2Matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [h2, hn2, hi, map_smul, map_neg, smul_apply, neg_apply, Complex.real_smul]
  norm_num
  have hzero : ((0,0) : KPArch.H3) = 0 := rfl
  simp only [hzero, map_zero, zero_apply]
  ring

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)

include hf in
private theorem second_apply (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y w) x v =
      fderiv ℝ (fderiv ℝ f) x v w := by
  simpa using (congrArg (fun A : E →L[ℝ] ℂ => A v) ((((hf.fderiv_right (by simp) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f)).differentiable (by simp)) x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv)

 include hf in
theorem first_precomp (L : KPArch.H3 →L[ℝ] E)
    (x v : KPArch.H3) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x ((hf.differentiable (by simp)) (L x)) L.differentiableAt]
  simp

include hf in
private theorem second_precomp (L : KPArch.H3 →L[ℝ] E)
    (x v w : KPArch.H3) :
    fderiv ℝ (fderiv ℝ (f ∘ L)) x v w = fderiv ℝ (fderiv ℝ f) (L x) (L v) (L w) := by
  rw [← second_apply (f ∘ L) (hf.comp L.contDiff) x v w]
  simp_rw [first_precomp f hf L]
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y (L w)) (L x) := by
    have hh : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    exact (((hh.differentiable (by simp)) (L x)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (L w) (L x))).differentiableAt
  change fderiv ℝ ((fun y => fderiv ℝ f y (L w)) ∘ L) x v = _
  rw [fderiv_comp x hd L.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  exact second_apply f hf (L x) (L v) (L w)

end

def localCasimir (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℂ) : ℂ :=
  -((1 : ℂ) / 4) * (localD 0 (localD 0 f) g - localD 1 (localD 1 f) g +
    2 * (localD 2 (localD 4 f) g + localD 4 (localD 2 f) g -
      localD 3 (localD 5 f) g - localD 5 (localD 3 f) g))

section

variable (d : ℕ) (f : KPArch.Space d → ℂ)

def productCasimir
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) : ℂ :=
  ∑ i : Fin d, localCasimir
    (fun a => f (fun k => KPArch.action (Function.update g i a k) (0,0))) (g i)

 theorem product_basepoint_casimir
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    productCasimir d f (fun _ => 1) =
      KPContActualSphericalFlatStage.localLaplacian d f 0 := by
  change productCasimir d f (fun _ => 1) = KPContFlatCuspCasimirSpecialization.Δloc d f 0
  rw [KPContFlatCuspCasimirSpecialization.Δloc_coordinate_expression d f (hf.of_le (by simp))]
  unfold productCasimir
  apply Finset.sum_congr rfl
  intro i _
  let L := ContinuousLinearMap.single ℝ (fun _ : Fin d => KPArch.H3) i
  have he (a : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      (fun k => KPArch.action (Function.update (fun _ : Fin d => (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ)) i a k) (0,0)) =
        L (KPArch.action a (0,0)) := by
    funext k
    by_cases hk : k = i
    · subst k; simp [L]
    · simp [L, Function.update_of_ne hk, Pi.single_eq_of_ne hk, (KPArch.action_laws 1 1 (0,0)).1]
  simp_rw [he]
  let fderiv₀ := fderiv ℝ (fderiv ℝ (f ∘ L)) (0,0)
  rw [show localCasimir (fun a => f (L (KPArch.action a (0,0)))) 1 =
      -fderiv₀ (0,1) (0,1) -
        fderiv₀ (1,0) (1,0) -
        fderiv₀ (Complex.I,0) (Complex.I,0) +
        2 * fderiv ℝ (f ∘ L) (0,0) (0,1) from basepoint_casimir (f ∘ L) (hf.comp L.contDiff)]
  rw [second_precomp f hf L, second_precomp f hf L, second_precomp f hf L, first_precomp f hf L]
  simp only [KPArch.height, Pi.zero_apply, Prod.snd_zero, Real.exp_zero, one_pow,
    Complex.ofReal_one, one_smul, smul_eq_mul]
  simp_rw [second_apply f hf]
  have h0 : L (0,0) = 0 := L.map_zero
  rw [h0]
  simp only [KPContFlatCuspCasimirSpecialization.coordinateDirection, ↓reduceIte,
    show L (0,1) = Pi.single i (0,1) from rfl,
    show L (1,0) = Pi.single i (1,0) from rfl,
    show L (Complex.I,0) = Pi.single i (Complex.I,0) from rfl]
  norm_num
  ring

end

 theorem localD_left (i : Fin 6) (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (a g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    localD i (fun x => f (a*x)) g = localD i f (a*g) := by
  simp only [localD, mul_assoc]

private theorem localCasimir_left (f : Matrix.GeneralLinearGroup (Fin 2) ℂ → ℂ)
    (a g : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    localCasimir (fun x => f (a*x)) g = localCasimir f (a*g) := by
  have h (i : Fin 6) : localD i (fun x => f (a*x)) = fun x => localD i f (a*x) :=
    funext (localD_left i f a)
  unfold localCasimir
  simp only [h, localD_left]

variable (d : ℕ) (f : KPArch.Space d → ℂ)

private theorem productCasimir_pullback
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    productCasimir d (fun y => f (KPArch.productAction d g y)) (fun _ => 1) =
      productCasimir d f g := by
  unfold productCasimir
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Matrix.GeneralLinearGroup (Fin 2) ℂ) :
      KPArch.productAction d g
          (fun k => KPArch.action (Function.update (fun _ : Fin d => (1 : Matrix.GeneralLinearGroup (Fin 2) ℂ)) i a k) (0,0)) =
        fun k => KPArch.action (Function.update g i (g i * a) k) (0,0) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp only [KPArch.productAction, Function.update_self]
      exact (KPArch.action_laws (g i) a (0,0)).2.symm
    · simp only [KPArch.productAction, Function.update_of_ne hk,
        (KPArch.action_laws 1 1 (0,0)).1]
  simp_rw [he]
  exact (localCasimir_left
    (fun a => f (fun k => KPArch.action (Function.update g i a k) (0,0))) (g i) 1).trans
      (by rw [mul_one])

 theorem product_casimir
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (g : Fin d → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    productCasimir d f g = KPContActualSphericalFlatStage.localLaplacian d f
      (fun i => KPArch.action (g i) (0,0)) := by
  rw [← productCasimir_pullback]
  have hb := product_basepoint_casimir d (f ∘ KPArch.productAction d g)
    (hf.comp ((KPArch.productAction_contDiff d g).of_le (by simp)))
  simp only [Function.comp_def] at hb
  rw [hb]
  exact KPContArchLaplacianNaturality.pullback d g f hf 0

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalMetric

end
