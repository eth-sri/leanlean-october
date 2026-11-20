module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompactAverages.TaylorJets

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution
open MeasureTheory Set Filter Topology

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel (Mat matrixClass matrixDomain matrixDomain_open matrix_pullback_smooth matrixClass_mul matrixClass_out joint_spatial_jets_on localMatrixLift localMatrixLift_continuousAt localMatrixLift_reconstruct localMatrixLift_eventually actualSmoothBridge affineDomain_open affineEll_continuousAt toAffine_contDiff toAffine_mapsTo affineEll_toAffine gauss_domain_open)
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

variable (F : Type) [Field F] [NumberField F]

 def inverseShiftMatrix (b : L F) (p : Mat F × Y F) : Mat F := fun w =>
  (b⁻¹ w).out.val * PGLComplex.affineAdjugate (p.2 w) * p.1 w

private theorem inverseShiftMatrix_smooth (b : L F) :
    ContDiff ℝ (⊤ : ℕ∞) (inverseShiftMatrix F b) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  have hc (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Mat F × Y F => PGLComplex.affineAdjugate (p.2 w) i j) :=
    (contDiff_pi.mp (contDiff_pi.mp PGLComplex.contDiff_affineAdjugate i) j).comp
      ((contDiff_apply ℝ _ w).comp contDiff_snd)
  simp only [inverseShiftMatrix, Matrix.mul_apply, Fin.sum_univ_two]
  fun_prop (disch := exact hc _ _)

section

variable (b : L F) (M : Mat F) (hM : M ∈ matrixDomain F) (x : Y F) (hx : x ∈ affineDomain F)

include hM hx in
private theorem inverseShiftMatrix_mem :
    inverseShiftMatrix F b (M,x) ∈ matrixDomain F := by
  intro w
  change ((b⁻¹ w).out.val * PGLComplex.affineAdjugate (x w) * M w).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul, PGLComplex.affineAdjugate_det]
  exact mul_ne_zero (mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero _) (hx w)) (hM w)

include hM hx in
private theorem inverseShiftMatrix_class :
    matrixClass F (inverseShiftMatrix F b (M,x)) =
      b⁻¹ * (affineEll F x)⁻¹ * matrixClass F M := by
  let B := fun w => (b⁻¹ w).out.val
  let A := fun w => PGLComplex.affineAdjugate (x w)
  have hB : B ∈ matrixDomain F := fun w => Matrix.GeneralLinearGroup.det_ne_zero _
  have hA : A ∈ matrixDomain F := fun w => by
    rw [PGLComplex.affineAdjugate_det]
    exact hx w
  rw [show inverseShiftMatrix F b (M,x) = fun w => (B w * A w) * M w from rfl,
    matrixClass_mul F _ _ (fun w => by
      rw [Matrix.det_mul]
      exact mul_ne_zero (hB w) (hA w)) hM, matrixClass_mul F B A hB hA, matrixClass_out F]
  congr 1
  congr 1
  funext w
  change Matrix.ProjGenLinGroup.mk (if h : (A w).det ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero (A w) h else 1) = (PGLComplex.affinePoint (x w))⁻¹
  rw [dite_eq_left (hA w)]
  exact PGLComplex.affineAdjugate_class (x w) (hx w)

end

section

variable (q : L F → ℝ) (hd : AffineSmooth F q)

include hd in
private theorem inverse_shift_matrix_jets (b : L F) (n : ℕ) :
    ContinuousOn (fun p : Mat F × Y F => iteratedFDeriv ℝ n
      (fun x => q (b⁻¹ * (affineEll F x)⁻¹ * matrixClass F p.1)) p.2)
      (matrixDomain F ×ˢ affineDomain F) := by
  have hsm' : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : Mat F × Y F => q (b⁻¹ * (affineEll F p.2)⁻¹ * matrixClass F p.1))
      (matrixDomain F ×ˢ affineDomain F) := by
    apply ((matrix_pullback_smooth F q hd).comp (inverseShiftMatrix_smooth F b).contDiffOn
      (fun p hp => inverseShiftMatrix_mem F b p.1 hp.1 p.2 hp.2)).congr
    intro p hp
    change _ = q (matrixClass F (inverseShiftMatrix F b p))
    rw [inverseShiftMatrix_class F b p.1 hp.1 p.2 hp.2]
  exact (joint_spatial_jets_on _ ((matrixDomain_open F).prod (affineDomain_open F)) _ hsm' n).continuousOn

include hd in
private theorem inverse_shift_jets
    (b : L F) (n : ℕ) :
    ContinuousOn (fun p : Y F × L F => iteratedFDeriv ℝ n
      (fun x => q (b⁻¹ * (affineEll F x)⁻¹ * p.2)) p.1)
      (affineDomain F ×ˢ univ) := by
  intro p hp
  let ML := localMatrixLift F p.2
  have hEq : (fun u : Y F × L F => iteratedFDeriv ℝ n
      (fun x => q (b⁻¹ * (affineEll F x)⁻¹ * u.2)) u.1) =ᶠ[𝓝 p]
      (fun u => iteratedFDeriv ℝ n
        (fun x => q (b⁻¹ * (affineEll F x)⁻¹ * matrixClass F (ML u.2))) u.1) := by
    filter_upwards [(continuousAt_snd (localMatrixLift_eventually F p.2))] with u hu
    rw [hu.2]
  exact ((((inverse_shift_matrix_jets F q hd b n).continuousAt
    (((matrixDomain_open F).prod (affineDomain_open F)).mem_nhds ⟨(localMatrixLift_reconstruct F p.2 p.2
      (show p.2⁻¹ * p.2 ∈ gaussTarget F by
        simp only [inv_mul_cancel]; intro w; exact PGLComplex.one_mem_affineTarget)).1,hp.1⟩)).comp_of_eq (((localMatrixLift_continuousAt F p.2).comp_of_eq continuousAt_snd rfl).prodMk (show ContinuousAt (fun u : Y F × L F => u.1) p from continuousAt_fst)) rfl).congr_of_eventuallyEq hEq).continuousWithinAt

include hd in
private theorem inverse_shift_slice
    (b y : L F) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => q (b⁻¹ * (affineEll F x)⁻¹ * y)) (affineDomain F) := by
  let M := fun w => (y w).out.val
  have hM : M ∈ matrixDomain F := fun w => Matrix.GeneralLinearGroup.det_ne_zero _
  apply ((matrix_pullback_smooth F q hd).comp ((inverseShiftMatrix_smooth F b).comp (contDiff_const.prodMk contDiff_id)).contDiffOn
    (fun x hx => inverseShiftMatrix_mem F b M hM x hx)).congr
  intro x hx
  change _ = q (matrixClass F (inverseShiftMatrix F b (M,x)))
  rw [inverseShiftMatrix_class F b M hM x hx, matrixClass_out F]

end

private theorem weighted_inverse_shift_smooth
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
    (q : L F → ℝ) (hd : AffineSmooth F q) (b : L F)
    (v : K → L F) (hv : Continuous v) (f : K → ℂ) (hf : Continuous f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Y F =>
      ∫ k, q (b⁻¹ * (affineEll F x)⁻¹ * v k) • f k ∂μ) (affineDomain F) := by
  let g := fun x k => q (b⁻¹ * (affineEll F x)⁻¹ * v k) • f k
  have hslice (k : K) : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => g x k) (affineDomain F) :=
    (inverse_shift_slice F q hd b (v k)).smul contDiffOn_const
  apply CompactJets.contDiffOn_average_of_taylor μ (affineDomain F) (affineDomain_open F) g
    (fun x k => ftaylorSeriesWithin ℝ (fun x => g x k) (affineDomain F) x)
  · intro k
    exact (hslice k).ftaylorSeriesWithin (affineDomain_open F).uniqueDiffOn
  · intro n
    apply (((ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin n => Y F) ℂ).continuous.comp_continuousOn ((inverse_shift_jets F q hd b n).comp
      (continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1, mem_univ _⟩))).clm_apply
      (hf.comp continuous_snd).continuousOn).congr
    intro p hp
    change iteratedFDerivWithin ℝ n (fun x => g x p.2) (affineDomain F) p.1 = _
    rw [iteratedFDerivWithin_of_isOpen n (affineDomain_open F) hp.1]
    rw [iteratedFDeriv_smul_const_apply
      (((inverse_shift_slice F q hd b (v p.2)).contDiffAt
        ((affineDomain_open F).mem_nhds hp.1)).of_le (by simp))]
    rfl

theorem shifted_kernel_contDiffOn
    (F : Type) [Field F] [NumberField F]
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (q : L F → ℝ) (hq : Continuous q)
    (hs : HasCompactSupport q) (hd : KernelSmooth F q)
    (f : L F → ℂ) (hf : Continuous f) (b : L F) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : X F => ∫ y : L F,
        (q (b⁻¹ * (ell F z)⁻¹ * y) : ℂ) * f y ∂μL) (D0 F) := by
  have hda := (actualSmoothBridge F q).mp hd
  have hAf := affineDomain_open F
  have hlocal (x : Y F) (hx : x ∈ affineDomain F) :
      ContDiffAt ℝ (⊤ : ℕ∞) (fun u : Y F => ∫ y : L F,
        q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y ∂μL) x := by
    obtain ⟨C, hC, hxC, hCD⟩ := exists_compact_subset hAf hx
    let S : Set (L F) := (fun p : Y F × L F => affineEll F p.1 * b * p.2) '' (C ×ˢ tsupport q)
    have hcEll : ContinuousOn (affineEll F) C := fun u hu =>
      (affineEll_continuousAt F u (hCD hu)).continuousWithinAt
    have hS : IsCompact S := (hC.prod hs).image_of_continuousOn
      ((hcEll.comp continuousOn_fst (fun p hp => hp.1)).mul continuousOn_const |>.mul continuousOn_snd)
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    let ν : Measure S := Measure.comap Subtype.val μL
    have hSm : MeasurableSet S := hS.measurableSet
    letI : IsFiniteMeasure ν := ⟨by
      change Measure.comap Subtype.val μL univ < ⊤
      rw [comap_subtype_coe_apply hSm μL]
      have heS : (Subtype.val : S → L F) '' univ = S := by ext y; simp
      rw [heS]
      exact hS.measure_lt_top⟩
    have hInt := weighted_inverse_shift_smooth F ν q hda b
      (Subtype.val : S → L F) continuous_subtype_val (fun y : S => f y) (hf.comp continuous_subtype_val)
    have he (u : Y F) (hu : u ∈ C) :
        (∫ y : S, q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y ∂ν) =
          ∫ y : L F, q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y ∂μL := by
      change (∫ y : S, (fun y : L F => q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y) y
        ∂Measure.comap Subtype.val μL) = _
      refine (integral_subtype_comap (μ := μL) hSm
        (fun y : L F => q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y)).trans ?_
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hzero : q (b⁻¹ * (affineEll F u)⁻¹ * y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro ht
        apply hy
        refine ⟨(u, b⁻¹ * (affineEll F u)⁻¹ * y), ⟨hu, ht⟩, ?_⟩
        dsimp
        group
      rw [hzero, zero_smul]
    apply (hInt.contDiffAt (hAf.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [mem_interior_iff_mem_nhds.mp hxC] with u hu
    exact (he u hu).symm
  have hAll : ContDiffOn ℝ (⊤ : ℕ∞) (fun u : Y F => ∫ y : L F,
      q (b⁻¹ * (affineEll F u)⁻¹ * y) • f y ∂μL) (affineDomain F) :=
    fun x hx => (hlocal x hx).contDiffWithinAt
  have H := hAll.comp (toAffine_contDiff F) (toAffine_mapsTo F)
  apply H.congr
  intro z hz
  simp only [Function.comp_apply]
  rw [affineEll_toAffine F z hz]
  simp only [Complex.real_smul, Complex.ofReal_mul]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution

end
