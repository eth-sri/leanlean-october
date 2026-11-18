module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.WeakTimeDerivative
public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDerivativeKernel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevSeparable

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Function MeasureTheory Set Filter
open scoped ENNReal

private theorem integrable_vstar
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    Integrable (fun tau => g tau) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo 0 T))
    infer_instance
  exact (MeasureTheory.Lp.memLp g).integrable (by norm_num)

/-- The restricted-measure Bochner primitive of a reverse-time dual curve. -/
noncomputable def reverseTimeVStarPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    ℝ → H10HilbertGraphDual hΩ :=
  fun t => ∫ tau in Set.Ioc 0 t, g tau ∂reverseTimeVolume T

/-- The dual primitive is continuous on the closed reverse-time interval. -/
theorem continuousOn_reverseTimeVStarPrimitive
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    ContinuousOn (reverseTimeVStarPrimitive hΩ T g) (Set.Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo 0 T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_vstar hΩ T g).integrableOn

/-- The restricted-measure primitive vanishes at time zero. -/
theorem reverseTimeVStarPrimitive_zero
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) :
    reverseTimeVStarPrimitive hΩ T g 0 = 0 := by
  change ∫ tau in Set.Ioc 0 0, g tau ∂reverseTimeVolume T = 0
  simp

/-- Increments of the dual primitive are the corresponding restricted-time integrals. -/
theorem reverseTimeVStarPrimitive_sub
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    reverseTimeVStarPrimitive hΩ T g t -
        reverseTimeVStarPrimitive hΩ T g s =
      ∫ tau in Set.Ioc s t, g tau ∂reverseTimeVolume T := by
  change (∫ tau in Ioc 0 t, g tau ∂reverseTimeVolume T) -
      ∫ tau in Ioc 0 s, g tau ∂reverseTimeVolume T = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_vstar hΩ T g).intervalIntegrable
      (integrable_vstar hΩ T g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]

/-- Evaluation by a fixed spatial test commutes with the dual primitive. -/
theorem reverseTimeVStarPrimitive_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) (t : ℝ) :
    reverseTimeVStarPrimitive hΩ T g t v =
      ∫ tau in Set.Ioc 0 t, (g tau) v ∂reverseTimeVolume T := by
  exact ContinuousLinearMap.integral_apply
    ((integrable_vstar hΩ T g).integrableOn) v

/-- A fixed-vector evaluation of the dual primitive is integrable in reverse time. -/
theorem integrable_reverseTimeVStarPrimitive_apply
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)
    (v : H10HilbertGraph hΩ) :
    MeasureTheory.Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v)
      (reverseTimeVolume T) := by
  have hcont :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
      (continuousOn_reverseTimeVStarPrimitive hΩ T g)
  exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)




/-- The canonical Bochner-average constant in the reverse-time affine Gelfand
identification.  The positive-time proof argument guards this normalization. -/
noncomputable def reverseTimeGelfandAffineConstant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (_hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
    H10HilbertGraphDual hΩ :=
  T⁻¹ • ∫ tau,
    (reverseTimeGelfandCLM hΩ T u tau -
      reverseTimeVStarPrimitive hΩ T g tau) ∂reverseTimeVolume T






private theorem h10HilbertGraphDual_eq_of_dense_apply_eq
    {d : ℕ} {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω}
    (q : ℕ → H10HilbertGraph hΩ) (hqDense : DenseRange q)
    (ell ell' : H10HilbertGraphDual hΩ)
    (hpair : ∀ n : ℕ, ell (q n) = ell' (q n)) :
    ell = ell' := by
  apply ContinuousLinearMap.coeFn_injective
  exact Continuous.ext_on hqDense ell.continuous ell'.continuous (by
    rintro _ ⟨n, rfl⟩
    exact hpair n)


private theorem ae_eq_add_of_ae_sub_eq
    {alpha E : Type _} [MeasurableSpace alpha] [AddCommGroup E]
    {mu : Measure alpha} {G P : alpha → E} {c : E}
    (h : (fun x => G x - P x) =ᵐ[mu] fun _ => c) :
    G =ᵐ[mu] fun x => P x + c := by
  filter_upwards [h] with x hx
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hx

/-- The reverse-time Gelfand curve agrees almost everywhere with its dual
Bochner primitive plus the canonical affine Bochner-average constant. -/
theorem reverseTimeGelfandCLM_ae_eq_reverseTimeVStarPrimitive_add_affineConstant
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    reverseTimeGelfandCLM hΩ T u =ᵐ[reverseTimeVolume T] fun tau =>
      reverseTimeVStarPrimitive hΩ T g tau +
        reverseTimeGelfandAffineConstant hΩ T hT u g   := by
  have reverseTimeGelfandAffineDifference_ae_eq_affineConstant {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (hF : Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T)) :
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
      reverseTimeVStarPrimitive hΩ T g tau) =ᵐ[reverseTimeVolume T]
      fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g := by
    have ae_all_h10HilbertGraphDual_apply_eq {Ω : Set (PDE.Vec d)} {hΩ : IsOpen Ω} (F : ℝ → H10HilbertGraphDual hΩ) (c : H10HilbertGraphDual hΩ) (q : ℕ → H10HilbertGraph hΩ) (hpair : ∀ n : ℕ, (fun tau => F tau (q n)) =ᵐ[reverseTimeVolume T]
        fun _ => c (q n)) : ∀ᵐ tau ∂reverseTimeVolume T, ∀ n : ℕ, F tau (q n) = c (q n) :=
      ae_all_iff.mpr hpair
    have reverseTimeGelfandAffineDifference_apply_ae_eq_affineConstant_apply {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (hF : Integrable
        (fun tau => reverseTimeGelfandCLM hΩ T u tau -
          reverseTimeVStarPrimitive hΩ T g tau)
        (reverseTimeVolume T)) (v : H10HilbertGraph hΩ) :
        (fun tau =>
        (reverseTimeGelfandCLM hΩ T u tau -
          reverseTimeVStarPrimitive hΩ T g tau) v) =ᵐ[reverseTimeVolume T]
        fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g v := by
      have integral_reverseTimeGelfandAffineDifference_apply_deriv_eq_zero {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
          (∫ tau,
          (reverseTimeGelfandCLM hΩ T u tau -
            reverseTimeVStarPrimitive hΩ T g tau) v * eta.deriv tau
          ∂reverseTimeVolume T) = 0 := by
        have reverseTimeVStarPrimitive_test_deriv {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) (eta : ReverseTimeScalarTest T) :
            MeasureTheory.Integrable
            (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
            (reverseTimeVolume T) ∧
          MeasureTheory.Integrable (fun tau => (g tau) v * eta tau)
            (reverseTimeVolume T) ∧
          (∫ tau,
            reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
            ∂reverseTimeVolume T) =
            -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
          have primitive_apply_on_Ioo {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T) (v : H10HilbertGraph hΩ) {t : ℝ} (ht : t ∈ Ioo 0 T) :
              reverseTimeVStarPrimitive hΩ T g t v =
              PDE.intervalPrimitive 0 (fun s => (g s) v) t := by
            rw [reverseTimeVStarPrimitive_apply]
            rw [show (∫ s in Ioc 0 t, (g s) v ∂reverseTimeVolume T) =
                ∫ s in Ioc 0 t, (g s) v ∂volume by
              simp only [reverseTimeVolume, reverseTimeOpenInterval,
                Measure.restrict_restrict measurableSet_Ioc]
              rw [inter_eq_left.mpr]
              intro s hs
              exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩]
            exact (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm
          have hleft : Integrable
              (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
              (reverseTimeVolume T) := by
            exact (((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn (continuousOn_reverseTimeVStarPrimitive hΩ T g)).mul eta.contDiff_deriv.continuous.continuousOn).integrableOn_Icc.mono_set Ioo_subset_Icc_self
          letI : IsFiniteMeasure (reverseTimeVolume T) := by
            change IsFiniteMeasure (volume.restrict (Ioo 0 T))
            infer_instance
          have hqLp : MemLp (fun tau => (g tau) v) 2 (reverseTimeVolume T) :=
            (MeasureTheory.Lp.memLp g).continuousLinearMap_comp
              (ContinuousLinearMap.apply ℝ ℝ v)
          have hright : Integrable (fun tau => (g tau) v * eta tau)
              (reverseTimeVolume T) := by
            simpa only [Pi.mul_def] using hqLp.integrable_mul (eta.memLp 2)
          refine ⟨hleft, hright, ?_⟩
          have hqIcc : IntegrableOn (fun tau => (g tau) v) (Icc 0 T) volume := by
            change Integrable (fun tau => (g tau) v) (volume.restrict (Icc 0 T))
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc] using hqLp.integrable (by norm_num)
          have hae : (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau) =ᵐ[
              reverseTimeVolume T] fun tau =>
                PDE.intervalPrimitive 0 (fun s => (g s) v) tau * _root_.deriv eta tau := by
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
            rw [primitive_apply_on_Ioo hΩ T g v ht, eta.deriv_apply]
          calc
            (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
              ∂reverseTimeVolume T) =
                ∫ tau, PDE.intervalPrimitive 0 (fun s => (g s) v) tau * _root_.deriv eta tau
                  ∂reverseTimeVolume T := integral_congr_ae hae
            _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
              simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
                PDE.intervalPrimitive_scalar_weak_identity_Ioo hqIcc
                  (eta.contDiff.of_le (by simp)) eta.tsupport_subset
        let G : ℝ → H10HilbertGraphDual hΩ := fun tau => reverseTimeGelfandCLM hΩ T u tau
        let P : ℝ → H10HilbertGraphDual hΩ := fun tau => reverseTimeVStarPrimitive hΩ T g tau
        change (∫ tau, (G tau - P tau) v * eta.deriv tau ∂reverseTimeVolume T) = 0
        obtain ⟨hGInner, _, hGIdentity⟩ := hderiv v eta
        obtain ⟨hP, _, hPIdentity⟩ :=
          reverseTimeVStarPrimitive_test_deriv hΩ T g v eta
        have hGae :
            (fun tau => G tau v * eta.deriv tau) =ᵐ[
              reverseTimeVolume T]
              fun tau => inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau := by
          filter_upwards [coeFn_reverseTimeGelfandCLM hΩ T u,
            coeFn_reverseTimeValueCLM hΩ T u] with tau hGelfand hValue
          dsimp only [G]
          rw [hGelfand, scalarLpToH10HilbertGraphDual_apply, hValue]
        have hG :=
          hGInner.congr hGae.symm
        have hIdentity :
            (∫ tau, G tau v * eta.deriv tau
              ∂reverseTimeVolume T) =
              ∫ tau, P tau v * eta.deriv tau
                ∂reverseTimeVolume T := by
          calc
            (∫ tau, G tau v * eta.deriv tau
              ∂reverseTimeVolume T) =
                ∫ tau, inner ℝ (valueCLM hΩ v) (reverseTimeValueCLM hΩ T u tau) * eta.deriv tau
                  ∂reverseTimeVolume T := integral_congr_ae hGae
            _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := hGIdentity
            _ = ∫ tau, P tau v * eta.deriv tau
                ∂reverseTimeVolume T := hPIdentity.symm
        calc
          (∫ tau,
            (G tau - P tau) v * eta.deriv tau
            ∂reverseTimeVolume T) =
              ∫ tau, (G tau v * eta.deriv tau - P tau v * eta.deriv tau)
                ∂reverseTimeVolume T := by
                  apply integral_congr_ae
                  filter_upwards with tau
                  rw [ContinuousLinearMap.sub_apply, sub_mul]
          _ = (∫ tau, G tau v * eta.deriv tau
              ∂reverseTimeVolume T) -
              ∫ tau, P tau v * eta.deriv tau
                ∂reverseTimeVolume T := integral_sub hG hP
          _ = 0 := by rw [hIdentity, sub_self]
      have reverseTimeVolume_real_univ :
          (reverseTimeVolume T).real univ = T := by
        change (volume.restrict (Ioo 0 T)).real univ = T
        rw [MeasureTheory.measureReal_restrict_apply_univ,
          Real.volume_real_Ioo_of_le (le_of_lt hT)]
        norm_num
      let F : ℝ → H10HilbertGraphDual hΩ := fun tau =>
        reverseTimeGelfandCLM hΩ T u tau - reverseTimeVStarPrimitive hΩ T g tau
      change Integrable F (reverseTimeVolume T) at hF
      change (fun tau => F tau v) =ᵐ[reverseTimeVolume T]
        fun _ => reverseTimeGelfandAffineConstant hΩ T hT u g v
      have hScalar : Integrable (fun tau => F tau v) (reverseTimeVolume T) :=
        (ContinuousLinearMap.apply ℝ ℝ v).integrable_comp hF
      obtain ⟨a, ha⟩ := exists_ae_eq_const_of_integral_deriv_eq_zero T hT hScalar (by
        intro eta
        exact integral_reverseTimeGelfandAffineDifference_apply_deriv_eq_zero
          hΩ T hT u g hderiv v eta)
      have hIntegral : (∫ tau, F tau v ∂reverseTimeVolume T) = T • a := by
        calc
          (∫ tau, F tau v ∂reverseTimeVolume T) = ∫ _ : ℝ, a ∂reverseTimeVolume T :=
            integral_congr_ae ha
          _ = (reverseTimeVolume T).real univ • a := MeasureTheory.integral_const a
          _ = T • a := by rw [reverseTimeVolume_real_univ]
      have hConstant : reverseTimeGelfandAffineConstant hΩ T hT u g v = a := by
        rw [reverseTimeGelfandAffineConstant, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.integral_apply hF v]
        change T⁻¹ * (∫ tau, F tau v ∂reverseTimeVolume T) = a
        rw [hIntegral, smul_eq_mul]
        calc
          T⁻¹ * (T * a) = (T⁻¹ * T) * a := (mul_assoc _ _ _).symm
          _ = a := by rw [inv_mul_cancel₀ hT.ne', one_mul]
      filter_upwards [ha] with tau htau
      rw [htau, hConstant]
    let F : ℝ → H10HilbertGraphDual hΩ := fun tau =>
      reverseTimeGelfandCLM hΩ T u tau - reverseTimeVStarPrimitive hΩ T g tau
    let c := reverseTimeGelfandAffineConstant hΩ T hT u g
    change Integrable F (reverseTimeVolume T) at hF
    change F =ᵐ[reverseTimeVolume T] fun _ => c
    letI : TopologicalSpace.SeparableSpace (H10HilbertGraph hΩ) :=
      h10HilbertGraphSeparableSpace hΩ
    let q := TopologicalSpace.denseSeq (H10HilbertGraph hΩ)
    have hpairAE : ∀ n : ℕ, (fun tau => F tau (q n)) =ᵐ[reverseTimeVolume T]
        fun _ => c (q n) := by
      intro n
      simpa only [F, c] using
        reverseTimeGelfandAffineDifference_apply_ae_eq_affineConstant_apply
          hΩ T hT u g hderiv hF (q n)
    filter_upwards [(ae_all_h10HilbertGraphDual_apply_eq F c q hpairAE)] with tau htau
    exact h10HilbertGraphDual_eq_of_dense_apply_eq q (TopologicalSpace.denseRange_denseSeq (H10HilbertGraph hΩ)) (F tau) c (htau)
  have integrable_reverseTimeGelfandAffineDifference {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) :
      Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T) := by
    letI : IsFiniteMeasure (reverseTimeVolume T) := by
      change IsFiniteMeasure (volume.restrict (Ioo 0 T))
      infer_instance
    have hG :=
      (MeasureTheory.Lp.memLp (reverseTimeGelfandCLM hΩ T u)).integrable (by norm_num)
    have hP : Integrable (reverseTimeVStarPrimitive hΩ T g) (reverseTimeVolume T) := by
      change IntegrableOn (reverseTimeVStarPrimitive hΩ T g) (Ioo 0 T) volume
      exact (continuousOn_reverseTimeVStarPrimitive hΩ T g).integrableOn_Icc
        |>.mono_set Ioo_subset_Icc_self
    exact hG.sub hP
  have hF : Integrable
      (fun tau => reverseTimeGelfandCLM hΩ T u tau -
        reverseTimeVStarPrimitive hΩ T g tau)
      (reverseTimeVolume T) :=
    integrable_reverseTimeGelfandAffineDifference hΩ T u g
  exact ae_eq_add_of_ae_sub_eq
    (reverseTimeGelfandAffineDifference_ae_eq_affineConstant hΩ T hT u g hderiv hF)

end HypoellipticAleksandrov.Parabolic.Dirichlet

