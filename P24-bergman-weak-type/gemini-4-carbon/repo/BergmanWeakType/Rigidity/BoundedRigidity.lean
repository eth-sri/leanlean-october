module

public import BergmanWeakType.WeightedSharp
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.Schwarz
public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.UniformSpace.Ascoli

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter Complex Real Function
open scoped Pointwise Topology ComplexConjugate ENNReal BigOperators Uniformity UniformConvergence

namespace Complex.UnitDisc

lemma shift_den_ne_zero (z w : 𝔻) : 1 + conj (z : ℂ) * w ≠ 0 :=
  (star z * w).one_add_coe_ne_zero

def shiftFun (z w : 𝔻) : 𝔻 :=
  mk ((z + w : ℂ) / (1 + conj ↑z * w)) <| by
    have hd : 0 < ‖(1 + conj ↑z * w : ℂ)‖ := norm_pos_iff.mpr (shift_den_ne_zero z w)
    rw [norm_div, div_lt_one hd, ← sq_lt_sq₀ (norm_nonneg _) hd.le,
      ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
    have hid : normSq (1 + conj (z : ℂ) * w) - normSq (z + w : ℂ) =
        (1 - normSq (z : ℂ)) * (1 - normSq (w : ℂ)) := by simp [normSq_apply]; ring
    nlinarith [z.normSq_lt_one, w.normSq_lt_one]

theorem shiftFun_neg_apply_shiftFun (u w : 𝔻) : shiftFun (-u) (shiftFun u w) = w := by
  have hc (a b : 𝔻) : (shiftFun a b : ℂ) = (a + b) / (1 + conj ↑a * b) := rfl
  rw [← coe_inj, hc, div_eq_iff (shift_den_ne_zero _ _), hc]
  have : 1 + (w : ℂ) * conj ↑u ≠ 0 := mul_comm (conj (u : ℂ)) w ▸ shift_den_ne_zero u w
  simp only [coe_neg, map_neg]; field_simp; ring

def shift (z : 𝔻) : 𝔻 ≃ 𝔻 where
  toFun := shiftFun z
  invFun := shiftFun (-z)
  left_inv := shiftFun_neg_apply_shiftFun z
  right_inv w := by simpa using shiftFun_neg_apply_shiftFun (-z) w

theorem coe_shift (z w : 𝔻) : (shift z w : ℂ) = (z + w) / (1 + conj ↑z * w) := rfl

@[simp] theorem shift_apply_zero (z : 𝔻) : shift z 0 = z := by ext; simp [coe_shift]
@[simp] theorem shift_neg_apply_self (z : 𝔻) : shift (-z) z = 0 := by ext; simp [coe_shift]

theorem hasDerivAt_shift_comp {f : ℂ → ℂ} {z f' : ℂ} (w : 𝔻)
    (hf : HasDerivAt f f' z) (hd : 1 + conj (w : ℂ) * f z ≠ 0) :
    HasDerivAt (fun x ↦ (w + f x) / (1 + conj ↑w * f x))
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z := by
  convert (hf.const_add _).fun_div ((hf.const_mul _).const_add _) hd using 1
  rw [← mul_conj']; ring

theorem bijOn_shift (z : 𝔻) :
    BijOn (fun w : ℂ ↦ (z + w) / (1 + conj ↑z * w)) (ball 0 1) (ball 0 1) :=
  ⟨fun w hw ↦ mem_ball_zero_iff.mpr (z.shift (.mk w (mem_ball_zero_iff.mp hw))).norm_lt_one,
   fun u hu v hv h ↦ by
     simpa using congrArg UnitDisc.coe (z.shift.injective (UnitDisc.coe_inj.mp
       (show (z.shift (.mk u (mem_ball_zero_iff.mp hu)) : ℂ) =
         z.shift (.mk v (mem_ball_zero_iff.mp hv)) from h))),
   fun w hw ↦
     let u := z.shift.symm (.mk w (mem_ball_zero_iff.mp hw))
     ⟨u, mem_ball_zero_iff.mpr u.norm_lt_one, congrArg UnitDisc.coe (z.shift.apply_symm_apply _)⟩⟩

end Complex.UnitDisc

namespace BergmanWeakType

theorem not_eventually_constant_of_injOn {U : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : InjOn f U) (hx : x ∈ U) : ¬ ∀ᶠ z in 𝓝 x, f z = f x := fun h ↦
  not_isOpen_singleton x <| isOpen_singleton_of_finite_mem_nhds x
    ((h.and (hU.eventually_mem hx)).mono fun _ ⟨hz, hzU⟩ ↦ hf hzU hx hz) (finite_singleton x)

structure IsBergmanKernel (Ω : Set ℂ) (K : ℂ → ℂ → ℂ) : Prop where
  holomorphic : ∀ w ∈ Ω, DifferentiableOn ℂ (fun z ↦ K z w) Ω
  hermitian : ∀ z ∈ Ω, ∀ w ∈ Ω, K z w = star (K w z)
  squareIntegrable : ∀ z ∈ Ω, MemLp (fun w ↦ K z w) 2 (area.restrict Ω)
  reproduces : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → MemLp f 2 (area.restrict Ω) →
    ∀ z ∈ Ω, (∫ w, K z w * f w ∂area.restrict Ω) = f z

def domainPositiveProjection (Ω : Set ℂ) (K : ℂ → ℂ → ℂ) (f : ℂ → ℂ)
    (z : ℂ) : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal ‖K z w‖ * ‖f w‖ₑ ∂area.restrict Ω

theorem measure_univ_div_mass_le_weakTypeConstant_of_witness
    {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {f : ℂ → ℂ}
    (hf : Integrable f μ) (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    μ univ / (∫⁻ z, ‖f z‖ₑ ∂μ) ≤ weakTypeConstant μ T := by
  refine le_sInf fun C hC ↦ ENNReal.div_le_of_le_mul <| ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  by_cases ha0 : a = 0
  · simp [ha0]
  have hatop : a ≠ ⊤ := ne_top_of_lt ha
  have hbound := hC f hf a.toReal (ENNReal.toReal_pos ha0 hatop)
  rwa [ENNReal.ofReal_toReal hatop, measure_congr (show {z | a < T f z} =ᵐ[μ] univ from
    hout.mono fun _ hz ↦ propext (iff_true_intro (ha.trans_le hz)))] at hbound

instance area_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts area :=
  IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top

theorem det_complex_derivative (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

theorem hasFDerivWithinAt_real {U : Set ℂ} {φ : ℂ → ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) :
    ∀ w ∈ U, HasFDerivWithinAt φ ((ContinuousLinearMap.toSpanSingleton ℂ (deriv φ w)).restrictScalars ℝ) U w :=
  fun _ hw ↦ ((hφ.hasDerivAt (hU.mem_nhds hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

theorem area_integral_image_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℂ} {φ : ℂ → ℂ} (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hinj : InjOn φ U) (g : ℂ → E) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w) ∂area := by
  simp only [area, Measure.restrict_smul, integral_smul_measure]
  congr 1
  simpa only [det_complex_derivative, abs_sq] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
      (hasFDerivWithinAt_real hU hφ) hinj g

theorem area_integrableOn_image_iff_norm_deriv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    IntegrableOn g (φ '' U) area ↔
      IntegrableOn (fun w ↦ (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w)) U area := by
  simp only [IntegrableOn, area, Measure.restrict_smul,
    integrable_smul_measure (by positivity : ENNReal.ofReal π⁻¹ ≠ 0) ENNReal.ofReal_ne_top]
  simpa only [IntegrableOn, det_complex_derivative, abs_sq] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
      (hasFDerivWithinAt_real hU hφ) hinj g

theorem deriv_comp_eq_one {Ω : Set ℂ} {φ ψ : ℂ → ℂ} (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω) {u : ℂ} (hu : u ∈ disk) :
    deriv ψ (φ u) * deriv φ u = 1 :=
  (((hψ.differentiableAt (hΩ.mem_nhds (hbij.mapsTo hu))).hasDerivAt.comp u
    (hφ.differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt).congr_of_eventuallyEq
    ((isOpen_ball.eventually_mem hu).mono fun _ hv ↦ (hinv.1 hv).symm)).unique (hasDerivAt_id u)

theorem isBergmanKernel_disk : IsBergmanKernel disk kernel where
  holomorphic w hw :=
    (((differentiableOn_const 1).sub (differentiableOn_id.mul_const (star w))).inv
      fun _ hz ↦ kernel_denominator_ne_zero_closed_left ((mem_disk_iff _).mp hz).le hw).pow 2
  hermitian _ _ _ _ := by simp [kernel, star_mul]
  squareIntegrable z hz := by
    change MemLp (kernel z) 2 diskArea
    have hc : ContinuousOn (kernel z) disk := by
      simpa [funext (weightedKernel_zero z)] using continuousOn_weightedKernel 0 hz
    exact MemLp.of_bound (hc.aestronglyMeasurable measurableSet_disk) ((1 - ‖z‖)⁻¹ ^ 2)
      (ae_mem_disk.mono fun _ hw ↦ by
        simp only [kernel, norm_pow, norm_inv]
        exact pow_le_pow_left₀ (by positivity)
          (inv_anti₀ (sub_pos.mpr ((mem_disk_iff z).mp hz)) (kernel_denominator_norm_lower z hw)) 2)
  reproduces f hf hfi z hz := by
    let Z := Complex.UnitDisc.mk z ((mem_disk_iff z).mp hz)
    let φ (u : ℂ) : ℂ := (z + u) / (1 + conj z * u)
    have hd {u : ℂ} (hu : u ∈ disk) : 1 + conj z * u ≠ 0 :=
      Z.shift_den_ne_zero (.mk u ((mem_disk_iff u).mp hu))
    have hbij : BijOn φ disk disk := Z.bijOn_shift
    have hφhd {u : ℂ} (hu : u ∈ disk) := Z.hasDerivAt_shift_comp (hasDerivAt_id u) (hd hu)
    have hφ : DifferentiableOn ℂ φ disk := fun _ hu ↦ (hφhd hu).differentiableAt.differentiableWithinAt
    let g (u : ℂ) := (1 + conj z * u)⁻¹ ^ 2 * f (φ u)
    have hpull {u : ℂ} (hu : u ∈ disk) :
        (‖deriv φ u‖ ^ 2 : ℝ) • (kernel z (φ u) * f (φ u)) = g u := by
      have hznorm : ((‖z‖ : ℂ) ^ 2) = conj z * z := by
        rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      have hz2 : 1 - conj z * z ≠ 0 := by
        rw [← hznorm, ← Complex.ofReal_pow, ← Complex.ofReal_one, ← Complex.ofReal_sub]
        exact Complex.ofReal_ne_zero.mpr (by nlinarith [(mem_disk_iff z).mp hz, norm_nonneg z])
      have hdu := hd hu
      have hdu' : 1 + z * conj u ≠ 0 := fun h ↦ hdu (by simpa using congrArg (starRingEnd ℂ) h)
      have h1z : 1 - z * star (φ u) = (1 - conj z * z) / (1 + z * conj u) := by
        simp only [φ, Complex.star_def, map_div₀, map_add, map_one, map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
        field_simp [hdu']; ring
      have hφd : deriv φ u = (1 - conj z * z) / (1 + conj z * u) ^ 2 := by
        simpa [Z, φ, hznorm] using (hφhd hu).deriv
      rw [Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hφd]
      simp only [map_div₀, map_sub, map_one, map_pow, map_add, map_mul,
        RingHomCompTriple.comp_apply, RingHom.id_apply, mul_comm z (conj z)]
      rw [kernel, h1z]; dsimp only [g]
      field_simp [hdu, hdu', hz2]
    have hkf : IntegrableOn (fun w ↦ kernel z w * f w) disk area := by
      change MemLp f 2 diskArea at hfi
      change Integrable _ diskArea
      simpa using integrable_weightedKernel_mul (α := 0) (by norm_num)
        (by simpa using hfi.integrable (by norm_num)) hz
    have hgi : Integrable g diskArea :=
      ((area_integrableOn_image_iff_norm_deriv_sq isOpen_ball hφ hbij.injOn
        (fun w ↦ kernel z w * f w)).mp (hbij.image_eq.symm ▸ hkf)).congr
        (ae_mem_disk.mono fun _ hu ↦ hpull hu)
    have hg : DifferentiableOn ℂ g disk :=
      ((((differentiableOn_id.const_mul (conj z)).const_add 1).inv fun _ hu ↦ hd hu).pow 2).mul
        (hf.comp hφ hbij.mapsTo)
    change (∫ w in disk, kernel z w * f w ∂area) = f z
    rw [← hbij.image_eq, area_integral_image_eq (U := disk) isOpen_ball hφ hbij.injOn,
      show ∫ w in disk, (‖deriv φ w‖ ^ 2 : ℝ) • (kernel z (φ w) * f (φ w)) ∂area = ∫ u, g u ∂diskArea from
        integral_congr_ae (ae_mem_disk.mono fun _ hu ↦ hpull hu),
      integral_diskArea_eq_circleAverage hgi,
      setIntegral_congr_fun measurableSet_Ioo fun r hr ↦ congrArg ((2 * r) • ·) <|
        ((hg.mono (closure_ball_subset_closedBall.trans fun _ hw ↦ (mem_disk_iff _).mpr
          ((mem_closedBall_zero_iff.mp hw).trans_lt (by rw [abs_of_pos hr.1]; exact hr.2)))).diffContOnCl).circleAverage.trans
          (circleAverage_const (g 0) 0 r).symm,
      ← integral_diskArea_eq_circleAverage (integrable_const (g 0)), integral_const, probReal_univ, one_smul]
    simp [g, φ]

theorem memLp_pullback_deriv {U V : Set ℂ} {φ f : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hbij : BijOn φ U V)
    (hf : ContinuousOn f V) (hfi : MemLp f 2 (area.restrict V)) :
    MemLp (fun w ↦ deriv φ w * f (φ w)) 2 (area.restrict U) := by
  have hc : ContinuousOn (fun w ↦ deriv φ w * f (φ w)) U :=
    (hφ.analyticOnNhd hU).deriv.continuousOn.mul (hf.comp hφ.continuousOn hbij.mapsTo)
  refine (memLp_two_iff_integrable_sq_norm (hc.aestronglyMeasurable hU.measurableSet)).mpr ?_
  have hi : IntegrableOn (fun w ↦ ‖f w‖ ^ 2) (φ '' U) area := by
    rw [hbij.image_eq]; exact hfi.integrable_norm_pow two_ne_zero
  simpa only [IntegrableOn, norm_mul, mul_pow, smul_eq_mul] using
    (area_integrableOn_image_iff_norm_deriv_sq hU hφ hbij.injOn _).mp hi

theorem IsBergmanKernel.disk_jacobian_formula {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    (‖deriv φ w‖ ^ 2 : ℝ) • K (φ z) (φ w) = (deriv φ w * kernel z w) / deriv φ z := by
  have hψbij : BijOn ψ Ω disk := hbij.symm hinv.symm
  have hd_mul {u : ℂ} (hu : u ∈ disk) := deriv_comp_eq_one hΩ hφ hψ hbij hinv hu
  have hcol {V : Set ℂ} {L : ℂ → ℂ → ℂ} (hL : IsBergmanKernel V L) (hV : MeasurableSet V)
      {x : ℂ} (hx : x ∈ V) : MemLp (fun y ↦ L y x) 2 (area.restrict V) :=
    (memLp_congr_ae ((ae_restrict_mem hV).mono fun _ hy ↦ (hL.hermitian _ hy x hx).symm)).mp
      (hL.squareIntegrable x hx).star
  let PK (u v : ℂ) := deriv φ u * K (φ u) (φ v) * star (deriv φ v)
  have h1 := isBergmanKernel_disk.reproduces (fun u ↦ PK u w)
    (((hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn.mul
      ((hK.holomorphic _ (hbij.mapsTo hw)).comp hφ hbij.mapsTo)).mul_const _)
    ((memLp_pullback_deriv isOpen_ball hφ hbij (hK.holomorphic _ (hbij.mapsTo hw)).continuousOn
      (hcol hK hΩ.measurableSet (hbij.mapsTo hw))).mul_const _) z hz
  let F (v : ℂ) := deriv ψ v * kernel (ψ v) z
  have hrep := hK.reproduces F
    ((hψ.analyticOnNhd hΩ).deriv.differentiableOn.mul
      ((isBergmanKernel_disk.holomorphic z hz).comp hψ hψbij.mapsTo))
    (memLp_pullback_deriv hΩ hψ hψbij (isBergmanKernel_disk.holomorphic z hz).continuousOn
      (hcol isBergmanKernel_disk measurableSet_disk hz)) (φ w) (hbij.mapsTo hw)
  have h2 : (∫ u, PK w u * kernel u z ∂diskArea) = kernel w z := by
    have hch := area_integral_image_eq (U := disk) isOpen_ball hφ hbij.injOn fun v ↦ K (φ w) v * F v
    rw [hbij.image_eq] at hch
    symm; trans deriv φ w * ∫ v, K (φ w) v * F v ∂area.restrict Ω
    · rw [hrep]; dsimp only [F]; rw [hinv.1 hw]
      linear_combination -(kernel w z * hd_mul hw)
    · rw [hch, ← integral_const_mul]
      refine integral_congr_ae (ae_mem_disk.mono fun u hu ↦ ?_)
      dsimp only [F, PK]
      rw [hinv.1 hu, Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
      simp only [starRingEnd_apply]
      linear_combination (PK w u * kernel u z) * hd_mul hu
  have huni : PK z w = kernel z w := by
    rw [← h1, isBergmanKernel_disk.hermitian z hz w hw, Complex.star_def, ← h2, ← integral_conj]
    refine integral_congr_ae (ae_mem_disk.mono fun u hu ↦ ?_)
    have hK' := hK.hermitian (φ u) (hbij.mapsTo hu) (φ w) (hbij.mapsTo hw)
    have hk' := isBergmanKernel_disk.hermitian z hz u hu
    simp only [PK, map_mul, Complex.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply] at hK' hk' ⊢
    rw [← hK', ← hk']; ring
  rw [Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
    eq_div_iff (right_ne_zero_of_mul_eq_one (hd_mul hz)), ← huni]
  simp only [PK, Complex.star_def]; ring

theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  have : IsFiniteMeasure (area.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbounded.measure_lt_top.ne
  refine ⟨fun hc1 ↦ ?_, ?_⟩
  · by_contra hnd
    refine hc1.not_gt ?_
    obtain ⟨x₀, hx₀⟩ := hconnected.nonempty
    set 𝔖 : Set (Set ℂ) := {S | S ⊆ Ω ∧ IsCompact S}
    set F : (ℂ →ᵤ[𝔖] ℂ) → (ℂ → ℂ) := fun f ↦ UniformOnFun.toFun _ f
    have hF : ∀ {f : ℂ →ᵤ[𝔖] ℂ} {s}, TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) Ω := fun {f s} ↦ by
      have : Tendsto id (𝓝[s] f) (𝓝 f) := tendsto_id'.mpr nhdsWithin_le_nhds
      simpa [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen,
        UniformOnFun.tendsto_iff_tendstoUniformlyOn, 𝔖] using this
    set s : Set (ℂ →ᵤ[𝔖] ℂ) :=
      {f | MapsTo (F f) Ω (ball 0 1) ∧ InjOn (F f) Ω ∧ DifferentiableOn ℂ (F f) Ω ∧
        deriv (F f) x₀ ≠ 0 ∧ F f x₀ = 0}
    have hsd : ∀ f ∈ s, DifferentiableOn ℂ (F f) Ω := fun _ hf ↦ hf.2.2.1
    have hs_ne : s.Nonempty := by
      obtain ⟨M, _, hM⟩ := hbounded.exists_pos_norm_le
      set R : ℝ := 2 * M + 1
      have hR : 0 < R := by positivity
      have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
      refine ⟨UniformOnFun.ofFun 𝔖 (fun z ↦ (z - x₀) / R), fun z hz ↦ ?_,
        fun _ _ _ _ h ↦ sub_left_inj.mp ((div_left_inj' hRc).mp h), by dsimp [F]; fun_prop,
        by simpa [F, (((hasDerivAt_id x₀).sub_const x₀).div_const R).deriv] using hRc, by simp [F]⟩
      rw [mem_ball_zero_iff]; dsimp [F]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR]
      linarith [norm_sub_le z x₀, hM z hz, hM x₀ hx₀]
    have hcmpct := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun _ h ↦ h.2)
      (α := ℂ) (s := s) (F := F) .id
      (fun S ⟨hSΩ, _⟩ z hz ↦ by
        rcases nhds_basis_ball.mem_iff.mp (hopen.mem_nhds (hSΩ hz)) with ⟨r, hr₀, hr⟩
        refine (Metric.equicontinuousAt_of_continuity_modulus (fun y ↦ 2 / r * dist y z)
          (by simpa using ((by fun_prop : Continuous fun y ↦ 2 / r * dist y z).continuousAt (x := z)).tendsto)
          _ ?_).equicontinuousWithinAt _
        filter_upwards [ball_mem_nhds z hr₀] with y hy i
        dsimp only [Function.comp_apply]; rw [dist_comm]
        exact dist_le_div_mul_dist_of_mapsTo_ball ((hsd _ i.2).mono hr)
          (fun w hw ↦ mem_closedBall.mpr <| by
            linarith [(mem_ball_zero_iff.mp (i.2.1 (hr hw))).le,
              (mem_ball_zero_iff.mp (i.2.1 (hr (mem_ball_self hr₀)))).le,
              dist_le_norm_add_norm (F i w) (F i z)]) hy)
      (fun _ hS _ hx ↦ ⟨closedBall 0 1, isCompact_closedBall _ _, fun _ hi ↦
        ball_subset_closedBall (hi.1 (hS.1 hx))⟩)
    have hcl : closure s ⊆
        {f | MapsTo (F f) Ω (ball 0 1) ∧ ((∃ C, EqOn (F f) (const ℂ C) Ω) ∨ InjOn (F f) Ω) ∧
          DifferentiableOn ℂ (F f) Ω ∧ F f x₀ = 0} := by
      intro f hf
      rw [mem_closure_iff_nhdsWithin_neBot] at hf
      have htendsto : TendstoLocallyUniformlyOn F (F f) (𝓝[s] f) Ω := hF
      have hdf : DifferentiableOn ℂ (F f) Ω := htendsto.differentiableOn
        (eventually_mem_nhdsWithin.mono hsd) hopen
      have hf_le : ∀ z ∈ Ω, ‖F f z‖ ≤ 1 := fun z hz ↦
        le_of_tendsto (htendsto.tendsto_at hz).norm <|
          eventually_mem_nhdsWithin.mono fun _ hg ↦ (mem_ball_zero_iff.mp (hg.1 hz)).le
      have hUp := hconnected.isPathConnected.isConnected.isPreconnected
      have hfx₀ : F f x₀ = 0 := tendsto_nhds_unique (htendsto.tendsto_at hx₀) <|
        tendsto_const_nhds.congr' <| eventually_mem_nhdsWithin.mono fun _ hg ↦ hg.2.2.2.2.symm
      refine ⟨?_, or_iff_not_imp_left.mpr fun hfU x hx y hy hxy ↦ ?_, hdf, hfx₀⟩
      · by_contra hf_ball
        obtain ⟨z, hzU, hz⟩ : ∃ z ∈ Ω, 1 ≤ ‖F f z‖ := by simpa [MapsTo] using hf_ball
        have heq : F f x₀ = F f z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
          hUp hopen hdf hzU (fun y hy ↦ (hf_le y hy).trans hz) hx₀
        norm_num [← heq, hfx₀] at hz
      · by_contra! hne
        rcases ((hdf.sub_const (F f x)).analyticAt (hopen.mem_nhds hx)).eventually_eq_zero_or_eventually_ne_zero
          with hfx | hfx
        · exact hfU ⟨F f x, (hdf.analyticOnNhd hopen).eqOn_of_preconnected_of_eventuallyEq
            analyticOnNhd_const hUp hx (hfx.mono fun _ hz ↦ sub_eq_zero.mp hz)⟩
        rw [eventually_nhdsWithin_iff] at hfx
        obtain ⟨R, hR₀, hR⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
          (hfx.and ((hopen.eventually_mem hx).and (compl_singleton_mem_nhds hne)))
        have hRU : closedBall x R ⊆ Ω := fun w hw ↦ (hR hw).2.1
        have hyR : y ∉ closedBall x R := fun hw ↦ (hR hw).2.2 rfl
        obtain ⟨w₀, hw₀, hw₀_min⟩ := (isCompact_sphere x R).exists_isMinOn
          (NormedSpace.sphere_nonempty.mpr hR₀.le)
          ((hdf.sub_const (F f x)).continuousOn.mono (sphere_subset_closedBall.trans hRU)).norm
        let m := ‖F f w₀ - F f x‖ / 2
        have hm : 0 < m := half_pos (norm_pos_iff.mpr
          ((hR (sphere_subset_closedBall hw₀)).1 (ne_of_mem_sphere hw₀ hR₀.ne')))
        have huni := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
          ((isCompact_closedBall x R).insert y)).mp (htendsto.mono (insert_subset hy hRU))
        obtain ⟨i, hi_s, hi_dist⟩ := (eventually_mem_nhdsWithin.and <|
          Metric.tendstoUniformlyOn_iff.mp huni (m / 4) (by positivity)).exists
        have hix : ‖F f x - F i x‖ < m / 4 :=
          by simpa [dist_eq_norm] using hi_dist x (mem_insert_of_mem _ (mem_closedBall_self hR₀.le))
        have hiy : ‖F f y - F i y‖ < m / 4 := by simpa [dist_eq_norm] using hi_dist y (mem_insert _ _)
        have hdc : DiffContOnCl ℂ (F i) (ball x R) :=
          ⟨hi_s.2.2.1.mono (ball_subset_closedBall.trans hRU),
            (hi_s.2.2.1.continuousOn.mono hRU).mono closure_ball_subset_closedBall⟩
        have hmem : F i y ∈ F i '' closedBall x R :=
          hdc.ball_subset_image_closedBall (ε := m) hR₀
            (fun w hw ↦ by
              have hw' : ‖F f w - F i w‖ < m / 4 :=
                by simpa [dist_eq_norm] using hi_dist w (mem_insert_of_mem _ (sphere_subset_closedBall hw))
              have hmin : 2 * m ≤ ‖F f w - F f x‖ := by
                dsimp [m]; linarith [show ‖F f w₀ - F f x‖ ≤ ‖F f w - F f x‖ from hw₀_min hw]
              rw [show F f w - F f x = (F i w - F i x) + (F f w - F i w) - (F f x - F i x) by ring] at hmin
              linarith [norm_add_le (F i w - F i x) (F f w - F i w),
                norm_sub_le ((F i w - F i x) + (F f w - F i w)) (F f x - F i x)])
            (not_eventually.mp (not_eventually_constant_of_injOn hopen hi_s.2.1 hx))
            (mem_ball_iff_norm.mpr <| by
              rw [show F i y - F i x = (F f x - F i x) - (F f y - F i y) by rw [hxy]; ring]
              linarith [norm_sub_le (F f x - F i x) (F f y - F i y)])
        obtain ⟨z, hz, hzy⟩ := hmem
        exact hyR (hi_s.2.1 (hRU hz) hy hzy ▸ hz)
    have hcont : ContinuousOn (fun f ↦ ‖deriv (F f) x₀‖) (closure s) :=
      .mono (.norm fun _ _ ↦ (hF.deriv (eventually_mem_nhdsWithin.mono fun _ hg ↦ hg.2.2.1) hopen).tendsto_at hx₀) hcl
    rcases hcmpct.exists_isMaxOn hs_ne.closure hcont with ⟨f₀, hf₀_mem, hf₀_max⟩
    have hdf₀_x₀ : 0 < ‖deriv (F f₀) x₀‖ := by
      rcases hs_ne with ⟨f', hf'⟩
      exact (norm_pos_iff.mpr hf'.2.2.2.1).trans_le (hf₀_max (subset_closure hf'))
    rcases hcl hf₀_mem with ⟨hf₀_mapsTo, hf₀_inj, hψ, hf₀_x₀⟩
    replace hf₀_inj : InjOn (F f₀) Ω := hf₀_inj.resolve_left fun ⟨C, hC⟩ ↦ by
      rw [(hC.eventuallyEq_of_mem (hopen.mem_nhds hx₀)).deriv_eq] at hdf₀_x₀
      unfold const at hdf₀_x₀; simp at hdf₀_x₀
    have hsurj_ball : SurjOn (F f₀) Ω (ball 0 1) := by
      by_contra! hsurj
      classical
      let f : ℂ → UnitDisc := fun z ↦
        if hz : z ∈ Ω then .mk (F f₀ z) (mem_ball_zero_iff.mp (hf₀_mapsTo hz)) else 0
      have hf_eq : EqOn (UnitDisc.coe ∘ f) (F f₀) Ω := fun z hz ↦ by simp [f, hz]
      have hdf : DifferentiableOn ℂ (UnitDisc.coe ∘ f) Ω := hψ.congr hf_eq
      have hf₀ : f x₀ = 0 := by simp [f, hx₀, hf₀_x₀]
      have hf_inj : InjOn f Ω := fun z hz w hw h ↦
        hf₀_inj hz hw (by simpa [f, hz, hw] using congrArg UnitDisc.coe h)
      have hf_der : deriv (UnitDisc.coe ∘ f) x₀ = deriv (F f₀) x₀ :=
        (hf_eq.eventuallyEq_of_mem (hopen.mem_nhds hx₀)).deriv_eq
      obtain ⟨c, hc⟩ : ∃ c : UnitDisc, ∀ z ∈ Ω, f z ≠ c := by
        by_contra! hall
        exact hsurj fun w hw ↦
          let ⟨z, hz, hzw⟩ := hall (.mk w (mem_ball_zero_iff.mp hw))
          ⟨z, hz, by simpa [f, hz] using congrArg UnitDisc.coe hzw⟩
      have h0not : (0 : UnitDisc) ∉ ((-c).shift ∘ f) '' Ω := by
        rintro ⟨z, hz, h⟩
        exact hc z hz (((-c).shift.eq_symm_apply.mpr h).trans (by change (- -c).shiftFun 0 = c; simp [UnitDisc.shiftFun]))
      have hcs : ContinuousOn ((-c).shift ∘ f) Ω :=
        UnitDisc.isEmbedding_coe.continuousOn_iff.mpr <|
          ((hdf.continuousOn.const_add _).div ((hdf.continuousOn.const_mul _).const_add _)
            fun z _ ↦ (-c).shift_den_ne_zero (f z))
      rcases UnitDisc.exists_continuousOn_pow_eq hconnected hopen hcs h0not 2 with ⟨g, hgc, hgf⟩
      have hg₀ : ∀ z ∈ Ω, g z ≠ 0 := fun z hz h ↦ h0not ⟨z, hz,
        (hgf z).symm.trans (UnitDisc.pow_eq_zero.mpr h)⟩
      have hdg : ∀ z ∈ Ω, HasDerivAt (g · : ℂ → ℂ)
          ((1 - ‖(c : ℂ)‖ ^ 2) / (2 * g z * (1 - conj ↑c * f z) ^ 2) * deriv (f · : ℂ → ℂ) z) z := by
        intro z hz
        convert (hasDerivAt_pow 2 _).of_comp_left
          (UnitDisc.continuous_coe.continuousAt.comp <| hgc.continuousAt <| hopen.mem_nhds hz)
          (UnitDisc.hasDerivAt_shift_comp (-c) (hdf.hasDerivAt (hopen.mem_nhds hz))
            ((-c).shift_den_ne_zero (f z))) _
          (.of_forall fun x ↦ congr(UnitDisc.coe $(hgf x))) using 1
        · rfl
        · simp [Function.comp_def, field]; ring
        · simp [hg₀ z hz]
      let h : ℂ → UnitDisc := (-g x₀).shift ∘ g
      have hg_norm (z : ℂ) : ‖(g z : ℂ)‖ = √‖((-c).shift (f z) : ℂ)‖ := by
        rw [← Real.sqrt_sq (norm_nonneg _), ← norm_pow, ← PNat.val_ofNat, ← UnitDisc.coe_pow,
          hgf, Function.comp_apply]
      have hdhAt (z : ℂ) (hz : z ∈ Ω) :=
        UnitDisc.hasDerivAt_shift_comp (-g x₀) (hdg z hz) ((-g x₀).shift_den_ne_zero (g z))
      have hlt : ‖deriv (F f₀) x₀‖ < ‖deriv (UnitDisc.coe ∘ h) x₀‖ := by
        rw [← hf_der]
        have hgx : ‖(g x₀ : ℂ)‖ = √‖(c : ℂ)‖ := by simp [hg_norm, hf₀]
        have hkey : ‖deriv (UnitDisc.coe ∘ h) x₀‖ =
            ‖deriv (f · : ℂ → ℂ) x₀‖ * (√‖(c : ℂ)‖ + √‖(c⁻¹ : ℂ)‖) / 2 := by
          dsimp only [h, Function.comp_def, UnitDisc.coe_shift]
          rw [(hdhAt x₀ hx₀).deriv]
          simp only [norm_mul, norm_div, ← mul_assoc, conj_mul',
            UnitDisc.coe_neg, map_neg, neg_mul, norm_neg]
          conv_rhs => rw [mul_comm, mul_div_right_comm]
          congr 1; norm_cast
          have hpos₁ : 0 < 1 - ‖(c : ℂ)‖ := sub_pos.2 c.norm_lt_one
          have hpos₂ : 0 < 1 - ‖(c : ℂ)‖ ^ 2 := sub_pos.2 c.sq_norm_lt_one
          simp [field, hgx, hf₀, ← sub_eq_add_neg, abs_of_pos, hpos₁, hpos₂]; ring
        rw [hkey, mul_div_assoc]
        apply lt_mul_of_one_lt_right (hf_der.symm ▸ hdf₀_x₀)
        have hc₀ : 0 < ‖(c : ℂ)‖ := by simpa [hf₀] using (hc x₀ hx₀).symm
        suffices √‖(c : ℂ)‖ * 2 < ‖(c : ℂ)‖ + 1 by simpa [field] using this
        have : √‖(c : ℂ)‖ ≠ 1 := by simp [c.norm_ne_one]
        rw [← sub_ne_zero, ← sq_pos_iff, sub_sq, Real.sq_sqrt (norm_nonneg _)] at this
        linear_combination this
      have hh_inj : InjOn h Ω := (-g x₀).shift.injective.comp_injOn fun z hz w hw hzw ↦ by
        simpa [hgf, hf_inj.eq_iff hz hw] using congr($hzw ^ (2 : ℕ+))
      have hdh : DifferentiableOn ℂ (UnitDisc.coe ∘ h) Ω := fun z hz ↦
        (hdhAt z hz).differentiableAt.differentiableWithinAt
      refine (@hf₀_max (UniformOnFun.ofFun _ (h · : ℂ → ℂ)) (subset_closure ?_)).not_gt hlt
      exact ⟨fun z _ ↦ (h z).2, by simpa [F, InjOn] using hh_inj, hdh,
        norm_pos_iff.mp (hdf₀_x₀.trans hlt), by simp [F, h]⟩
    let ψ := F f₀
    have hψbij : BijOn ψ Ω disk := ⟨hf₀_mapsTo, hf₀_inj, hsurj_ball⟩
    let φ := invFunOn ψ Ω
    have hinv0 := hψbij.invOn_invFunOn
    have hinv : InvOn ψ φ disk Ω := hinv0.symm
    have hbij : BijOn φ disk Ω := hψbij.symm hinv
    have hcont_φ {y : ℂ} (hy : y ∈ disk) : ContinuousAt φ y := by
      have hx := hbij.mapsTo hy
      have hop : 𝓝 (ψ (φ y)) ≤ Filter.map ψ (𝓝 (φ y)) :=
        (hψ.analyticAt (hopen.mem_nhds hx)).eventually_constant_or_nhds_le_map_nhds.resolve_left
          (not_eventually_constant_of_injOn hopen hψbij.injOn hx)
      rw [hinv0.2 hy] at hop
      exact (Filter.map_mono hop).trans <| by
        rw [Filter.map_map]
        exact tendsto_id.congr' ((hopen.eventually_mem hx).mono fun _ hz ↦ (hinv0.1 hz).symm)
    have hφ : DifferentiableOn ℂ φ disk := fun y hy ↦ by
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
        (hcont_φ hy)).differentiableAt.differentiableWithinAt
      have hcrit : ∀ᶠ z in 𝓝[≠] (φ y), deriv ψ z ≠ 0 :=
        ((hψ.analyticOnNhd hopen).deriv _ (hbij.mapsTo hy)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
          fun hzero ↦ by
            obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp
              (hzero.and (hopen.eventually_mem (hbij.mapsTo hy)))
            exact not_eventually_constant_of_injOn hopen hψbij.injOn (hbij.mapsTo hy)
              (mem_of_superset (ball_mem_nhds _ hr) fun z hz ↦ isOpen_ball.is_const_of_deriv_eq_zero
                (convex_ball _ r).isPreconnected (hψ.mono fun _ h ↦ (hrU h).2)
                (fun _ h ↦ (hrU h).1) hz (mem_ball_self hr))
      rw [eventually_nhdsWithin_iff] at hcrit
      filter_upwards [((hcont_φ hy).tendsto.eventually hcrit).filter_mono nhdsWithin_le_nhds,
        (isOpen_ball.eventually_mem hy).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with z hz hzV hzne
      exact ((hψ.differentiableAt (hopen.mem_nhds (hbij.mapsTo hzV))).hasDerivAt.of_local_left_inverse
        (hcont_φ hzV) (hz fun heq ↦ hzne <| (hinv0.2 hzV).symm.trans ((congrArg ψ heq).trans (hinv0.2 hy)))
        ((isOpen_ball.eventually_mem hzV).mono fun _ hw ↦ hinv0.2 hw)).differentiableAt
    have hne {z : ℂ} (hz : z ∈ disk) : deriv φ z ≠ 0 :=
      right_ne_zero_of_mul_eq_one (deriv_comp_eq_one hopen hφ hψ hbij hinv hz)
    have hsub : ball (0 : ℂ) (1 / 2) ⊆ disk := ball_subset_ball (by norm_num)
    let E := φ '' ball 0 (1 / 2)
    have hEopen : IsOpen E := by
      rw [isOpen_iff_mem_nhds]
      rintro _ ⟨w, hw, rfl⟩
      exact ((hφ.mono hsub).analyticAt (isOpen_ball.mem_nhds hw)).eventually_constant_or_nhds_le_map_nhds.resolve_left
        (not_eventually_constant_of_injOn isOpen_ball (hbij.injOn.mono hsub) hw)
        (image_mem_map (isOpen_ball.mem_nhds hw))
    have hq : DifferentiableOn ℂ (deriv φ) disk := (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
    have hp2 {p : ℂ × ℂ} (hp : p ∈ closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) (1 / 2)) : p.2 ∈ disk :=
      (mem_disk_iff _).mpr ((mem_closedBall_zero_iff.mp hp.2).trans_lt (by norm_num))
    have hprod : ContinuousOn (fun p : ℂ × ℂ ↦ deriv φ p.2 * kernel p.1 p.2)
        (closedBall 0 1 ×ˢ closedBall 0 (1 / 2)) :=
      (hq.continuousOn.comp continuous_snd.continuousOn fun _ hp ↦ hp2 hp).mul
        (((continuousOn_const.sub (continuous_fst.continuousOn.mul
          continuous_snd.star.continuousOn)).inv₀ fun _ hp ↦
            kernel_denominator_ne_zero_closed_left (mem_closedBall_zero_iff.mp hp.1) (hp2 hp)).pow 2)
    let ν := area.restrict (ball 0 (1 / 2))
    have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr isBounded_ball.measure_lt_top.ne
    have hν : ∀ᵐ w ∂ν, w ∈ closedBall 0 (1 / 2) :=
      (ae_restrict_mem isOpen_ball.measurableSet).mono fun _ hw ↦ ball_subset_closedBall hw
    have hc_int {F : ℂ → ℂ → ℂ}
        (hF : ContinuousOn (fun p : ℂ × ℂ ↦ F p.1 p.2) (closedBall 0 1 ×ˢ closedBall 0 (1 / 2))) :
        ContinuousOn (fun z ↦ ∫ w, F z w ∂ν) (closedBall 0 1) := by
      obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) 1).prod
        (isCompact_closedBall (0 : ℂ) (1 / 2))).bddAbove_image hF.norm
      exact continuousOn_of_dominated (bound := fun _ ↦ M)
        (fun z hz ↦ by
          have hc : ContinuousOn (F z) (closedBall 0 (1 / 2)) :=
            hF.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hw ↦ ⟨hz, hw⟩
          simpa only [Measure.restrict_eq_self_of_ae_mem hν] using
            hc.aestronglyMeasurable isClosed_closedBall.measurableSet (μ := ν))
        (fun z hz ↦ hν.mono fun w hw ↦ hM (mem_image_of_mem _ (mk_mem_prod hz hw)))
        (integrable_const M)
        (hν.mono fun w hw ↦ hF.comp (continuous_id.prodMk continuous_const).continuousOn
          fun _ hz ↦ ⟨hz, hw⟩)
    have hslice_cont {ζ : ℂ} (hζ : ζ ∈ closedBall 0 1) :
        ContinuousOn (fun w ↦ deriv φ w * kernel ζ w) (closedBall 0 (1 / 2)) :=
      hprod.comp (continuous_const.prodMk continuous_id).continuousOn fun _ hw ↦ ⟨hζ, hw⟩
    have hslice_int {ζ : ℂ} (hζ : ζ ∈ closedBall 0 1) :
        Integrable (fun w ↦ deriv φ w * kernel ζ w) ν :=
      ((hslice_cont hζ).integrableOn_compact (isCompact_closedBall 0 _)).mono_set ball_subset_closedBall
    have hI_cont := (hc_int (F := fun ζ w ↦ deriv φ w * kernel ζ w) hprod).norm
    have hJ_cont : ContinuousOn (fun ζ ↦ ∫ w, ‖deriv φ w * kernel ζ w‖ ∂ν) (closedBall 0 1) :=
      (Complex.continuous_re.comp_continuousOn
        (hc_int (F := fun ζ w ↦ (‖deriv φ w * kernel ζ w‖ : ℂ))
          (Complex.continuous_ofReal.comp_continuousOn hprod.norm))).congr fun _ hζ ↦ by
        simpa using integral_re (f := fun w ↦ (‖deriv φ w * kernel _ w‖ : ℂ)) (hslice_int hζ).norm.ofReal
    have hJ_pos {ζ : ℂ} (hζ : ζ ∈ closedBall 0 1) :
        0 < ∫ w, ‖deriv φ w * kernel ζ w‖ ∂ν := by
      have hζn : ‖ζ‖ ≤ 1 := by simpa using hζ
      refine (integral_pos_iff_support_of_nonneg (fun _ ↦ norm_nonneg _) (hslice_int hζ).norm).mpr ?_
      have hsupp : ball 0 (1 / 2) ⊆ support fun w ↦ ‖deriv φ w * kernel ζ w‖ :=
        fun w hw ↦ norm_ne_zero_iff.mpr <| mul_ne_zero (hne (hsub hw))
          (pow_ne_zero 2 (inv_ne_zero (kernel_denominator_ne_zero_closed_left hζn (hsub hw))))
      exact (measure_ball_pos area (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)).trans_le
        (by simpa [ν] using measure_mono (μ := ν) hsupp)
    obtain ⟨ζ₀, hζ₀, hmax⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_isMaxOn ⟨0, by simp⟩
      (hI_cont.div hJ_cont fun _ hζ ↦ (hJ_pos hζ).ne')
    have hlt : (‖∫ w, deriv φ w * kernel ζ₀ w ∂ν‖) < ∫ w, ‖deriv φ w * kernel ζ₀ w‖ ∂ν :=
      lt_of_le_of_ne (norm_integral_le_integral_norm _) fun heq ↦ by
        have hζn : ‖ζ₀‖ ≤ 1 := by simpa using hζ₀
        let g (w : ℂ) := deriv φ w * kernel ζ₀ w
        let c₀ := ∫ w, g w ∂ν
        have hc₀ : c₀ ≠ 0 := norm_pos_iff.mp (heq ▸ hJ_pos hζ₀)
        have hg := (hslice_int hζ₀).div_const c₀
        have hre : (fun z ↦ (g z / c₀).re) =ᵐ[ν] fun z ↦ ‖g z / c₀‖ :=
          (integral_eq_iff_of_ae_le hg.re hg.norm (.of_forall fun _ ↦ Complex.re_le_norm _)).mp <| by
            simp_rw [norm_div]
            rw [integral_re hg, integral_div, div_self hc₀, integral_div, ← heq,
              div_self (norm_ne_zero_iff.mpr hc₀)]
            rfl
        have hphase := Measure.eqOn_open_of_ae_eq
          (hre.mono fun z hz ↦ show (g z / c₀).im = 0 from
            Complex.abs_re_eq_norm.mp (by dsimp only at hz; rw [hz, abs_of_nonneg (norm_nonneg _)]))
          isOpen_ball
          (Complex.continuous_im.comp_continuousOn (((hslice_cont hζ₀).mono ball_subset_closedBall).div_const c₀))
          continuousOn_const
        let G (w : ℂ) := deriv φ w * (1 - star ζ₀ * w) ^ 2 / c₀
        have hGd : DifferentiableOn ℂ G disk :=
          (hq.mul (((differentiableOn_const 1).sub
            ((differentiableOn_const (star ζ₀)).mul differentiableOn_id)).pow 2)).div_const c₀
        have hinner : ∀ w ∈ ball 0 (1 / 2), (G w).im = 0 := fun w hw ↦ by
          have hd := kernel_denominator_ne_zero_closed_left hζn (hsub hw)
          have hform : G w = (g w / c₀) * (‖1 - ζ₀ * star w‖ ^ 4 : ℝ) := by
            rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← Complex.normSq_eq_norm_sq]
            push_cast
            rw [← Complex.mul_conj, show conj (1 - ζ₀ * star w) = 1 - star ζ₀ * w by simp]
            dsimp [G, g, kernel]
            simp only [← starRingEnd_apply] at hd ⊢
            field_simp [hd, hc₀]
          rw [hform, Complex.mul_im, Complex.ofReal_im, show (g w / c₀).im = 0 from hphase hw]; ring
        obtain ⟨d₀, hd₀⟩ := ((hGd.analyticOnNhd isOpen_ball).mono hsub).eq_const_of_im_eq_const
          hinner isOpen_ball ⟨⟨0, mem_ball_self (by norm_num)⟩, (convex_ball 0 _).isPreconnected⟩
        have hderiv (w : ℂ) (hw : w ∈ disk) : deriv φ w * (1 - star ζ₀ * w) ^ 2 = deriv φ 0 := by
          have hval : G w = G 0 :=
            ((hGd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
              (convex_ball 0 1).isPreconnected (by simp [disk])
              ((isOpen_ball.eventually_mem (mem_ball_self (by norm_num))).mono hd₀) hw).trans
              (hd₀ 0 (mem_ball_self (by norm_num))).symm
          dsimp [G] at hval; simpa using (div_left_inj' hc₀).mp hval
        have hφ0 : deriv φ 0 ≠ 0 := hne (by simp)
        have hden {w : ℂ} (hw : w ∈ disk) : 1 - star ζ₀ * w ≠ 0 := by
          simpa using kernel_denominator_ne_zero_closed_left (show ‖star ζ₀‖ ≤ 1 by simpa using hζn)
            (show star w ∈ disk by simpa [mem_disk_iff] using hw)
        let H (w : ℂ) := φ 0 + deriv φ 0 * w / (1 - star ζ₀ * w)
        have hH {w : ℂ} (hw : w ∈ disk) : HasDerivAt H (deriv φ w) w := by
          have hn := hden hw
          convert (((hasDerivAt_id w).const_mul (deriv φ 0)).div
            ((hasDerivAt_const w 1).sub ((hasDerivAt_id w).const_mul (star ζ₀))) hn).const_add (φ 0) using 1
          · rfl
          · simp only [Pi.sub_apply, id_eq, (eq_div_iff (pow_ne_zero 2 hn)).mpr (hderiv w hw)]; ring
        have heq_img : Ω = H '' disk := by
          rw [← show φ '' disk = Ω from hbij.image_eq]
          refine image_congr fun w hw ↦ ?_
          have heq' := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball 0 1).isPreconnected
            (hφ.sub fun u hu ↦ (hH hu).differentiableAt.differentiableWithinAt)
            (fun u hu ↦ by
              simpa using (((hφ u hu).differentiableAt (isOpen_ball.mem_nhds hu)).hasDerivAt.sub (hH hu)).deriv)
            hw (show (0 : ℂ) ∈ disk by simp [disk])
          simpa [H] using sub_eq_zero.mp (by simpa [H] using heq')
        have hζlt : ‖ζ₀‖ < 1 := lt_of_le_of_ne hζn fun hζ1 ↦ by
          obtain ⟨M, _, hM⟩ := (heq_img ▸ hbounded).exists_pos_norm_le
          let N : ℝ := (M + ‖φ 0‖ + 1) / ‖deriv φ 0‖
          have hN : 0 < N := div_pos (by positivity) (norm_pos_iff.mpr hφ0)
          have hw : ((N / (N + 1) : ℝ) : ℂ) * ζ₀ ∈ disk := by
            rw [mem_disk_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), hζ1, mul_one]
            exact (div_lt_one (by positivity)).mpr (by linarith)
          have hb : ‖H (((N / (N + 1) : ℝ) : ℂ) * ζ₀)‖ ≤ M := hM _ ⟨_, hw, rfl⟩
          have hζm : conj ζ₀ * ζ₀ = 1 := by
            rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hζ1]; norm_num
          have hN1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : N + 1 ≠ 0)
          have hval : H (((N / (N + 1) : ℝ) : ℂ) * ζ₀) = φ 0 + deriv φ 0 * ζ₀ * N := by
            dsimp [H]
            rw [show conj ζ₀ * (↑(N / (N + 1)) * ζ₀) = ↑(N / (N + 1)) * (conj ζ₀ * ζ₀) by ring,
              hζm, mul_one]
            push_cast; field_simp [hN1]; ring
          rw [hval] at hb
          have hn := norm_sub_le (φ 0 + deriv φ 0 * ζ₀ * N) (φ 0)
          simp only [add_sub_cancel_left, norm_mul, hζ1, mul_one, Complex.norm_real, Real.norm_of_nonneg hN.le] at hn
          have hNm := div_mul_cancel₀ (M + ‖φ 0‖ + 1) (norm_ne_zero_iff.mpr hφ0)
          dsimp [N] at hn; linarith
        let d : ℝ := 1 - ‖ζ₀‖ ^ 2
        have hd : 0 < d := by dsimp [d]; nlinarith [norm_nonneg ζ₀]
        have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
        let Z := Complex.UnitDisc.mk ζ₀ hζlt
        let c : ℂ := φ 0 + deriv φ 0 * ζ₀ / (d : ℂ)
        let s : ℂ := deriv φ 0 / (d : ℂ)
        have hs : s ≠ 0 := div_ne_zero hφ0 hdc
        have hform {w : ℂ} (hw : w ∈ disk) : H w = c + s * ((-ζ₀ + w) / (1 + conj (-ζ₀) * w)) := by
          have hn : 1 - conj ζ₀ * w ≠ 0 := hden hw
          have hn' : 1 - w * conj ζ₀ ≠ 0 := by rwa [mul_comm]
          have hnorm : ((‖ζ₀‖ ^ 2 : ℝ) : ℂ) = conj ζ₀ * ζ₀ := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
          dsimp [H, c, s]; simp only [map_neg, neg_mul, ← sub_eq_add_neg]
          field_simp [hn, hn', hdc]; dsimp [d]; push_cast; rw [← Complex.ofReal_pow, hnorm]; ring
        refine hnd ⟨c, ‖s‖, norm_pos_iff.mpr hs, heq_img.trans ?_⟩
        rw [image_congr fun _ hw ↦ hform hw, ← image_image (fun u ↦ c + s * u)]
        erw [(-Z).bijOn_shift.image_eq]
        ext z; simp only [mem_image, mem_ball_iff_norm, sub_zero]
        exact ⟨by rintro ⟨u, hu, rfl⟩; simpa [norm_mul] using mul_lt_of_lt_one_right (norm_pos_iff.mpr hs) hu,
          fun hz ↦ ⟨(z - c) / s, by rwa [norm_div, div_lt_one (norm_pos_iff.mpr hs)], by field_simp [hs]; ring⟩⟩
    let η := 1 - (‖∫ w, deriv φ w * kernel ζ₀ w ∂ν‖) / ∫ w, ‖deriv φ w * kernel ζ₀ w‖ ∂ν
    have hη : 0 < η := sub_pos.mpr ((div_lt_one (hJ_pos hζ₀)).mpr hlt)
    have hη1 : η ≤ 1 := sub_le_self 1 (div_nonneg (norm_nonneg _) (hJ_pos hζ₀).le)
    let μ := area.restrict Ω
    have hE : MeasurableSet E := hEopen.measurableSet
    have hEsub : E ⊆ Ω := fun _ ⟨w, hw, h⟩ ↦ h ▸ hbij.mapsTo (hsub hw)
    have hre : μ.restrict E = area.restrict E := by
      rw [Measure.restrict_restrict hE, inter_eq_left.mpr hEsub]
    have hEr : 0 < μ.real E := ENNReal.toReal_pos
      (by rw [show μ E = area E by rw [Measure.restrict_apply hE, inter_eq_left.mpr hEsub]]
          exact (hEopen.measure_pos area ⟨φ 0, 0, mem_ball_self (by norm_num), rfl⟩).ne')
      (measure_ne_top _ _)
    let f (w : ℂ) : ℂ := 1 - E.indicator (fun _ ↦ (η : ℂ)) w
    have hfn (w : ℂ) : ‖f w‖ = 1 - E.indicator (fun _ ↦ η) w := by
      by_cases hw : w ∈ E
      · simp only [f, indicator_of_mem hw, ← Complex.ofReal_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hη1)]
      · simp [f, hw]
    have hf : Integrable f μ := (integrable_const (1 : ℂ)).sub ((integrable_const (η : ℂ)).indicator hE)
    have hmass : (∫⁻ z, ‖f z‖ₑ ∂μ) < μ univ := by
      rw [← ofReal_integral_norm_eq_lintegral_enorm hf]
      simp_rw [hfn]
      rw [integral_sub (integrable_const 1) ((integrable_const η).indicator hE),
        integral_indicator hE, integral_const, setIntegral_const, smul_eq_mul, mul_one, smul_eq_mul]
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
        (ENNReal.ofReal_lt_ofReal_iff (hEr.trans_le (measureReal_mono (subset_univ E)))).mpr
          (sub_lt_self (μ.real univ) (mul_pos hEr hη))
    have hout : ∀ᵐ a ∂μ, 1 ≤ domainPositiveProjection Ω K f a :=
      (ae_restrict_mem hopen.measurableSet).mono fun a ha ↦ by
        obtain ⟨z, hz, rfl⟩ := hbij.surjOn ha
        have hI_eq : (∫ w in E, K (φ z) w ∂area) = (∫ w, deriv φ w * kernel z w ∂ν) / deriv φ z := by
          rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub), ← integral_div]
          exact integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun w hw ↦
            hK.disk_jacobian_formula hopen hφ hψ hbij hinv hz (hsub hw))
        have hJ_eq : (∫ w in E, ‖K (φ z) w‖ ∂area) = (∫ w, ‖deriv φ w * kernel z w‖ ∂ν) / ‖deriv φ z‖ := by
          rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub), ← integral_div]
          refine integral_congr_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun w hw ↦ ?_)
          simpa only [norm_smul, Real.norm_eq_abs, abs_sq, norm_div, smul_eq_mul] using
            congrArg norm (hK.disk_jacobian_formula hopen hφ hψ hbij hinv hz (hsub hw))
        have hgap0 : ‖∫ w, deriv φ w * kernel z w ∂ν‖ ≤ (1 - η) * ∫ w, ‖deriv φ w * kernel z w‖ ∂ν := by
          have hb := (div_le_iff₀ (hJ_pos (ball_subset_closedBall hz))).mp (hmax (ball_subset_closedBall hz))
          dsimp only [Pi.div_apply, η] at hb ⊢; linarith
        have hg : ‖∫ w in E, K (φ z) w ∂μ‖ ≤ (1 - η) * ∫ w in E, ‖K (φ z) w‖ ∂μ := by
          rw [hre, hI_eq, hJ_eq, norm_div, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right hgap0 (norm_nonneg _)
        have hk : Integrable (K (φ z)) μ := (hK.squareIntegrable (φ z) ha).integrable (by norm_num)
        have hsp1 := integral_add_compl hE hk
        have hsp2 := integral_add_compl hE hk.norm
        have htri := norm_add_le (∫ w in E, K (φ z) w ∂μ) (∫ w in Eᶜ, K (φ z) w ∂μ)
        have hsec : (∫ w, K (φ z) w ∂μ) = 1 := by
          simpa only [mul_one] using hK.reproduces (fun _ ↦ 1) (differentiableOn_const 1) (memLp_const 1) (φ z) ha
        rw [hsp1, hsec, norm_one] at htri
        have hcomp := norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) (K (φ z))
        have heq (w : ℂ) : ‖K (φ z) w‖ * ‖f w‖ = ‖K (φ z) w‖ - E.indicator (fun w ↦ η * ‖K (φ z) w‖) w := by
          rw [hfn]; by_cases hw : w ∈ E <;> simp [hw]; ring
        have hge : 1 ≤ ∫ w, ‖K (φ z) w‖ * ‖f w‖ ∂μ := by
          simp_rw [heq]
          rw [integral_sub hk.norm ((hk.norm.const_mul η).indicator hE),
            integral_indicator hE, integral_const_mul]
          nlinarith
        have hi : Integrable (fun w ↦ ‖K (φ z) w‖ * ‖f w‖) μ :=
          (hk.norm.sub ((hk.norm.const_mul η).indicator hE)).congr (.of_forall fun w ↦ (heq w).symm)
        refine (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal hge).trans_eq ?_
        rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ ↦ by positivity), domainPositiveProjection]
        exact lintegral_congr fun _ ↦ by rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    exact ((ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inr one_ne_zero)).2
      (by simpa only [one_mul] using hmass)).trans_le
      (measure_univ_div_mass_le_weakTypeConstant_of_witness hf hout)
  · rintro ⟨a, R, hR, rfl⟩
    have hlo : 1 ≤ weakTypeConstant (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) := by
      have hout : ∀ᵐ z ∂area.restrict (ball a R), 1 ≤ domainPositiveProjection (ball a R) K (fun _ ↦ 1) z :=
        (ae_restrict_mem isOpen_ball.measurableSet).mono fun z hz ↦ by
          have hnorm := enorm_integral_le_lintegral_enorm (μ := area.restrict (ball a R)) (K z)
          have hsec : (∫ w, K z w ∂area.restrict (ball a R)) = 1 := by
            simpa only [mul_one] using hK.reproduces (fun _ ↦ 1) (differentiableOn_const 1) (memLp_const 1) z hz
          rw [hsec] at hnorm
          simpa [domainPositiveProjection, ← ofReal_norm] using hnorm
      have huniv : (area.restrict (ball a R)) univ ≠ 0 := by simpa using (measure_ball_pos area a hR).ne'
      simpa only [enorm_one, lintegral_const, one_mul, ENNReal.div_self huniv (measure_ne_top _ _)] using
        measure_univ_div_mass_le_weakTypeConstant_of_witness (integrable_const (1 : ℂ)) hout
    refine le_antisymm (sInf_le fun f hf t ht ↦ ?_) hlo
    have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    let e : ℂ ≃ᵐ ℂ :=
      { toFun := fun w ↦ a + (R : ℂ) * w, invFun := fun z ↦ (z - a) / (R : ℂ),
        left_inv := fun _ ↦ by field_simp [hRc]; ring,
        right_inv := fun _ ↦ by field_simp [hRc]; ring,
        measurable_toFun := by simp; fun_prop,
        measurable_invFun := by simp; fun_prop }
    have he : DifferentiableOn ℂ e disk := by simp [e]; fun_prop
    have hg : DifferentiableOn ℂ e.symm (ball a R) := by simp [e]; fun_prop
    have hinv : InvOn e.symm e disk (ball a R) :=
      ⟨fun _ _ ↦ e.symm_apply_apply _, fun _ _ ↦ e.apply_symm_apply _⟩
    have hbij : BijOn e disk (ball a R) :=
      ⟨fun w hw ↦ by
          simpa [e, dist_eq_norm, norm_mul, abs_of_pos hR] using mul_lt_of_lt_one_right hR ((mem_disk_iff w).mp hw),
        e.injective.injOn,
        fun z hz ↦ ⟨e.symm z, by
          simpa [e, mem_disk_iff, abs_of_pos hR, div_lt_one hR] using mem_ball_iff_norm.mp hz,
          e.apply_symm_apply z⟩⟩
    have hde (w : ℂ) : deriv e w = R := by simp [e]
    let c := ENNReal.ofReal (R ^ 2)
    have hμ : area.restrict (ball a R) = c • Measure.map e diskArea := by
      ext T hT
      rw [Measure.smul_apply, smul_eq_mul, e.map_apply, ← lintegral_indicator_one hT,
        ← hbij.image_eq, area, Measure.restrict_smul, lintegral_smul_measure,
        lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_disk
          (hasFDerivWithinAt_real isOpen_ball he) hbij.injOn (T.indicator 1)]
      simp_rw [det_complex_derivative, abs_sq, hde, Complex.norm_real, Real.norm_of_nonneg hR.le]
      change ENNReal.ofReal π⁻¹ • (∫⁻ w in disk, c * T.indicator 1 (e w)) = _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator_one (e.measurable hT),
        diskArea, area, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, smul_eq_mul,
        ← mul_assoc, mul_comm (ENNReal.ofReal π⁻¹), mul_assoc]
      exact congrArg (c * ·) (congrArg _ (lintegral_congr fun w ↦ by by_cases hw : e w ∈ T <;> simp [hw]))
    have hproj {z : ℂ} (hz : z ∈ disk) :
        domainPositiveProjection (ball a R) K f (e z) = positiveProjection (f ∘ e) z := by
      rw [domainPositiveProjection, hμ, lintegral_smul_measure, e.measurableEmbedding.lintegral_map,
        smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_congr_ae (ae_mem_disk.mono fun w hw ↦ ?_)
      have hjac := congrArg norm (hK.disk_jacobian_formula isOpen_ball he hg hbij hinv hz hw)
      simp only [hde, Complex.norm_real, Real.norm_of_nonneg hR.le, norm_smul, Real.norm_eq_abs,
        abs_sq, norm_div, norm_mul] at hjac
      rw [mul_div_cancel_left₀ _ hR.ne'] at hjac
      dsimp only
      rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg R), hjac]; rfl
    have hfi : Integrable (f ∘ e) diskArea :=
      e.measurableEmbedding.integrable_map_iff.mp <|
        (integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR))
          ENNReal.ofReal_ne_top).mp (hμ ▸ hf)
    have hbound := isWeakTypeBound_weightedPositiveProjection (α := 0) (by norm_num)
      (f ∘ e) (by simpa using hfi) t ht
    simp only [gammaConstant_zero, ENNReal.ofReal_one, one_mul, weightedArea_zero,
      weightedPositiveProjection_zero] at hbound
    rw [hμ, Measure.smul_apply, smul_eq_mul, e.map_apply,
      measure_congr (t := {z | ENNReal.ofReal t < positiveProjection (f ∘ e) z})
        (ae_mem_disk.mono fun w hw ↦ propext (by simp [hproj hw])),
      lintegral_smul_measure, e.measurableEmbedding.lintegral_map, one_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (ENNReal.ofReal t) c, mul_assoc]
    exact mul_le_mul_right hbound c

end BergmanWeakType
