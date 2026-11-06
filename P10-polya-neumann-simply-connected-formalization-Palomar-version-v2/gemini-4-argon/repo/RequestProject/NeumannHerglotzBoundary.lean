module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.DenseEmbedding
public import RequestProject.NeumannBoundaryResolvent

/-!
# The genuine Herglotz wave as Neumann boundary data

The H¹ lift below is built from the actual Herglotz coefficient and its
actual classical derivatives. Complex Green's formula gives its prescribed
conormal load with ordinary parameter measure `dθ`. The continuous trace is
identified with its actual boundary values by a smooth cutoff which is one
near the closure of the domain.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Metric
open scoped Real InnerProductSpace ComplexConjugate ContDiff

variable {Ω : Set ℂ} {a : ℝ → ℂ} {γ : ℝ → ℂ}

/-- Closing the derivative formula under differentiation proves genuine
smoothness of every Herglotz coefficient. -/
theorem contDiff_herglotzCoeff_infty 
    (ha : IntervalIntegrable a volume 0 (2 * π)) k m :
    ContDiff ℝ ∞ (herglotzCoeff k a m) := by
  exact contDiff_infty.2 (fun n => (show ∀ n : ℕ, ∀ m : ℤ, ContDiff ℝ n (herglotzCoeff k a m) by
    intro n
    induction n with
    | zero =>
        intro m
        exact contDiff_zero.2 (continuous_herglotzCoeff ha k m)
    | succ n ih =>
        intro m
        rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = n + 1 by simp,
          contDiff_succ_iff_fderiv]
        refine ⟨differentiable_herglotzCoeff ha k m, by simp, ?_⟩
        rw [show fderiv ℝ (herglotzCoeff k a m) = fun z => (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) • ContinuousLinearMap.id ℝ ℂ + (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) • Complex.conjCLE.toContinuousLinearMap by
          funext z
          ext1 w
          rw [fderiv_herglotzCoeff_apply ha]
          simp
          ring]
        exact ((contDiff_const.mul (ih (m + 1))).smul_const _).add
          ((contDiff_const.mul (ih (m - 1))).smul_const _)) n m)

lemma herglotzCoeff_memLp_domain  (hb : Bornology.IsBounded Ω)
     (ha : IsDirDensity a) k m :
    MemLp (herglotzCoeff k a m) 2 (volume.restrict Ω) :=
  memLp_of_continuous_bounded hb (continuous_herglotzCoeff ha.intervalIntegrable k m)
    (fun z => norm_herglotzCoeff_le k m z)

lemma herglotzCoeff_memLp_deriv_domain  (hb : Bornology.IsBounded Ω)
     (ha : IsDirDensity a) k m i :
    MemLp (fun z => fderiv ℝ (herglotzCoeff k a m) z (coordDir i)) 2 (volume.restrict Ω) := by
  apply memLp_of_continuous_bounded hb (((contDiff_herglotzCoeff ha.intervalIntegrable k m).continuous_fderiv (by simp)).clm_apply continuous_const)
  intro z
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_herglotzCoeff_le ha.intervalIntegrable k m z)
      (norm_nonneg _))

/-- The actual Herglotz wave in the weak-gradient H¹ space. Coefficient zero
is exactly `herglotzWave`, and its classical derivatives are retained. -/
def herglotzWaveH1  (hb : Bornology.IsBounded Ω)
     (ha : IsDirDensity a) (k : ℝ) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_of_contDiff_one (contDiff_herglotzCoeff ha.intervalIntegrable k 0)
    (herglotzCoeff_memLp_domain hb ha k 0)
    (herglotzCoeff_memLp_deriv_domain hb ha k 0))

@[simp] theorem h1Value_herglotzWaveH1  hb
     ha k :
    h1Value Ω (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_domain hb ha k 0).toLp (herglotzCoeff k a 0) := rfl

@[simp] theorem h1Gradient_herglotzWaveH1  hb
     ha k i :
    h1Gradient Ω i (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_deriv_domain hb ha k 0 i).toLp
        (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) := rfl

local notation "Φ0" => IsBoundaryParam Ω γ

lemma herglotzConormal_memLp_boundary  
    (hγ : Φ0)  (ha : IsDirDensity a) k :
    MemLp (herglotzConormal k a γ) 2 (volume.restrict (Ioc 0 (2 * π))) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)

/-- The actual density `D u(γ θ)(-i γ'(θ))`, not the unweighted unit-normal
derivative. Its boundary measure is ordinary `dθ`. -/
def herglotzConormalL2   (hγ : Φ0)
     (ha : IsDirDensity a) (k : ℝ) : BoundaryL2 :=
  (herglotzConormal_memLp_boundary hγ ha k).toLp (herglotzConormal k a γ)

theorem herglotzConormalL2_ae   (hγ : Φ0)
     (ha : IsDirDensity a) k :
    (herglotzConormalL2 hγ ha k : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioc 0 (2 * π))] herglotzConormal k a γ :=
  (herglotzConormal_memLp_boundary hγ ha k).coeFn_toLp

/-- A smooth compactly supported representative equal to the actual wave
near the closure of the domain identifies its genuine trace. -/
theorem exists_smoothTraceTest_herglotz  (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω)  (hγ : Φ0)
     (ha : IsDirDensity a) k :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ θ ∈ Icc 0 (2 * π), f (γ θ) = herglotzCoeff k a 0 (γ θ) := by
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ closure Ω ⊆ ball 0 R := by
    obtain ⟨R, hR⟩ := hb.closure.subset_ball 0
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  obtain ⟨χ, hχs, hχc, hχ1⟩ := exists_cutoff_one_on_ball R hR0
  let f : smoothTraceTests := ⟨fun z => χ z * herglotzCoeff k a 0 z,
    ⟨(Complex.ofRealCLM.contDiff.comp hχs).mul
      (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0),
      (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
      subset_univ _⟩⟩
  have hf : ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
    intro z hz
    simp [f, hχ1 z (ball_subset_closedBall (hR hz))]
  refine ⟨f, ?_, ?_⟩
  · apply h1Value_injective hL.1.1
    rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem hL.1.1.measurableSet] with z hz
    exact hf z (subset_closure hz)
  · intro θ hθ
    exact hf _ (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ))

private lemma inner_toLp_pair {α : Type*} [MeasurableSpace α] {μ}
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, conj (f x) * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

private lemma integrable_conj_mul_of_memLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => conj (f x) * g x) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

/-- Every genuine Herglotz wave solves the weak Helmholtz equation with its
own actual conormal data. Smooth Green's formula extends to all H¹ tests
through the already established density theorem. -/
theorem herglotzWaveH1_isBoundaryNeumannSolution 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
     (hγ : Φ0) 
    (ha : IsDirDensity a) k :
    IsBoundaryNeumannSolution hb hL hγ (k ^ 2)
      (herglotzConormalL2 hγ ha k) (herglotzWaveH1 hb ha k) := by
  apply (isBoundaryNeumannSolution_iff_form_eq hb hL hγ (k ^ 2) _ _).2
  apply ext_inner_left ℂ
  intro v
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on v
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro f
  rw [smoothTraceH1Lin_apply, h1BoundaryLoad_inner]
  exact (by
    have hi : ∀ i : Fin 2, IntegrableOn
        (fun z => conj (fderiv ℝ f z (coordDir i)) *
          fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) Ω := fun i =>
      integrable_conj_mul_of_memLp ((f.property.dirD (coordDir i)).memLp' 2)
        (herglotzCoeff_memLp_deriv_domain hb ha k 0 i)
    rw [h1HelmholtzForm_inner, h1BoundaryTrace_inner_smooth]
    simp only [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1,
      h1Value_herglotzWaveH1, h1Gradient_herglotzWaveH1, inner_toLp_pair]
    have hboundary : (∫ θ in Ioc 0 (2 * π),
        conj (f (γ θ)) * (herglotzConormalL2 hγ ha k) θ) =
        ∫ θ in 0..(2 * π), conj (f (γ θ)) * herglotzConormal k a γ θ := by
      rw [intervalIntegral.integral_of_le (by positivity)]
      apply integral_congr_ae
      filter_upwards [herglotzConormalL2_ae hγ ha k] with θ hθ
      rw [hθ]
    rw [hboundary, show ∫ θ in 0..(2 * π), conj (f (γ θ)) * herglotzConormal k a γ θ = ∫ z in Ω, ((∑ i : Fin 2, conj (fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) * fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) - (k ^ 2 : ℝ) * (conj (f z) * herglotzCoeff k a 0 z)) by
      obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
      obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
        f.property.2.1 f.property.1 (by simp)
      obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
      obtain ⟨K1, hK1⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k 1
      obtain ⟨Km, hKm⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k (-1)
      let A := (2 * π)⁻¹ * ∫ φ in 0..(2 * π), ‖a φ‖
      have hA : ∀ m z, ‖herglotzCoeff k a m z‖ ≤ A := fun m z => norm_herglotzCoeff_le k m z
      have hB0 := (norm_nonneg _).trans (hB 0)
      have hcfB : ∀ z, ‖conj (f z)‖ ≤ B := fun z => by rw [Complex.norm_conj]; exact hB z
      have hcmB : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤ A := fun z => by
        rw [Complex.norm_conj]
        exact hA (-1) z
      obtain ⟨KP, hKP⟩ := lipschitzWith_mul_of_bounded
        (Complex.isometry_conj.lipschitz.comp hKf) hK1 hcfB (hA 1)
      obtain ⟨KQ, hKQ⟩ := lipschitzWith_mul_of_bounded hKf
        (Complex.isometry_conj.lipschitz.comp hKm) hB hcmB
      let P : ℂ → ℂ := fun z => conj (f z) * herglotzCoeff k a 1 z
      let Q : ℂ → ℂ := fun z => f z * conj (herglotzCoeff k a (-1) z)
      have hPB : ∀ z, ‖P z‖ ≤ B * A := fun z => by
        rw [norm_mul]
        exact mul_le_mul (hcfB z) (hA 1 z) (norm_nonneg _) hB0
      have hQB : ∀ z, ‖Q z‖ ≤ B * A := fun z => by
        rw [norm_mul]
        exact mul_le_mul (hB z) (hcmB z) (norm_nonneg _) hB0
      have gP := integral_boundary_eq_dbar_of_bounded hb hL hγ hKP hPB
      have gQ := integral_boundary_eq_dbar_of_bounded hb hL hγ hKQ hQB
      have hiP := intervalIntegrable_comp_mul_deriv hKγ hKP.continuous
      have hiQ := intervalIntegrable_comp_mul_deriv hKγ hKQ.continuous
      change IntervalIntegrable (fun θ => P (γ θ) * deriv γ θ) volume 0 (2 * π) at hiP
      change IntervalIntegrable (fun θ => Q (γ θ) * deriv γ θ) volume 0 (2 * π) at hiQ
      change (∫ θ in 0..(2 * π), P (γ θ) * deriv γ θ) =
        2 * Complex.I * ∫ z in Ω, dbar P z at gP
      change (∫ θ in 0..(2 * π), Q (γ θ) * deriv γ θ) =
        2 * Complex.I * ∫ z in Ω, dbar Q z at gQ
      have hiQc : IntervalIntegrable (fun θ => conj (Q (γ θ) * deriv γ θ)) volume 0 (2 * π) := by
        rw [intervalIntegrable_iff] at hiQ ⊢
        exact hiQ.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
          hiQ.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp [Q])
      have hconj : ∫ θ in 0..(2 * π), conj (Q (γ θ) * deriv γ θ) =
          conj (∫ θ in 0..(2 * π), Q (γ θ) * deriv γ θ) := by
        rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le
          (by positivity), integral_conj]
      have hQd : IntegrableOn (dbar Q) Ω :=
        Measure.integrableOn_of_bounded (M := KQ) hb.measure_lt_top.ne
          (measurable_dbar Q).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKQ))
      have hQc :=
        hQd.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
          hQd.aestronglyMeasurable) (Eventually.of_forall fun z => by simp)
      calc
        _ = -(Complex.I * k) * ((∫ z in Ω, dbar P z) + ∫ z in Ω, conj (dbar Q z)) := by
          simp_rw [show ∀ θ, conj (f (γ θ)) * herglotzConormal k a γ θ = k / 2 * (conj (Q (γ θ) * deriv γ θ) - P (γ θ) * deriv γ θ) by
            intro θ
            rw [herglotzConormal_eq ha.intervalIntegrable]
            simp only [P, Q, map_mul, Complex.conj_conj]
            ring]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiQc hiP,
            hconj, gQ, gP]
          simp only [map_mul, map_ofNat, Complex.conj_I]
          rw [← integral_conj]
          ring
        _ = ∫ z in Ω, -(Complex.I * k) * (dbar P z + conj (dbar Q z)) := by
          rw [integral_const_mul, integral_add (Measure.integrableOn_of_bounded (M := KP) hb.measure_lt_top.ne (measurable_dbar P).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKP))) hQc]
        _ = _ := by
          refine setIntegral_congr_fun hL.1.1.measurableSet fun z _ => ?_
          exact (show -(Complex.I * k) * (dbar (fun x => conj (f x) * herglotzCoeff k a 1 x) z + conj (dbar (fun x => f x * conj (herglotzCoeff k a (-1) x)) z)) = (∑ i : Fin 2, conj (fderiv ℝ (f : ℂ → ℂ) z (coordDir i)) * fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) - (k ^ 2 : ℝ) * (conj (f z) * herglotzCoeff k a 0 z) by
            have hf : DifferentiableAt ℝ f z := f.property.1.differentiable (by simp) z
            have h1 := differentiable_herglotzCoeff ha.intervalIntegrable k 1 z
            have hm := differentiable_herglotzCoeff ha.intervalIntegrable k (-1) z
            have hcf : DifferentiableAt ℝ (fun x => conj (f x)) z :=
              Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hf
            have hcm : DifferentiableAt ℝ (fun x => conj (herglotzCoeff k a (-1) x)) z :=
              Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hm
            unfold dbar
            simp [fderiv_fun_mul hcf h1, fderiv_fun_mul hf hcm, fderiv_conj_apply hf, fderiv_conj_apply hm, fderiv_herglotzCoeff_apply ha.intervalIntegrable, coordDir]
            simp only [map_ofNat]
            ring_nf
            simp
            ring)]
    simp only [Fin.sum_univ_two] at hi ⊢
    symm
    refine (integral_sub ((hi 0).add (hi 1))
      ((integrable_conj_mul_of_memLp (f.property.memLp' 2) (herglotzCoeff_memLp_domain hb ha k 0)).const_mul (k ^ 2 : ℝ))).trans ?_
    exact congrArg₂ (fun x y => x - y)
      (integral_add (hi 0) (hi 1))
      (integral_const_mul ((k ^ 2 : ℝ) : ℂ) (fun z => conj (f z) * herglotzCoeff k a 0 z)))

theorem herglotzWaveH1_sqrt_isBoundaryNeumannSolution 
    (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω)
     (hγ : Φ0) 
    (ha : IsDirDensity a)  (hE : 0 ≤ E) :
    IsBoundaryNeumannSolution hb hL hγ E
      (herglotzConormalL2 hγ ha (Real.sqrt E))
      (herglotzWaveH1 hb ha (Real.sqrt E)) := by
  simpa [Real.sq_sqrt hE] using
    herglotzWaveH1_isBoundaryNeumannSolution hb hL hγ ha (Real.sqrt E)

end PolyaNeumann

end
