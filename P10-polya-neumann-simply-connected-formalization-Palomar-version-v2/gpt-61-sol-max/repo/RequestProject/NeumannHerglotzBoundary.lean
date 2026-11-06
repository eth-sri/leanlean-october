module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

open scoped ContDiff

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Filter Topology Metric
open scoped InnerProductSpace ComplexConjugate

/-- Closing the derivative formula under differentiation proves genuine
smoothness of every Herglotz coefficient. -/
theorem contDiff_herglotzCoeff_infty 
    (ha : IntervalIntegrable a volume 0 circlePeriod) k m :
    RealSmooth (herglotzCoeff k a m) := by
  have hn : ∀ n : ℕ, ∀ m : ℤ, ContDiff ℝ n (herglotzCoeff k a m) := by
    intro n
    induction n with
    | zero =>
        fun_prop (disch := aesop)
    | succ n ih =>
        intro m
        rw [show ((n + 1 : ℕ)) = (n : WithTop ℕ∞) + 1 by simp,
          contDiff_succ_iff_fderiv]
        refine ⟨differentiable_herglotzCoeff ha k m, by simp, ?_⟩
        have hfd : fderiv ℝ (herglotzCoeff k a m) = fun z =>
            (-(Complex.I * k / 2) * herglotzCoeff k a (m + 1) z) • ContinuousLinearMap.id ℝ ℂ +
            (-(Complex.I * k / 2) * herglotzCoeff k a (m - 1) z) •
              Complex.conjCLE.toContinuousLinearMap := by
          funext z
          ext1 w
          rw [fderiv_herglotzCoeff_apply ha]
          simp  
          ring
        rw [hfd]
        fun_prop
  exact contDiff_infty.2 (fun n => hn n m)

section
variable {Ω : PlanarSet} (hb : Bornology.IsBounded Ω) {a } (ha : IsDirDensity a) (k : ℝ)

section
include Ω hb a ha k

lemma herglotzCoeff_memLp_domain m :
    MemLp (herglotzCoeff k a m) 2 (volume.restrict Ω) :=
  memLp_of_continuous_bounded hb (continuous_herglotzCoeff ha.intervalIntegrable k m)
    (fun z => norm_herglotzCoeff_le k m z)

lemma herglotzCoeff_memLp_deriv_domain m i :
    MemLp (fun z => fderiv ℝ (herglotzCoeff k a m) z (coordDir i)) 2 (volume.restrict Ω) := by
  have hc : Continuous (fun z => fderiv ℝ (herglotzCoeff k a m) z (coordDir i)) :=
    ((contDiff_herglotzCoeff ha.intervalIntegrable k m).continuous_fderiv (by simp)).clm_apply
      continuous_const
  apply memLp_of_continuous_bounded hb hc
  intro z
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_herglotzCoeff_le ha.intervalIntegrable k m z)
      (norm_nonneg _))

end


/-- The actual Herglotz wave in the weak-gradient H¹ space. Coefficient zero
is exactly `herglotzWave`, and its classical derivatives are retained. -/
def herglotzWaveH1 {Ω : PlanarSet} (hb : Bornology.IsBounded Ω)
    {a : ComplexCurve} (ha : IsDirDensity a) (k : ℝ) : NeumannH1 Ω :=
  h1Vector (isWeakGradient_of_contDiff_one (contDiff_herglotzCoeff ha.intervalIntegrable k 0)
    (herglotzCoeff_memLp_domain hb ha k 0)
    (herglotzCoeff_memLp_deriv_domain hb ha k 0))

section
include Ω hb a ha k

@[simp] theorem h1Value_herglotzWaveH1 :
    h1Value Ω (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_domain hb ha k 0).toLp (herglotzCoeff k a 0) := rfl

@[simp] theorem h1Gradient_herglotzWaveH1 i :
    h1Gradient Ω i (herglotzWaveH1 hb ha k) =
      (herglotzCoeff_memLp_deriv_domain hb ha k 0 i).toLp
        (fun z => fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) := rfl

end


end


section
variable {Ω } {γ } (hγ : IsBoundaryParam Ω γ) {a } (ha : IsDirDensity a) (k : ℝ)

include Ω γ hγ a ha k in
lemma herglotzConormal_memLp_boundary :
    MemLp (herglotzConormal k a γ) 2 (volume.restrict boundaryHalfOpenInterval) := by
  obtain ⟨K, hK⟩ := hγ.lipschitz
  obtain ⟨hgm, B, hgB⟩ := herglotzConormal_bounded ha.intervalIntegrable k hK
  exact MemLp.of_bound hgm.restrict B (Eventually.of_forall hgB)

/-- The actual density `D u(γ θ)(-i γ'(θ))`, not the unweighted unit-normal
derivative. Its boundary measure is ordinary `dθ`. -/
def herglotzConormalL2 {Ω } {γ } (hγ : IsBoundaryParam Ω γ)
    {a } ha k  :=
  (herglotzConormal_memLp_boundary hγ ha k).toLp (herglotzConormal k a γ)

include Ω γ hγ a ha k in
theorem herglotzConormalL2_ae :
    (herglotzConormalL2 hγ ha k : ComplexCurve)
      =ᵐ[volume.restrict boundaryHalfOpenInterval] herglotzConormal k a γ :=
  (herglotzConormal_memLp_boundary hγ ha k).coeFn_toLp

end


section
variable {Ω } (hb : Bornology.IsBounded Ω) (hL : IsLipschitzDomain Ω) {γ } (hγ : IsBoundaryParam Ω γ) {a } (ha : IsDirDensity a)

include Ω hb hL γ hγ a ha in
/-- A smooth compactly supported representative equal to the actual wave
near the closure of the domain identifies its genuine trace. -/
theorem exists_smoothTraceTest_herglotz k :
    ∃ f : smoothTraceTests, smoothTraceH1 Ω f = herglotzWaveH1 hb ha k ∧
      ∀ θ ∈ boundaryInterval, f (γ θ) = herglotzCoeff k a 0 (γ θ) := by
  obtain ⟨χ, U, hχs, hχc, -, hU, hχ1⟩ := exists_cutoff_one_near_closure hb
  let f : smoothTraceTests := ⟨fun z => (χ z) * herglotzCoeff k a 0 z,
    ⟨(Complex.ofRealCLM.contDiff.comp hχs).mul
      (contDiff_herglotzCoeff_infty ha.intervalIntegrable k 0),
      (hχc.comp_left (g := fun x : ℝ => (x : ℂ)) Complex.ofReal_zero).mul_right,
      subset_univ _⟩⟩
  have hf : ∀ z ∈ closure Ω, f z = herglotzCoeff k a 0 z := by
    intro z hz
    simp [f, hχ1 z (hU hz)]
  refine ⟨f, ?_, ?_⟩
  · apply h1Value_injective hL.1.1
    rw [h1Value_smoothTraceH1, h1Value_herglotzWaveH1]
    apply MemLp.toLp_congr
    filter_upwards [ae_restrict_mem hL.1.1.measurableSet] with z hz
    exact hf z (subset_closure hz)
  · intro θ hθ
    exact hf _ (frontier_subset_closure (hγ.image ▸ mem_image_of_mem γ hθ))

private lemma mixedHerglotzGreen_pointwise 
    (ha : IntervalIntegrable a volume 0 circlePeriod) k (f : smoothTraceTests) z :
    -(Complex.I * k) *
      (dbar (fun x => conj (f x) * herglotzCoeff k a 1 x) z +
        conj (dbar (fun x => f x * conj (herglotzCoeff k a (-1) x)) z)) =
      (∑ i : Coord, conj (fderiv ℝ (f : PlaneMap) z (coordDir i)) *
        fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) -
          ((k ^ 2 : ℝ) : ℂ) * (conj (f z) * herglotzCoeff k a 0 z) := by
  have hf  := f.property.1.differentiable (by simp) z
  have h1 := differentiable_herglotzCoeff ha k 1 z
  have hm := differentiable_herglotzCoeff ha k (-1) z
  have hcf : DifferentiableAt ℝ (fun x => conj (f x)) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hf
  have hcm : DifferentiableAt ℝ (fun x => conj (herglotzCoeff k a (-1) x)) z :=
    Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hm
  unfold dbar
  simp  [fderiv_fun_mul hcf h1, fderiv_fun_mul hf hcm, fderiv_conj_apply hf, fderiv_conj_apply hm, fderiv_herglotzCoeff_apply ha, coordDir]
  simp  [     map_ofNat,
     ]
  push_cast
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four]
  ring

include Ω hb hL γ hγ a ha in
/-- Mixed Green identity between a genuine Herglotz wave and a smooth test
function. This is derived from the actual complex boundary Green formula. -/
theorem integral_test_mul_herglotzConormal k (f : smoothTraceTests) :
    ∫ θ in (0 : ℝ)..circlePeriod, conj (f (γ θ)) * herglotzConormal k a γ θ =
      ∫ z in Ω, ((∑ i : Coord, conj (fderiv ℝ (f : PlaneMap) z (coordDir i)) *
        fderiv ℝ (herglotzCoeff k a 0) z (coordDir i)) -
          ((k ^ 2 : ℝ) : ℂ) * (conj (f z) * herglotzCoeff k a 0 z)) := by
  obtain ⟨Kγ, hKγ⟩ := hγ.lipschitz
  obtain ⟨Kf, hKf⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    f.property.2.1 f.property.1 (by simp)
  obtain ⟨B, hB⟩ := f.property.2.1.exists_bound_of_continuous f.property.1.continuous
  obtain ⟨K1, hK1⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k 1
  obtain ⟨Km, hKm⟩ := lipschitzWith_herglotzCoeff ha.intervalIntegrable k (-1)
  let A := circlePeriod⁻¹ * ∫ φ in (0)..circlePeriod, ‖a φ‖
  have hA : ∀ m z, ‖herglotzCoeff k a m z‖ ≤ A := (norm_herglotzCoeff_le k)
  have hB0  := (norm_nonneg _).trans (hB 0)
  have hcfB : ∀ z, ‖conj (f z)‖ ≤ B := fun z => by rw [Complex.norm_conj]; exact hB z
  have hcmB : ∀ z, ‖conj (herglotzCoeff k a (-1) z)‖ ≤ A := fun z => by
    simp_all
  obtain ⟨KP, hKP⟩ := lipschitzWith_mul_of_bounded
    (Complex.isometry_conj.lipschitz.comp hKf) hK1 hcfB (hA 1)
  obtain ⟨KQ, hKQ⟩ := lipschitzWith_mul_of_bounded hKf
    (Complex.isometry_conj.lipschitz.comp hKm) hB hcmB
  let P  := fun z => conj (f z) * herglotzCoeff k a 1 z
  let Q  := fun z => f z * conj (herglotzCoeff k a (-1) z)
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
  change IntervalIntegrable (fun θ => P (γ θ) * deriv γ θ) volume 0 circlePeriod at hiP
  change (∫ θ in (0)..circlePeriod, P (γ θ) * deriv γ θ) =
    2 * Complex.I * ∫ z in Ω, dbar P z at gP
  change (∫ θ in (0)..circlePeriod, Q (γ θ) * deriv γ θ) =
    2 * Complex.I * ∫ z in Ω, dbar Q z at gQ
  have hiQc : IntervalIntegrable (fun θ => conj (Q (γ θ) * deriv γ θ)) volume 0 circlePeriod := by
    rw [intervalIntegrable_iff] at hiQ ⊢
    exact hiQ.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hiQ.aestronglyMeasurable) (Eventually.of_forall fun θ => by simp [Q])
  have hpt : ∀ θ, conj (f (γ θ)) * herglotzConormal k a γ θ =
      (k / 2 : ℂ) * (conj (Q (γ θ) * deriv γ θ) - P (γ θ) * deriv γ θ) := by
    intro θ
    rw [herglotzConormal_eq ha.intervalIntegrable]
    simp only [P, Q, map_mul, Complex.conj_conj]
    ring
  have hconj : ∫ θ in (0 : ℝ)..circlePeriod, conj (Q (γ θ) * deriv γ θ) =
      conj (∫ θ in (0 : ℝ)..circlePeriod, Q (γ θ) * deriv γ θ) := by
    rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le
      (by positivity), integral_conj]
  have hPd : IntegrableOn (dbar P) Ω :=
    Measure.integrableOn_of_bounded (M := KP) hb.measure_lt_top.ne
      (measurable_dbar P).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKP))
  have hQd : IntegrableOn (dbar Q) Ω :=
    Measure.integrableOn_of_bounded (M := KQ) hb.measure_lt_top.ne
      (measurable_dbar Q).aestronglyMeasurable (Eventually.of_forall (norm_dbar_le hKQ))
  have hQc  :=
    hQd.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable
      hQd.aestronglyMeasurable) (Eventually.of_forall fun z => by simp)
  calc
    _ = -(Complex.I * k) * ((∫ z in Ω, dbar P z) + ∫ z in Ω, conj (dbar Q z)) := by
      simp_rw [hpt]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiQc hiP,
        hconj, gQ, gP]
      simp only [map_mul, map_ofNat, Complex.conj_I]
      rw [← integral_conj]
      ring
    _ = ∫ z in Ω, -(Complex.I * k) * (dbar P z + conj (dbar Q z)) := by
      rw [integral_const_mul, integral_add hPd hQc]
    _ = _ := by
      refine setIntegral_congr_fun hL.1.1.measurableSet fun z _ => ?_
      exact mixedHerglotzGreen_pointwise ha.intervalIntegrable k f z

private lemma inner_toLp_pair {α : Type*} [MeasurableSpace α] {μ }
    {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, conj (f x) * g x ∂μ := by
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

private lemma integrable_conj_mul_of_memLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => conj (f x) * g x) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply', hfx, hgx]

section
include Ω hb hL γ hγ a ha

/-- The mixed Green identity in the actual H¹ form, with the constructed
continuous trace and the actual conormal L² class. -/
theorem herglotzWaveH1_green_smooth k f :
    ⟪smoothTraceH1 Ω f, h1HelmholtzForm Ω (k ^ 2) (herglotzWaveH1 hb ha k)⟫_ℂ =
      ⟪h1BoundaryTrace hL hγ (smoothTraceH1 Ω f), herglotzConormalL2 hγ ha k⟫_ℂ := by
  have hi  := fun i =>
    integrable_conj_mul_of_memLp ((f.property.dirD (coordDir i)).memLp' 2)
      (herglotzCoeff_memLp_deriv_domain hb ha k 0 i)
  have hm  :=
    integrable_conj_mul_of_memLp (f.property.memLp' 2)
      (herglotzCoeff_memLp_domain hb ha k 0)
  rw [h1HelmholtzForm_inner, h1BoundaryTrace_inner_smooth hb]
  simp only [h1Value_smoothTraceH1, h1Gradient_smoothTraceH1,
    h1Value_herglotzWaveH1, h1Gradient_herglotzWaveH1, inner_toLp_pair]
  have hboundary : (∫ θ in boundaryHalfOpenInterval,
      conj (f (γ θ)) * (herglotzConormalL2 hγ ha k : ComplexCurve) θ) =
      ∫ θ in (0 : ℝ)..circlePeriod, conj (f (γ θ)) * herglotzConormal k a γ θ := by
    rw [intervalIntegral.integral_of_le (by positivity)]
    apply integral_congr_ae
    filter_upwards [herglotzConormalL2_ae hγ ha k] with θ hθ
    rw [hθ]
  rw [hboundary, integral_test_mul_herglotzConormal hb hL hγ ha k f]
  simp only [Fin.sum_univ_two] at hi ⊢
  symm
  refine (integral_sub ((hi 0).add (hi 1))
    (hm.const_mul ((k ^ 2 : ℝ)))).trans ?_
  exact congrArg₂ (fun x y : ℂ => x - y)
    (integral_add (hi 0) (hi 1))
    (integral_const_mul ((k ^ 2 : ℝ) : ℂ) (fun z => conj (f z) * herglotzCoeff k a 0 z))

/-- Every genuine Herglotz wave solves the weak Helmholtz equation with its
own actual conormal data. Smooth Green's formula extends to all H¹ tests
through the already established density theorem. -/
theorem herglotzWaveH1_isBoundaryNeumannSolution k :
    IsBoundaryNeumannSolution hL hγ (k ^ 2)
      (herglotzConormalL2 hγ ha k) (herglotzWaveH1 hb ha k) := by
  apply (isBoundaryNeumannSolution_iff_form_eq hL hγ (k ^ 2) _ _).2
  apply ext_inner_left ℂ
  intro v
  refine (denseRange_smoothTraceH1Lin hb hL).induction_on v
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro f
  rw [smoothTraceH1Lin_apply, h1BoundaryLoad_inner]
  exact herglotzWaveH1_green_smooth hb hL hγ ha k f

theorem herglotzWaveH1_sqrt_isBoundaryNeumannSolution  (hE : 0 ≤ E) :
    IsBoundaryNeumannSolution hL hγ E
      (herglotzConormalL2 hγ ha (Real.sqrt E))
      (herglotzWaveH1 hb ha (Real.sqrt E)) := by
  grind [herglotzWaveH1_isBoundaryNeumannSolution]

end


end


end PolyaNeumann

end
