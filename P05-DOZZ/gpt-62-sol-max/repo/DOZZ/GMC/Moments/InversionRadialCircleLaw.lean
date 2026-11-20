/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.Field
public import DOZZ.GMC.Moments.InversionCircleJointLaw
public import DOZZ.GMC.Moments.InversionMixedCovariance
public import DOZZ.GFFStructure.CircleCovariance

/-! The coupled inversion law includes the concentric radial coordinates, with time reversed. -/
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal NNReal
namespace DOZZ.Proofs

section
variable (s : ℝ) (x : ℂ)

/-- Inversion reverses the radial covariance coordinate. -/
theorem originRadialCovariance_inversion :
    originRadialCovariance (-s) x⁻¹ = originRadialCovariance s x := by
  simp only [originRadialCovariance, norm_inv, Real.log_inv, neg_neg]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The concentric potential of the reversed circle, evaluated at the inverse point,
is the original circle potential away from zero. -/
theorem innerPot_origin_inversion (hx : x ≠ 0) :
    CirclePotential.innerPot 0 (-s) x⁻¹ = CirclePotential.innerPot 0 s x := by
  rw [← CirclePotential.integral_gffKernel_circleMeasure,
    ← CirclePotential.integral_gffKernel_circleMeasure,
    origin_circleKernelPotential_eq _ _ (inv_ne_zero hx),
    origin_circleKernelPotential_eq _ _ hx, originRadialCovariance_inversion]

end

/-- Inverted tests have exactly the reversed concentric source pairing. -/
theorem circleCross_origin_inversionTest (s : ℝ) (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    circleCross 0 (-s) (inversionTest f hf) = circleCross 0 s f := by
  rw [circleCross_inversionTest]
  change _ = ∫ x, f x * ∫ w, gffKernel x w ∂circleMeasure 0 s
  simp_rw [CirclePotential.integral_gffKernel_circleMeasure]
  apply integral_congr_ae
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with x hx
  rw [innerPot_origin_inversion s x hx]

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
  (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
include hX hc

/-- The actual coupled inverted concentric circle is the source circle with its
logarithmic radius reversed. This supplies the joint radial input, not just its marginal law. -/
theorem inversionCircle_origin_ae_eq
    (s : ℝ) (Z : Ω → ℝ) (hZ : MemLp Z 2 P)
    (f : ℕ → TestFn) (hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : Tendsto (fun n => circleEnergyGap 0 s (f n)) atTop (𝓝 0))
    (hlim : Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f n) (hf n)) - Z ω) 2 P) atTop (𝓝 0)) :
    Z =ᵐ[P] (fun ω => Xc ω 0 (-s)) := by
  let : IsProbabilityMeasure P := hX.1
  let U := fun ω => Xc ω 0 (-s)
  let V := fun ω => Xc ω 0 s
  have hU : MemLp U 2 P := hc.2.1 _ _
  have hV : MemLp V 2 P := hc.2.1 _ _
  have hzeroU : Tendsto (fun _ : ℕ => eLpNorm (fun ω => U ω - U ω) 2 P)
      atTop (𝓝 0) := by simp only [sub_self, ← Pi.zero_def, eLpNorm_zero]; exact tendsto_const_nhds
  have hzeroV : Tendsto (fun _ : ℕ => eLpNorm (fun ω => V ω - V ω) 2 P)
      atTop (𝓝 0) := by simp only [sub_self, ← Pi.zero_def, eLpNorm_zero]; exact tendsto_const_nhds
  have hinv := tendsto_covariance_of_eLpNorm_sub
    (fun _ => hU) (fun n => equatorGFF_test_memLp X hX (inversionTest (f n) (hf n)))
    hU hZ hzeroU hlim
  have hsrc := tendsto_covariance_of_eLpNorm_sub
    (fun _ => hV) (fun n => equatorGFF_test_memLp X hX (f n))
    hV hV hzeroV (hc.2.2 0 s f hgap)
  have he n : covariance U (fun ω => X ω (inversionTest (f n) (hf n))) P =
      covariance V (fun ω => X ω (f n)) P := by
    rw [circleAverage_test_covariance P X Xc hX hc,
      circleAverage_test_covariance P X Xc hX hc, circleCross_origin_inversionTest]
  have hmix : covariance U Z P = covariance V V P :=
    tendsto_nhds_unique (hinv.congr' (Eventually.of_forall he)) hsrc
  have hselfU : covariance U U P = |s| := by
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin, origin_circle_variance_algebra, abs_neg]
  have hselfV : covariance V V P = |s| := by
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin, origin_circle_variance_algebra]
  have hmeanZ : (∫ ω, Z ω ∂P) = 0 := integral_eq_zero_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX _) hZ
    (fun n => equatorGFF_test_integral X hX _) hlim
  obtain ⟨_, hmean⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hlaw := inversionCircle_fdd_law P X hX P X hX Xc hc
    (fun _ : Fin 1 => (0, s)) (fun _ => Z) (fun _ => hZ)
    (fun _ => f) (fun _ => hf) (fun _ => hgap) (fun _ => hlim)
  have hs := congrArg (fun μ : Measure (Fin 1 → ℝ) => ∫ v, (v 0) ^ 2 ∂μ) hlaw
  have hZm : AEMeasurable (fun ω (_ : Fin 1) => Z ω) P := AEMeasurable.of_eval fun _ => hZ.aemeasurable
  have hVm : AEMeasurable (fun ω (_ : Fin 1) => V ω) P := AEMeasurable.of_eval fun _ => hV.aemeasurable
  rw [integral_map hZm ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable,
    integral_map hVm ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable] at hs
  have hselfZ : covariance Z Z P = |s| := by
    simpa only [covariance, hmeanZ, hmean, sub_zero, ← pow_two, V] using hs.trans
      (by simpa only [covariance, hmean, sub_zero, ← pow_two, V] using hselfV)
  have hD : MemLp (fun ω => Z ω - U ω) 2 P := hZ.sub hU
  have hDmean : (∫ ω, Z ω - U ω ∂P) = 0 := by
    rw [integral_sub (hZ.integrable (by norm_num)) (hU.integrable (by norm_num)), hmeanZ]
    change 0 - (∫ ω, Xc ω 0 (-s) ∂P) = 0
    rw [hmean, sub_zero]
  have hDcov : covariance (fun ω => Z ω - U ω) (fun ω => Z ω - U ω) P = 0 := by
    rw [covariance_fun_sub_fun_sub hZ hU hZ hU, covariance_comm Z U,
      hmix, hselfZ, hselfU, hselfV]
    ring
  have hDsquare : (∫ ω, (Z ω - U ω) ^ 2 ∂P) = 0 := by
    simpa only [covariance, hDmean, sub_zero, ← pow_two] using hDcov
  have hi : Integrable (fun ω => (Z ω - U ω) ^ 2) P := by
    have ht : Integrable (fun ω => (Z ω - U ω) * (Z ω - U ω)) P := hD.integrable_mul hD
    simpa only [pow_two] using ht
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hi).mp hDsquare
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

/-- Inverted cutoffs retain the reversed source radial coordinates in their full joint
finite-dimensional law. All circles come from one coupled inverted-test construction. -/
theorem inversionCircle_radial_joint_fdd_law
    (Z : Ω → ℂ → ℝ → ℝ) (f : (ℂ × ℝ) → ℕ → TestFn)
    (hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : ∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0))
    (hmem : ∀ x r, MemLp (fun ω => Z ω x r) 2 P)
    (hlim : ∀ p, Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0))
    {k m : ℕ} (s : Fin k → ℝ) (q : Fin m → ℂ × ℝ) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => Z ω (q j).1 (q j).2)) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => Xc ω (q j).1 (q j).2)) := by
  let Q  := Fin.append (fun i => (0, s i)) q
  have hv := inversionCircle_fdd_law P X hX P X hX Xc hc Q
    (fun i ω => Z ω (Q i).1 (Q i).2) (fun i => hmem _ _)
    (fun i => f (Q i)) (fun i => hf (Q i)) (fun i => hgap (Q i)) (fun i => hlim (Q i))
  let L : (Fin (k + m) → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun v =>
    (fun i => v (Fin.castAdd m i), fun j => v (Fin.natAdd k j))
  have hL : Measurable L := by fun_prop
  have hZm : AEMeasurable (fun ω i => Z ω (Q i).1 (Q i).2) P :=
    AEMeasurable.of_eval fun i => (hmem _ _).aemeasurable
  have hXm : AEMeasurable (fun ω i => Xc ω (Q i).1 (Q i).2) P :=
    AEMeasurable.of_eval fun i => (hc.2.1 _ _).aemeasurable
  have hp := congrArg (fun μ => μ.map L) hv
  rw [AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hZm,
    AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hXm] at hp
  simp only [Function.comp_def, L, Q, Fin.append_left, Fin.append_right] at hp
  have he  :=
    ae_all_iff.mpr fun i => inversionCircle_origin_ae_eq P X Xc hX hc (s i)
      (fun ω => Z ω 0 (s i)) (hmem _ _) (f (0, s i)) (hf _) (hgap _) (hlim _)
  calc
    _ = P.map (fun ω => (fun i => Z ω 0 (s i), fun j => Z ω (q j).1 (q j).2)) := by
      apply Measure.map_congr
      filter_upwards [he] with ω hω
      exact Prod.ext (funext fun i => (hω i).symm) rfl
    _ = _ := hp

end


end DOZZ.Proofs
