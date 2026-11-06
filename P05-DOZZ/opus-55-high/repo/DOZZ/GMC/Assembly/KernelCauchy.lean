/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.KernelLimit
public import DOZZ.GMC.AdmissibleGMCBarrierParameters
public import DOZZ.GMC.AdmissibleGMCReferenceKernel
public import DOZZ.GMC.AdmissibleGMCReferenceFinite

/-! A uniform integrable majorant of the growing-barrier two-root kernels and their uniform `L¹` Cauchy property on compact charts. -/

@[expose] public section

/-! ### Integrable majorant

One integrable majorant `B₁ ‖x - y‖ ^ (-κ) + B₂` for every growing-barrier two-root kernel at
sufficiently fine cutoffs, uniformly for charges in a compact interval.

Near the diagonal the coarse barrier at the floor-log scale of `max ‖x - y‖ ε δ` gives the
power bound; away from it the Wick pair expectation is bounded by the covariance bound. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
include hY

/-- The Wick pair expectation of one admissible regularization is the exponential of the
covariance of its two roots. -/
theorem admissible_wick_pair_lintegral
    (g ε δ : ℝ)
    (hε : 0 < ε) (hεcut : ε ≤ ε₀) (hδ : 0 < δ) (hδcut : δ ≤ ε₀) (x y : ℂ) :
    ∫⁻ ω, admissibleLogWickWeight P Y g ε x ω * admissibleLogWickWeight P Y g δ y ω ∂P =
      ENNReal.ofReal (Real.exp (g ^ 2 *
        gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y))) := by
  let q : Fin 2 → ℝ × ℂ := fun i => if i = 0 then (ε, x) else (δ, y)
  let V : Ω → Fin 2 → ℝ := fun ω i => Y ω (q i).1 (q i).2
  have hV : IsCenteredJointlyGaussian P V := by
    apply hY.gaussian 2 q
    aesop
  have h := finite_gaussian_wick_pair_tilt P V hV 0 1 g (fun _ => 1) measurable_const
  have hP := hV.1
  have hV0 : (fun ω => V ω 0) = fun ω => Y ω ε x := by rfl
  have hV1 : (fun ω => V ω 1) = fun ω => Y ω δ y := by rfl
  have hsymm : gaussianCovariance P (fun ω => Y ω δ y) (fun ω => Y ω ε x) =
      gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y) := by
    unfold gaussianCovariance
    grind
  rw [hV0, hV1, hsymm] at h
  have hexp : g ^ 2 / 2 * (gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y) +
      gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y)) =
      g ^ 2 * gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y) := by ring
  aesop

/-- The growing-barrier kernel is at most the barrier-free Wick pair expectation. -/
theorem growingPairKernel_le_wick_pair
    (g a : ℝ) (k₀ : ℕ) (r s : ℝ)
    (hr : Real.exp (-r) ≤ ε₀) (hs : Real.exp (-s) ≤ ε₀) (p : ℂ × ℂ) :
    growingPairKernel P Y g a k₀ r s p ≤
      ENNReal.ofReal (Real.exp (g ^ 2 * gaussianCovariance P
        (fun ω => Y ω (Real.exp (-r)) p.1) (fun ω => Y ω (Real.exp (-s)) p.2))) := by
  rw [← admissible_wick_pair_lintegral P U dens ε₀ Y hY g _ _ (Real.exp_pos _) hr
    (Real.exp_pos _) hs p.1 p.2]
  apply lintegral_mono
  intro ω
  simp
  calc _ ≤ admissibleLogWickWeight P Y g _ p.1 ω *
        admissibleLogWickWeight P Y g _ p.2 ω * 1 * 1 := by
        gcongr <;> exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
    _ = _ := by ring

end

/-- A coarse scale present in both growing barriers dominates the kernel by the one-scale
barrier expectation at the first root. -/
theorem growingPairKernel_le_one_scale
    (Y : Ω → ℝ → ℂ → ℝ) (g a : ℝ) (k₀ k : ℕ) (r s : ℝ)
    (hk₀ : k₀ ≤ k) (hkr : (k : ℝ) ≤ r) (p : ℂ × ℂ) :
    growingPairKernel P Y g a k₀ r s p ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp
          (g * Y ω (Real.exp (-r)) p.1 - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Y ω (Real.exp (-r)) p.1))) *
        ENNReal.ofReal (Real.exp
          (g * Y ω (Real.exp (-s)) p.2 - g ^ 2 / 2 * gaussianVariance P
            (fun ω => Y ω (Real.exp (-s)) p.2))) *
        Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) p.1 ≤ a * (k : ℝ)}
          (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
  apply lintegral_mono
  intro ω
  simp
  have hbar : Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
      (fun _ => (1 : ℝ≥0∞)) (ω, p.1) ≤
      Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) p.1 ≤ a * (k : ℝ)}
        (fun _ => (1 : ℝ≥0∞)) ω := by
    by_cases hmem : (ω, p.1) ∈ admissibleGrowingBarrierSet Y a k₀ r
    · have hk := hmem k hk₀ hkr
      simp_all
    simp_all
  have hone : Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
      (fun _ => (1 : ℝ≥0∞)) (ω, p.2) ≤ 1 :=
    Set.indicator_le_self' (fun _ _ => zero_le_one) _
  calc _ ≤ admissibleLogWickWeight P Y g _ p.1 ω *
        admissibleLogWickWeight P Y g _ p.2 ω *
        Set.indicator {ω | Y ω (Real.exp (-(k : ℝ))) p.1 ≤ a * (k : ℝ)}
          (fun _ => (1 : ℝ≥0∞)) ω * 1 := by gcongr
    _ = _ := by rw [mul_one]; rfl

end

/-- The exponential prefactor of the near-diagonal power bound is uniform on a charge interval. -/
theorem near_power_prefactor_le (g gHi a η C : ℝ) (hg : 0 < g) (hgHi : g ≤ gHi)
    (ha : 0 ≤ a) (hag : 0 < 2 * g - a) (hη : 0 < η) (hη1 : η < 1) (hC : 0 ≤ C) :
    g ^ 2 * C + ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤
      gHi ^ 2 * C + 2 * gHi ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg.le hgHi 2) hC
  have hsq : (2 * g - a) ^ 2 ≤ (2 * gHi) ^ 2 := by
    nlinarith
  have hη' : (1 - η) ^ 2 ≤ 1 := by nlinarith
  have hnum : (1 - η) ^ 2 * (2 * g - a) ^ 2 ≤ (2 * gHi) ^ 2 := by
    nlinarith
  have hden : 2 ≤ 2 * (1 + η) := by linarith
  have h2 : (1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)) ≤ (2 * gHi) ^ 2 / 2 := by
    bound
  linarith

/-- Uniform integrable majorant of the growing-barrier two-root kernels. -/
theorem growingPairKernel_majorant
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (gLo gHi a η κ : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (ha : 0 ≤ a)
    (ha2 : a < 2 * gLo) (hη : 0 < η) (hη1 : η < 1) (hκ : 0 ≤ κ)
    (hκexp : ∀ g ∈ Icc gLo gHi, g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ)
    (k₀ : ℕ) :
    ∃ R₀ B₁ B₂ : ℝ, 0 ≤ B₁ ∧ 0 ≤ B₂ ∧ ∀ r s : ℝ, R₀ ≤ r → R₀ ≤ s →
      ∀ g ∈ Icc gLo gHi, ∀ p ∈ K ×ˢ K, 0 < ‖p.1 - p.2‖ →
        growingPairKernel P Y g a k₀ r s p ≤
          ENNReal.ofReal (B₁ * ‖p.1 - p.2‖ ^ (-κ) + B₂) := by
  obtain ⟨C, hC, hnear⟩ := compatible_two_root_wick_pair_good_barrier_power_bound_BarrierCauchyLocalEstimates
    P U dens ε₀ ε₀ Y Y hY hY (isCompatibleAdmissibleRegularizations_self P U dens ε₀ Y hY) true true K hK hKU
  obtain ⟨Cc, hCc, hcov⟩ := hY.covarianceBound K hK hKU
  obtain ⟨K₁', hK₁cut, hK₁C, hK₁η, hK₁off⟩ := exists_natural_scale_after_covariance_errors
    C gHi η (2 * gLo - a) ε₀ hC (lt_of_lt_of_le hgLo hgLoHi) hη (by linarith)
    hY.cutoffPositive
  let K₁ := max K₁' k₀
  have hK₁ge' : (K₁' : ℝ) ≤ K₁ := by exact_mod_cast le_max_left K₁' k₀
  -- every scale `k ≥ K₁` satisfies all threshold conditions
  have hthr (k : ℕ) (hk : K₁ ≤ k) :
      Real.exp (-(k : ℝ)) ≤ ε₀ ∧ k₀ ≤ k ∧ C < (k : ℝ) ∧ C ≤ η * (k : ℝ) ∧
        ∀ g ∈ Icc gLo gHi, 2 * g * C + 1 ≤ η * (2 * g - a) * (k : ℝ) := by
    have hkK : (K₁' : ℝ) ≤ k := hK₁ge'.trans (by exact_mod_cast hk)
    refine ⟨le_trans (Real.exp_le_exp.mpr (by linarith)) hK₁cut,
      le_trans (le_max_right ..) hk, lt_of_lt_of_le hK₁C hkK, ?_, ?_⟩
    · exact hK₁η.trans (mul_le_mul_of_nonneg_left hkK hη.le)
    · intro g hg
      have hb : 0 < 2 * gLo - a := by linarith
      calc 2 * g * C + 1 ≤ 2 * gHi * C + 1 := by linarith only [mul_le_mul_of_nonneg_right hg.2 hC]
        _ ≤ η * (2 * gLo - a) * (K₁' : ℝ) := hK₁off
        _ ≤ η * (2 * gLo - a) * (k : ℝ) :=
            by bound
        _ ≤ η * (2 * g - a) * (k : ℝ) := by
            have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
            have : η * (2 * gLo - a) ≤ η * (2 * g - a) :=
              mul_le_mul_of_nonneg_left (by linarith [hg.1]) hη.le
            exact mul_le_mul_of_nonneg_right this hk0
  let ρ₀ := Real.exp (-((K₁ : ℝ) + 1))
  have hρ₀ : 0 < ρ₀ := Real.exp_pos _
  have hρ₀1 : ρ₀ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : (0 : ℝ) ≤ K₁ := Nat.cast_nonneg _
    linarith)
  let B₁ := Real.exp (gHi ^ 2 * C + 2 * gHi ^ 2)
  let B₂ := Real.exp (gHi ^ 2 * max (Real.log (1 / ρ₀) + Cc) 0)
  refine ⟨(K₁ : ℝ) + 1, B₁, B₂, (Real.exp_pos _).le, (Real.exp_pos _).le, ?_⟩
  intro r s hr hs g hg p hp hpos
  have hgpos : 0 < g := lt_of_lt_of_le hgLo hg.1
  have hr₀ : Real.exp (-r) ≤ ρ₀ := by bound
  have hs₀ : Real.exp (-s) ≤ ρ₀ := by bound
  have hrcut : Real.exp (-r) ≤ ε₀ := by
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) ((hthr K₁ le_rfl).1)
  have hscut : Real.exp (-s) ≤ ε₀ := by
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) ((hthr K₁ le_rfl).1)
  have hpow_nonneg : 0 ≤ B₁ * ‖p.1 - p.2‖ ^ (-κ) :=
    by positivity
  set ρ := max ‖p.1 - p.2‖ (max ..) with hρdef
  have hρpos : 0 < ρ := by positivity
  by_cases hnearρ : ρ ≤ ρ₀
  · -- near the diagonal: barrier at the floor-log scale
    have hρ1 : ρ ≤ 1 := hnearρ.trans hρ₀1
    have hlog0 : 0 ≤ Real.log (1 / ρ) := by bound
    set k := ⌊Real.log _⌋₊ with hkdef
    have hkle : (k : ℝ) ≤ Real.log (1 / ρ) := Nat.floor_le hlog0
    have hklt : Real.log (1 / ρ) < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hexpk : ρ ≤ Real.exp (-(k : ℝ)) := by
      have h1 : Real.exp (-Real.log (1 / ρ)) = ρ := by
        rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hρpos)]; field_simp
      calc ρ = Real.exp _ := h1.symm
        _ ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    have hlogρ₀ : (K₁ : ℝ) + 1 ≤ Real.log (1 / ρ) := by
      have h1 : Real.log (1 / ρ₀) = (K₁ : ℝ) + 1 := by
        simp [ρ₀, Real.log_exp]
      have h2 : Real.log (1 / ρ₀) ≤ Real.log (1 / ρ) :=
        Real.log_le_log (one_div_pos.mpr hρ₀) (one_div_le_one_div_of_le hρpos hnearρ)
      linarith
    have hkK₁ : K₁ ≤ k := by
      have : (K₁ : ℝ) < (k : ℝ) + 1 := by linarith
      have : K₁ < k + 1 := by exact_mod_cast this
      omega
    obtain ⟨hkcut, hk₀k, hkC, hkη, hkoff⟩ := hthr k hkK₁
    have hxy : ‖p.1 - p.2‖ ≤ Real.exp (-(k : ℝ)) := (le_max_left ..).trans hexpk
    have hεk : Real.exp (-r) ≤ Real.exp (-(k : ℝ)) :=
      ((le_max_left ..).trans (le_max_right ..)).trans hexpk
    have hδk : Real.exp (-s) ≤ Real.exp (-(k : ℝ)) :=
      ((le_max_right ..).trans (le_max_right ..)).trans hexpk
    have hkr : (k : ℝ) ≤ r := by
      have := Real.exp_le_exp.mp hεk
      linarith
    have hfloor : Real.log (1 / ρ) - 1 < (k : ℝ) := by linarith
    have hag : 0 < 2 * g - a := by linarith [hg.1]
    have hbound := hnear k (by bound) _ _
      (Real.exp_pos _) (by bound) hεk (Real.exp_pos _)
      (by bound) hδk κ p.1 p.2 hp.1 hp.2 hxy hpos ρ hρdef hfloor
      η g a hη hη1 hgpos (by linarith) hkC hkη (hkoff g hg) hκ (hκexp g hg)
    refine (growingPairKernel_le_one_scale P Y g a k₀ k r s hk₀k hkr p).trans
      (hbound.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    have hexp_le : Real.exp (g ^ 2 * C +
        ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η)))) ≤ B₁ :=
      Real.exp_le_exp.mpr (near_power_prefactor_le g gHi a η C hgpos hg.2 ha hag hη hη1 hC)
    have hpw : 0 ≤ ‖p.1 - p.2‖ ^ (-κ) := Real.rpow_nonneg (norm_nonneg _) _
    have := mul_le_mul_of_nonneg_right hexp_le hpw
    linarith [(Real.exp_pos _).le.trans (le_refl B₂), show (0 : ℝ) ≤ B₂ from
      (Real.exp_pos _).le]
  · -- away from the diagonal: the barrier-free Wick pair bound
    have hρgt : ρ₀ < ρ := lt_of_not_ge hnearρ
    refine (growingPairKernel_le_wick_pair P U dens ε₀ Y hY g a k₀ r s hrcut hscut p).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hc := (abs_le.mp (hcov _ _ (Real.exp_pos _) hrcut
      (Real.exp_pos _) hscut p.1 hp.1 p.2 hp.2)).2
    have hlogle : Real.log (1 / ρ) ≤ Real.log (1 / ρ₀) :=
      Real.log_le_log (one_div_pos.mpr hρpos) (one_div_le_one_div_of_le hρ₀ hρgt.le)
    have hcovle : gaussianCovariance P (fun ω => Y ω (Real.exp (-r)) p.1)
        (fun ω => Y ω (Real.exp (-s)) p.2) ≤ max (Real.log (1 / ρ₀) + Cc) 0 := by
      have : gaussianCovariance P (fun ω => Y ω (Real.exp (-r)) p.1)
          (fun ω => Y ω (Real.exp (-s)) p.2) ≤ Real.log (1 / ρ₀) + Cc := by
        linarith
      exact this.trans (le_max_left ..)
    have hg2 : g ^ 2 ≤ gHi ^ 2 := pow_le_pow_left₀ hgpos.le hg.2 2
    have hexp_le : Real.exp (g ^ 2 * gaussianCovariance P (fun ω => Y ω (Real.exp (-r)) p.1)
        (fun ω => Y ω (Real.exp (-s)) p.2)) ≤ B₂ := by
      apply Real.exp_le_exp.mpr
      calc g ^ 2 * gaussianCovariance P (fun ω => Y ω _ p.1)
            (fun ω => Y ω _ p.2) ≤ g ^ 2 * max _ 0 :=
            mul_le_mul_of_nonneg_left hcovle (sq_nonneg g)
        _ ≤ gHi ^ 2 * max _ 0 :=
            mul_le_mul_of_nonneg_right hg2 (le_max_right ..)
    linarith

end DOZZ.Assembly

/-! ### Kernel `L¹` Cauchy property

The growing-barrier two-root kernels are Cauchy in `L¹` of the product reference measure on a
compact chart, uniformly for charges in a compact interval.

The integrable majorant controls a thin neighbourhood of the diagonal, and the off-diagonal
uniform Cauchy property controls the rest. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The product of the reference measure restricted to a compact chart with itself. -/
noncomputable abbrev chartPairMeasure (U : Set ℂ) (dens : ℂ → ℝ) (K : Set ℂ) :
    Measure (ℂ × ℂ) :=
  ((logRegularizationReference U dens).restrict K).prod
    ((logRegularizationReference U dens).restrict K)

/-- Symmetric truncated difference of two extended reals. -/
noncomputable abbrev ennDist (x y : ℝ≥0∞) : ℝ≥0∞ := (x - y) + (y - x)

theorem ennDist_le_add (x y : ℝ≥0∞) : ennDist x y ≤ x + y := by
  bound

theorem ennDist_eq_ofReal_abs {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    ennDist x y = ENNReal.ofReal |x.toReal - y.toReal| := by
  unfold ennDist
  rcases le_total x y with h | h
  · have hle := ENNReal.toReal_mono hy h
    rw [tsub_eq_zero_of_le h, zero_add, abs_of_nonpos (by linarith), neg_sub,
      ← ENNReal.toReal_sub_of_le h hy, ENNReal.ofReal_toReal (ne_top_of_le_ne_top hy tsub_le_self)]
  · have hle := ENNReal.toReal_mono hx h
    rw [tsub_eq_zero_of_le h, add_zero, abs_of_nonneg (by linarith),
      ← ENNReal.toReal_sub_of_le h hx, ENNReal.ofReal_toReal (ne_top_of_le_ne_top hx tsub_le_self)]

/-- The reference measure is s-finite. -/
instance instSFiniteLogRegularizationReference (U : Set ℂ) (dens : ℂ → ℝ) :
    SFinite (logRegularizationReference U dens) := by
  unfold logRegularizationReference
  infer_instance
section
variable (U : Set ℂ) (dens : ℂ → ℝ)

/-- The reference measure has no atoms. -/
theorem logRegularizationReference_singleton (x : ℂ) :
    logRegularizationReference U dens {x} = 0 := by
  unfold logRegularizationReference
  simp

/-- The chart pair measure is carried by `K × K` off the diagonal. -/
theorem chartPairMeasure_ae_offDiagonal (K : Set ℂ)
    (hK : MeasurableSet K) :
    ∀ᵐ p ∂chartPairMeasure U dens K, p ∈ K ×ˢ K ∧ p.1 ≠ p.2 := by
  have hcarry : ∀ᵐ p ∂chartPairMeasure U dens K, p ∈ K ×ˢ K := by
    rw [chartPairMeasure, Measure.prod_restrict]
    exact ae_restrict_mem (hK.prod hK)
  have hdiag0 : chartPairMeasure U dens K (Set.diagonal ℂ) = 0 := by
    rw [chartPairMeasure, Measure.prod_apply measurableSet_diagonal]
    have hzero (x : ℂ) : ((logRegularizationReference U dens).restrict K)
        (Prod.mk x ⁻¹' Set.diagonal ℂ) = 0 := by
      have hset : Prod.mk x ⁻¹' Set.diagonal ℂ = {x} := by
        aesop
      rw [hset]
      exact le_antisymm ((Measure.restrict_le_self _).trans
        (logRegularizationReference_singleton U dens x).le) zero_le
    simp_all
  have hdiag : ∀ᵐ p ∂chartPairMeasure U dens K, p.1 ≠ p.2 := by
    rw [ae_iff]
    aesop
  simp_all

end
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The chart pair measure is finite. -/
theorem chartPairMeasure_univ_ne_top
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    chartPairMeasure U dens K univ ≠ ⊤ := by
  have hσK := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  rw [chartPairMeasure, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ]
  exact ENNReal.mul_ne_top hσK hσK
section
variable [IsProbabilityMeasure P]

/-- The growing-barrier kernels are measurable in the two roots. -/
theorem growingPairKernel_measurable
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (g a : ℝ) (k₀ : ℕ) (r s : ℝ) :
    Measurable (growingPairKernel P Y g a k₀ r s) :=
  compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_measurable P U dens ε₀ ε₀ Y Y hY hY
    g a k₀ r s true true
section
variable (U : Set ℂ) (dens : ℂ → ℝ)
section
variable (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (gLo gHi a η κ : ℝ) (hgLo : 0 < gLo) (hgLoHi : gLo ≤ gHi) (hga : gHi < a) (ha2 : a < 2 * gLo) (hη : 0 < η) (hη1 : η < 1) (hκ : 0 < κ) (hκ2 : κ < 2) (hκexp : ∀ g ∈ Icc gLo gHi, g ^ 2 - ((1 - η) ^ 2 * (2 * g - a) ^ 2 / (2 * (1 + η))) ≤ κ) (k₀ : ℕ)
include hY hK hKU hgLo hgLoHi hga ha2 hη hη1 hκ hκ2 hκexp

/-- The growing-barrier kernels at sufficiently fine cutoffs share one majorant integrable for
the chart pair measure. -/
theorem growingPairKernel_ae_le_integrable_majorant
    :
    ∃ R₀ : ℝ, ∃ Maj : ℂ × ℂ → ℝ≥0∞, Measurable Maj ∧
      ∫⁻ p, Maj p ∂chartPairMeasure U dens K ≠ ⊤ ∧
      ∀ r s : ℝ, R₀ ≤ r → R₀ ≤ s → ∀ g ∈ Icc gLo gHi,
        ∀ᵐ p ∂chartPairMeasure U dens K, growingPairKernel P Y g a k₀ r s p ≤ Maj p := by
  have hμfin :=
    chartPairMeasure_univ_ne_top P U dens ε₀ Y hY K hK hKU
  obtain ⟨R₀, B₁, B₂, hB₁, hB₂, hmaj⟩ := growingPairKernel_majorant P U dens ε₀ Y hY K hK hKU
    gLo gHi a η κ hgLo hgLoHi (le_trans hgLo.le (hgLoHi.trans hga.le)) ha2 hη hη1 hκ.le hκexp k₀
  let Maj : ℂ × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (B₁ * ‖p.1 - p.2‖ ^ (-κ) + B₂)
  have hMajMeas : Measurable Maj := by
    have h : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
    exact ENNReal.measurable_ofReal.comp
      (((h.pow_const (-κ)).const_mul B₁).add_const B₂)
  have hMajInt : ∫⁻ p, Maj p ∂chartPairMeasure U dens K ≠ ⊤ := by
    have hpow := admissible_logRegularization_reference_pair_kernel_lintegrable P U dens ε₀ Y hY
      K hK hKU κ hκ hκ2
    have hle : ∀ p, Maj p ≤ ENNReal.ofReal B₁ * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) +
        ENNReal.ofReal B₂ := by
      intro p
      rw [← ENNReal.ofReal_mul hB₁, ← ENNReal.ofReal_add (mul_nonneg hB₁
        (Real.rpow_nonneg (norm_nonneg _) _)) hB₂]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    have hmeasPow : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ))) := by
      have h : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
      exact ENNReal.measurable_ofReal.comp (h.pow_const (-κ))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeasPow,
      lintegral_const]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpow,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin⟩
  refine ⟨R₀, Maj, hMajMeas, hMajInt, fun r s hr hs g hg => ?_⟩
  filter_upwards [(chartPairMeasure_ae_offDiagonal U dens K hK.measurableSet)] with p hp
  exact hmaj r s hr hs g hg p hp.1 (norm_pos_iff.mpr (sub_ne_zero.mpr hp.2))

/-- Growing-barrier kernels are Cauchy in `L¹` of the chart pair measure, uniformly for charges
in a compact interval below the barrier slope with subcritical two-root exponent. -/
theorem growingPairKernel_L1_uniform_cauchy
    (hk₀cut : Real.exp (-(k₀ : ℝ)) ≤ ε₀)
    (hvar : ∀ k : ℕ, k₀ ≤ k → ∀ x ∈ K,
      1 ≤ gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r s r' s' : ℝ, R ≤ r → R ≤ s → R ≤ r' → R ≤ s' → ∀ g ∈ Icc gLo gHi,
      ∫⁻ p, ennDist (growingPairKernel P Y g a k₀ r s p)
          (growingPairKernel P Y g a k₀ r' s' p) ∂chartPairMeasure U dens K <
        ENNReal.ofReal ε := by
  classical
  set μ := chartPairMeasure U dens K with hμdef
  have hμfin := chartPairMeasure_univ_ne_top P U dens ε₀ Y hY K hK hKU
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.mpr hμfin⟩
  have hcarry := chartPairMeasure_ae_offDiagonal U dens K hK.measurableSet
  obtain ⟨R₀, B₁, B₂, hB₁, hB₂, hmaj⟩ := growingPairKernel_majorant P U dens ε₀ Y hY K hK hKU
    gLo gHi a η κ hgLo hgLoHi (le_trans hgLo.le (hgLoHi.trans hga.le)) ha2 hη hη1 hκ.le hκexp k₀
  let Maj : ℂ × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal (B₁ * ‖p.1 - p.2‖ ^ (-κ) + B₂)
  have hMajMeas : Measurable Maj := by
    have h : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
    exact ENNReal.measurable_ofReal.comp
      (((h.pow_const (-κ)).const_mul B₁).add_const B₂)
  have hMajInt : ∫⁻ p, Maj p ∂μ ≠ ⊤ := by
    have hpow := admissible_logRegularization_reference_pair_kernel_lintegrable P U dens ε₀ Y hY
      K hK hKU κ hκ hκ2
    have hle : ∀ p, Maj p ≤ ENNReal.ofReal B₁ * ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ)) +
        ENNReal.ofReal B₂ := by
      intro p
      rw [← ENNReal.ofReal_mul hB₁, ← ENNReal.ofReal_add (mul_nonneg hB₁
        (Real.rpow_nonneg (norm_nonneg _) _)) hB₂]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hle)
    have hmeasPow : Measurable (fun p : ℂ × ℂ => ENNReal.ofReal (‖p.1 - p.2‖ ^ (-κ))) := by
      have h : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖) := by fun_prop
      exact ENNReal.measurable_ofReal.comp (h.pow_const (-κ))
    rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeasPow,
      lintegral_const]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hpow,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin⟩
  -- the thin diagonal neighbourhoods
  let N : ℕ → Set (ℂ × ℂ) := fun n => {p | ‖p.1 - p.2‖ < 1 / (n + 1)}
  have hNmeas (n : ℕ) : MeasurableSet (N n) :=
    measurableSet_lt (by fun_prop) measurable_const
  have hNanti : Antitone N := by
    intro n m hnm p hp
    have hnm' : n + 1 ≤ (m : ℝ) + 1 := by simpa
    exact lt_of_lt_of_le hp (one_div_le_one_div_of_le (by positivity) hnm')
  let ν := μ.withDensity (fun p => 2 * Maj p)
  have hνN (n : ℕ) : ν (N n) = ∫⁻ p in N n, 2 * Maj p ∂μ := withDensity_apply _ (hNmeas n)
  have hνfin : ν (N 0) ≠ ⊤ := by
    rw [hνN]
    refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral ..)
    rw [lintegral_const_mul _ hMajMeas]
    exact ENNReal.mul_ne_top (by norm_num) hMajInt
  have hlim := tendsto_measure_iInter_atTop (fun n => (hNmeas n).nullMeasurableSet)
    hNanti ⟨0, hνfin⟩
  have hInter : ν (⋂ n, N n) = 0 := by
    have hsub : (⋂ n, N n) ⊆ {p : ℂ × ℂ | ¬ (p ∈ K ×ˢ K ∧ p.1 ≠ p.2)} := by
      intro p hp
      simp at hp
      simp only [Set.mem_ofPred_eq, not_and, not_not]
      intro _
      by_contra hne
      have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      exact absurd (hp n) (not_lt.mpr hn.le)
    exact withDensity_absolutelyContinuous μ _ (measure_mono_null hsub (ae_iff.mp hcarry))
  rw [hInter] at hlim
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := by positivity
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε2)).exists
  have hnear : ∫⁻ p in N n, 2 * Maj p ∂μ < ENNReal.ofReal (ε / 2) := by
    rw [← hνN]; exact hn
  -- the off-diagonal part
  set s₀ : ℝ := 1 / ((n : ℝ) + 1) with hs₀def
  have hs₀ : 0 < s₀ := by positivity
  set T := (μ univ).toReal with hTdef
  have hT : 0 ≤ T := ENNReal.toReal_nonneg
  set η₀ := ε / (2 * (T + 1)) with hη₀def
  have hη₀ : 0 < η₀ := by positivity
  obtain ⟨R₁, hR₁⟩ := growingPairKernel_offDiagonal_uniform_cauchy P U dens ε₀ Y hY K hK hKU
    gLo gHi a hgLo hgLoHi hga k₀ hk₀cut hvar s₀ hs₀ η₀ hη₀
  refine ⟨max R₀ R₁, ?_⟩
  intro r s r' s' hr hs hr' hs' g hg
  have hr₀' := le_trans (le_max_left ..) hr'
  have hs₀'' := le_trans (le_max_left ..) hs'
  have hr₁ := le_trans (le_max_right ..) hr
  have hs₁ := le_trans (le_max_right ..) hs
  have hr₁' := le_trans (le_max_right ..) hr'
  have hs₁' := le_trans (le_max_right ..) hs'
  have hsplit := lintegral_add_compl (μ := μ) (fun p => ennDist
    (growingPairKernel P Y g a k₀ r s p) (growingPairKernel P Y g a k₀ r' s' p)) (hNmeas n)
  rw [← hsplit]
  have hnearBound : ∫⁻ p in N n, ennDist (growingPairKernel P Y g a k₀ r s p)
      (growingPairKernel P Y g a k₀ r' s' p) ∂μ ≤ ∫⁻ p in N n, 2 * Maj p ∂μ := by
    apply setLIntegral_mono_ae' (hNmeas n)
    filter_upwards [hcarry] with p hp _
    have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr hp.2)
    have h1 := hmaj r s (le_trans (le_max_left ..) hr) (le_trans (le_max_left ..) hs) g hg p hp.1 hpos
    calc _ ≤ growingPairKernel P Y g a k₀ r s p + growingPairKernel P Y g a k₀ r' s' p :=
          ennDist_le_add ..
      _ ≤ Maj p + Maj p := add_le_add h1 (hmaj r' s' hr₀' hs₀'' g hg p hp.1 hpos)
      _ = 2 * Maj p := by ring
  have hfarBound : ∫⁻ p in (N n)ᶜ, ennDist (growingPairKernel P Y g a k₀ r s p)
      (growingPairKernel P Y g a k₀ r' s' p) ∂μ ≤ ENNReal.ofReal η₀ * μ univ := by
    calc _ ≤ ∫⁻ _ in (N n)ᶜ, ENNReal.ofReal η₀ ∂μ := by
          apply setLIntegral_mono_ae' (hNmeas n).compl
          filter_upwards [hcarry] with p hp hpN
          have hsep : p ∈ separatedPairs K s₀ := by
            refine ⟨hp.1, ?_⟩
            simp only [N, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hpN
            exact hpN
          obtain ⟨htop, hclose⟩ := hR₁ r s r' s' hr₁ hs₁ hr₁' hs₁' g hg p hsep
          obtain ⟨htop', -⟩ := hR₁ r' s' r s hr₁' hs₁' hr₁ hs₁ g hg p hsep
          rw [ennDist_eq_ofReal_abs htop htop']
          exact ENNReal.ofReal_le_ofReal hclose.le
      _ = ENNReal.ofReal η₀ * μ (N n)ᶜ := setLIntegral_const ..
      _ ≤ ENNReal.ofReal η₀ * μ univ := by gcongr; exact Set.subset_univ _
  have hfarSmall : ENNReal.ofReal η₀ * μ univ < ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_toReal hμfin, ← ENNReal.ofReal_mul hη₀.le, ← hTdef]
    apply (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr
    rw [hη₀def, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith only [hε]
  calc _ ≤ ∫⁻ p in N n, 2 * Maj p ∂μ + ENNReal.ofReal η₀ * μ univ :=
        add_le_add hnearBound hfarBound
    _ < ENNReal.ofReal _ + ENNReal.ofReal _ := ENNReal.add_lt_add hnear hfarSmall
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1
        ring

end

end

end

end

end DOZZ.Assembly
