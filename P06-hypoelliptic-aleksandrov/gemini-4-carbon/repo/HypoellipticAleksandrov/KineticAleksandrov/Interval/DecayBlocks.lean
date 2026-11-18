module

public import HypoellipticAleksandrov.KineticAleksandrov.Interval.FourierKernels
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsComposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Interval.Killing
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Interval
open MeasureTheory Set HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Decay
open scoped ENNReal ProbabilityTheory
variable {a c : ℝ}






/-- Temporal Fourier composition contracts total variation by the largest terminal norm. -/
theorem intervalFourierKernel_totalVariation_composition {a c : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) :
    totalVariationNorm (intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v) ≤
      totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) *
        ⨆ v' : PDE.oneDimensionalAxisBox a c,
          totalVariationNorm (intervalFourierKernel K r τ hrτ ξ v')   := by
  have measurable_intervalFourierKernelZero_apply (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (E : Set (PDE.Vec 1)) (hE : MeasurableSet E) :
      Measurable (fun v => intervalFourierKernelZero K σ τ hστ ξ v E) := by
    convert (MeasurableEmbedding.subtype_coe hJ).measurable_extend (measurable_intervalFourierKernel_apply K σ τ hστ ξ E hE) (measurable_const (a := 0)) using 1
    funext v
    by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
    · have he := Subtype.val_injective.extend_apply
        (fun w => intervalFourierKernel K σ τ hστ ξ w E) (fun _ => 0) ⟨v, hv⟩
      exact (congrArg (fun ν : ComplexMeasure (PDE.Vec 1) => ν E)
        (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩)).trans he.symm
    · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
      exact (Function.extend_apply'

        (fun w => intervalFourierKernel K σ τ hστ ξ w E) (fun _ => 0) v
        (by rintro ⟨w, rfl⟩; exact hv w.2)).symm
  have intervalFourierKernel_composition (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1)) (hE : MeasurableSet E) :
      intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v E =
      ∫ᵛ v', intervalFourierKernelZero K r τ hrτ ξ v' E
        ∂[ContinuousLinearMap.mul ℝ ℂ; intervalFourierKernel K σ r hσr ξ v] := by
    have intervalFourierKernelZero_apply_norm_le_one (σ τ : ℝ) (hστ : σ ≤ τ) (ξ v : PDE.Vec 1) (E : Set (PDE.Vec 1)) :
        ‖intervalFourierKernelZero K σ τ hστ ξ v E‖ ≤ 1 := by
      have intervalFourierKernel_apply_norm_le_one (σ τ : ℝ) (hστ : σ ≤ τ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c) (E : Set (PDE.Vec 1)) :
          ‖intervalFourierKernel K σ τ hστ ξ v E‖ ≤ 1 := by
        have he : (intervalFourierKernel K σ τ hστ ξ v).variation E ≤ 1 :=
          (measure_mono (subset_univ E)).trans
            (intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ v)
        have hn := VectorMeasure.norm_measure_le_variation
          (μ := intervalFourierKernel K σ τ hστ ξ v) (ne_of_lt (he.trans_lt ENNReal.one_lt_top))
        exact hn.trans (by simpa only [Measure.real, ENNReal.toReal_one] using
          ENNReal.toReal_mono ENNReal.one_ne_top he)
      by_cases hv : v ∈ PDE.oneDimensionalAxisBox a c
      · exact (intervalFourierKernelZero_coe K σ τ hστ ξ ⟨v, hv⟩ ▸
          intervalFourierKernel_apply_norm_le_one σ τ hστ ξ ⟨v, hv⟩ E)
      · rw [intervalFourierKernelZero_of_notMem K σ τ hστ ξ v hv]
        simp
    let p : EvolutionState (PDE.oneDimensionalAxisBox a c) stationary σ :=
      ⟨(v.1, 0), ⟨by simpa only [movingDomain_stationary] using v.2, mem_univ _⟩⟩
    let f := fun v' => intervalFourierKernelZero K r τ hrτ ξ v' E
    let g := (E ×ˢ univ).indicator (fourierPhase ξ 0)
    have hf : Measurable f := measurable_intervalFourierKernelZero_apply r τ hrτ ξ E hE
    have hg : Measurable g := (continuous_fourierPhase ξ 0).measurable.indicator
      (hE.prod MeasurableSet.univ)
    have hgb : ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
      refine ⟨1, fun w => ?_⟩
      by_cases hw : w ∈ E ×ˢ univ
      · simpa only [g, indicator_of_mem hw] using (norm_fourierPhase ξ 0 w).le
      · simp only [g, indicator_of_notMem hw, norm_zero, zero_le_one]
    have hfb : ∃ C : ℝ, ∀ v', ‖f v'‖ ≤ C :=
      ⟨1, fun v' => intervalFourierKernelZero_apply_norm_le_one r τ hrτ ξ v' E⟩
    rw [fourierProjection_integral_complex K _ ξ _
      (intervalFourierKernel_spec K σ r hσr ξ v) f hf hfb]
    change _ = ∫ w, f w.1 * fourierPhase ξ 0 w
      ∂K.master (evolutionQueryOfState (PDE.oneDimensionalAxisBox a c)
        stationary σ r hσr p)
    rw [intervalFourierKernel_spec K σ τ (hσr.trans hrτ) ξ v E hE,
      ← integral_indicator (hE.prod MeasurableSet.univ)]
    change (∫ w, g w ∂K.master
      (evolutionQueryOfState (PDE.oneDimensionalAxisBox a c)
        stationary σ τ (hσr.trans hrτ) p)) = _
    rw [master_integral_composition K hJ hcomp σ r τ hσr hrτ p g hg hgb,
      master_integral_eq_fiber K hJ σ r hσr p
        (fun w => f w.1 * fourierPhase ξ 0 w)
        ((hf.comp measurable_fst).mul (continuous_fourierPhase ξ 0).measurable)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w
    let wv : PDE.oneDimensionalAxisBox a c :=
      ⟨w.1.1, by simpa using w.2.1⟩
    change (∫ w', g w' ∂K.master
      (movingQuery r τ hrτ wv.1 w.1.2
        (by simpa using wv.2))) =
      intervalFourierKernelZero K r τ hrτ ξ wv.1 E * fourierPhase ξ 0 w.1
    rw [(intervalFourierKernelZero_coe K r τ hrτ ξ wv), ← intervalFourierKernel_eq_startingPosition K hJ hcov r τ hrτ ξ wv w.1.2,
      fourierProjection_spec K _ ξ E hE,
      ← integral_indicator (hE.prod MeasurableSet.univ), ← integral_mul_const]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro w'
    by_cases hw' : w'.1 ∈ E
    · simp only [g, indicator_of_mem (show w' ∈ E ×ˢ univ from ⟨hw', mem_univ _⟩)]
      rw [fourierPhase_factor ξ 0 w.1 w', mul_comm]
      rfl
    · simp [g, indicator_of_notMem
        (show w' ∉ E ×ˢ univ from fun hw => hw' hw.1)]
  classical
  let ν := intervalFourierKernel K σ r hσr ξ v
  let ν' := intervalFourierKernel K σ τ (hσr.trans hrτ) ξ v
  let C := ⨆ v' : PDE.oneDimensionalAxisBox a c,
    totalVariationNorm (intervalFourierKernel K r τ hrτ ξ v')
  have hB : ‖ContinuousLinearMap.mul ℝ ℂ‖ₑ ≤ 1 := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_ofReal
      (LinearMap.mkContinuous₂_norm_le (LinearMap.mul ℝ ℂ) zero_le_one
        (fun x y => by simpa using norm_mul_le x y))).trans_eq
      ENNReal.ofReal_one
  by_contra hn
  have hlt : totalVariationNorm ν * C < ν'.variation univ := lt_of_not_ge hn
  obtain ⟨P, _, hPd, hPm, hPgt⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation ν' MeasurableSet.univ hlt
  have hsum : ∑ E ∈ P, ‖ν' E‖ₑ ≤ totalVariationNorm ν * C := by
    calc
      _ ≤ ∑ E ∈ P, ∫⁻ v', ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        apply Finset.sum_le_sum
        intro E hEP
        rw [intervalFourierKernel_composition σ r τ hσr hrτ ξ v E (hPm E hEP)]
        exact (VectorMeasure.enorm_integral_le_lintegral_enorm).trans
          (by
            simpa only [one_mul] using
              (mul_le_mul' hB (le_refl
                (∫⁻ v', ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation))))
      _ = ∫⁻ v', ∑ E ∈ P, ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ ∂ν.variation := by
        rw [lintegral_finsetSum P (fun E hEP =>
          (measurable_intervalFourierKernelZero_apply r τ hrτ ξ E (hPm E hEP)).enorm)]
      _ ≤ ∫⁻ v', C ∂ν.variation := by
        apply lintegral_mono
        intro v'
        change (∑ E ∈ P, ‖intervalFourierKernelZero K r τ hrτ ξ v' E‖ₑ) ≤ C
        by_cases hv' : v' ∈ PDE.oneDimensionalAxisBox a c
        · rw [intervalFourierKernelZero_coe K r τ hrτ ξ ⟨v', hv'⟩]
          exact (VectorMeasure.le_variation (intervalFourierKernel K r τ hrτ ξ ⟨v', hv'⟩)
            MeasurableSet.univ (fun E _ => subset_univ E) hPd).trans
            (le_iSup (fun x => totalVariationNorm (intervalFourierKernel K r τ hrτ ξ x))
              ⟨v', hv'⟩)
        · simp [intervalFourierKernelZero_of_notMem K r τ hrτ ξ v' hv', zero_apply, enorm_zero, zero_le]
      _ = totalVariationNorm ν * C := by
        rw [lintegral_const, mul_comm]
  exact (not_lt_of_ge hsum) hPgt


/-- Each full block contributes its contraction; the leftover interval contributes at most one. -/
theorem interval_natural_block_iteration {a b : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a b) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a b))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a b) stationary hJ K)
    (ξ : PDE.Vec 1) {T c : ℝ} (hT : 0 < T) (_hc : 0 ≤ c)
    (hstep : ∀ (s : ℝ) (v : PDE.oneDimensionalAxisBox a b),
      totalVariationNorm (intervalFourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤
        ENNReal.ofReal c) (k : ℕ) (σ τ : ℝ) (hστ : σ ≤ τ)
    (hk : (k : ℝ) * T ≤ τ - σ) (v : PDE.oneDimensionalAxisBox a b) :
    totalVariationNorm (intervalFourierKernel K σ τ hστ ξ v) ≤ ENNReal.ofReal c ^ k := by
  induction k generalizing σ τ v with
  | zero => simpa using intervalFourierKernel_totalVariation_le_one K σ τ hστ ξ v
  | succ k ih =>
    let r := σ + T
    have hσr : σ ≤ r := le_add_of_nonneg_right hT.le
    have hrτ : r ≤ τ := by
      have hn : 0 ≤ k := Nat.cast_nonneg k
      rw [Nat.cast_succ] at hk
      nlinarith only [hk, hT, hn]
    have hremain : (k : ℝ) * T ≤ τ - r := by
      rw [Nat.cast_succ] at hk
      dsimp [r]
      linarith only [hk]
    have htail : (⨆ w : PDE.oneDimensionalAxisBox a b,
        totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w)) ≤
        ENNReal.ofReal c ^ k :=
      iSup_le fun w => ih r τ hrτ hremain w
    calc
      _ ≤ totalVariationNorm (intervalFourierKernel K σ r hσr ξ v) *
          ⨆ w : PDE.oneDimensionalAxisBox a b,
            totalVariationNorm (intervalFourierKernel K r τ hrτ ξ w) :=
        intervalFourierKernel_totalVariation_composition K hJ hcomp hcov σ r τ hσr hrτ ξ v
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal c ^ k := mul_le_mul' (hstep σ v) htail
      _ = ENNReal.ofReal c ^ (k + 1) := by rw [pow_succ, mul_comm]


/-- Full-block contractions imply exponential decay, including durations shorter than a block. -/
theorem interval_exponential_of_blocks {a c T q : ℝ}
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (hcomp : K.HasComposition hJ)
    (hcov : IsTranslationCovariantEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ K)
    (hT : 0 < T) (hq : 0 < q) (hq1 : q ≤ 1) (ξ : PDE.Vec 1)
    (hsteps : ∀ (s : ℝ) (v : PDE.oneDimensionalAxisBox a c),
      TV (intervalFourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤ q)
    (σ τ : ℝ) (hστ : σ ≤ τ) (v : PDE.oneDimensionalAxisBox a c) :
    TV (intervalFourierKernel K σ τ hστ ξ v) ≤
      q⁻¹ * Real.exp (-(-Real.log q / T) * (τ - σ)) := by
  let x := (τ - σ) / T
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hστ) hT.le
  have hk : (Nat.floor x : ℝ) * T ≤ τ - σ := by
    calc (Nat.floor x : ℝ) * T ≤ x * T :=
          mul_le_mul_of_nonneg_right (Nat.floor_le hx) hT.le
      _ = τ - σ := div_mul_cancel₀ _ hT.ne'
  have hstep : ∀ (s : ℝ) (w : PDE.oneDimensionalAxisBox a c),
      totalVariationNorm (intervalFourierKernel K s (s + T)
        (le_add_of_nonneg_right hT.le) ξ w) ≤ ENNReal.ofReal q := by
    intro s w
    have hf : totalVariationNorm (intervalFourierKernel K s (s + T)
        (le_add_of_nonneg_right hT.le) ξ w) ≠ ⊤ :=
      ne_of_lt ((intervalFourierKernel_totalVariation_le_one K _ _ _ ξ w).trans_lt
        ENNReal.one_lt_top)
    rw [← ENNReal.ofReal_toReal hf]
    exact ENNReal.ofReal_le_ofReal (hsteps s w)
  have hr := ENNReal.toReal_mono (by simp) (interval_natural_block_iteration K hJ hcomp hcov ξ hT hq.le hstep (Nat.floor x) σ τ hστ hk v)
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hq.le] at hr
  have he := decay_power_exponential hq hT (τ - σ) 1
  simp only [mul_one] at he
  exact hr.trans ((decay_floor_power hq hq1).trans_eq he)

/-- Over a squared-length block the largest endpoint barrier is length independent. -/
theorem intervalHeat_squared_length {lam ℓ : ℝ} (hlam : 0 < lam) (hℓ : 0 < ℓ) :
    intervalHeat lam (ℓ ^ 2) (ℓ / 2) = intervalErf (1 / (4 * Real.sqrt lam)) := by
  unfold intervalHeat
  rw [Real.sqrt_mul hlam.le, Real.sqrt_sq_eq_abs, abs_of_pos hℓ]
  congr 1
  field_simp
  ring

/-- Every Fourier mode contracts over one squared-length killing block. -/
theorem interval_killing_block
    (hH : HormanderHypoellipticityStatement)
    (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam m Lb a c : ℝ} (hac : a < c)
    (B : CoefficientField 1) (b : PDE.Vec 1 → PDE.Vec 1)
    (hs : SourceSetting lam Lam m Lb (PDE.oneDimensionalAxisBox a c) B b)
    (hJ : MeasurableSet (PDE.oneDimensionalAxisBox a c))
    (S : TerminalOperatorFamily (PDE.oneDimensionalAxisBox a c) stationary)
    (K : MovingFiberKernel (PDE.oneDimensionalAxisBox a c) stationary)
    (hr : RealizesTerminalEvolution (PDE.oneDimensionalAxisBox a c) stationary hJ
      (zIndependentCoefficient B) b S K)
    (σ : ℝ) (ξ : PDE.Vec 1) (v : PDE.oneDimensionalAxisBox a c)
    (ht : σ ≤ σ + (c - a) ^ 2) :
    TV (intervalFourierKernel K σ (σ + (c - a) ^ 2) ht ξ v) ≤
      intervalErf (1 / (4 * Real.sqrt lam)) := by
  have hlen : 0 < c - a := sub_pos.mpr hac
  have hT := sq_pos_of_pos hlen
  have hv : v.1 ∈ movingDomain (PDE.oneDimensionalAxisBox a c) stationary σ := by
    simpa only [movingDomain_stationary] using v.2
  have htv := interval_fourier_tv_le_mass hJ K B ((interval_evolution_clauses hH hLE hac B b hs hJ S K hr).2.1) σ (σ + (c - a) ^ 2) ht
    v.1 0 ξ hv _ (intervalFourierKernel_spec K _ _ ht ξ v)
  have hkill := interval_killing hH hLE hac B b hs hJ S K hr σ (σ + (c - a) ^ 2)
    (lt_add_of_pos_right σ hT) v.1 hv
  have he : σ + (c - a) ^ 2 - σ = (c - a) ^ 2 := by ring
  rw [he] at hkill
  have hd : min (v.1 0 - a) (c - v.1 0) ≤ (c - a) / 2 := by
    rcases le_total (v.1 0 - a) (c - v.1 0) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hm := intervalHeat_mono_distance hs.1.1 hT hd
  rw [intervalHeat_squared_length hs.1.1 hlen] at hm
  exact htv.trans (hkill.trans hm)

/-- The killing-block contraction factor belongs to `(0,1)`. -/
theorem interval_killing_factor {lam : ℝ} (hlam : 0 < lam) :
    0 < intervalErf (1 / (4 * Real.sqrt lam)) ∧
      intervalErf (1 / (4 * Real.sqrt lam)) < 1 := by
  have hx : 0 < 1 / (4 * Real.sqrt lam) := by positivity
  refine ⟨?_, intervalErf_lt_one hx.le⟩
  rw [← intervalErf_zero]
  exact strictMono_intervalErf hx

end HypoellipticAleksandrov.KineticAleksandrov.Interval

