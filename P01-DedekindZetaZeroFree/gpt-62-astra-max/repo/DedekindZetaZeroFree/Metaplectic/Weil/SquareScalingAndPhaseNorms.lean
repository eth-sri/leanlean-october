module
public import DedekindZetaZeroFree.Metaplectic.Weil.FiniteQuadraticFourierKernel

public import DedekindZetaZeroFree.Metaplectic.Weil.Finite.OscillatoryIntegralStabilization
public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.SIntegers.DilationAndTranslation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SArithmeticData
open NumberField IsDedekindDomain MeasureTheory Filter
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private lemma squareScaling_cutoff_scale (v : HeightOneSpectrum (𝓞 F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (a t : (v.adicCompletion F)ˣ) (n m : ℕ)
    (h : (v.asIdeal.absNorm : ℝ)^m = ‖t.val‖ * (v.asIdeal.absNorm : ℝ)^n) :
    exteriorRawQuadraticCutoff v μ (a * t^2) n = exteriorRawQuadraticCutoff v μ a m := by
  let f : v.adicCompletion F → ℂ := fun x =>
    (ResidueTrace.localTraceCharacter v (a.val * x^2) : ℂ)
  have hs (r : ℕ) : MeasurableSet (exteriorQuadraticCutoff v r) :=
    (isClosed_le continuous_norm continuous_const).measurableSet
  have he : ∀ x : v.adicCompletion F,
      (exteriorQuadraticCutoff v m).indicator f (t.val * x) =
      (exteriorQuadraticCutoff v n).indicator
        (fun x => (ResidueTrace.localTraceCharacter v ((a * t^2).val * x^2) : ℂ)) x := by
    intro x
    have ht : 0 < ‖t.val‖ := norm_pos_iff.mpr t.ne_zero
    have hx : t.val * x ∈ exteriorQuadraticCutoff v m ↔ x ∈ exteriorQuadraticCutoff v n := by
      change ‖t.val*x‖ ≤ _ ↔ ‖x‖ ≤ _
      rw [norm_mul, h]
      exact mul_le_mul_iff_right₀ ht
    by_cases H : x ∈ exteriorQuadraticCutoff v n
    · rw [Set.indicator_of_mem (hx.mpr H), Set.indicator_of_mem H]
      dsimp [f]
      congr 1
      congr 1
      ring
    · rw [Set.indicator_of_notMem (mt hx.mp H), Set.indicator_of_notMem H]
  have hi := PoissonS.finite_unit_integral_scale F v μ t⁻¹
    ((exteriorQuadraticCutoff v m).indicator f)
  simp only [inv_inv] at hi
  simp_rw [he] at hi
  rw [integral_indicator (hs n), integral_indicator (hs m)] at hi
  unfold exteriorRawQuadraticCutoff
  rw [hi]
  have hn : ‖(2 : v.adicCompletion F) * (a * t ^ 2).val‖ =
      ‖(2 : v.adicCompletion F) * a.val‖ * ‖t.val‖^2 := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, ← mul_assoc, norm_mul, norm_pow]
  rw [hn, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [Complex.ofReal_mul]
  have ht : (‖t.val‖ : ℂ) * (‖t⁻¹.val‖ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← norm_mul, Units.mul_inv, norm_one, Complex.ofReal_one]
  change ((Real.sqrt ‖(2 : v.adicCompletion F) * a.val‖ : ℂ) * (‖t.val‖ : ℂ)) *
    ((‖t⁻¹.val‖ : ℂ) * _) = _
  rw [mul_assoc, ← mul_assoc (‖t.val‖ : ℂ), ht, one_mul]
private alias squareScaling_traceHaar := FiniteQuadraticFourierKernel.finiteKernel_traceHaar

theorem finiteGamma_mul_sq (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (a t : (v.adicCompletion F)ˣ) :
    A.finiteGamma v (a * t ^ 2) = A.finiteGamma v a := by
  haveI := squareScaling_traceHaar A v
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have ht : Valued.v t.val ≠ (0 : WithZero (Multiplicative ℤ)) :=
    (Valued.v.map_eq_zero_iff).not.mpr t.ne_zero
  let k : ℤ := WithZero.log (Valued.v t.val)
  have hk : ‖t.val‖ = (v.asIdeal.absNorm : ℝ)^k := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ ht]
    simp [k]
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (A.finiteQuadraticCutoff_eventually_eq_gamma v (a*t^2) (A.finiteQuadratic_stabilizes v _))
  obtain ⟨M, hM⟩ := eventually_atTop.1
    (A.finiteQuadraticCutoff_eventually_eq_gamma v a (A.finiteQuadratic_stabilizes v _))
  let n := N + M + (-k).toNat
  let m := N + M + k.toNat
  have hm : (m : ℤ) = k + (n : ℤ) := by
    dsimp [n, m]
    omega
  have hh : (v.asIdeal.absNorm : ℝ)^m = ‖t.val‖ * (v.asIdeal.absNorm : ℝ)^n := by
    rw [hk, ← zpow_natCast, ← zpow_natCast, hm, zpow_add₀ hq.ne']
  rw [← hN n (by dsimp [n]; omega), ← hM m (by dsimp [m]; omega)]
  exact squareScaling_cutoff_scale v (A.finiteTraceHaar v) a t n m hh

alias finiteGamma_norm := norm_finiteGamma

section

variable (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))

theorem finiteWeilPhase_mul_sq (a t : (v.adicCompletion F)ˣ) :
    A.finiteWeilPhase v (a * t ^ 2) = A.finiteWeilPhase v a := by
  rw [finiteWeilPhase, finiteWeilPhase, finiteGamma_mul_sq]

theorem finiteWeilPhase_one : A.finiteWeilPhase v 1 = 1 := by
  have hne : A.finiteGamma v 1 ≠ 0 := by
    intro h0
    have h := A.finiteGamma_norm v 1
    rw [h0, norm_zero] at h
    exact one_ne_zero h.symm
  rw [finiteWeilPhase, div_self hne]

theorem finiteWeilPhase_sq (a : (v.adicCompletion F)ˣ) :
    A.finiteWeilPhase v (a ^ 2) = 1 := by
  rw [← one_mul (a ^ 2), finiteWeilPhase_mul_sq, finiteWeilPhase_one]

theorem finiteWeilPhase_norm (a : (v.adicCompletion F)ˣ) :
    ‖A.finiteWeilPhase v a‖ = 1 := by
  rw [finiteWeilPhase, norm_div, A.finiteGamma_norm v a, A.finiteGamma_norm v 1, div_one]

end

variable (A : SArithmeticData F) (w : InfinitePlace F)

theorem complexWeilPhase_mul_sq (a t : w.Completionˣ) :
    A.complexWeilPhase w (a * t ^ 2) = A.complexWeilPhase w a := by
  simp [complexWeilPhase, complexGamma]

theorem complexWeilPhase_one : A.complexWeilPhase w 1 = 1 := by
  simp [complexWeilPhase, complexGamma]

end DedekindZetaZeroFree.SArithmeticData

end
