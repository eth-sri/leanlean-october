module
public import GuthMaynard.Improvement.SamplingVariation
public import GuthMaynard.Improvement.ReflectedBandMeanValue
public import GuthMaynard.Improvement.SourceDirichletPairing
public import GuthMaynard.Improvement.AmplifierArithmetic
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory Set Finset
namespace GuthMaynard.Improvement

/-- Integer-frequency masking preserves the original real-N source interval. -/
def sourceIntegerCoefficient (N : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ sourceRatioIndices N then a n else 0

def sourceDerivativeCoefficient (N : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n*((Real.log ((n:ℝ)/N):ℂ)*Complex.I)

section
variable {N : ℝ} (hN : 0 < N)
include N hN
theorem source_log_bounds {n : ℕ} (hn : n ∈ sourceRatioIndices N) :
    0 ≤ Real.log ((n:ℝ)/N) ∧ Real.log ((n:ℝ)/N) ≤ 1 := by
  have hb := (sourceRatioIndices_mem hN.le n).mp hn
  pm_751 hratio hratio2
  exact ⟨Real.log_nonneg hratio,(Real.log_le_log (by positivity) hratio2).trans
    (by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith)⟩

theorem source_derivative_coefficient_bound (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) :
    ∀ n ∈ sourceRatioIndices N, ‖sourceDerivativeCoefficient N a n‖ ≤ 1 := by
  intro n hn
  have hl := source_log_bounds hN hn
  rw [sourceDerivativeCoefficient,norm_mul,norm_mul,Complex.norm_I,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl.1]
  pm_7856
end

theorem boundedPolynomial_hasDerivAt (N : ℝ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (boundedPolynomial N a) (boundedPolynomial N (sourceDerivativeCoefficient N a) t) t := by
  unfold boundedPolynomial
  apply HasDerivAt.fun_sum
  intro n _
  have hd : HasDerivAt (fun s : ℝ => ((s*Real.log ((n:ℝ)/N):ℝ):ℂ)*Complex.I)
      ((Real.log ((n:ℝ)/N):ℂ)*Complex.I) t := by
    simpa only [id_eq,one_mul] using
      (((hasDerivAt_id t).mul_const (Real.log ((n:ℝ)/N))).ofReal_comp).mul_const Complex.I
  have hh := (hd.cexp).const_mul (a n)
  convert hh using 1
  simp only [sourceDerivativeCoefficient]
  ring

/-- Actual continuous mean value for the literal normalized source polynomial. -/
theorem boundedPolynomial_mean_value {N : ℝ} (hN : 0 < N) (a : ℕ → ℂ)
    (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    (∫ x in Icc s t, ‖boundedPolynomial N a x‖^2) ≤
      ((t-s)+4*(⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)))*(N+1) := by
  let X := ⌊2*N⌋₊
  let c := sourceIntegerCoefficient N a
  have hsub : sourceRatioIndices N ⊆ Finset.Icc 1 X := by
    intro n hn
    have hb := (sourceRatioIndices_mem hN.le n).mp hn
    exact mem_Icc.mpr ⟨by exact_mod_cast hN.trans hb.1,Nat.le_floor hb.2⟩
  have hpoly (x : ℝ) : finiteDirichletPolynomial X c x =
      ∑ n ∈ sourceRatioIndices N, a n*dirichletPhase n x := by
    unfold finiteDirichletPolynomial
    pm_1591
    exact sum_congr rfl (fun n hn => by simp [c,sourceIntegerCoefficient,hn])
  have hnorm (x : ℝ) : ‖boundedPolynomial N a x‖=‖finiteDirichletPolynomial X c x‖ := by
    rw [boundedPolynomial_integer_phase hN,norm_mul,MathCollab.Density.norm_dirichletPhase,one_mul,hpoly]
  have henergy : (∑ n ∈ Finset.Icc 1 X, ‖c n‖^2) ≤ N+1 := by
    pm_1591
    calc
      _ ≤ ∑ _n ∈ sourceRatioIndices N, (1:ℝ) := by
        apply sum_le_sum
        intro n hn
        simp only [c,sourceIntegerCoefficient,ite_eq_left hn]
        pm_7856
      _ ≤ _ := by simpa [sourceRatioIndices,amplifierSource] using amplifier_source_card hN.le
  have hcoef : 0 ≤ (t-s)+4*(X:ℝ)*(1+Real.log (X:ℝ)) := by
    by_cases hx : X=0
    · simp only [hx,Nat.cast_zero,mul_zero,zero_mul,add_zero]; linarith
    · have hh : 1 ≤ (X:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx
      have hl := Real.log_nonneg hh
      positivity
  simp_rw [hnorm]
  exact (dirichlet_mean_value X c hst).trans (mul_le_mul_of_nonneg_left henergy hcoef)

/-- Actual separated sampling of D²; the derivative is another bounded-coefficient source polynomial. -/
theorem separated_second_moment_raw {N T t₀ : ℝ} (hN : 0 < N) (hT : 0 ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t-s|) :
    (∑ t ∈ W, ‖boundedPolynomial N a t‖^2) ≤
      3*((T+1)+4*(⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)))*(N+1) := by
  let D := boundedPolynomial N a
  let D' := boundedPolynomial N (sourceDerivativeCoefficient N a)
  let S := Icc t₀ (t₀+T+1)
  have hc : Continuous D := (boundedPolynomial_regular N a).1
  have hc' : Continuous D' := (boundedPolynomial_regular N _).1
  have hd : ∀ t, HasDerivAt (fun x => D x^2) (2*D t*D' t) t := by
    intro t
    convert (boundedPolynomial_hasDerivAt N a t).pow 2 using 1
    simp [D,D',pow_one]
  have hf : IntegrableOn (fun t => D t^2) S := (hc.pow 2).continuousOn.integrableOn_Icc
  have hi : IntegrableOn (fun t => 2*D t*D' t) S := ((continuous_const.mul hc).mul hc').continuousOn.integrableOn_Icc
  have hs : Pairwise (fun t s : W => (1:ℝ) ≤ |(t:ℝ)-(s:ℝ)|) := by
    pm_7924 s s.property
  have hsub : ∀ t : W, Ioc (t:ℝ) ((t:ℝ)+1) ⊆ S := by
    pm_8314
    exact ⟨by linarith [ht.1,hx.1],by linarith [ht.2,hx.2]⟩
  have hh := sampling_separated_norm (fun t : W => (t:ℝ)) (by norm_num : (0:ℝ)<1) hd hs hsub hf hi
  simp only [inv_one,one_mul,norm_pow] at hh
  rw [Finset.sum_coe_sort W (fun t => ‖D t‖^2)] at hh
  pm_8183 hD D hc.norm.pow
  pm_8183 hD' D' hc'.norm.pow
  have hiBound : (∫ t in S, ‖2*D t*D' t‖) ≤
      (∫ t in S, ‖D t‖^2)+(∫ t in S, ‖D' t‖^2) := by
    pm_6687
    simp only [norm_mul,Complex.norm_ofNat,Pi.add_apply]
    nlinarith [sq_nonneg (‖D t‖-‖D' t‖)]
  have hb := boundedPolynomial_mean_value hN a ha (show t₀ ≤ t₀+T+1 by linarith)
  have hb' := boundedPolynomial_mean_value hN (sourceDerivativeCoefficient N a)
    (source_derivative_coefficient_bound hN a ha) (show t₀ ≤ t₀+T+1 by linarith)
  change (∑ t ∈ W, ‖D t‖^2) ≤ _
  dsimp only [S,D,D'] at hh hiBound
  nlinarith

/-- Uniform scalar simplification of the checked raw sampling cost. -/
theorem separated_second_moment_scalar {N T : ℝ} (hN : 2 ≤ N) (hT : 0 ≤ T) :
    3*((T+1)+4*(⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)))*(N+1) ≤
      102*N*(T+N*Real.log (2*N)) := by
  have hN0 : 0 ≤ N := by linarith
  have hx : (⌊2*N⌋₊:ℝ) ≤ 2*N := Nat.floor_le (by positivity)
  have hx1 : (1:ℝ) ≤ ⌊2*N⌋₊ := by
    pm_5703
  have hlg : Real.log (⌊2*N⌋₊:ℝ) ≤ Real.log (2*N) := Real.log_le_log (by linarith) hx
  pm_4553
  have hm : (⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)) ≤ 4*N*Real.log (2*N) := by
    have hh := mul_le_mul hx (show 1+Real.log (⌊2*N⌋₊:ℝ) ≤ 2*Real.log (2*N) by linarith)
      (by linarith [Real.log_nonneg hx1]) (by positivity : 0 ≤ 2*N)
    nlinarith
  have hfac : (T+1)+4*(⌊2*N⌋₊:ℝ)*(1+Real.log (⌊2*N⌋₊:ℝ)) ≤ T+17*N*Real.log (2*N) := by
    nlinarith
  calc
    _ ≤ 3*(T+17*N*Real.log (2*N))*(2*N) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hfac (by norm_num)
      · linarith
      · linarith
      · positivity
    _ ≤ _ := by nlinarith [mul_nonneg hN0 hT]

section
variable {N T t₀ : ℝ} (hN : 2 ≤ N)
include N T t₀ hN
/-- Actual separated second moment with an absolute constant and no analytic premise. -/
theorem separated_second_moment (hT : 0 ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t-s|) :
    (∑ t ∈ W, ‖boundedPolynomial N a t‖^2) ≤ 102*N*(T+N*Real.log (2*N)) :=
  (separated_second_moment_raw (by linarith) hT a ha W hW hsep).trans
    (separated_second_moment_scalar hN hT)

/-- Long-interval form used by the source extraction and low-value range. -/
theorem separated_second_moment_long (hNT : N ≤ T)
    (a : ℕ → ℂ) (ha : ∀ n ∈ sourceRatioIndices N, ‖a n‖ ≤ 1)
    (W : Finset ℝ) (hW : ∀ t ∈ W, t ∈ Icc t₀ (t₀+T))
    (hsep : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t-s|) :
    (∑ t ∈ W, ‖boundedPolynomial N a t‖^2) ≤ 204*T*N*Real.log (2*N) := by
  pm_4553
  apply (separated_second_moment hN (by linarith) a ha W hW hsep).trans
  pm_6303
  have ht := mul_le_mul_of_nonneg_left hlog (show 0 ≤ T by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (show T+N*Real.log (2*N) ≤ 2*T*Real.log (2*N) by linarith)
    (show 0 ≤ 102*N by positivity)]
end

end GuthMaynard.Improvement
