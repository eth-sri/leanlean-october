module
public import PottsDiscontinuity.Bethe.RatioProfile

public import Mathlib
public import PottsDiscontinuity.Analysis.Section4Series

/-!
# The explicit τ integral in Section 4

The literal τ series is interpreted by its ordered partial sums.  This file uses Abel means of
that series.  The Poisson regularization splits into a sawtooth term and an exponentially
convergent correction, which gives the uniform local bound needed against the singular `P'`.
-/

@[expose] public section

open Complex Filter MeasureTheory Real Topology Set intervalIntegral

namespace PottsDiscontinuity

private alias fourier_one_sub_cos_lower_tau := Bethe.ratio_one_sub_cos_lower

 noncomputable def fourierPrimeControl (lam : ℝ) : ℝ :=
  (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) / 2

private theorem fourierPPrime_alpha_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α| * |α| ≤ fourierPrimeControl lam := by
  by_cases hα0 : α = 0
  · have hcosh : 1 < Real.cosh (2 * lam) :=
      Real.one_lt_cosh.mpr (by positivity)
    simp [hα0]
    dsimp [fourierPrimeControl]
    positivity
  · have hcosLower := fourier_one_sub_cos_lower_tau hα
    
    
    have hdenLower : 0 < 1 - Real.cos α := lt_of_lt_of_le (by positivity) hcosLower
    have hcosh : 1 < Real.cosh (2 * lam) :=
      Real.one_lt_cosh.mpr (by positivity)
    have hden1 : 0 < Real.cosh (2 * lam) - Real.cos α := by
      linarith 
    
    
    
    
    
    
    have hformula : fourierPPrime lam α =  1 / 2  *
        (Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
          Real.sin α / (1 - Real.cos α)) := by
      simp [fourierPPrime, hα0]
    rw [hformula]
    rw [abs_mul, abs_of_pos (by norm_num )]
    calc
       1 / 2  *
          |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
            Real.sin α / (1 - Real.cos α)| * |α| ≤
         1 / 2  *
          (|Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| +
            |Real.sin α / (1 - Real.cos α)|) * |α| :=
            by
              have hab :
                  |Real.sin α / (Real.cosh (2 * lam) - Real.cos α) -
                    Real.sin α / (1 - Real.cos α)| ≤
                    |Real.sin α / (Real.cosh (2 * lam) - Real.cos α)| +
                      |Real.sin α / (1 - Real.cos α)| := abs_sub _ _
              simp_all
      _ =  1 / 2  *
            (|Real.sin α| * |α| / (Real.cosh (2 * lam) - Real.cos α) +
              |Real.sin α| * |α| / (1 - Real.cos α)) := by
              rw [abs_div, abs_div, abs_of_pos hden1, abs_of_pos hdenLower]
              ring_nf
      _ ≤  1 / 2  *
            (π / (Real.cosh (2 * lam) - 1) + π ^ 2 / 2) :=
              mul_le_mul_of_nonneg_left (add_le_add (by
                                                       apply (div_le_div_iff₀ hden1 (by linarith)).2
                                                       have hnum : |Real.sin α| * |α| ≤ π := by
                                                         calc
                                                           |Real.sin α| * |α| ≤ 1 * |α| :=
                                                             mul_le_mul_of_nonneg_right (Real.abs_sin_le_one α) (abs_nonneg α)
                                                           _ ≤ 1 * π := mul_le_mul_of_nonneg_left (by
                                                                                                                             grind) (by norm_num)
                                                           _ = π := by ring
                                                       calc
                                                         |Real.sin α| * |α| * (Real.cosh (2 * lam) - 1) ≤
                                                             π * (Real.cosh (2 * lam) - 1) := by
                                                               simp_all
                                                         _ ≤ π * (Real.cosh (2 * lam) - Real.cos α) := mul_le_mul_of_nonneg_left (by
                                                                                                                                    linarith ) (by positivity)) (by
                                                              apply (div_le_iff₀ hdenLower).2
                                                              calc
                                                                |Real.sin α| * |α| ≤ α ^ 2 := by
                                                                  calc
                                                                    |Real.sin α| * |α| ≤ |α| * |α| :=
                                                                      mul_le_mul_of_nonneg_right  Real.abs_sin_le_abs  (abs_nonneg α)
                                                                    _ = α ^ 2 := by
                                                                      grind
                                                                _ ≤  π ^ 2 / 2  * (1 - Real.cos α) := by
                                                                  have hfactor : 0 < π ^ 2 / 2 := by positivity
                                                                  have hmul := mul_le_mul_of_nonneg_left hcosLower (le_of_lt hfactor)
                                                                  simp_all)) (by norm_num)
      _ = fourierPrimeControl lam := by
          dsimp [fourierPrimeControl]
          ring

noncomputable def tauFourierTerm (lam α : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / (π * ((n : ℝ) + 1)) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) * Real.sin (((n + 1 : ℕ) : ℝ) * α)

noncomputable def tauAbel (lam μ α : ℝ)  :=
  ∑' n : ℕ, tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)

noncomputable def tauAbelCorrectionTerm (lam μ α : ℝ) (n : ℕ)  :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) *
    Bethe.tauCoeff lam n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

private theorem summable_tauAbelCorrection {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) (α : ℝ) : Summable (tauAbelCorrectionTerm lam μ α) := by
  
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hrle : Real.exp (-μ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  apply Summable.of_norm_bounded (g := fun n => |Bethe.tauCoeff lam n| / (2 * π))
    ((Bethe.summable_tauCoeff hlam).abs.div_const (2 * π))
  intro n
  
  
  
  
  have hconst : 0 < (1 / (2 * π) : ℝ) := by positivity
  
  calc
    |(1 / (2 * π) ) * Real.exp (-μ) ^ (n + 1) *
        Bethe.tauCoeff lam n * Real.sin ( (n + 1 : ℕ)  * α)| = _ :=  by
                                                                           rw [abs_mul, abs_mul, abs_mul, abs_of_pos hconst] 
    _ ≤  1 / (2 * π)  * 1 * |Bethe.tauCoeff lam n| * 1 := by
          
          calc
             1 / (2 * π)  * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
                |Real.sin ( (n + 1 : ℕ)  * α)| ≤
               1 / (2 * π)  * 1 * |Bethe.tauCoeff lam n| *
                |Real.sin ( (n + 1 : ℕ)  * α)| := by
                  aesop
                     (add
                      unsafe
                        apply [_root_.Nat.cast_one, _root_.congrArg, _root_.mul_le_mul_of_nonneg_right, _root_.IsOrderedRing.toMulPosMono,
                          _root_.IsOrderedRing.toPosMulMono, _root_.IsOrderedAddMonoid.toAddLeftMono, _root_.pow_le_one₀, _root_.LT.lt.le,
                          _root_.PosMulReflectLE.toPosMulReflectLT, _root_.PosMulStrictMono.toPosMulReflectLE,
                          _root_.IsStrictOrderedRing.toPosMulStrictMono, _root_.IsOrderedAddMonoid.toAddRightMono])
            _ ≤  1 / (2 * π)  * 1 * |Bethe.tauCoeff lam n| * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
            _ = _ := by ring
    _ = |Bethe.tauCoeff lam n| / (2 * π) := by ring

private theorem tauAbel_eq_sawS_add_correction {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    tauAbel lam μ α = (1 / (2 * π) : ℝ) * Bethe.sawS μ α +
      ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by
  let r  := Real.exp (-μ)
  
  have hr1 : r < 1 := by
    aesop
  have hbase : Summable  fun n : ℕ =>
      2 * (-1 ) ^ (n + 1) * r ^ (n + 1) / ( n  + 1) *
        Real.sin ( (n + 1 : ℕ)  * α)  := by
    apply Summable.of_norm_bounded (g := fun n  => 2 * r ^ (n + 1))
    · have hgeom := (summable_geometric_of_lt_one (Real.exp_pos _).le hr1).mul_left (2 * r)
      grind
    · intro n
      rw [Real.norm_eq_abs]
      have hn : 0 < (n : ℝ) + 1 := by positivity
      have hrpow : 0 ≤ r ^ (n + 1) := by positivity
      have hsin : |Real.sin ( (n + 1 : ℕ)  * α)| ≤ 1 := Real.abs_sin_le_one _
      have habs :
          |2 * (-1 ) ^ (n + 1) * r ^ (n + 1) / ( n  + 1) *
            Real.sin ( (n + 1 : ℕ)  * α)| =
          2 * r ^ (n + 1) / ( n  + 1) *
            |Real.sin ( (n + 1 : ℕ)  * α)| := by
        rw [abs_mul, abs_div, abs_mul, abs_mul, abs_pow, abs_of_nonneg hrpow, abs_of_pos hn]
        ring
      rw [habs]
      calc
        2 * r ^ (n + 1) / ( n  + 1) * |Real.sin ( (n + 1 : ℕ)  * α)| ≤
          2 * r ^ (n + 1) / ( n  + 1) * 1 := by gcongr
        _ ≤ 2 * r ^ (n + 1) := by
          aesop
             (add
              unsafe
                apply [_root_.congrArg, _root_.Nat.cast_one, _root_.div_le_self, _root_.PosMulReflectLE.toPosMulReflectLT,
                  _root_.PosMulStrictMono.toPosMulReflectLE, _root_.IsStrictOrderedRing.toPosMulStrictMono, _root_.Eq.trans,
                  _root_.congr, _root_.IsOrderedAddMonoid.toAddLeftMono])
        _ = 2 * r ^ (n + 1) := rfl
  have hcorr := summable_tauAbelCorrection hlam hμ α
  have hbaseScaled := hbase.mul_left (1 / (2 * π) )
  
  
  
  have hsumTau : HasSum (fun n  => tauFourierTerm lam α n * r ^ (n + 1))
      (∑' n : ℕ,
        ( 1 / (2 * π)  *
          (2 * (-1 ) ^ (n + 1) * r ^ (n + 1) / ( n  + 1) *
            Real.sin ( (n + 1 : ℕ)  * α)) +
          tauAbelCorrectionTerm lam μ α n)) := by
                                                 exact HasSum.congr_fun (Summable.hasSum (hbaseScaled.add hcorr)) (by
                                                                                                          grind [tauFourierTerm, tauAbelCorrectionTerm, Bethe.tauCoeff])
  have hsumEq := hsumTau.tsum_eq
  have hbaseTsum : Bethe.sawS μ α = ∑' n : ℕ,
      2 * (-1 ) ^ (n + 1) * r ^ (n + 1) / ( n  + 1) *
        Real.sin ( (n + 1 : ℕ)  * α) := by
    simp [Bethe.sawS, r]
  calc
    tauAbel lam μ α = ∑' n : ℕ, tauFourierTerm lam α n * r ^ (n + 1) := by
      simp [tauAbel, r]
    _ =  1 / (2 * π)  *
           ∑' n : ℕ, 2 * (-1 ) ^ (n + 1) * r ^ (n + 1) / ( n  + 1) *
            Real.sin ( (n + 1 : ℕ)  * α)  +
          ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := Trans.trans (Trans.trans hsumEq (Summable.tsum_add hbaseScaled hcorr))
                                                         (Eq.mpr
                                                           (congrArg
                                                             (fun _a =>
                                                               _a + tsum (tauAbelCorrectionTerm lam μ α) =
                                                                 1 / (2 * π) * ∑' (n : ℕ), 2 * (-1) ^ (n + 1) * r ^ (n + 1) / (↑n + 1) * Real.sin (↑(n + 1) * α) +
                                                                   tsum (tauAbelCorrectionTerm lam μ α))
                                                             tsum_mul_left)
                                                           (Eq.refl
                                                             (1 / (2 * π) * ∑' (n : ℕ), 2 * (-1) ^ (n + 1) * r ^ (n + 1) / (↑n + 1) * Real.sin (↑(n + 1) * α) +
                                                               tsum (tauAbelCorrectionTerm lam μ α))))
    _ =  1 / (2 * π)  * Bethe.sawS μ α +
          ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n := by rw [hbaseTsum]

private theorem summable_tauCoeff_weighted {lam : ℝ} (hlam : 0 < lam) :
    Summable  fun n : ℕ => ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|  := by
  let r  := Real.exp (-lam)
  
  
  have hrnorm : ‖r‖ < 1 := by
    aesop
  
  
  have hshift := (summable_nat_add_iff 1
    (f := fun n  =>  n  * r ^ n)).mpr (summable_norm_iff.mp (by
                                                                        have h := summable_norm_pow_mul_geometric_of_norm_lt_one (k := 1) hrnorm
                                                                        simp_all))
  have hgeom : Summable  fun n : ℕ => ( n  + 1) * r ^ (n + 1)  := by
    simpa  using hshift
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => 2 * (( n  + 1) * r ^ (n + 1))) (hgeom.mul_left 2)
  intro n
  
  
  
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (by positivity)) (abs_nonneg _))]
  calc
    ( n  + 1) * |Bethe.tauCoeff lam n| ≤
        ( n  + 1) * (2 * r ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left (Bethe.abs_tauCoeff_le lam n) (le_of_lt (by positivity))
    _ = 2 * (( n  + 1) * r ^ (n + 1)) := by ring

noncomputable def tauCoeffWeightedSum (lam : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * |Bethe.tauCoeff lam n|

private theorem tauAbelCorrection_abs_bound {lam μ α : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) :
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
      (1 / (2 * π) : ℝ) * |α| * tauCoeffWeightedSum lam := by
  let c  := 1 / (2 * π)
  have hc : 0 < c := by  positivity
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hrle : Real.exp (-μ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  
  have hsin (n : ℕ) :
      |Real.sin ( (n + 1 : ℕ)  * α)| ≤ ( n  + 1) * |α| := by
    calc
      |Real.sin ( (n + 1 : ℕ)  * α)| ≤
          |( (n + 1 : ℕ)  * α)| := Real.abs_sin_le_abs
      _ = ( n  + 1) * |α| := by
          grind
  
  have hnormSum : Summable  fun n  => |tauAbelCorrectionTerm lam μ α n|  := by
    simpa  using (summable_tauAbelCorrection hlam hμ α).norm
  
  
  calc
    |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
        ∑' n : ℕ, |tauAbelCorrectionTerm lam μ α n| := by
          have hnormTsum :
              ‖∑' n : ℕ, tauAbelCorrectionTerm lam μ α n‖ ≤
                ∑' n : ℕ, ‖tauAbelCorrectionTerm lam μ α n‖ :=
            norm_tsum_le_tsum_norm hnormSum
          simp_all
    _ ≤ ∑' n : ℕ,
          c * |α| * (( n  + 1) * |Bethe.tauCoeff lam n|) :=
            hnormSum.tsum_le_tsum (fun (n : ℕ) => by
                                     rw [tauAbelCorrectionTerm, abs_mul, abs_mul, abs_mul, abs_of_pos hc]
                                     calc
                                       c * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| *
                                           |Real.sin (((n + 1 : ℕ) ) * α)| ≤
                                         c * 1 * |Bethe.tauCoeff lam n| * (((n ) + 1) * |α|) := by
                                             calc
                                               _ ≤ c * 1 * |Bethe.tauCoeff lam n| *
                                                     |Real.sin (((n + 1 : ℕ) ) * α)| := by
                                                       
                                                       aesop
                                                          (add
                                                           unsafe
                                                             apply [_root_.Nat.cast_one, _root_.congrArg, _root_.mul_le_mul_of_nonneg_right, _root_.IsOrderedRing.toMulPosMono,
                                                               _root_.IsOrderedRing.toPosMulMono, _root_.IsOrderedAddMonoid.toAddLeftMono,
                                                               _root_.IsStrictOrderedRing.toPosMulStrictMono, _root_.pow_le_one₀, _root_.LT.lt.le,
                                                               _root_.PosMulReflectLE.toPosMulReflectLT, _root_.PosMulStrictMono.toPosMulReflectLE,
                                                               _root_.IsOrderedAddMonoid.toAddRightMono])
                                               _ ≤ _ := by
                                                     
                                                     bound
                                       _ = c * |α| * (((n ) + 1) * |Bethe.tauCoeff lam n|) := by ring) ((summable_tauCoeff_weighted hlam).mul_left (c * |α|))
    _ = c * |α| * tauCoeffWeightedSum lam := tsum_mul_left
    _ =  1 / (2 * π)  * |α| * tauCoeffWeightedSum lam := rfl

private theorem sawS_abs_le_pi {μ α : ℝ} (hμ : 0 < μ) :
    |Bethe.sawS μ α| ≤ π := by
                              rw [Bethe.sawS_eq_arctan hμ α, abs_mul, abs_of_neg (by norm_num )]
                              have hlow := Real.neg_pi_div_two_lt_arctan
                                (Real.sin α / (Real.exp μ + Real.cos α))
                              have hupp := Real.arctan_lt_pi_div_two
                                (Real.sin α / (Real.exp μ + Real.cos α))
                              grind

private theorem sawS_abs_le_two_mul_abs {μ α : ℝ} (hμ : 0 < μ)
    (hα : |α| ≤ π / 2) :
    |Bethe.sawS μ α| ≤ 2 * |α| := by
  rw [Bethe.sawS_eq_arctan hμ α, abs_mul,
    abs_of_neg (by norm_num )]
  
  have hcos  :=
    Real.cos_nonneg_of_mem_Icc (abs_le.mp hα)
  have hden : 1 ≤ Real.exp μ + Real.cos α := by
    have hexp : 1 < Real.exp μ := by simpa using hμ
    linarith
  have hdenPos : 0 < Real.exp μ + Real.cos α := by linarith
  have hratio :
      |Real.sin α / (Real.exp μ + Real.cos α)| ≤ |α| := by
    rw [abs_div, abs_of_pos hdenPos]
    calc
      |Real.sin α| / (Real.exp μ + Real.cos α) ≤ |Real.sin α| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
      _ ≤ |α| := by
        simpa only [div_one] using  Real.abs_sin_le_abs (x := α) 
  
  
  nlinarith [((Real.abs_arctan_le_abs).trans hratio), abs_nonneg α]

noncomputable def tauAbelCorrectionCoeff (lam μ : ℝ) (n : ℕ)  :=
  (1 / (2 * π) : ℝ) * Real.exp (-μ) ^ (n + 1) * Bethe.tauCoeff lam n

private theorem summable_tauAbelCorrectionCoeff {lam μ : ℝ} (hlam : 0 < lam)
    (hμ : 0 < μ) : Summable (tauAbelCorrectionCoeff lam μ) := by
  let c  := 1 / (2 * π)
  have hc : 0 < c := by  positivity
  
  
  
  apply Summable.of_norm_bounded (g := fun n  => c * |Bethe.tauCoeff lam n|) ((Bethe.summable_tauCoeff hlam).abs.mul_left c)
  intro n
  rw [Real.norm_eq_abs, tauAbelCorrectionCoeff]
  
  rw [abs_mul, abs_mul, abs_of_pos hc]
  calc
    c * |Real.exp (-μ) ^ (n + 1)| * |Bethe.tauCoeff lam n| ≤
        c * 1 * |Bethe.tauCoeff lam n| := mul_le_mul_of_nonneg_right
                                      (mul_le_mul_of_nonneg_left (by
                                                                    rw [abs_of_nonneg (by positivity)]
                                                                    exact pow_le_one₀ (Real.exp_pos _).le (by
                                                                                               rw [Real.exp_le_one_iff]
                                                                                               linarith)) hc.le) (abs_nonneg _)
    _ = c * |Bethe.tauCoeff lam n| := by ring

private theorem tauAbelCorrection_eq_trigSeries {lam μ α : ℝ} :
     ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n  =
      Bethe.trigSeries 0 (fun _ => 0) (tauAbelCorrectionCoeff lam μ) α := by
                                                                            simp_all [tauAbelCorrectionTerm, tauAbelCorrectionCoeff, Bethe.trigSeries]

section

variable {lam μ : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
include hlam hμ

private theorem continuous_tauAbelCorrection  :
    Continuous  fun α => ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n  := Eq.mpr (congrArg Continuous (funext (@tauAbelCorrection_eq_trigSeries lam μ)))
                                                                         (Bethe.continuous_trigSeries summable_zero (summable_tauAbelCorrectionCoeff hlam hμ) 0)

private theorem continuous_tauAbel  :
    Continuous (tauAbel lam μ) := Eq.mpr (congrArg Continuous (funext fun α => tauAbel_eq_sawS_add_correction hlam hμ))
                                    (Continuous.add
                                      (Continuous.mul continuous_const
                                        (continuous_iff_continuousAt.mpr fun α => HasDerivAt.continuousAt (Bethe.hasDerivAt_sawS hμ α)))
                                      (continuous_tauAbelCorrection hlam hμ))

end

private theorem measurable_fourierPPrime (lam : ℝ) :
    Measurable (fourierPPrime lam) := Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

 noncomputable def tauLocalControl (lam : ℝ) : ℝ :=
  1 / π +  1 / (2 * π)  * tauCoeffWeightedSum lam

 noncomputable def tauGlobalControl (lam : ℝ) : ℝ :=
  1 / 2 +  1 / 2  * tauCoeffWeightedSum lam

private theorem tauCoeffWeightedSum_nonneg {lam : ℝ} :
    0 ≤ tauCoeffWeightedSum lam := by
  
  apply tsum_nonneg
  intro n
  positivity

private theorem tauLocalControl_nonneg {lam : ℝ} :
    0 ≤ tauLocalControl lam := by
  have hW := tauCoeffWeightedSum_nonneg (lam := lam)
  dsimp [tauLocalControl]
  positivity

private theorem tauGlobalControl_nonneg {lam : ℝ} :
    0 ≤ tauGlobalControl lam := by
  grind [tauGlobalControl, tauCoeffWeightedSum_nonneg]

section

variable {lam μ α : ℝ} (hlam : 0 < lam) (hμ : 0 < μ)
include hlam hμ

private theorem tauAbel_local_abs_bound  (hα : |α| ≤ π / 2) :
    |tauAbel lam μ α| ≤ tauLocalControl lam * |α| := by
  let c  := 1 / (2 * π)
  have hc : 0 < c := by  positivity
  
  have hsaw := sawS_abs_le_two_mul_abs (μ := μ) (α := α) hμ hα
  
  
  calc
    |tauAbel lam μ α| =
        |c * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := by
          rw [ tauAbel_eq_sawS_add_correction
                 (lam := lam) (μ := μ) (α := α) hlam hμ ]
    _ ≤ |c * Bethe.sawS μ α| +
        |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := abs_add_le _ _
    _ ≤ c * (2 * |α|) + c * |α| * tauCoeffWeightedSum lam :=
        add_le_add (by
                      aesop) (by simpa [c] using  tauAbelCorrection_abs_bound (lam := lam) (μ := μ) (α := α) hlam hμ )
    _ = tauLocalControl lam * |α| := by
        grind +locals

private theorem tauAbel_global_abs_bound  (hα : α ∈ Icc (-π) π) :
    |tauAbel lam μ α| ≤ tauGlobalControl lam := by
  let c  := 1 / (2 * π)
  have hc : 0 < c := by  positivity
  
  
  
  have hsaw := sawS_abs_le_pi (μ := μ) (α := α) hμ
  
  
  calc
    |tauAbel lam μ α| =
        |c * Bethe.sawS μ α + ∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := by
          rw [ tauAbel_eq_sawS_add_correction
                 (lam := lam) (μ := μ) (α := α) hlam hμ ]
    _ ≤ |c * Bethe.sawS μ α| +
        |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| := abs_add_le _ _
    _ ≤ c * π + c * π * tauCoeffWeightedSum lam := by
        apply add_le_add
        · aesop
        · exact  by
                   calc
                     |∑' n : ℕ, tauAbelCorrectionTerm lam μ α n| ≤
                         c * |α| * tauCoeffWeightedSum lam := by simpa [c] using  tauAbelCorrection_abs_bound (lam := lam) (μ := μ) (α := α) hlam hμ 
                     _ ≤ c * π * tauCoeffWeightedSum lam := by
                         exact mul_le_mul_of_nonneg_right
                           (mul_le_mul_of_nonneg_left (by
                                                                                 grind) hc.le) (tauCoeffWeightedSum_nonneg (lam := lam)) 
    _ = tauGlobalControl lam := by
        grind +locals

end

noncomputable def fourierTauProductControl (lam : ℝ) : ℝ :=
  max (fourierPrimeControl lam * tauLocalControl lam)
    ( 2 * fourierPrimeControl lam / π  * tauGlobalControl lam)

theorem fourierTauProductControl_nonneg {lam : ℝ} (hlam : 0 < lam) :
    0 ≤ fourierTauProductControl lam := by
  have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
  have hprime : 0 < fourierPrimeControl lam := by
    dsimp [fourierPrimeControl]
    positivity
  have hlocal := tauLocalControl_nonneg (lam := lam)
  
  dsimp [fourierTauProductControl]
  positivity

private theorem fourierPPrime_mul_tauAbel_abs_bound {lam μ α : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * tauAbel lam μ α| ≤ fourierTauProductControl lam := by
  have hprime := fourierPPrime_alpha_bound hlam hα
  
  
  
  rw [abs_mul]
  by_cases hnear : |α| ≤ π / 2
  · 
    calc
      |fourierPPrime lam α| * |tauAbel lam μ α| ≤
          |fourierPPrime lam α| * (tauLocalControl lam * |α|) :=
            mul_le_mul_of_nonneg_left (tauAbel_local_abs_bound hlam hμ hnear) (abs_nonneg _)
      _ = tauLocalControl lam *
          (|fourierPPrime lam α| * |α|) := by ring
      _ ≤ tauLocalControl lam * fourierPrimeControl lam :=
            mul_le_mul_of_nonneg_left hprime (tauLocalControl_nonneg (lam := lam))
      _ = fourierPrimeControl lam * tauLocalControl lam := mul_comm _ _
      _ ≤ fourierTauProductControl lam := le_max_left _ _
  · 
    
    
    
    
    calc
      |fourierPPrime lam α| * |tauAbel lam μ α| ≤
          |fourierPPrime lam α| * tauGlobalControl lam :=
            mul_le_mul_of_nonneg_left (tauAbel_global_abs_bound hlam hμ hα) (abs_nonneg _)
      _ ≤  2 * fourierPrimeControl lam / π  * tauGlobalControl lam :=
            mul_le_mul_of_nonneg_right (by
                                          calc
                                            |fourierPPrime lam α| ≤ fourierPrimeControl lam / |α| :=  (le_div_iff₀ (by
                                                                                                                                              grind)).2 (by simpa  using hprime) 
                                            _ ≤ fourierPrimeControl lam / (π / 2) :=
                                                div_le_div_of_nonneg_left (by
                                                                             have hcosh : 1 < Real.cosh (2 * lam) := Real.one_lt_cosh.mpr (by positivity)
                                                                             dsimp [fourierPrimeControl]
                                                                             positivity) (by positivity) (le_of_not_ge hnear)
                                            _ = 2 * fourierPrimeControl lam / π := by
                                                field_simp ) (tauGlobalControl_nonneg (lam := lam))
      _ ≤ fourierTauProductControl lam := le_max_right _ _

/-- Abel regularization along the same exponential mesh for any convergent ordered series. -/
private theorem tendsto_abel_mesh {a : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 L)) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, a n *
      Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)) atTop (𝓝 L) := by
  let r : ℕ → ℝ := fun N => Real.exp (-(1 / ( N  + 1)))
  
  
  have hr0 : Tendsto r atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp (by
                                                                                                   simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg)
  
  
  have heq (N : ℕ) :  ∑' n : ℕ, a n * r N ^ (n + 1)  =
      r N * ∑' n : ℕ, a n * r N ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    
    ring
  simpa only [Function.comp_def, ← heq, one_mul] using  hr0.mul ((Real.tendsto_tsum_powerSeries_nhdsWithin_lt h).comp (tendsto_nhdsWithin_iff.mpr ⟨hr0, Filter.Eventually.of_forall fun N => by
                                                                                                                                      change Real.exp (-(1 / ((N : ℝ) + 1))) < 1
                                                                                                                                      rw [Real.exp_lt_one_iff]
                                                                                                                                      exact neg_neg_of_pos (by positivity)⟩)) 

noncomputable def tauAbelSeq (lam α : ℝ) (N : ℕ) : ℝ :=
  tauAbel lam (1 / ((N : ℝ) + 1)) α

private theorem tauAbelSeq_tendsto_tauSeries {lam α : ℝ} (hlam : 0 < lam)
    (hα : |α| < π) : Tendsto (tauAbelSeq lam α) atTop (𝓝 (Bethe.tauSeries lam α)) := by
  apply tendsto_abel_mesh (a := tauFourierTerm lam α)
  have heq : (fun N => ∑ n ∈ Finset.range N, tauFourierTerm lam α n) =
      Bethe.tauPartial lam α := by
    funext N
    simp [tauFourierTerm, Bethe.tauPartial]
  rw [Bethe.tauSeries_eq hlam hα]
  exact Bethe.tendsto_tauPartial hlam hα

/-- A uniform bound for the product of the punctured derivative and the literal `τ` series.
The estimate is first proved for Abel means and then passed to their pointwise limit; the two
endpoints use the literal series value zero. -/
theorem fourierPPrime_tauSeries_abs_bound {lam α : ℝ} (hlam : 0 < lam)
    (hα : α ∈ Icc (-π) π) :
    |fourierPPrime lam α * Bethe.tauSeries lam α| ≤ fourierTauProductControl lam := by
  by_cases hαp : α = π
  · subst α
    calc
      |fourierPPrime lam π * Bethe.tauSeries lam π| = 0 := by
        simp [Bethe.tauSeries_pi]
      _ ≤ fourierTauProductControl lam := fourierTauProductControl_nonneg hlam
  by_cases hαm : α = -π
  · subst α
    calc
      |fourierPPrime lam (-π) * Bethe.tauSeries lam (-π)| = 0 := by
        simp [Bethe.tauSeries_neg_pi]
      _ ≤ fourierTauProductControl lam := fourierTauProductControl_nonneg hlam
  
  
  
  
  apply le_of_tendsto_of_tendsto' (by
                                                                                              exact Tendsto.norm (Tendsto.mul tendsto_const_nhds (tauAbelSeq_tendsto_tauSeries hlam (abs_lt.mpr
                                                                                                                                                                                                    ⟨lt_of_le_of_ne hα.1 (Ne.symm hαm), lt_of_le_of_ne hα.2 hαp⟩)))) tendsto_const_nhds
  intro N
  
  simpa [tauAbelSeq] using
     fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) hα 

private theorem tauFourierTerm_abs_bound (lam α : ℝ) (n : ℕ) :
    |tauFourierTerm lam α n| ≤ |α| / π := by
  
  have hsign : |(-1 : ℝ) ^ (n + 1)| = 1 := by simp
  have hden : |π * ( n  + 1)| = π * ( n  + 1) :=
    abs_of_pos (mul_pos Real.pi_pos (by positivity))
  have hcoeff :
      |(-1 ) ^ (n + 1) / (π * ( n  + 1))| =
        1 / (π * ( n  + 1)) := by rw [abs_div, hsign, hden]
  have htanh :
      |Real.tanh (lam *  (n + 1 : ℕ) )| ≤ 1 :=
    (Real.abs_tanh_lt_one _).le
  have hsin :
      |Real.sin ( (n + 1 : ℕ)  * α)| ≤ ( n  + 1) * |α| := by
    calc
      |Real.sin ( (n + 1 : ℕ)  * α)| ≤
          |((n + 1 : ℕ) ) * α| := Real.abs_sin_le_abs
      _ = ( n  + 1) * |α| := by
          simp_all
  rw [tauFourierTerm, abs_mul, abs_mul, hcoeff]
  calc
     1 / (π * ( n  + 1))  *
        |Real.tanh (lam *  (n + 1 : ℕ) )| *
        |Real.sin ( (n + 1 : ℕ)  * α)| ≤
       1 / (π * ( n  + 1))  * 1 *
        (( n  + 1) * |α|) := by
          gcongr
    _ = |α| / π := by
      field_simp 

private theorem summable_tauAbelTerms {lam μ α : ℝ}
    (hμ : 0 < μ) :
    Summable  fun n : ℕ => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1)  := by
  have hr : 0 < Real.exp (-μ) := Real.exp_pos _
  have hr1 : Real.exp (-μ) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeo : Summable  fun n  => Real.exp (-μ) ^ (n + 1)  := by
    have h := (summable_geometric_of_lt_one hr.le hr1).mul_left (Real.exp (-μ))
    all_goals grind
  apply Summable.of_norm_bounded
    (g := fun n  =>  |α| / π  * Real.exp (-μ) ^ (n + 1))
    (hgeo.mul_left (|α| / π))
  intro n
  have hpow : 0 ≤ Real.exp (-μ) ^ (n + 1) := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpow]
  exact mul_le_mul_of_nonneg_right (tauFourierTerm_abs_bound lam α n) hpow

private theorem hasSum_tauAbelTerms {lam μ α : ℝ}
    (hμ : 0 < μ) :
    HasSum (fun n : ℕ => tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1))
      (tauAbel lam μ α) := Summable.hasSum (summable_tauAbelTerms hμ)

noncomputable def tauCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    Real.tanh (lam * ((n + 1 : ℕ) : ℝ)) *
      (Real.exp (-2 * lam * ((n + 1 : ℕ) : ℝ)) - 1)

private theorem tauAbel_integral_term {lam μ : ℝ} (hlam : 0 < lam)
    (n : ℕ) :
    ∫ α in (-π)..π,
        fourierPPrime lam α * tauFourierTerm lam α n * Real.exp (-μ) ^ (n + 1) =
      tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
                                                             
                                                             
                                                             have hsine := fourierP_prime_sine_integral hlam (n + 1) (Nat.succ_pos n)
                                                             have hsine' :
                                                                 ∫ α in (-π)..π, fourierPPrime lam α *
                                                                     Real.sin ( (n + 1 : ℕ)  * α) =
                                                                   π * (Real.exp (-2 * lam *  (n + 1 : ℕ) ) - 1) := by
                                                               calc
                                                                 _ = π * ( 1 / π  *
                                                                     ∫ α in (-π)..π, fourierPPrime lam α *
                                                                       Real.sin ( (n + 1 : ℕ)  * α)) := by field_simp 
                                                                 _ = _ := by rw [hsine]
                                                             have hfun :
                                                                 (fun α  => fourierPPrime lam α * tauFourierTerm lam α n *
                                                                     Real.exp (-μ) ^ (n + 1)) =
                                                                   fun α =>
                                                                      Real.exp (-μ) ^ (n + 1) *
                                                                       ((-1 ) ^ (n + 1) / (π * ( n  + 1)) *
                                                                         Real.tanh (lam *  (n + 1 ) ))  *
                                                                       (fourierPPrime lam α * Real.sin ( (n + 1 : ℕ)  * α)) := by
                                                               funext α
                                                               simp [tauFourierTerm]
                                                               ring
                                                             rw [hfun, intervalIntegral.integral_const_mul]
                                                             dsimp [tauCorrectionTerm]
                                                             grind

private theorem fourierPPrime_tauAbel_integral {lam μ : ℝ}
    (hlam : 0 < lam) (hμ : 0 < μ) :
    ∫ α in (-π)..π, fourierPPrime lam α * tauAbel lam μ α =
      ∑' n : ℕ, tauCorrectionTerm lam n * Real.exp (-μ) ^ (n + 1) := by
  let r  := Real.exp (-μ)
  let B  := fun n =>  fourierPrimeControl lam / π  * r ^ (n + 1)
  let F  := fun n α =>
    fourierPPrime lam α * tauFourierTerm lam α n * r ^ (n + 1)
  have hr : 0 < r := by  positivity
  
  
  
  have hB : Summable B := by
                            exact Summable.mul_left (fourierPrimeControl lam / π) (by
                                                                                     have h := (summable_geometric_of_lt_one hr.le (by
                                                                                                                                      aesop)).mul_left r
                                                                                     grind)
  
  
  
  
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * tauAbel lam μ α)
    (fun n α => B n) (by
                        intro n
                        
                        have hF : Measurable (F n) := by
                                                        exact Measurable.mul (Measurable.mul (measurable_fourierPPrime lam) (by
                                                                                                                               unfold tauFourierTerm
                                                                                                                               fun_prop)) measurable_const
                        exact hF.aestronglyMeasurable) (by
                              intro n
                              filter_upwards with α
                              intro hα
                              
                              
                              have hP := fourierPPrime_alpha_bound hlam (Ioc_subset_Icc_self (by
                                                                                                                              simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα))
                              
                              
                              have hpow : 0 ≤ r ^ (n + 1) := by positivity
                              
                              rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hpow]
                              exact mul_le_mul_of_nonneg_right (by
                                                                  calc
                                                                    |fourierPPrime lam α| * |tauFourierTerm lam α n| ≤
                                                                        |fourierPPrime lam α| * (|α| / π) :=
                                                                          mul_le_mul_of_nonneg_left (tauFourierTerm_abs_bound lam α n) (abs_nonneg _)
                                                                    _ =  |fourierPPrime lam α| * |α|  / π := by ring
                                                                    _ ≤ fourierPrimeControl lam / π :=
                                                                          div_le_div_of_nonneg_right hP (le_of_lt Real.pi_pos)) hpow)
    (Filter.Eventually.of_forall fun α _ => hB) (by
                                                   simp_all) (by
                                                             refine Filter.Eventually.of_forall fun α _ => ?_
                                                             have hs := (hasSum_tauAbelTerms (lam := lam) (μ := μ) (α := α) hμ).mul_left
                                                               (fourierPPrime lam α)
                                                             grind)
  have hsum' := hsum.tsum_eq
  
  rw [← hsum']
  exact tsum_congr (tauAbel_integral_term hlam)

noncomputable def tauCorrectionPartial (lam : ℝ) (N : ℕ)  :=
  ∑ n ∈ Finset.range N, tauCorrectionTerm lam n

private theorem tauCorrectionPartial_eq (lam : ℝ) (N : ℕ) :
    tauCorrectionPartial lam N =
      logCoshTauCorrectionPartial lam N := by
  have hfin : Finset.Icc 1 N = (Finset.range N).image Nat.succ := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hm1, hmN⟩
      refine ⟨m - 1, ?_, ?_⟩ <;> omega
    · 
      omega
  unfold tauCorrectionPartial logCoshTauCorrectionPartial
  rw [hfin, Finset.sum_image]
  · grind +locals
  · intro i hi j hj hij
    exact Nat.succ.inj hij

noncomputable def tauCorrectionAbelSeq (lam : ℝ) (N : ℕ)  :=
  ∑' n : ℕ, tauCorrectionTerm lam n *
    Real.exp (-(1 / ((N : ℝ) + 1))) ^ (n + 1)

private theorem tauCorrectionAbelSeq_tendsto {lam L : ℝ}
    (hpartial : Tendsto (tauCorrectionPartial lam) atTop (𝓝 L)) :
    Tendsto (tauCorrectionAbelSeq lam) atTop (𝓝 L) := tendsto_abel_mesh hpartial

private theorem tauCorrectionAbelSeq_tendsto_value {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ, Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (tauCorrectionPartial lam) atTop
        (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) ∧
      Tendsto (tauCorrectionAbelSeq lam) atTop
        (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) := by
  obtain ⟨S, hS, hidentity⟩ := identity43 lam hlam
  have hCorr : Tendsto (logCoshTauCorrectionPartial lam) atTop
      (𝓝 (Real.log (Real.cosh lam) - (lam + 2 * S))) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log (Real.cosh lam)) atTop
        (𝓝 (Real.log (Real.cosh lam))) := tendsto_const_nhds
    have hsub := hconst.sub hidentity
    simp_all
  
  exact ⟨S, hS,  hCorr.congr' (Filter.Eventually.of_forall fun N =>
             (tauCorrectionPartial_eq lam N).symm) , tauCorrectionAbelSeq_tendsto (hCorr.congr' (Filter.Eventually.of_forall fun N =>
                                                                                       (tauCorrectionPartial_eq lam N).symm))⟩

/-- The `α`-coordinate value of the explicit series integral in §4.  The correction series is
interpreted by its ordered partial sums; Abel damping identifies the integral with that limit. -/
theorem fourierPPrime_tauSeries_integral {lam : ℝ} (hlam : 0 < lam) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial lam) atTop (𝓝 S) ∧
      Tendsto (logCoshTauCorrectionPartial lam) atTop
        (𝓝 (∫ α in (-π)..π, fourierPPrime lam α * Bethe.tauSeries lam α)) := by
  obtain ⟨S, hS, hPartialCorr, hAbelCorr⟩ := tauCorrectionAbelSeq_tendsto_value hlam
  let F  := fun N α => fourierPPrime lam α * tauAbelSeq lam α N
  
  
  
  
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := -π) (b := π) (F := F)
    (f := fun α => fourierPPrime lam α * Bethe.tauSeries lam α)
    (fun _  => fourierTauProductControl lam)
    (Filter.Eventually.of_forall  fun N =>
                                    Measurable.aestronglyMeasurable
                                      (Measurable.mul (measurable_fourierPPrime lam)
                                        (Continuous.measurable
                                          (continuous_tauAbel hlam
                                            (div_pos
                                              (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                                (Eq.refl (Nat.ble 1 1)))
                                              (Right.add_pos_of_nonneg_of_pos (Nat.cast_nonneg' N)
                                                (Mathlib.Meta.Positivity.pos_of_isNat (Mathlib.Meta.NormNum.isNat_ofNat ℝ Nat.cast_one)
                                                  (Eq.refl (Nat.ble 1 1)))))))) ) (Filter.Eventually.of_forall (by
                                                                        intro N
                                                                        filter_upwards with α
                                                                        intro hα
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        
                                                                        exact fourierPPrime_mul_tauAbel_abs_bound hlam (by positivity) (Ioc_subset_Icc_self (by
                                                                                                                                                                                              simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα))))
     intervalIntegrable_const  (by
                 filter_upwards [Measure.ae_ne volume π] with α hαπ
                 intro hα
                 have hαIoc : α ∈ Ioc (-π) π := by
                   simpa [uIoc_of_le (neg_le_self Real.pi_nonneg)] using hα
                 have hright  := lt_of_le_of_ne hαIoc.2 hαπ
                 have hαabs : |α| < π := by
                                           grind
                 have htau := tauAbelSeq_tendsto_tauSeries hlam hαabs
                 simpa  using  tendsto_const_nhds.mul htau )
  
  have hseqEq : (fun N  => ∫ α in (-π)..π, F N α) = tauCorrectionAbelSeq lam := by
                                                                                     exact funext  fun N => by
                                                                                                     change ∫ α in (-π)..π,
                                                                                                       fourierPPrime lam α * tauAbel lam (1 / ( N  + 1)) α = _
                                                                                                     rw [fourierPPrime_tauAbel_integral hlam (by positivity)]
                                                                                                     dsimp [tauCorrectionAbelSeq] 
  
  have hvalue := tendsto_nhds_unique (by
                                        rw [hseqEq] at hDCT
                                        exact hDCT) hAbelCorr
  
  exact ⟨S, hS,  by
                   have hCorr' := hPartialCorr.congr'
                     (Filter.Eventually.of_forall (tauCorrectionPartial_eq lam))
                   simp_all ⟩

end PottsDiscontinuity
