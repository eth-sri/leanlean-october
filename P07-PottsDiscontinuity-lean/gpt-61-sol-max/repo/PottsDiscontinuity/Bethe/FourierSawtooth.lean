module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierSaw

/-!
# The sawtooth series `∑ (-1)^m sin(mα)/m = -α/2` for `|α| < π`

The series is only conditionally convergent.  Its convergence follows from Dirichlet's test
(Mathlib: `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`), and its sum from Abel's
theorem (`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`) combined with the closed form
`sawS μ α = -2 arctan (sin α / (e^μ + cos α))` of the Poisson means (`sawS_eq_arctan`).
This is what gives the series of (2.1) for `τ` a meaning as the limit of its partial sums.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Closed form of the sawtooth Poisson series:
`∑_{m≥1} 2(-1)^m e^{-μ m} sin(mα)/m = -2 arctan (sin α / (e^μ + cos α))`. -/
theorem sawS_eq_arctan {μ : ℝ} (hμ : 0 < μ) (α : ℝ) :
    sawS μ α = -2 * Real.arctan (Real.sin α / (Real.exp μ + Real.cos α)) := by
  have hE : 1 < Real.exp μ := by simpa using hμ
  have hd : ∀ x , HasDerivAt (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) 0 x := by
    intro x
    
    have h1 : HasDerivAt (fun y => Real.sin y / (Real.exp μ + Real.cos y))
        ((Real.cos x * (Real.exp μ + Real.cos x) - Real.sin x * (0 + -Real.sin x)) /
          (Real.exp μ + Real.cos x) ^ 2) x :=
      (Real.hasDerivAt_sin x).div ((hasDerivAt_const x (Real.exp μ)).add (Real.hasDerivAt_cos x)) (by
                                                                                                     have := Real.neg_one_le_cos x; linarith)
     
    
    have e : (fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y))) =
        sawS μ + fun y => 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y)) := rfl
    rw [e]
    refine ((hasDerivAt_sawS hμ x).add (h1.arctan.const_mul 2)).congr_deriv ?_
    have hs := Real.sin_sq_add_cos_sq x
    have hc1 := Real.neg_one_le_cos x
    have hsinh : Real.sinh μ = (Real.exp μ - (Real.exp μ)⁻¹) / 2 := by
      rw [Real.sinh_eq, Real.exp_neg]
    have hcosh : Real.cosh μ = (Real.exp μ + (Real.exp μ)⁻¹) / 2 := by
      rw [Real.cosh_eq, Real.exp_neg]
    unfold Xi
    rw [Real.cos_add_pi, hsinh, hcosh]
    set E := Real.exp μ with hEdef
    set c := Real.cos x with hc
    set s := Real.sin x with hsdef
    have hE0 : E ≠ 0 := by positivity
    
    have hEc : E + c ≠ 0 := by linarith
    have hA : (E - E⁻¹) / 2 / ((E + E⁻¹) / 2 - -c) - 1 = -2 * (E * c + 1) / (E ^ 2 + 2 * E * c + 1) := by
      
      have h4' : (E + E⁻¹) / 2 - -c ≠ 0 := by
        rw [(by
               field_simp; ring : (E + E⁻¹) / 2 - -c = (E ^ 2 + 2 * E * c + 1) / (2 * E))]; exact div_ne_zero (by nlinarith) (by positivity)
      rw [div_sub_one h4', div_eq_div_iff h4' (by nlinarith)]
      field_simp
      ring
    have hB : 1 / (1 + (s / (E + c)) ^ 2) * ((c * (E + c) - s * (0 + -s)) / (E + c) ^ 2) =
        (E * c + 1) / (E ^ 2 + 2 * E * c + 1) := by
      have h5 : 1 + (s / (E + c)) ^ 2 = ((E + c) ^ 2 + s ^ 2) / (E + c) ^ 2 := by
        field_simp
      have h6 : (E + c) ^ 2 + s ^ 2 = E ^ 2 + 2 * E * c + 1 := by nlinarith [hs]
      have h7 : c * (E + c) - s * (0 + -s) = E * c + 1 := by nlinarith [hs]
      rw [h5, h6, h7]
      field_simp
    rw [hA, hB]
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero
    (f := fun y => sawS μ y + 2 * Real.arctan (Real.sin y / (Real.exp μ + Real.cos y)))
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) α 0
  simp only [sawS_zero, Real.sin_zero, zero_div, Real.arctan_zero, mul_zero, add_zero] at hc
  linarith


/-! ### Convergence of the sawtooth series (Dirichlet test) -/

/-- Telescoping identity for `∑ sin(kθ)`. -/
theorem two_sin_half_mul_sum_sin (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ) =
      Real.cos (θ / 2) - Real.cos (((n : ℝ) + 1 / 2) * θ) := by
  induction n with
  | zero =>  ring_nf
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 : Real.cos (( n  + 1 / 2) * θ) - Real.cos (( (n + 1 : ℕ)  + 1 / 2) * θ) =
        2 * Real.sin (θ / 2) * Real.sin ( (n + 1 : ℕ)  * θ) := by
      have e1 : ( n  + 1 / 2) * θ =  (n + 1 : ℕ)  * θ - θ / 2 := by push_cast; ring
      have e2 : ( (n + 1 : ℕ)  + 1 / 2) * θ =  (n + 1 : ℕ)  * θ + θ / 2 := by  ring
      rw [e1, e2, Real.cos_sub, Real.cos_add]; ring
    linarith

theorem abs_sum_sin_le {θ : ℝ} (h : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    |∑ i ∈ Finset.range n, Real.sin (((i + 1 : ℕ) : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h1 := two_sin_half_mul_sum_sin θ n
  have h2 : |2 * Real.sin (θ / 2) * ∑ i ∈ Finset.range n, Real.sin ( (i + 1 : ℕ)  * θ)| ≤ 2 := by
    rw [h1]
    have := Real.abs_cos_le_one (θ / 2)
    have := Real.abs_cos_le_one (((n : ℝ) + 1 / 2) * θ)
    grind
  rw [abs_mul, abs_mul] at h2
  
  rw [le_div_iff₀ (abs_pos.2 h)]
  linarith

section

variable {α : ℝ} (hα : |α| < π)
include hα

theorem cauchySeq_sawtooth  :
    CauchySeq  fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)  := by
  
  have hα' := abs_lt.1 hα
  have hs : 0 < Real.sin ((α + π) / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hz : ∀ i , (-1 ) ^ (i + 1) * Real.sin ( (i + 1 : ℕ)  * α) =
      Real.sin ( (i + 1 : ℕ)  * (α + π)) := by
    intro i
    rw [mul_add, Real.sin_add, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
    ring
  
  
  have e : (fun N  => ∑ i ∈ Finset.range N,
      (-1 ) ^ (i + 1) * Real.sin ( (i + 1 : ℕ)  * α) / ( i  + 1)) =
      fun n  => ∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1)) •
        Real.sin ( (i + 1 : ℕ)  * (α + π)) := by
    funext N
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hz i]
    ring
  rw [e]
  exact  Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (E := ℝ)
             (f := fun i  => 1 / ( i  + 1)) (z := fun i  => Real.sin ( (i + 1 : ℕ)  * (α + π)))
             (b := 1 / |Real.sin ((α + π) / 2)|)
             (fun i j hij => Nat.one_div_le_one_div hij)
             (by
                simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
              fun n => abs_sum_sin_le hs.ne' n  


theorem arctan_sin_div_one_add_cos  :
    Real.arctan (Real.sin α / (1 + Real.cos α)) = α / 2 := by
  
  have hα' := abs_lt.1 hα
  
  have h2 : α = 2 * (α / 2) := by ring
  have e1 : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
    conv_lhs => rw [h2]
    exact Real.sin_two_mul _
  have e2 : 1 + Real.cos α = 2 * Real.cos (α / 2) ^ 2 := by
    conv_lhs => rw [h2]
    rw [Real.cos_two_mul]; ring
  have e3 : Real.sin α / (1 + Real.cos α) = Real.tan (α / 2) := by
    rw [e1, e2, Real.tan_eq_sin_div_cos]
    field_simp
  rw [e3]
  exact Real.arctan_tan (by linarith) (by linarith)

/-- The classical sawtooth series: `∑_{m≥1} (-1)^m sin(mα)/m = -α/2` for `|α| < π` (as the limit
of the partial sums; the series is only conditionally convergent). -/
theorem tendsto_sawtooth  :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      (-1 : ℝ) ^ (i + 1) * Real.sin (((i + 1 : ℕ) : ℝ) * α) / ((i : ℝ) + 1)) atTop (𝓝 (-α / 2)) := by
  
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sawtooth hα)
  
  -- closed form of the Abel means
  let G  := fun x => -x⁻¹ * Real.arctan (Real.sin α / (x⁻¹ + Real.cos α))
  have hev : (fun x  => ∑' n : ℕ, (-1 ) ^ (n + 1) * Real.sin ( (n + 1 : ℕ)  * α) /
      ( n  + 1) * x ^ n) =ᶠ[𝓝[<] 1] G := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 ) < 1 by norm_num)] with x hx
    
    
    have h1 := sawS_eq_arctan (by
                                 have := Real.log_neg  hx.1  hx.2
                                 linarith : 0 < -Real.log x) α
    have hexp : Real.exp (-Real.log x) = x⁻¹ := by rw [Real.exp_neg, Real.exp_log  hx.1 ]
    
    
    unfold sawS at h1
    rw [(by rw [neg_neg, Real.exp_log  hx.1 ] : Real.exp (- -Real.log x ) = x)] at h1
    have h2 : ∀ n , 2 * (-1 ) ^ (n + 1) * x ^ (n + 1) / ( n  + 1) *
        Real.sin ( (n + 1 : ℕ)  * α) =
         2 * x  * ((-1 ) ^ (n + 1) * Real.sin ( (n + 1 : ℕ)  * α) / ( n  + 1) * x ^ n) := by
      grind
    simp_rw [h2] at h1
    rw [tsum_mul_left] at h1
    grind
  have hc1 : 0 < 1 + Real.cos α := by
    have h := abs_lt.1 hα
    have : Real.cos α ≠ -1 := by
      intro hh
      have h2 : Real.cos α = Real.cos π := by rw [hh, Real.cos_pi]
      rcases lt_or_ge α 0 with hneg | hpos
      · have := Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith ) (by linarith )
          (by linarith : -α < π)
        rw [Real.cos_neg] at this
        linarith
      · have := Real.cos_lt_cos_of_nonneg_of_le_pi hpos (le_refl π) (by linarith )
        linarith
    have := Real.neg_one_le_cos α
    grind
  
  have hlim : Tendsto G (𝓝[<] 1) (𝓝 (G 1)) := (by
                                                 fun_prop (disch := aesop) : ContinuousAt G 1).tendsto.mono_left nhdsWithin_le_nhds
  have hG1 : G 1 = -α / 2 := by
    grind [arctan_sin_div_one_add_cos]
  have hlim2 := (Real.tendsto_tsum_powerSeries_nhdsWithin_lt
                   (f := fun n  => (-1 ) ^ (n + 1) * Real.sin ( (n + 1 : ℕ)  * α) / ( n  + 1)) hℓ).congr' hev
  rw [hG1] at hlim
  
  rw [←  tendsto_nhds_unique hlim2 hlim ]
  exact hℓ

end

end PottsDiscontinuity.Bethe
