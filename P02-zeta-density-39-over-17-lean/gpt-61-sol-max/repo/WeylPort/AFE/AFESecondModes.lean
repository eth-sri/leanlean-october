module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.UpperModeTails
public import WeylPort.AFE.AFESecondWeights

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual AFE amplitudes in the second oscillatory integral estimate

All differentiability, continuity and positive-frequency quotient conditions
are derived for the actual power weight and logarithmic phase.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory

section
variable {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (h : ℝ → ℝ)
    (hh : h = deriv (afeWeight σ) ∨ h = fun u => afeWeight σ u * deriv (afePhase c) u)
include σ c a b hσ hc ha hab h hh

/-- Both actual AFE amplitudes satisfy the complete positive-frequency series estimate, with no quotient hypothesis remaining. -/
theorem afe_positive_second_tail_bound  :
    Summable (secondModeTerm (afePhase c) h a b) ∧
    ‖∑' n : ℕ, secondModeTerm (afePhase c) h a b n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (c / b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (c / a)‖ +
      (|deriv h a| / (4 * Real.pi ^ 3)) *
        ((Real.log (c / a + 1) + Real.eulerMascheroniConstant) / (c / a) ^ 2 -
          (1 + 2 * (c / a)) / (2 * (c / a) ^ 2 * (c / a + 1))) +
      (|h a * (-c / a ^ 2)| / (4 * Real.pi ^ 3)) *
        ((Real.log (c / a + 1) + Real.eulerMascheroniConstant) / (c / a) ^ 3 -
          (1 + 3 * (c / a) + 3 * (c / a) ^ 2) / (2 * (c / a) ^ 3 * (c / a + 1) ^ 2)) := by
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun u hu => hpos u hu
  have hr := afe_second_amplitude_regular σ c h hh
  have hf (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (afePhase c) (deriv (afePhase c) u) u :=
    (afePhase_hasDerivAt c (hpos u hu)).differentiableAt.hasDerivAt
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (deriv (afePhase c)) (deriv (deriv (afePhase c)) u) u :=
    (afePhase_deriv_hasDerivAt c (hpos u hu)).differentiableAt.hasDerivAt
  have hpc : ContinuousOn (deriv (afePhase c)) (Set.Icc a b) :=
    fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hppc : ContinuousOn (deriv (deriv (afePhase c))) (Set.Icc a b) := by
    have hd : ContinuousOn (fun u : ℝ => -c / u ^ 2) (Set.Icc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) (fun u hu => pow_ne_zero _ (hpos u hu).ne')
    exact hd.congr (fun u hu => (afePhase_deriv_hasDerivAt c (hpos u hu)).deriv)
  have hpPos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < deriv (afePhase c) u := by
    rw [(afePhase_hasDerivAt c (hpos u hu)).deriv]
    exact div_pos hc (hpos u hu)
  have hq (n : ℕ) :
      AntitoneOn (fun u => |deriv h u| / (((n : ℝ) + 1) + deriv (afePhase c) u) ^ 2) (Set.Icc a b) ∧
      AntitoneOn (fun u => |h u * deriv (deriv (afePhase c)) u| /
        (((n : ℝ) + 1) + deriv (afePhase c) u) ^ 3) (Set.Icc a b) := by
    have hq := afe_second_quotients_antitone hσ hc.le (show 0 < (n : ℝ) + 1 by positivity)
    rcases hh with rfl | rfl
    · exact ⟨hq.1.mono hsub, hq.2.1.mono hsub⟩
    · exact ⟨hq.2.2.1.mono hsub, hq.2.2.2.mono hsub⟩
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) := (hr.1 u (hpos u hu)).hasDerivAt
  have hs := (secondModeTail_bound hab hf hp hd hpc hppc (hr.2.mono hsub) hpPos
    (fun n => (hq n).1) (fun n => (hq n).2)).1
  refine ⟨hs, ?_⟩
  have hb := secondModeTail_source_bound hab hf hp hd hpc hppc (hr.2.mono hsub) hpPos
    (fun n => (hq n).1) (fun n => (hq n).2)
  simpa only [(afePhase_hasDerivAt c ha).deriv,
    (afePhase_hasDerivAt c (ha.trans hab)).deriv,
    (afePhase_deriv_hasDerivAt c ha).deriv] using hb

/-- Both actual AFE amplitudes satisfy the complete upper-frequency series estimate with the exact cutoff and δ. -/
theorem afe_upper_second_tail_bound 
    {M : ℕ} (hM : c / a < (M : ℝ) + 1) :
    let δ : ℝ := (M : ℝ) + 1 - c / a
    Summable (upperModeTerm (afePhase c) h a b M) ∧
    ‖∑' n : ℕ, upperModeTerm (afePhase c) h a b M n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖negativeTail M b (c / b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖negativeTail M a (c / a)‖ +
      (|deriv h a| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / (c / a) -
          (Real.log ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1) -
            (Complex.digamma (δ : ℂ)).re) / (c / a) ^ 2) +
      (|h a * (-c / a ^ 2)| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / (c / a) -
          (1 / δ ^ 2 + 1 / (δ + 1)) / (c / a) ^ 2 +
          (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
            (Complex.digamma (δ : ℂ)).re) / (c / a) ^ 3) := by
  have hpos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun u hu => hpos u hu
  have hr := afe_second_amplitude_regular σ c h hh
  have hf (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (afePhase c) (deriv (afePhase c) u) u :=
    (afePhase_hasDerivAt c (hpos u hu)).differentiableAt.hasDerivAt
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (deriv (afePhase c)) (deriv (deriv (afePhase c)) u) u :=
    (afePhase_deriv_hasDerivAt c (hpos u hu)).differentiableAt.hasDerivAt
  have hpc : ContinuousOn (deriv (afePhase c)) (Set.Icc a b) :=
    fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hppc : ContinuousOn (deriv (deriv (afePhase c))) (Set.Icc a b) := by
    have hd : ContinuousOn (fun u : ℝ => -c / u ^ 2) (Set.Icc a b) :=
      continuousOn_const.div (continuousOn_id.pow 2) (fun u hu => pow_ne_zero _ (hpos u hu).ne')
    exact hd.congr (fun u hu => (afePhase_deriv_hasDerivAt c (hpos u hu)).deriv)
  have hpPos (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < deriv (afePhase c) u := by
    rw [(afePhase_hasDerivAt c (hpos u hu)).deriv]
    exact div_pos hc (hpos u hu)
  have hpa : AntitoneOn (deriv (afePhase c)) (Set.Icc a b) := by
    intro u hu v hv huv
    rw [(afePhase_hasDerivAt c (hpos u hu)).deriv, (afePhase_hasDerivAt c (hpos v hv)).deriv]
    exact div_le_div_of_nonneg_left hc.le (hpos u hu) huv
  have ham := afe_second_amplitudes_antitone hσ hc.le h hh
  have hppa := (afe_second_derivatives_antitone hσ hc.le).2.1.mono hsub
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) := (hr.1 u (hpos u hu)).hasDerivAt
  have hMa : deriv (afePhase c) a < (M : ℝ) + 1 := by
    simpa only [(afePhase_hasDerivAt c ha).deriv] using hM
  have hs := (upperModeTail_bound hab hf hp hd hpc hppc (hr.2.mono hsub) hpa
    (ham.1.mono hsub) (ham.2.mono hsub) hppa hpPos hMa).1
  refine ⟨hs, ?_⟩
  have hb := upperModeTail_source_bound hab hf hp hd hpc hppc (hr.2.mono hsub) hpa
    (ham.1.mono hsub) (ham.2.mono hsub) hppa hpPos hMa
  simpa only [(afePhase_hasDerivAt c ha).deriv,
    (afePhase_hasDerivAt c (ha.trans hab)).deriv,
    (afePhase_deriv_hasDerivAt c ha).deriv] using hb
end



