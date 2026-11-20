module

import HypoellipticAleksandrov.Analysis.L2Convergence

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeBochner
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Local translation continuity for reverse-time Bochner spaces

This module obtains local literal-representative `L²` translation continuity
from the continuous domain-add action on ambient `Lp`.  The local statements
use a zero extension only as an `Lp` representative; they make no derivative
claim for that extension.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

theorem sqNorm_integral_eq_norm_sq_toLp
    {E : Type*} [NormedAddCommGroup E]
    {μ : Measure ℝ} (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) μ) :
    ∫ t, ‖F t‖ ^ 2 ∂μ = ‖hF.toLp F‖ ^ 2 := Analysis.integral_sq_eq_norm_toLp_sq hF

/-- Strong `L²` continuity of translations, restricted to any time set. -/
theorem tendsto_sqNorm_integral_translate_add_on_of_memLp_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 : ℝ≥0∞) volume) (s : Set ℝ) :
    Tendsto (fun h : ℝ => ∫ t in s, ‖F (t + h) - F t‖ ^ 2) (𝓝 0) (𝓝 0) := by
  let f : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hF.toLp F
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hcont : Continuous (fun h : ℝ => DomAddAct.mk h +ᵥ f) :=
    continuous_vadd.comp (DomAddAct.continuous_mk.prodMk continuous_const)
  have hzero : DomAddAct.mk (0 : ℝ) +ᵥ f = f := by
    simp
  have hcontsub : Continuous (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) :=
    hcont.sub continuous_const
  have hvalue : (DomAddAct.mk (0 : ℝ) +ᵥ f) - f = 0 := by
    rw [hzero, sub_self]
  have hsub : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0) (𝓝 0) := by
    have hat : Tendsto (fun h : ℝ => (DomAddAct.mk h +ᵥ f) - f) (𝓝 0)
        (𝓝 ((DomAddAct.mk (0 : ℝ) +ᵥ f) - f)) :=
      hcontsub.continuousAt
    rw [hvalue] at hat
    exact hat
  have hnorm : Tendsto (fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa using hsub.norm.pow 2
  refine squeeze_zero (g := fun h : ℝ => ‖(DomAddAct.mk h +ᵥ f) - f‖ ^ 2)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun h => ?_) hnorm
  let htrans : MemLp (fun t : ℝ => F (h + t)) (2 : ℝ≥0∞) volume :=
    hF.comp_measurePreserving (measurePreserving_add_left volume h)
  let hdiff : MemLp (fun t : ℝ => F (h + t) - F t) (2 : ℝ≥0∞) volume :=
    htrans.sub hF
  let q : Lp (α := ℝ) E (2 : ℝ≥0∞) volume := hdiff.toLp _
  let qS : Lp (α := ℝ) E (2 : ℝ≥0∞) (volume.restrict s) :=
    ((Lp.memLp q).restrict s).toLp q
  have hq : q =ᵐ[volume] fun t : ℝ => F (h + t) - F t := by
    simpa [q] using hdiff.coeFn_toLp
  have hqS : qS =ᵐ[volume.restrict s] q := by
    simpa [qS] using MemLp.coeFn_toLp ((Lp.memLp q).restrict s)
  have hsq : (∫ t in s, ‖F (t + h) - F t‖ ^ 2) = ‖qS‖ ^ 2 := by
    change (∫ t, ‖F (t + h) - F t‖ ^ 2 ∂volume.restrict s) = _
    have hqSsq := sqNorm_integral_eq_norm_sq_toLp (qS : ℝ → E) (Lp.memLp qS)
    rw [Lp.toLp_coeFn qS (Lp.memLp qS)] at hqSsq
    rw [← hqSsq]
    apply integral_congr_ae
    filter_upwards [hqS, ae_restrict_of_ae hq] with t htS ht
    rw [htS, ht, add_comm]
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Lp_toLp_restrict_le s q) 2

end HypoellipticAleksandrov.Parabolic.Dirichlet
