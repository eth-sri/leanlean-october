module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarAxis
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ScalarDerivativeGrowth
import Mathlib.Tactic

/-! # Scaled similarity tails stay bounded at every nonzero position-axis point -/

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter Asymptotics Set
open scoped Topology

section
variable {ι : Type*} (l : Filter ι)

/-- Two actual similarity-tail bounds give local boundedness after kinetic rescaling at an axis. -/
theorem scalar_scaled_tail_bounded (f : ℝ → ℝ) (beta : ℝ)
    (ht : IsBigO atTop f (fun s => Real.rpow |s| beta))
    (hb : IsBigO atBot f (fun s => Real.rpow |s| beta))
    (X V : ι → ℝ) (v : ℝ) (hv : v ≠ 0) (hX : Tendsto X l (𝓝 0))
    (hXp : ∀ᶠ i in l, 0 < X i) (hV : Tendsto V l (𝓝 v)) :
    IsBigO l (fun i => Real.rpow (X i) (beta / 3) * f (scalarSimilarity (X i) (V i)))
      (fun _ => (1 : ℝ)) := by
  have hS := scalarSimilarity_tendsto_axis l X V v hv hX hXp hV
  have hf : IsBigO l (fun i => f (scalarSimilarity (X i) (V i)))
      (fun i => Real.rpow |scalarSimilarity (X i) (V i)| beta) := by
    by_cases hvn : v < 0
    · rw [ite_eq_left hvn] at hS
      exact ht.comp_tendsto hS
    · rw [ite_eq_right hvn] at hS
      exact hb.comp_tendsto hS
  have hm := (isBigO_refl (fun i => Real.rpow (X i) (beta / 3)) l).mul hf
  have he : (fun i => Real.rpow (X i) (beta / 3) *
      Real.rpow |scalarSimilarity (X i) (V i)| beta) =ᶠ[l] fun i => Real.rpow |V i| beta := by
    filter_upwards [hXp] with i hi
    exact scalar_similarity_power_cancel_general beta (X i) (V i) hi
  have hP : Tendsto (fun i => Real.rpow |V i| beta) l (𝓝 (Real.rpow |v| beta)) := by
    simpa only [Real.rpow_eq_pow, Function.comp_def] using
      (Real.continuousAt_rpow_const |v| beta (Or.inl (abs_ne_zero.mpr hv))).tendsto.comp hV.abs
  exact (hm.congr' EventuallyEq.rfl he).trans (isBigO_const_of_tendsto hP one_ne_zero)

end

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
