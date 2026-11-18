module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.TimeCutoff
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

/-!
# Terminal height of the explicit cutoff

The terminal value is a height estimate; an interior witness additionally uses continuity.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter
open scoped Topology



/-- The time trace is continuous even when the spatial profile is only continuous. -/
theorem continuous_timeCutoffProfile_time {d : ℕ} (H : XV d → ℝ)
    (alpha r mu R : ℝ) (q : XV d) :
    Continuous (fun t => timeCutoffProfile H alpha r mu R ⟨t, q.1, q.2⟩) := by
  simpa only [timeCutoffProfile, barrier] using!
    contDiff_timeCutoffTheta.continuous.comp
      (continuous_const.sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          continuous_const))

/-- The terminal height is attained with a strict margin at an earlier positive time. -/
theorem timeCutoff_interior_height {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)
    (hH : H 0 = 0) (hr : 0 < r) (hmu : 0 < mu)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4) :
    ∃ t : ℝ, 0 < t ∧ t < barrierTime mu ∧
      5 / 16 < timeCutoffProfile H alpha r mu R ⟨t, 0, 0⟩  := by
  have timeCutoff_height :
      3 / 8 ≤ timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩ := by
    have barrier_terminal_origin :
        barrier mu R (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) = 1 / 4 := by
      simp only [barrier, barrier_terminal_factor hmu, PDE.vecNormSq, PDE.vecDot,
        Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_div, sub_zero]
      norm_num
    unfold timeCutoffProfile
    change 3 / 8 ≤ timeCutoffTheta
      (flatProfile H flatteningPsi flatteningOffset alpha r 0 -
        barrier mu R (⟨barrierTime mu, 0, 0⟩ : KineticPoint d))
    rw [(flatProfile_eq_constant H alpha r hr 0 (by rw [hH]; exact (Real.rpow_pos_of_pos hr alpha).le)), barrier_terminal_origin]
    have hl := timeCutoffTheta_lower (1 - flatteningOffset * Real.rpow r alpha - 1 / 4)
    linarith
  have he :=
    (continuous_timeCutoffProfile_time H alpha r mu R 0).continuousAt (x := barrierTime mu).eventually (Ioi_mem_nhds (by linarith :
      5 / 16 < timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩))
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := he.exists_Ioo_subset
  let t := (max a 0 + barrierTime mu) / 2
  have hT := barrierTime_pos hmu
  have hm := max_lt hat hT
  have ht0 : 0 < t := by dsimp [t]; have := le_max_right a 0; linarith
  have htT : t < barrierTime mu := by dsimp [t]; linarith
  refine ⟨t, ht0, htT, hab ?_⟩
  constructor
  · dsimp [t]; have := le_max_left a 0; linarith
  · exact htT.trans htb

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
