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
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter
open scoped Topology

variable {d : ℕ} (H : XV d → ℝ) (alpha r mu R : ℝ)

/-- The barrier takes the exact value one quarter at the terminal spatial origin. -/
theorem barrier_terminal_origin  (mu R : ℝ) (hmu : 0 < mu) :
    barrier mu R (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) = 1 / 4 := by
  simp only [barrier, barrier_terminal_factor hmu, PDE.vecNormSq, PDE.vecDot]
  norm_num

/-- A small flattening scale gives the terminal height required in Appendix C. -/
theorem timeCutoff_height 
    (hH : H 0 = 0) (hr : 0 < r) (hmu : 0 < mu)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4) :
    3 / 8 ≤ timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩ := by
  have hf := flatProfile_eq_constant H alpha r hr _
    (by rw [hH]; exact (Real.rpow_pos_of_pos hr alpha).le)
  change 3 / 8 ≤ timeCutoffTheta
    (flatProfile H flatteningPsi flatteningOffset alpha r 0 -
      barrier mu R _)
  rw [hf, barrier_terminal_origin mu R hmu]
  have hl := timeCutoffTheta_lower (1 - flatteningOffset * Real.rpow r alpha - 1 / 4)
  linarith

/-- The time trace is continuous even when the spatial profile is only continuous. -/
theorem continuous_timeCutoffProfile_time  (q : XV d) :
    Continuous (fun t => timeCutoffProfile H alpha r mu R ⟨t, q.1, q.2⟩) := by
  simpa only [timeCutoffProfile, barrier] using!
    contDiff_timeCutoffTheta.continuous.comp
      (continuous_const.sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          continuous_const))

/-- The terminal height is attained with a strict margin at an earlier positive time. -/
theorem timeCutoff_interior_height 
    (hH : H 0 = 0) (hr : 0 < r) (hmu : 0 < mu)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4) :
    ∃ t : ℝ, 0 < t ∧ t < barrierTime mu ∧
      5 / 16 < timeCutoffProfile H alpha r mu R ⟨t, 0, 0⟩ := by
  have hh := timeCutoff_height H alpha r mu R hH hr hmu hsmall
  have hc := (continuous_timeCutoffProfile_time H alpha r mu R (0)).continuousAt
    (x := barrierTime mu)
  have he : ∀ᶠ t in 𝓝 _,
      5 / 16 < timeCutoffProfile H alpha r mu R ⟨t, 0, 0⟩ :=
    hc.eventually (Ioi_mem_nhds (by linarith :
      5 / 16 < timeCutoffProfile H alpha r mu R ⟨barrierTime mu, 0, 0⟩))
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := he.exists_Ioo_subset
  let t := (max a 0 + barrierTime mu) / 2
  have hT := barrierTime_pos hmu
  have hm : max a 0 < barrierTime mu := max_lt hat hT
  have ht0 : 0 < t := by positivity
  have htT : t < barrierTime mu := by grind
  refine ⟨t, ht0, htT, hab ?_⟩
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
