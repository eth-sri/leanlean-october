module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability

/-! # Strict lateral exit support, including a pole at the lower time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E) (sMinus T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time)

/-- No velocity-face exit occurs at or before the pole time. -/
theorem stripExitOfRealization_face_at_pole_zero (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hlam hLam A H E hE T e
      {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} = 0 := by
  let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
  let c := d ^ 2 / (4 * Lam)
  have hc : 0 < c := div_pos (sq_pos_of_pos (lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)))
    (mul_pos (by norm_num) (hlam.trans_le hLam))
  have hn (n : ℕ) : 0 < n + 1 := by positivity
  have hb (n : ℕ) : (stripExitOfRealization hlam hLam A H E hE T e) {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} ≤
      ENNReal.ofReal (2 * Real.exp (-(n + 1) * c)) := by
    have h := strip_exit_early_face_of_realization hlam hLam A H E hE e.1.time T e
      le_rfl (1 / (n + 1)) (by positivity)
    have hsub : {p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} ⊆
        {p | p.velocity 0 ∈ frontier H.carrier ∧
          p.time ≤ e.1.time + 1 / (n + 1)} := fun p hp => ⟨hp.1, hp.2.trans (le_add_of_nonneg_right (by positivity))⟩
    have heq : -d ^ 2 / (4 * Lam * (1 / (n + 1))) = -(n + 1) * c := by
      dsimp only [c]
      field_simp
    exact (measure_mono hsub).trans (by simp_all <;> grind)
  have hz : Tendsto (fun n : ℕ => ENNReal.ofReal
      (2 * Real.exp (-(n + 1) * c))) atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(n + 1) * c)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, neg_mul] using
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hc))
    have hr : Tendsto (fun n : ℕ => 2 * Real.exp (-(n + 1) * c))
        atTop (𝓝 0) := by simpa using hexp.const_mul 2
    simpa [Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hr
  exact le_antisymm (ge_of_tendsto hz (Eventually.of_forall hb)) (zero_le)

include he in
/-- The actual probability measure has the prescribed exit support even at the lower time. -/
theorem strip_exit_probability_of_realization :
    stripExitOfRealization hlam hLam A H E hE T e univ = 1 ∧
      stripExitOfRealization hlam hLam A H E hE T e
        (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExitOfRealization hlam hLam A H E hE T e
        {p | p.time < e.1.time} = 0 := by
  refine ⟨stripExitOfRealization_mass_one hlam hLam A H E hE T e, ?_,
    stripExitOfRealization_before_pole hlam hLam A H E hE T e⟩
  have hf : ∀ᵐ p ∂stripExitOfRealization hlam hLam A H E hE T e,
      ¬ (p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time) := by
    rw [ae_iff]
    simpa using stripExitOfRealization_face_at_pole_zero hlam hLam A H E hE T e
  have hb : ∀ᵐ p ∂stripExitOfRealization hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    apply stripExitOfRealization_compl_closedExit
  have hs : ∀ᵐ p ∂stripExitOfRealization hlam hLam A H E hE T e,
      p ∈ reconstructionExit H sMinus T := by
    filter_upwards [hb, hf] with p hp hpf
    rcases hp with hp | hp
    · exact Or.inl hp
    · by_cases ht : p.time = T
      · refine Or.inl ⟨ht, ?_⟩
        rcases hp.2 with hv | hv <;> rw [hv]
        · exact ⟨le_rfl, H.ordered.le⟩
        · exact ⟨H.ordered.le, le_rfl⟩
      · have hv : p.velocity 0 ∈ frontier H.carrier := by
          change p.velocity 0 ∈ frontier (Ioo H.lo H.hi)
          rw [frontier_Ioo H.ordered]
          exact hp.2
        apply Or.inr <;> first | assumption | positivity | fun_prop | grind
  exact hs

include he in
/-- Canonical probability normalization and exact terminal/lateral exit support. -/
theorem strip_exit_probability :
    stripExit hlam hLam A H T e univ = 1 ∧
      stripExit hlam hLam A H T e (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExit hlam hLam A H T e {p | p.time < e.1.time} = 0 :=
  by apply strip_exit_probability_of_realization <;> assumption

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
