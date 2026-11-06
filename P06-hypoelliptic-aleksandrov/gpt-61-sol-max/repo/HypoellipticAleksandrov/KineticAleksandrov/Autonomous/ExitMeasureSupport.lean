module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability

/-! # Strict lateral exit support, including a pole at the lower time -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter

open scoped Topology

variable (hH : HormanderHypoellipticityStatement)

variable {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H) (hE : IsStripEvolution A H E)

/-- No velocity-face exit occurs at or before the pole time. -/
theorem stripExitOfRealization_face_at_pole_zero

     (T : ℝ) (e : StripPole H (T : WithTop ℝ)) :
    stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} = 0 := by
  let sharedTerm_e45d7447b3 := ({p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time})

  let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
  let c := d ^ 2 / (4 * Lam)

  have hc : 0 < c := div_pos (sq_pos_of_pos (lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)))
    (mul_pos (by norm_num) (hlam.trans_le hLam))

  have hb (n : ℕ) : (stripExitOfRealization hH hlam hLam A H E hE T e) sharedTerm_e45d7447b3 ≤
      ENNReal.ofReal (2 * Real.exp (-((n : ℝ) + 1) * c)) := by
    have h := strip_exit_early_face_of_realization hH hlam hLam A H E hE e.1.time T e
      le_rfl (1 / ((n : ℝ) + 1)) (by positivity)

    have heq : -d ^ 2 / (4 * Lam * (1 / ((n : ℝ) + 1))) = -((n : ℝ) + 1) * c := by
      dsimp only [c]
      field_simp
    exact (measure_mono (show sharedTerm_e45d7447b3 ⊆
        {p | p.velocity 0 ∈ frontier H.carrier ∧
          p.time ≤ e.1.time + 1 / ((n : ℝ) + 1)} by
        intro p hp
        exact ⟨hp.1, hp.2.trans (le_add_of_nonneg_right (by positivity))⟩)).trans (by simpa only [← heq, d] using h)


  exact le_antisymm (ge_of_tendsto (by
      have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * c)) atTop (𝓝 0) := by
        simpa only [Function.comp_def, neg_mul] using
          Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hc))

      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        (ENNReal.continuous_ofReal.tendsto 0).comp (by simpa using hexp.const_mul 2)) (Eventually.of_forall hb)) (zero_le)

/-- The actual probability measure has the prescribed exit support even at the lower time. -/
theorem strip_exit_probability_of_realization

     (sMinus T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    stripExitOfRealization hH hlam hLam A H E hE T e univ = 1 ∧
      stripExitOfRealization hH hlam hLam A H E hE T e
        (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExitOfRealization hH hlam hLam A H E hE T e
        {p | p.time < e.1.time} = 0 := by
  let sharedTerm_65eda965e0 := (stripExitOfRealization hH hlam hLam A H E hE T e)
  refine ⟨stripExitOfRealization_mass_one hH hlam hLam A H E hE T e, ?_,
    stripExitOfRealization_before_pole hH hlam hLam A H E hE T e⟩


  have hs : ∀ᵐ p ∂sharedTerm_65eda965e0,
      p ∈ reconstructionExit H sMinus T := by
    filter_upwards [(show ∀ᵐ p ∂sharedTerm_65eda965e0,
      p ∈ stripClosedExit H T by
        rw [ae_iff]
        exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e), (show ∀ᵐ p ∂sharedTerm_65eda965e0,
      ¬ (p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time) by
        rw [ae_iff]
        simpa using stripExitOfRealization_face_at_pole_zero hH hlam hLam A H E hE T e)] with p hp hpf
    rcases hp with hp | hp
    · exact Or.inl hp
    · by_cases ht : p.time = T
      · refine Or.inl ⟨ht, ?_⟩
        rcases hp.2 with hv | hv <;> rw [hv]
        · exact ⟨le_rfl, H.ordered.le⟩
        · exact ⟨H.ordered.le, le_rfl⟩
      ·

        exact Or.inr ⟨he.trans_lt (lt_of_not_ge (fun h => hpf ⟨(show p.velocity 0 ∈ frontier H.carrier by
            change p.velocity 0 ∈ frontier (Ioo H.lo H.hi)
            rw [frontier_Ioo H.ordered]
            exact hp.2), h⟩)), lt_of_le_of_ne hp.1 ht, hp.2⟩
  rw [ae_iff] at hs
  exact hs

/-- Canonical probability normalization and exact terminal/lateral exit support. -/
theorem strip_exit_probability
     (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    stripExit hH hLE hlam hLam A H T e univ = 1 ∧
      stripExit hH hLE hlam hLam A H T e (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExit hH hLE hlam hLam A H T e {p | p.time < e.1.time} = 0 :=
  strip_exit_probability_of_realization hH hlam hLam A H _
    _ sMinus T e he

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
