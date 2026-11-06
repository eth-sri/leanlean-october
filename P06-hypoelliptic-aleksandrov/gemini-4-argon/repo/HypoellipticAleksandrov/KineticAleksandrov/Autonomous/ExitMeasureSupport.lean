module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExit
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ExitMeasureProbability
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExitBarrier

/-! # Strict lateral exit support, including a pole at the lower time -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov Filter
open SectionTwo TheoremA Evolution
open scoped Topology
open scoped ENNReal

/- No velocity-face exit occurs at or before the pole time. -/
theorem strip_exit_probability_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    stripExitOfRealization hH hlam hLam A H E hE T e univ = 1 ∧
      stripExitOfRealization hH hlam hLam A H E hE T e
        (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExitOfRealization hH hlam hLam A H E hE T e
        {p | p.time < e.1.time} = 0 := by
  refine ⟨stripExitOfRealization_mass_one hH hlam hLam A H E hE T e, ?_,
    stripExitOfRealization_before_pole hH hlam hLam A H E hE T e⟩
  have hf : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      ¬ (p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time) := by
    rw [ae_iff]
    have _h_inl_9 : stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} = 0 := by
        let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
        let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
        let c := d ^ 2 / (4 * Lam)
        have hd : 0 < d := lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)
        have hc : 0 < c := div_pos (sq_pos_of_pos hd)
          (mul_pos (by norm_num) (hlam.trans_le hLam))
        have hn (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hb (n : ℕ) : Ω {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} ≤
            ENNReal.ofReal (2 * Real.exp (-((n : ℝ) + 1) * c)) := by
          have h : stripExitOfRealization hH hlam hLam A H E hE T e {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time + (1 / ((n : ℝ) + 1))} ≤ ENNReal.ofReal (2 * Real.exp (-(min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) ^ 2 / (4 * Lam * (1 / ((n : ℝ) + 1))))) := by
            let sMinus := e.1.time
            let theta := (1 / ((n : ℝ) + 1))
            have htheta : 0 < (1 / ((n : ℝ) + 1)) := by
              positivity
            let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
            have hd : 0 < d := lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)
            have hLam0 : 0 < Lam := hlam.trans_le hLam
            let k := d / (2 * Lam * theta)
            have hk : 0 < k := div_pos hd (by positivity)
            have hl := reconstruction_early_face_exponential_bound hH hlam hLam A H E hE sMinus T e le_rfl
              theta k (-k) H.lo d hk.le (by ring)
              (fun v hv => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le)
                (sub_nonneg.mpr hv.1))
              (by
                have hh := mul_le_mul_of_nonneg_left (min_le_left
                  (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) hk.le
                change -k * (e.1.velocity 0 - H.lo) ≤ -k * d
                nlinarith)
            have hr := reconstruction_early_face_exponential_bound hH hlam hLam A H E hE sMinus T e le_rfl
              theta k k H.hi d hk.le rfl
              (fun v hv => mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hv.2))
              (by
                have hh := mul_le_mul_of_nonneg_left (min_le_right
                  (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) hk.le
                change k * (e.1.velocity 0 - H.hi) ≤ -k * d
                nlinarith)
            have hfront (v : ℝ) (hv : v ∈ frontier H.carrier) : v = H.lo ∨ v = H.hi := by
              change v ∈ frontier (Ioo H.lo H.hi) at hv
              rw [frontier_Ioo H.ordered] at hv
              simpa only [mem_insert_iff, mem_singleton_iff] using hv
            let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
            have hsub : {p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta} ⊆
                {p | p.velocity 0 = H.lo ∧ p.time ≤ sMinus + theta} ∪
                  {p | p.velocity 0 = H.hi ∧ p.time ≤ sMinus + theta} := by
              intro p hp
              rcases hfront _ hp.1 with hv | hv
              · exact Or.inl ⟨hv, hp.2⟩
              · exact Or.inr ⟨hv, hp.2⟩
            have hexp : Lam * k ^ 2 * theta - k * d = -d ^ 2 / (4 * Lam * theta) := by
              dsimp only [k]
              field_simp
              ring
            calc Ω {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta}
                ≤ Ω {p | p.velocity 0 = H.lo ∧ p.time ≤ sMinus + theta} +
                  Ω {p | p.velocity 0 = H.hi ∧ p.time ≤ sMinus + theta} :=
                    (measure_mono hsub).trans (measure_union_le _ _)
              _ ≤ ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) +
                  ENNReal.ofReal (Real.exp (Lam * k ^ 2 * theta - k * d)) := add_le_add hl hr
              _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, hexp, ← two_mul]
          have hsub : {p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ e.1.time} ⊆
              {p | p.velocity 0 ∈ frontier H.carrier ∧
                p.time ≤ e.1.time + 1 / ((n : ℝ) + 1)} := by
            intro p hp
            exact ⟨hp.1, hp.2.trans (le_add_of_nonneg_right (by positivity))⟩
          have heq : -d ^ 2 / (4 * Lam * (1 / ((n : ℝ) + 1))) = -((n : ℝ) + 1) * c := by
            dsimp only [c]
            field_simp
          exact (measure_mono hsub).trans (by simpa only [← heq, d] using h)
        have htop :=
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const hc
        have hz : Tendsto (fun n : ℕ => ENNReal.ofReal
            (2 * Real.exp (-((n : ℝ) + 1) * c))) atTop (𝓝 0) := by
          have hexp : Tendsto (fun n : ℕ => Real.exp (-((n : ℝ) + 1) * c)) atTop (𝓝 0) := by
            simpa only [Function.comp_def, neg_mul] using
              Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp htop)
          have hr : Tendsto (fun n : ℕ => 2 * Real.exp (-((n : ℝ) + 1) * c))
              atTop (𝓝 0) := by simpa using hexp.const_mul 2
          simpa only [Function.comp_def, ENNReal.ofReal_zero] using
            (ENNReal.continuous_ofReal.tendsto 0).comp hr
        exact le_antisymm (ge_of_tendsto hz (Eventually.of_forall hb)) (zero_le)

      /- The actual probability measure has the prescribed exit support even at the lower time. -/
    simpa using _h_inl_9
  have hb : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
      p ∈ stripClosedExit H T := by
    rw [ae_iff]
    exact stripExitOfRealization_compl_closedExit hH hlam hLam A H E hE T e
  have hs : ∀ᵐ p ∂stripExitOfRealization hH hlam hLam A H E hE T e,
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
          simpa only [mem_insert_iff, mem_singleton_iff] using hp.2
        have htime := lt_of_not_ge (fun h => hpf ⟨hv, h⟩)
        exact Or.inr ⟨he.trans_lt htime, lt_of_le_of_ne hp.1 ht, hp.2⟩
  rw [ae_iff] at hs
  exact hs

/- Canonical probability normalization and exact terminal/lateral exit support. -/
theorem strip_exit_probability
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (sMinus T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (he : sMinus ≤ e.1.time) :
    stripExit hH hLE hlam hLam A H T e univ = 1 ∧
      stripExit hH hLE hlam hLam A H T e (reconstructionExit H sMinus T)ᶜ = 0 ∧
      stripExit hH hLE hlam hLam A H T e {p | p.time < e.1.time} = 0 :=
  strip_exit_probability_of_realization hH hlam hLam A H _
    (stripEvolution_spec hH hLE hlam hLam A H) sMinus T e he

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
