module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EarlyExitBarrier

/-! # The source's quantitative early velocity-face exit estimate -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open SectionTwo TheoremA Evolution
open scoped ENNReal

/-- The actual exit measure satisfies the explicit two-face Gaussian early-exit bound. -/
theorem strip_exit_early_face_of_realization
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (sMinus T : ℝ) (e : StripPole H (T : WithTop ℝ))
    (he : sMinus ≤ e.1.time) (theta : ℝ) (htheta : 0 < theta) :
    stripExitOfRealization hH hlam hLam A H E hE T e
      {p | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta} ≤
        ENNReal.ofReal (2 * Real.exp
          (-(min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) ^ 2 /
            (4 * Lam * theta))) := by
  let d := min (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)
  have hd : 0 < d := lt_min (sub_pos.mpr e.2.2.1) (sub_pos.mpr e.2.2.2)
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  let k := d / (2 * Lam * theta)
  have hk : 0 < k := div_pos hd (by positivity)
  have hl := reconstruction_early_face_exponential_bound hH hlam hLam A H E hE sMinus T e he
    theta k _ H.lo d hk.le (by ring)
    (fun v hv => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le)
      (sub_nonneg.mpr hv.1))
    (by
      aesop)
  have hr := reconstruction_early_face_exponential_bound hH hlam hLam A H E hE sMinus T e he
    theta k k H.hi d hk.le rfl
    (fun v hv => mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hv.2))
    (by
      have hh := mul_le_mul_of_nonneg_left (min_le_right
        (e.1.velocity 0 - H.lo) (H.hi - e.1.velocity 0)) hk.le
      linarith)
  have hfront (v : ℝ) (hv : v ∈ frontier H.carrier) : v = H.lo ∨ v = H.hi := by
    change v ∈ frontier (Ioo H.lo H.hi) at hv
    rw [frontier_Ioo H.ordered] at hv
    simp_all
  let Ω := stripExitOfRealization hH hlam hLam A H E hE T e
  have hsub : {p : Point | p.velocity 0 ∈ frontier H.carrier ∧ p.time ≤ sMinus + theta} ⊆
      {p | p.velocity 0 = H.lo ∧ p.time ≤ sMinus + theta} ∪
        {p | p.velocity 0 = H.hi ∧ p.time ≤ sMinus + theta} := by
    grind
  have hexp : Lam * k ^ 2 * theta - k * d = -d ^ 2 / (4 * Lam * theta) := by
    grind
  calc Ω _
      ≤ Ω _ +
        Ω _ :=
          (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal _ +
        ENNReal.ofReal _ := add_le_add hl hr
    _ = _ := by rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le, hexp, ← two_mul]

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
