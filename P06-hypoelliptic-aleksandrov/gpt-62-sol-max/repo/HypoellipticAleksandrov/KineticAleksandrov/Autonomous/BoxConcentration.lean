module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ReturnTime
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging

/-! # Box concentration from the return-time comparison -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- Concentration follows from occupation and the full bounded-Borel return-time conclusion.
 -/
theorem box_concentration
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) (A0 : ℝ) (hA0 : 0 < A0):
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (Y r : ℝ) (t : NNReal),
      0 < r → |z.2| ≤ 3 * r →
      (kernelXV (fullSpaceEvolution A) t z (box A0 r Y)).toReal ≤
        C * (1 + (t : ℝ) / r ^ 2) ^ (-gamma alpha / 2) := by
  obtain ⟨CR, hCR, hreturn⟩ := return_time_ambient hlam hLam
  obtain ⟨B, hB, hocc⟩ :=
    deterministic_box_occupation lam Lam hlam hLam alpha ha ha1 A0 1 hA0
  have hg : 0 < gamma alpha := by dsimp only [gamma]; linarith
  let K := CR * B * (3 : ℝ) ^ (alpha / 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  let C := (10 : ℝ) ^ (gamma alpha / 2) + K * (2 : ℝ) ^ (gamma alpha / 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A z Y r t hr hz
  let E := fullSpaceEvolution A
  let f := fun s : ℝ => (kernelXV E (Real.toNNReal s) z (box A0 r Y)).toReal
  let x := (t : ℝ) / r ^ 2
  have hx : 0 ≤ x := div_nonneg t.property (sq_nonneg r)
  have hx1 : 0 < 1 + x := by linarith
  have hdecay : 0 ≤ (1 + x) ^ (-gamma alpha / 2) := Real.rpow_nonneg hx1.le _
  by_cases hlarge : 9 * r ^ 2 ≤ (t : ℝ)
  · have ht : 0 < (t : ℝ) := lt_of_lt_of_le (by positivity) hlarge
    have hv : |z.2| ≤ Real.sqrt (t : ℝ) := hz.trans
      (Real.le_sqrt_of_sq_le (by nlinarith))
    have hfcomp (s : ℝ) (hs : s ∈ Ioc (2 * (t : ℝ)) (3 * (t : ℝ))) :
        f t ≤ CR * f s := by
      have hs0 : 0 ≤ s := by linarith [hs.1]
      have hh := hreturn A (boxIndicatorDatum A0 r Y) (fun p => by
        change 0 ≤ (box A0 r Y).indicator (fun _ => (1 : ℝ)) (p.1 0, p.2 0)
        exact indicator_nonneg (fun _ _ => zero_le_one) _)
        t (Real.toNNReal s) z ht
        (by simpa only [Real.coe_toNNReal s hs0] using hs.1.le)
        (by simpa only [Real.coe_toNNReal s hs0] using hs.2) hv
      dsimp only at hh
      rw [← box_action_eq_fullSpaceAction A E
        (fullSpaceEvolution_spec A) z t A0 r Y,
        ← box_action_eq_fullSpaceAction A E
        (fullSpaceEvolution_spec A) z (Real.toNNReal s) A0 r Y] at hh
      simpa only [f, Real.toNNReal_coe] using hh
    have hav := box_return_time_average E z A0 r Y t CR ht hCR.le hfcomp
    have htime : 0 ≤ 3 * (t : ℝ) := by positivity
    have hoc := hocc A z Y r (Real.toNNReal (3 * (t : ℝ))) hr (by
      simpa only [Real.coe_toNNReal _ htime, one_mul] using
        hv.trans (Real.sqrt_le_sqrt (by linarith : (t : ℝ) ≤ 3 * (t : ℝ))))
    simp only [Real.coe_toNNReal _ htime] at hoc
    have hprod := hav.trans (mul_le_mul_of_nonneg_left hoc hCR.le)
    have hpow : (3 * (t : ℝ)) ^ (alpha / 2) =
        (3 : ℝ) ^ (alpha / 2) * (t : ℝ) ^ (alpha / 2) :=
      Real.mul_rpow (by norm_num) t.property
    rw [hpow] at hprod
    have hraw : f t ≤ K * (r ^ (gamma alpha) * (t : ℝ) ^ (alpha / 2) / (t : ℝ)) := by
      have hdiv : f t ≤
          (CR * (B * r ^ (gamma alpha) *
            ((3 : ℝ) ^ (alpha / 2) * (t : ℝ) ^ (alpha / 2)))) / (t : ℝ) :=
        (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hprod)
      convert hdiv using 1
      dsimp only [K]
      ring
    rw [box_decay_scaling hr ht] at hraw
    have hxlarge : 1 ≤ x := by
      dsimp only [x]
      apply (le_div_iff₀ (by positivity : 0 < r ^ 2)).mpr
      nlinarith
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left
      (box_decay_large_comparison hxlarge hg.le) hK.le)
    have hKC : K * (2 : ℝ) ^ (gamma alpha / 2) ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_left (by positivity)
    have hbound : K * ((2 : ℝ) ^ (gamma alpha / 2) *
        (1 + x) ^ (-gamma alpha / 2)) ≤ C * (1 + x) ^ (-gamma alpha / 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hdecay
    simpa only [f, Real.toNNReal_coe] using hfinal.trans hbound
  · have hxsmall : 1 + x ≤ 10 := by
      dsimp only [x]
      have hh := (div_lt_iff₀ (by positivity : 0 < r ^ 2)).mpr (lt_of_not_ge hlarge)
      linarith
    have hp := Real.rpow_le_rpow_of_nonpos hx1 hxsmall
      (by linarith : -gamma alpha / 2 ≤ 0)
    have hm := mul_le_mul_of_nonneg_left hp
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (gamma alpha / 2))
    have hone : (10 : ℝ) ^ (gamma alpha / 2) * 10 ^ (-gamma alpha / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
      rw [show gamma alpha / 2 + -gamma alpha / 2 = 0 by ring, Real.rpow_zero]
    rw [hone] at hm
    have hmass : (kernelXV E t z (box A0 r Y)).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top
        ((measure_mono (subset_univ _)).trans (kernelXV_mass_le_one E t z))).trans_eq
          ENNReal.toReal_one
    have hsmallC : (10 : ℝ) ^ (gamma alpha / 2) ≤ C := by
      dsimp only [C]
      exact le_add_of_nonneg_right (by positivity)
    exact (hmass.trans hm).trans (mul_le_mul_of_nonneg_right hsmallC hdecay)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
