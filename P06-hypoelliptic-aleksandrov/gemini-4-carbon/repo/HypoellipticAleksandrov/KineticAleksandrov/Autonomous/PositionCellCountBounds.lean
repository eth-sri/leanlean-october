module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoxConcentrationAveraging
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.DeterministicBoxOccupation
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionPowerSum
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov MeasureTheory Set

/-- Concentration follows from occupation and the full bounded-Borel return-time conclusion.
The explicit conditional input quantifies over every coefficient field and every nonnegative
bounded Borel datum; it is not a box-specific comparison assumption. -/
theorem box_concentration_of_return_time
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) (alpha : ℝ)
    (ha : bellmanAdjointExponent (Lam / lam)
      (by apply (le_div_iff₀ hlam).2; simpa only [one_mul] using hLam) - 2 < alpha)
    (ha1 : alpha < 1) (A0 : ℝ) (hA0 : 0 < A0)
    (hReturn : ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam)
      (F : BoundedBorel (EvolutionAmbientState 1)), (∀ p, 0 ≤ F p) →
      ∀ (t s : NNReal) (z : Z), 0 < (t : ℝ) →
        2 * (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ 3 * (t : ℝ) →
        |z.2| ≤ Real.sqrt (t : ℝ) →
        let E := fullSpaceEvolution hH hLE hlam hLam A
        fullSpaceAction E F ⟨t, fun _ => z.1, fun _ => z.2⟩ ≤
          C * fullSpaceAction E F ⟨s, fun _ => z.1, fun _ => z.2⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (z : Z) (Y r : ℝ) (t : NNReal),
      0 < r → |z.2| ≤ 3 * r →
      (kernelXV (fullSpaceEvolution hH hLE hlam hLam A) t z (box A0 r Y)).toReal ≤
        C * (1 + (t : ℝ) / r ^ 2) ^ (-gamma alpha / 2) := by
  obtain ⟨CR, hCR, hreturn⟩ := hReturn
  obtain ⟨B, hB, hocc⟩ :=
    deterministic_box_occupation hH hLE lam Lam hlam hLam alpha ha ha1 A0 1 hA0
  have hg : 0 < gamma alpha := by dsimp only [gamma]; linarith
  let K := CR * B * 3 ^ (alpha / 2)
  have hK : 0 < K := by dsimp only [K]; positivity
  let C := 10 ^ (gamma alpha / 2) + K * 2 ^ (gamma alpha / 2)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A z Y r t hr hz
  let E := fullSpaceEvolution hH hLE hlam hLam A
  let f := fun s => (kernelXV E (Real.toNNReal s) z (box A0 r Y)).toReal
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
        exact indicator_nonneg (fun _ _ => zero_le_one) _)
        t (Real.toNNReal s) z ht
        (by simpa only [Real.coe_toNNReal s hs0] using hs.1.le)
        (by simpa using hs.2) hv
      dsimp only at hh
      rw [← box_action_eq_fullSpaceAction A E
        (fullSpaceEvolution_spec hH hLE hlam hLam A) z t A0 r Y,
        ← box_action_eq_fullSpaceAction A E
        (fullSpaceEvolution_spec hH hLE hlam hLam A) z (Real.toNNReal s) A0 r Y] at hh
      simpa only [f, Real.toNNReal_coe] using hh
    have htime : 0 ≤ 3 * (t : ℝ) := by positivity
    have hoc := hocc A z Y r (Real.toNNReal (3 * (t : ℝ))) hr (by
      simpa using
        hv.trans (Real.sqrt_le_sqrt (by linarith : (t : ℝ) ≤ 3 * (t : ℝ))))
    simp at hoc
    have hprod := (box_return_time_average E z A0 r Y t CR ht hCR.le hfcomp).trans (mul_le_mul_of_nonneg_left hoc hCR.le)
    have hpow : (3 * (t : ℝ)) ^ (alpha / 2) =
        3 ^ (alpha / 2) * (t : ℝ) ^ (alpha / 2) :=
      Real.mul_rpow (by norm_num) t.property
    rw [hpow] at hprod
    have hraw : f t ≤ K * (r ^ (gamma alpha) * (t : ℝ) ^ (alpha / 2) / (t : ℝ)) := by
      have hdiv : f t ≤
          (CR * (B * r ^ (gamma alpha) *
            (3 ^ (alpha / 2) * (t : ℝ) ^ (alpha / 2)))) / (t : ℝ) :=
        (le_div_iff₀ ht).mpr (by simpa only [mul_comm] using hprod)
      convert hdiv using 1
      ring
    rw [box_decay_scaling hr ht] at hraw
    have hxlarge : 1 ≤ x := by
      apply (le_div_iff₀ (by positivity : 0 < r ^ 2)).mpr
      nlinarith
    have hKC : K * 2 ^ (gamma alpha / 2) ≤ C := by
      exact le_add_of_nonneg_left (by positivity)
    have hbound : K * (2 ^ (gamma alpha / 2) *
        (1 + x) ^ (-gamma alpha / 2)) ≤ C * (1 + x) ^ (-gamma alpha / 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hdecay
    simpa only [f, Real.toNNReal_coe] using (hraw.trans (mul_le_mul_of_nonneg_left (box_decay_large_comparison hxlarge hg.le) hK.le)).trans hbound
  · have hxsmall : 1 + x ≤ 10 := by
      have hh := (div_lt_iff₀ (by positivity : 0 < r ^ 2)).mpr (lt_of_not_ge hlarge)
      linarith
    have hm := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx1 hxsmall (by linarith : -gamma alpha / 2 ≤ 0))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 10) (gamma alpha / 2))
    have hone : (10 : ℝ) ^ (gamma alpha / 2) * 10 ^ (-gamma alpha / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 10)]
      rw [show gamma alpha / 2 + -gamma alpha / 2 = 0 by ring, Real.rpow_zero]
    rw [hone] at hm
    have hmass : (kernelXV E t z (box A0 r Y)).toReal ≤ 1 := by
      exact (ENNReal.toReal_mono ENNReal.one_ne_top
        ((measure_mono (subset_univ _)).trans (kernelXV_mass_le_one E t z))).trans_eq
          ENNReal.toReal_one
    have hsmallC : 10 ^ (gamma alpha / 2) ≤ C := by
      exact le_add_of_nonneg_right (by positivity)
    exact (hmass.trans hm).trans (mul_le_mul_of_nonneg_right hsmallC hdecay)


/-- A short slab beginning in bin `j` retains the bin's concentration decay. -/
theorem position_concentration_slab_le
    (f : ℝ → ℝ) (B g r b : ℝ) (j : ℕ) (hB : 0 ≤ B) (hg : 0 ≤ g) (hr : 0 < r)
    (hab : (j : ℝ) * r ^ 2 ≤ b) (hlen : b - (j : ℝ) * r ^ 2 ≤ r ^ 2)
    (hi : Integrable f (volume.restrict (Ioc ((j : ℝ) * r ^ 2) b)))
    (hf : ∀ t : ℝ, 0 ≤ t → f t ≤ B * (1 + t / r ^ 2) ^ (-g / 2)) :
    f b + r ^ (-2 : ℤ) * (∫ t in Ioc ((j : ℝ) * r ^ 2) b, f t) ≤
      2 * B * (1 + (j : ℝ)) ^ (-g / 2) := by
  have hr2 := sq_pos_of_pos hr
  let D := B * (1 + (j : ℝ)) ^ (-g / 2)
  have hD : 0 ≤ D := mul_nonneg hB (Real.rpow_nonneg (by positivity) _)
  have hbound (t : ℝ) (ht : (j : ℝ) * r ^ 2 ≤ t) : f t ≤ D := by
    apply (hf t ((mul_nonneg (Nat.cast_nonneg j) hr2.le).trans ht)).trans
    apply mul_le_mul_of_nonneg_left _ hB
    have hratio := (le_div_iff₀ hr2).mpr ht
    exact Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + (j : ℝ))
      (by linarith) (by linarith)
  have hiBound : (∫ t in Ioc ((j : ℝ) * r ^ 2) b, f t) ≤
      D * (b - (j : ℝ) * r ^ 2) := by
    simpa [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab), mul_comm] using (integral_mono_ae hi (integrable_const D) ((ae_restrict_mem measurableSet_Ioc).mono fun t ht => hbound t ht.1.le))
  have hz : 0 ≤ r ^ (-2 : ℤ) := zpow_nonneg hr.le _
  have hnum := mul_le_mul_of_nonneg_left (hiBound.trans (mul_le_mul_of_nonneg_left hlen hD)) hz
  have he : r ^ (-2 : ℤ) * (D * r ^ 2) = D := by
    simp
    field_simp
  rw [he] at hnum
  calc
    _ ≤ D + D := add_le_add (hbound b hab) hnum
    _ = _ := by dsimp only [D]; ring

/-- Real full-space box probabilities are integrable on every finite time slab. -/
theorem position_box_probability_integrable (E : FullSpaceEvolution) (z : Z)
    (A0 r Y a b : ℝ) :
    Integrable (fun t => (kernelXV E (Real.toNNReal t) z (box A0 r Y)).toReal)
      (volume.restrict (Ioc a b)) := by
  apply Integrable.mono' (integrable_const 1) ((kernelXV_realTime_measurable E z _ (box_measurable A0 r Y)).ennreal_toReal).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have h :=
    (measure_mono (subset_univ (box A0 r Y))).trans
      (kernelXV_mass_le_one E (Real.toNNReal t) z)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

