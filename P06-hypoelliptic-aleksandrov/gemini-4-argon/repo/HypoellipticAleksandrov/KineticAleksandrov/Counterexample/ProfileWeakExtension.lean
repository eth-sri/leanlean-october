module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeak
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileBounds
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-! # Removing the origin from position weak-derivative tests -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Filter Set

/- A C2 test has continuous position derivative components. -/
theorem continuous_dx_test {d : ℕ} (test : XV d → ℝ)
    (ht : ContDiff ℝ 2 test) (i : Fin d) : Continuous (fun q => dx test q i) := by
  exact ((ht.contDiff_fderiv_apply (m := 1) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/- A C2 test has continuous velocity derivative components. -/
theorem continuous_dv_test {d : ℕ} (test : XV d → ℝ)
    (ht : ContDiff ℝ 2 test) (i : Fin d) : Continuous (fun q => dv test q i) :=
  (contDiff_dv_test test ht i).continuous

/- Punctured position integration by parts extends across the origin without cutoff errors. -/
theorem continuous_dvv_test {d : ℕ} (test : XV d → ℝ)
    (ht : ContDiff ℝ 2 test) (i k : Fin d) : Continuous (fun q => dvv test q i k) := by
  exact (((contDiff_dv_test test ht k).contDiff_fderiv_apply (m := 0) (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)).continuous

/- Punctured velocity integration by parts extends across the origin without cutoff errors. -/
theorem profile_weak_identities_extend (d ) (hd : 1 ≤ d)
    (H : XV d → ℝ) (gx gv : XV d → PDE.Vec d) (hess : XV d → PDE.Mat d)
    (hH : Continuous H)
    (hgx : ∀ i, LocallyIntegrable (fun q => gx q i) volume)
    (hgv : ∀ i, LocallyIntegrable (fun q => gv q i) volume)
    (hhess : ∀ i k, LocallyIntegrable (fun q => hess q i k) volume)
    (hweak : ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (0 : XV d) ∉ tsupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q))) :
    ∀ test : XV d → ℝ, ContDiff ℝ 2 test → HasCompactSupport test →
      (∀ i, (∫ q, H q * dx test q i) = -(∫ q, gx q i * test q)) ∧
      (∀ i, (∫ q, H q * dv test q i) = -(∫ q, gv q i * test q)) ∧
      (∀ i k, (∫ q, H q * dvv test q i k) = (∫ q, hess q i k * test q)) := by
  intro test ht hs
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let g := (fun q => gx q i)
    have hg := (hgx i)
    have hweak := (fun t htc hts hto => (hweak t htc hts hto).1 i)
    have hleft : Integrable (fun q => H q * dx test q i) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hH.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          (continuous_dx_test test ht i) (hs.fderiv_apply ℝ (Pi.single i 1, 0))
    have hright : Integrable (fun q => g q * test q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hg.integrable_smul_left_of_hasCompactSupport ht.continuous hs
    let cut : ℕ → XV d → ℝ := fun n q => originCutoff n q.2
    have hc (n : ℕ) : Measurable (cut n) :=
      ((contDiff_originCutoff d n).continuous.comp continuous_snd).measurable
    have hb (n : ℕ) (q : XV d) : |cut n q| ≤ 1 := abs_originCutoff_le_one n q.2
    have hl : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (nhds 1) := by
      filter_upwards [coordinates_ne_zero_ae d hd] with q hq
      exact originCutoff_tendsto q.2 hq.2
    have hlimLeft := integral_mul_cutoff_tendsto _ hleft cut hc hb hl
    have hlimRight := (integral_mul_cutoff_tendsto _ hright cut hc hb hl).neg
    have he (n : ℕ) :
        (∫ q, (H q * dx test q i) * cut n q) =
          -(∫ q, (g q * test q) * cut n q) := by
      have hc2 : ContDiff ℝ 2 (cut n) :=
        ((contDiff_originCutoff d n).of_le (by simp)).comp contDiff_snd
      have _h_xinl_0 : (0 : XV d) ∉ tsupport (fun q => test q * originCutoff n q.2) := by
        apply notMem_tsupport_iff_eventuallyEq.mpr
        have ht : Tendsto (Prod.snd : XV d → PDE.Vec d) (nhds 0) (nhds 0) :=
          continuous_snd.tendsto 0
        filter_upwards [((originCutoff_eventually_zero d n).comp_tendsto ht)] with q hq
        change originCutoff n q.2 = 0 at hq
        rw [hq, mul_zero]
        rfl
      have hw := hweak (fun q => test q * cut n q) (ht.mul hc2)
        hs.mul_right _h_xinl_0
      simpa only [cut, dx_mul_velocity_cutoff test n _ (ht.differentiable (by norm_num) _) i,
        mul_assoc] using hw
    have hlimLeft' := hlimLeft.congr (fun n => he n)
    exact tendsto_nhds_unique hlimLeft' hlimRight
  · intro i
    let g := (fun q => gv q i)
    have hg := (hgv i)
    have hweak := (fun t htc hts hto => (hweak t htc hts hto).2.1 i)
    have hleft : Integrable (fun q => H q * dv test q i) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hH.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          (continuous_dv_test test ht i) (hs.fderiv_apply ℝ (0, Pi.single i 1))
    have hright : Integrable (fun q => g q * test q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hg.integrable_smul_left_of_hasCompactSupport ht.continuous hs
    let cut : ℕ → XV d → ℝ := fun n q => originCutoff n q.1
    have hc (n : ℕ) : Measurable (cut n) :=
      ((contDiff_originCutoff d n).continuous.comp continuous_fst).measurable
    have hb (n : ℕ) (q : XV d) : |cut n q| ≤ 1 := abs_originCutoff_le_one n q.1
    have hl : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (nhds 1) := by
      filter_upwards [coordinates_ne_zero_ae d hd] with q hq
      exact originCutoff_tendsto q.1 hq.1
    have hlimLeft := integral_mul_cutoff_tendsto _ hleft cut hc hb hl
    have hlimRight := (integral_mul_cutoff_tendsto _ hright cut hc hb hl).neg
    have he (n : ℕ) :
        (∫ q, (H q * dv test q i) * cut n q) =
          -(∫ q, (g q * test q) * cut n q) := by
      have hc2 : ContDiff ℝ 2 (cut n) :=
        ((contDiff_originCutoff d n).of_le (by simp)).comp contDiff_fst
      have hw := hweak (fun q => test q * cut n q) (ht.mul hc2)
        hs.mul_right (zero_notMem_tsupport_position_cutoff test n)
      simpa only [cut, dv_mul_position_cutoff test n _ (ht.differentiable (by norm_num) _) i,
        mul_assoc] using hw
    have hlimLeft' := hlimLeft.congr (fun n => he n)
    exact tendsto_nhds_unique hlimLeft' hlimRight
  · intro i k
    let g := (fun q => hess q i k)
    have hg := (hhess i k)
    have hweak := (fun t htc hts hto => (hweak t htc hts hto).2.2 i k)
    have hleft : Integrable (fun q => H q * dvv test q i k) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hH.locallyIntegrable.integrable_smul_left_of_hasCompactSupport
          (continuous_dvv_test test ht i k)
          ((hs.fderiv_apply ℝ (0, Pi.single k 1)).fderiv_apply ℝ (0, Pi.single i 1))
    have hright : Integrable (fun q => g q * test q) volume := by
      simpa only [smul_eq_mul, mul_comm] using
        hg.integrable_smul_left_of_hasCompactSupport ht.continuous hs
    let cut : ℕ → XV d → ℝ := fun n q => originCutoff n q.1
    have hc (n : ℕ) : Measurable (cut n) :=
      ((contDiff_originCutoff d n).continuous.comp continuous_fst).measurable
    have hb (n : ℕ) (q : XV d) : |cut n q| ≤ 1 := abs_originCutoff_le_one n q.1
    have hl : ∀ᵐ q ∂volume, Tendsto (fun n => cut n q) atTop (nhds 1) := by
      filter_upwards [coordinates_ne_zero_ae d hd] with q hq
      exact originCutoff_tendsto q.1 hq.1
    have hlimLeft := integral_mul_cutoff_tendsto _ hleft cut hc hb hl
    have hlimRight := integral_mul_cutoff_tendsto _ hright cut hc hb hl
    have he (n : ℕ) :
        (∫ q, (H q * dvv test q i k) * cut n q) =
          (∫ q, (g q * test q) * cut n q) := by
      have hc2 : ContDiff ℝ 2 (cut n) :=
        ((contDiff_originCutoff d n).of_le (by simp)).comp contDiff_fst
      have hw := hweak (fun q => test q * cut n q) (ht.mul hc2)
        hs.mul_right (zero_notMem_tsupport_position_cutoff test n)
      simpa only [cut, dvv_mul_position_cutoff test n ht _ i k,
        mul_assoc] using hw
    have hlimLeft' := hlimLeft.congr (fun n => he n)
    exact tendsto_nhds_unique hlimLeft' hlimRight

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
