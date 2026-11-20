module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.GeometricCoreCoverSeries
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.RestartTailStatement
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite
import Mathlib.Tactic

/-! # Countable geometric core cover for near-velocity density estimates -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

/-- Power-integral bounds on intersecting cores glue to the homogeneous cylinder bound. -/
theorem geometricCoreDensity_of_power_bounds
    {lam Lam : ℝ} (A : SmoothAutonomous lam Lam) (Z₀ : Point) (R : ℝ) (hR : 0 < R)
    (P : Point) (hP : P ∈ forwardCylinder Z₀ R hR) (hnear : |Z₀.velocity 0| ≤ 8 * R)
    (C delta q : ℝ) (hC : 0 ≤ C) (hd : 0 < delta) (hq : 0 < q)
    (hlocal : ∀ i : Bool × ℕ,
      let c := geometricCoreClock R hR i.2 i.1
      (c.core ∩ (capacityCylinderInterval Z₀ R hR).carrier).Nonempty →
      ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
        (stripGreen A (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
          (capacityCylinderPole Z₀ P R hR hP)).restrict {z | z.velocity 0 ∈ c.core} =
          (volume.restrict (densityObservationStrip Z₀ R hR)).withDensity
            (fun z => ENNReal.ofReal (f z)) ∧
        (∫⁻ z, ‖f z‖ₑ ^ q ∂volume.restrict (densityObservationStrip Z₀ R hR)) ≤
          ENNReal.ofReal (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2)) :
    enlargedDensityBound
      ((stripGreen A (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
        (capacityCylinderPole Z₀ P R hR hP)).restrict (forwardCylinder Z₀ R hR))
      (forwardCylinder Z₀ R hR) q
      ((2 * C * (∑' j, geometricBandPower delta j)) ^ (1 / q) * R ^ (6 / q - 4)) := by
  let Q := forwardCylinder Z₀ R hR
  let D := densityObservationStrip Z₀ R hR
  let ν := stripGreen A (capacityCylinderInterval Z₀ R hR)
    (Z₀.time + R ^ 2) (capacityCylinderPole Z₀ P R hR hP)
  let S : Bool × ℕ → Set Point := fun i =>
    {z | z.velocity 0 ∈ (geometricCoreClock R hR i.2 i.1).core}
  have hS (i : Bool × ℕ) : MeasurableSet (S i) :=
    (isClosed_Icc.preimage ((continuous_apply 0).comp continuous_velocity)).measurableSet
  have hQ : MeasurableSet Q := (isOpen_forwardCylinder Z₀ R hR).measurableSet
  have hQD : Q ⊆ D := cylinder_subset_density_strip Z₀ R hR
  have hpiece (i : Bool × ℕ) : ∃ f : Point → ℝ, Measurable f ∧ (∀ z, 0 ≤ f z) ∧
      (ν.restrict Q).restrict (S i) ≤ (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (f z)) ∧
      (∫⁻ z, ‖f z‖ₑ ^ q ∂volume.restrict Q) ≤
        ENNReal.ofReal (C * R ^ (6 - 4 * q) * geometricBandPower delta i.2) := by
    by_cases hm : (Q ∩ S i).Nonempty
    · obtain ⟨z, hzQ, hzS⟩ := hm
      obtain ⟨f, hfm, hf0, hfd, hfi⟩ := hlocal i
        ⟨z.velocity 0, hzS, (capacityCylinderPole Z₀ z R hR hzQ).2.2⟩
      refine ⟨f, hfm, hf0, ?_, (lintegral_mono' (Measure.restrict_mono_set _ hQD) le_rfl).trans hfi⟩
      change ν.restrict (S i) = (volume.restrict D).withDensity _ at hfd
      rw [Measure.restrict_comm (hS i), hfd, restrict_withDensity hQ,
        Measure.restrict_restrict hQ, inter_eq_left.mpr hQD]
    · refine ⟨0, measurable_const, fun _ => le_rfl, ?_, by simp [ENNReal.zero_rpow_of_pos hq]⟩
      rw [Measure.restrict_restrict (hS i), inter_comm, not_nonempty_iff_eq_empty.mp hm,
        Measure.restrict_empty]
      exact bot_le
  choose f hfm hf0 hle hfi using hpiece
  have hcover : (ν.restrict Q) (⋃ i, S i)ᶜ = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.iUnion hS).compl]
    apply measure_mono_null (t := {z | z.velocity 0 = 0})
    · intro z hz
      by_contra hv
      have hvQ := (capacityCylinderPole Z₀ z R hR hz.2).2.2
      have hab : |z.velocity 0| ≤ 9 * R := by
        have h := abs_le.mp hnear
        change Z₀.velocity 0 - R < z.velocity 0 ∧
          z.velocity 0 < Z₀.velocity 0 + R at hvQ
        apply abs_le.mpr
        constructor <;> linarith [h.1, h.2, hvQ.1, hvQ.2]
      obtain ⟨j, s, hs⟩ := geometricCoreClock_covers R (z.velocity 0) hR hv hab
      exact hz.1 (mem_iUnion.mpr ⟨(s, j), hs⟩)
    · exact cylinder_strip_velocity_slice_zero A Z₀ P R hR hP 0
  have : IsFiniteMeasure ν := stripGreen_isFiniteMeasure A
    (capacityCylinderInterval Z₀ R hR) (Z₀.time + R ^ 2)
    (capacityCylinderPole Z₀ P R hR hP)
  have := density_volume_sigmaFinite
  obtain ⟨g, hgm, hg0, hgd, hgi⟩ := density_of_countable_cover
    (volume.restrict Q) (ν.restrict Q) S hS hcover f hfm hf0 q hq hle
  let total := ∑' j, geometricBandPower delta j
  have ht := (geometricBandPower_tsum_pos delta hd).le
  have hi := hgi.trans ((ENNReal.tsum_le_tsum hfi).trans_eq
    (geometricBandPower_sum C R delta (6 - 4 * q) hC hR hd))
  obtain ⟨hgp, hgn⟩ := density_norm_of_power_bound (volume.restrict Q) g hgm q
    (2 * C * total * R ^ (6 - 4 * q)) hq (by positivity) hi
  exact ⟨g, ⟨hgm, hg0, hgd⟩, hgp, hgn.trans_eq (geometricBandPower_root C R delta q hC hR hd hq)⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
