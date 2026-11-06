/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RadialCriteria
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! Sharp integrability tests for products of two planar radial powers. -/

public section

open MeasureTheory Set Metric
open scoped Topology

namespace DOZZ.Proofs

private theorem measurable_norm_rpow (s : ℝ) :
    Measurable (fun w : ℂ => ‖w‖ ^ s) := by
  fun_prop

private theorem measurable_rpow_of_nonneg {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (s : ℝ) : Measurable (fun u => f u ^ s) := by
  fun_prop

private theorem continuousOn_norm_comp_rpow {s : Set ℂ} (f : ℂ → ℂ)
    (hf : Continuous f) (hs : ∀ u ∈ s, f u ≠ 0) (p : ℝ) :
    ContinuousOn (fun u => ‖f u‖ ^ p) s := (continuous_norm.comp hf).continuousOn.rpow_const fun u hu =>
    Or.inl (norm_ne_zero_iff.mpr (hs u hu))

private theorem integrableOn_mul_factor_iff {s : Set ℂ} (hs : MeasurableSet s)
    {f g : ℂ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hnf : ∀ x, 0 ≤ f x) {c C : ℝ} (hc : 0 < c)
    (hlower : ∀ x ∈ s, c ≤ g x) (hupper : ∀ x ∈ s, g x ≤ C) :
    IntegrableOn (fun x => f x * g x) s volume ↔ IntegrableOn f s volume := by
  change Integrable (fun x => f x * g x) (volume.restrict s) ↔
    Integrable f (volume.restrict s)
  constructor
  · intro hfg
    apply (hfg.const_mul c⁻¹).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hnf x)]
    have hprod : c * f x ≤ f x * g x := by
      nlinarith [mul_le_mul_of_nonneg_left (hlower x hx) (hnf x)]
    exact (le_inv_mul_iff₀ hc).mpr hprod
  · intro hf
    apply (hf.const_mul C).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem hs] with x hx
    change |f x * g x| ≤ C * f x
    rw [abs_of_nonneg (mul_nonneg (hnf x) (le_trans hc.le (hlower x hx)))]
    nlinarith [mul_le_mul_of_nonneg_left (hupper x hx) (hnf x)]

private theorem exists_rpow_interval_bounds {A B s : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x, A ≤ x → x ≤ B → c ≤ x ^ s ∧ x ^ s ≤ C := by
  by_cases hs : 0 ≤ s
  · refine ⟨A ^ s, B ^ s, Real.rpow_pos_of_pos hA s,
      Real.rpow_pos_of_pos (lt_of_lt_of_le hA hAB) s, ?_⟩
    intro x hxA hxB
    exact ⟨Real.rpow_le_rpow hA.le hxA hs,
      Real.rpow_le_rpow (le_trans hA.le hxA) hxB hs⟩
  · have hs'  := le_of_lt (lt_of_not_ge hs)
    refine ⟨B ^ s, A ^ s, Real.rpow_pos_of_pos (lt_of_lt_of_le hA hAB) s,
      Real.rpow_pos_of_pos hA s, ?_⟩
    intro x hxA hxB
    exact ⟨Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hA hxA) hxB hs',
      Real.rpow_le_rpow_of_nonpos hA hxA hs'⟩

private theorem norm_sub_bounds_on_ball_zero {z : ℂ} {R : ℝ}
    {u : ℂ} (hu : u ∈ ball 0 R) :
    ‖z‖ - R ≤ ‖u - z‖ ∧ ‖u - z‖ ≤ ‖z‖ + R := by
  have huR : ‖u‖ < R := by simp_all
  have hsum : (z - u) + u = z := by abel
  have htriangle := norm_add_le (z - u) u
  rw [hsum] at htriangle
  
  have heq : ‖z - u‖ = ‖u - z‖ := by rw [← norm_neg, neg_sub]
  constructor
  · rw [← heq]
    linarith
  · calc
      ‖u - z‖ = ‖u + (-z)‖ := by rw [sub_eq_add_neg]
      _ ≤ ‖u‖ + ‖z‖ := by simpa only [norm_neg] using norm_add_le u (-z)
      _ ≤ ‖z‖ + R := by nlinarith

private theorem norm_center_bounds_on_ball {z : ℂ} {R : ℝ} {u : ℂ}
    (hu : u ∈ ball z R) : ‖z‖ - R ≤ ‖u‖ ∧ ‖u‖ ≤ ‖z‖ + R := by
  have huR : ‖u - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hsum : u = z + (u - z) := by abel
  have hzrep : u - (u - z) = z := by abel
  
  have htriangle' : ‖u - (u - z)‖ ≤ ‖u‖ + ‖u - z‖ := by
    bound
  rw [hzrep] at htriangle'
  
  constructor
  · linarith
  · calc
      ‖u‖ = ‖z + (u - z)‖ := congrArg norm hsum
      _ ≤ ‖z‖ + ‖u - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + R := by linarith

private theorem integrableOn_norm_sub_rpow_ball_iff (b : ℝ) (z : ℂ)
    (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun u : ℂ => ‖u - z‖ ^ b) (ball z R) volume ↔ -2 < b := by
  let τ  := fun v => v + z
  have himage : τ '' ball (0 : ℂ) R = ball z R := by
    aesop
  have htrans : IntegrableOn (fun u : ℂ => ‖u - z‖ ^ b) (ball z R) volume ↔
      IntegrableOn (fun v : ℂ => ‖v‖ ^ b) (ball 0 R) volume := by
    rw [← himage]
    simpa [τ, Function.comp_def] using
      (MeasureTheory.measurePreserving_add_right volume z).integrableOn_image
        (Homeomorph.addRight z).measurableEmbedding (s := ball 0 R)
        (f := fun u : ℂ => ‖u - z‖ ^ b)
  exact htrans.trans (integrableOn_norm_rpow_ball_iff b R hR)

private theorem norm_sub_ratio_bounds_on_tail {z : ℂ} {R : ℝ}
    (hz : 0 < ‖z‖) (hR : 2 * ‖z‖ ≤ R) {u : ℂ}
    (hu : u ∈ (ball 0 R)ᶜ) :
    (1 / 2 : ℝ) ≤ ‖u - z‖ / ‖u‖ ∧ ‖u - z‖ / ‖u‖ ≤ 3 / 2 := by
  have hnorm : R ≤ ‖u‖ := by
    simp_all
  have hnormz : ‖z‖ ≤ ‖u‖ := by nlinarith
  have huPos  := lt_of_lt_of_le hz hnormz
  have hsub : ‖u‖ - ‖z‖ ≤ ‖u - z‖ := by
    exact norm_sub_norm_le u z
  have hadd : ‖u - z‖ ≤ ‖u‖ + ‖z‖ := by
    bound
  constructor
  · apply (le_div_iff₀ huPos).2
    
    nlinarith
  · apply (div_le_iff₀ huPos).2
    
    nlinarith

variable (a b : ℝ) (z : ℂ) (hz : z ≠ 0)

include a b z hz in
private theorem integrableOn_two_point_rpow_tail_iff  :
    IntegrableOn (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b)
      (ball 0 (2 * ‖z‖))ᶜ volume ↔ a + b < -2 := by
  have hzpos  := norm_pos_iff.mpr hz
  let R := 2 * ‖z‖
  let q  := fun u => ‖u - z‖ / ‖u‖
  have hR : 0 < R := by dsimp [R]; positivity
  have hqmeas : Measurable q := by dsimp [q]; fun_prop
  have hqnonneg : ∀ u, 0 ≤ q u := fun u => div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hqpowmeas  := measurable_rpow_of_nonneg hqmeas hqnonneg b
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    exists_rpow_interval_bounds (A := (1 / 2 : ℝ)) (B := (3 / 2 : ℝ)) (s := b)
      (by norm_num) (by norm_num)
  have hfactorBounds : ∀ u ∈ (ball (0 : ℂ) R)ᶜ,
      c ≤ q u ^ b ∧ q u ^ b ≤ C := by
    intro u hu
    rcases norm_sub_ratio_bounds_on_tail hzpos (by dsimp [R]; rfl) hu with ⟨hlo, hhi⟩
    exact hbounds (q u) hlo hhi
  have hEqOn : EqOn
      (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b)
      (fun u => ‖u‖ ^ (a + b) * q u ^ b) (ball 0 R)ᶜ := by
    intro u hu
    have hnorm : R ≤ ‖u‖ := by
      simp_all
    have huPos  := lt_of_lt_of_le hzpos (by dsimp [R] at hnorm; nlinarith)
    have hratio : ‖u - z‖ ^ b = ‖u‖ ^ b * q u ^ b := by
      have hmul : ‖u‖ * q u = ‖u - z‖ := by
        dsimp [q]
        field_simp [ne_of_gt huPos]
      calc
        ‖u - z‖ ^ b = (‖u‖ * q u) ^ b := by rw [hmul]
        _ = ‖u‖ ^ b * q u ^ b := Real.mul_rpow (norm_nonneg _) (hqnonneg u)
    change ‖u‖ ^ a * ‖u - z‖ ^ b = ‖u‖ ^ (a + b) * q u ^ b
    rw [hratio]
    calc
      ‖u‖ ^ a * (‖u‖ ^ b * q u ^ b) =
          (‖u‖ ^ a * ‖u‖ ^ b) * q u ^ b := by ring
      _ = ‖u‖ ^ (a + b) * q u ^ b := by rw [← Real.rpow_add huPos a b]
  have hcongr := integrableOn_congr_fun (μ := volume) hEqOn
    (MeasurableSet.compl Metric.isOpen_ball.measurableSet)
  have hlocal := integrableOn_mul_factor_iff
    (MeasurableSet.compl Metric.isOpen_ball.measurableSet)
    (measurable_norm_rpow (a + b)) hqpowmeas
    (fun u => Real.rpow_nonneg (norm_nonneg u) (a + b)) hc
    (fun u hu => (hfactorBounds u hu).1) (fun u hu => (hfactorBounds u hu).2)
  rw [hcongr, hlocal, integrableOn_norm_rpow_ball_compl_iff (a + b) R hR]

include a b z hz in
theorem integrableOn_two_point_rpow_ball_zero_iff 
    (R : ℝ) (hR : 0 < R) (hRz : R < ‖z‖) :
    IntegrableOn (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b) (ball 0 R) volume ↔ -2 < a := by
  
  have hAB : ‖z‖ - R ≤ ‖z‖ + R := by linarith
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    exists_rpow_interval_bounds (s := b) (sub_pos.mpr hRz) hAB
  have hfactorBounds : ∀ u ∈ ball (0 : ℂ) R,
      c ≤ ‖u - z‖ ^ b ∧ ‖u - z‖ ^ b ≤ C := by
    intro u hu
    rcases norm_sub_bounds_on_ball_zero hu with ⟨hlo, hhi⟩
    exact hbounds ‖u - z‖ hlo hhi
  have hlocal := integrableOn_mul_factor_iff (Metric.isOpen_ball.measurableSet)
    (measurable_norm_rpow a) (by fun_prop)
    (fun u => Real.rpow_nonneg (norm_nonneg u) a) hc
    (fun u hu => (hfactorBounds u hu).1) (fun u hu => (hfactorBounds u hu).2)
  rw [hlocal, integrableOn_norm_rpow_ball_iff a R hR]

include a b z hz in
theorem integrableOn_two_point_rpow_ball_z_iff 
    (R : ℝ) (hR : 0 < R) (hRz : R < ‖z‖) :
    IntegrableOn (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b) (ball z R) volume ↔ -2 < b := by
  
  have hAB : ‖z‖ - R ≤ ‖z‖ + R := by linarith
  obtain ⟨c, C, hc, hC, hbounds⟩ :=
    exists_rpow_interval_bounds (s := a) (sub_pos.mpr hRz) hAB
  have hfactorBounds : ∀ u ∈ ball z R, c ≤ ‖u‖ ^ a ∧ ‖u‖ ^ a ≤ C := by
    intro u hu
    rcases norm_center_bounds_on_ball hu with ⟨hlo, hhi⟩
    exact hbounds ‖u‖ hlo hhi
  have hlocal := integrableOn_mul_factor_iff (Metric.isOpen_ball.measurableSet)
    (by fun_prop) (measurable_norm_rpow a)
    (fun u => Real.rpow_nonneg (norm_nonneg (u - z)) b) hc
    (fun u hu => (hfactorBounds u hu).1) (fun u hu => (hfactorBounds u hu).2)
  rw [show (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b) =
      fun u => ‖u - z‖ ^ b * ‖u‖ ^ a by funext; ring]
  exact hlocal.trans (integrableOn_norm_sub_rpow_ball_iff b z R hR)

include a b z hz in
theorem integrableOn_two_point_rpow_iff  :
    Integrable (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b) volume ↔
      -2 < a ∧ -2 < b ∧ a + b < -2 := by
  have hzpos  := norm_pos_iff.mpr hz
  let δ := ‖z‖ / 3
  let R := 2 * ‖z‖
  let s₀ := ball (0 : ℂ) δ
  let sz := ball z δ
  let sm := Metric.closedBall (0 : ℂ) R ∩ (s₀ ∪ sz)ᶜ
  let st := (ball (0 : ℂ) R)ᶜ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδz : δ < ‖z‖ := by dsimp [δ]; linarith
  
  have h0 := integrableOn_two_point_rpow_ball_zero_iff a b z hz δ hδ hδz
  have hzLocal := integrableOn_two_point_rpow_ball_z_iff a b z hz δ hδ hδz
  have htail := integrableOn_two_point_rpow_tail_iff a b z hz
  have htailR : IntegrableOn (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b)
      (ball (0 : ℂ) R)ᶜ volume ↔ a + b < -2 := by
    exact htail
  have hsmclosed : IsClosed sm := by
    exact Metric.isClosed_closedBall.inter <| isClosed_compl_iff.mpr
      (Metric.isOpen_ball.union Metric.isOpen_ball)
  have hsmcompact  :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hsmclosed (by
      intro u hu
      exact hu.1)
  have hsm_avoid_zero : ∀ u ∈ sm, u ≠ 0 := by
    intro u hu huz
    aesop
  have hsm_avoid_z : ∀ u ∈ sm, u - z ≠ 0 := by
    intro u hu huz
    have huz'  := sub_eq_zero.mp huz
    have hcenter : z ∈ sz := by
      dsimp [sz]
      simpa [Metric.mem_ball, dist_self] using hδ
    grind
  have hcont₀  :=
    continuousOn_norm_comp_rpow (fun u => u) continuous_id hsm_avoid_zero a
  have hcontz  :=
    continuousOn_norm_comp_rpow (fun u => u - z) (continuous_id.sub continuous_const)
      hsm_avoid_z b
  have hmiddle : IntegrableOn (fun u : ℂ => ‖u‖ ^ a * ‖u - z‖ ^ b) sm volume :=
    (hcont₀.mul hcontz).integrableOn_compact hsmcompact
  have hcover : univ = s₀ ∪ (sz ∪ (sm ∪ st)) := by
    ext u
    simp only [mem_univ, mem_union, true_iff]
    by_cases htail' : u ∈ st
    · exact Or.inr (Or.inr (Or.inr htail'))
    · have huBall : u ∈ ball (0 : ℂ) R := by
        grind
      by_cases hu₀ : u ∈ s₀
      · exact Or.inl hu₀
      · by_cases huz' : u ∈ sz
        · exact Or.inr (Or.inl huz')
        · apply Or.inr (Or.inr (Or.inl ?_))
          refine ⟨?_, ?_⟩
          · simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt
              (by simp_all)
          simp_all
  rw [← integrableOn_univ, hcover, integrableOn_union, integrableOn_union,
    integrableOn_union]
  grind

end DOZZ.Proofs
