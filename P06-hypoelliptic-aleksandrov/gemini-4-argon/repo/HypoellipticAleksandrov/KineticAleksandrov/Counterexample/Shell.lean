module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ShellGeometry
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Ring

/-! # Shell volume with the exact homogeneous dimension `4d` -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set

/- The closed shell that contains the stationary source. -/
def profileShell {d : ℕ} (H : XV d → ℝ) (alpha r : ℝ) : Set (XV d) :=
  {q | Real.rpow r alpha ≤ H q ∧ H q ≤ 2 * Real.rpow r alpha}

/- Comparison with a positive gauge power traps any fixed upper profile sublevel. -/
theorem profile_sublevel_subset_rho {d : ℕ} (H : XV d → ℝ) (alpha c M : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hM : 0 < M)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q) :
    {q | H q ≤ M} ⊆ {q | rho q ≤ Real.rpow (M / c) alpha⁻¹} := by
  intro q hq
  have hb :=
    (le_div_iff₀ hc).2 (by simpa only [mul_comm] using (hlo q).trans hq)
  have hbase := div_pos hM hc
  apply (Real.rpow_le_rpow_iff (rho_nonneg q) (Real.rpow_pos_of_pos hbase alpha⁻¹).le ha).mp
  simp only [Real.rpow_eq_pow] at hb ⊢
  rw [Real.rpow_inv_rpow hbase.le ha.ne']
  exact hb

/- A continuous comparable profile has finite-volume upper sublevels. -/
theorem profile_sublevel_volume_lt_top {d : ℕ} (H : XV d → ℝ) (alpha c M : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hM : 0 < M)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q) :
    volume {q | H q ≤ M} < ⊤ := by
  exact lt_of_le_of_lt
    (measure_mono (profile_sublevel_subset_rho H alpha c M ha hc hM hlo))
    (isCompact_rho_sublevel d (Real.rpow (M / c) alpha⁻¹)).measure_lt_top

/- Homogeneity identifies the radius-r shell as the inverse-dilation preimage. -/
theorem shell_volume_bound {d : ℕ} (H : XV d → ℝ) (alpha c : ℝ)
    (ha : 0 < alpha) (hc : 0 < c) (hH : Continuous H)
    (hlo : ∀ q, c * Real.rpow (rho q) alpha ≤ H q)
    (hhom : ∀ s : ℝ, 0 < s → ∀ q,
      H (dilate s q) = Real.rpow s alpha * H q) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      volume (profileShell H alpha r) ≤ ENNReal.ofReal (C * r ^ (4 * d)) := by
  let m := volume {q : XV d | 1 ≤ H q ∧ H q ≤ 2}
  have hm : m < ⊤ := lt_of_le_of_lt
    (measure_mono (show {q : XV d | 1 ≤ H q ∧ H q ≤ 2} ⊆ {q | H q ≤ 2} from
      fun _ hq => hq.2))
    (profile_sublevel_volume_lt_top H alpha c 2 ha hc (by norm_num) hlo)
  refine ⟨m.toReal + 1, by positivity, ?_⟩
  intro r hr
  have _h_inl_10 : volume (profileShell H alpha r) =
      ENNReal.ofReal (r ^ (4 * d)) * volume {q | 1 ≤ H q ∧ H q ≤ 2} := by
      have hm : MeasurableSet {q : XV d | 1 ≤ H q ∧ H q ≤ 2} :=
        ((isClosed_le continuous_const hH).inter (isClosed_le hH continuous_const)).measurableSet
      have _h_inl_10 : profileShell H alpha r = dilate r⁻¹ ⁻¹' {q | 1 ≤ H q ∧ H q ≤ 2} := by
          ext q
          simp only [profileShell, mem_ofPred_eq, mem_preimage]
          rw [hhom r⁻¹ (inv_pos.mpr hr) q]
          simp only [Real.rpow_eq_pow]
          rw [Real.inv_rpow hr.le, inv_mul_eq_div]
          have hp := Real.rpow_pos_of_pos hr alpha
          constructor
          · rintro ⟨hlo, hhi⟩
            exact ⟨(le_div_iff₀ hp).2 (by simpa only [one_mul] using hlo),
              (div_le_iff₀ hp).2 hhi⟩
          · rintro ⟨hlo, hhi⟩
            exact ⟨by simpa only [one_mul] using (le_div_iff₀ hp).1 hlo,
              (div_le_iff₀ hp).1 hhi⟩

        /- The source shell has exactly the expected kinetic dilation factor. -/
      rw [_h_inl_10]
      have _h_xinl_0 : Measure.map (dilate (d := d) r⁻¹) volume = ENNReal.ofReal (r⁻¹⁻¹ ^ (4 * d)) • volume := by
        let r := r⁻¹
        have hr := (inv_pos.mpr hr)
        rw [Measure.volume_eq_prod]
        change Measure.map (Prod.map (fun x : PDE.Vec d => r ^ 3 • x)
          (fun v : PDE.Vec d => r • v)) ((volume : Measure (PDE.Vec d)).prod volume) = _
        rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
          Measure.map_addHaar_smul volume (pow_ne_zero 3 hr.ne'),
          Measure.map_addHaar_smul volume hr.ne',
          Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
          ← ENNReal.ofReal_mul (abs_nonneg _)]
        simp only [Module.finrank_pi, Fintype.card_fin]
        congr 2
        rw [abs_of_pos (inv_pos.mpr (pow_pos (pow_pos hr 3) _)),
          abs_of_pos (inv_pos.mpr (pow_pos hr _)), ← mul_inv, ← pow_mul,
          ← pow_add, inv_pow]
        congr 1
        ring
      rw [← Measure.map_apply (by unfold dilate; fun_prop) hm,
        _h_xinl_0, inv_inv,
        Measure.smul_apply, smul_eq_mul]

    /- A comparable homogeneous profile gives a radius-uniform shell-volume constant. -/
  rw [_h_inl_10,
    ENNReal.ofReal_mul (by positivity : 0 ≤ m.toReal + 1), mul_comm]
  exact mul_le_mul_left
    ((le_of_eq (ENNReal.ofReal_toReal hm.ne).symm).trans
      (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one))) _

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
