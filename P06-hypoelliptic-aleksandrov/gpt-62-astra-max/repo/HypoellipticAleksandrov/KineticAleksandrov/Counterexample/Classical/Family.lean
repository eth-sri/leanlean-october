module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Cylinder
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Classical.Rescaling
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionInterface
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SourceNorm
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionStationaryNorm
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyOperator
import Mathlib

/-! # Subcritical decay: amplitude times the `p`-th root of the core volume -/

@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
open MeasureTheory Set Filter Real
open scoped Topology ENNReal

variable {d : ℕ} {α : ℝ}

private theorem core_volume (d : ℕ) : ∃ V : ℝ, 0 < V ∧ ∀ r, 0 < r →
    volume {q : XV d | rho q ≤ r} ≤ ENNReal.ofReal (V*r^(4*d)) := by
  let D := {q : XV d | rho q ≤ 1}
  have hD := isCompact_rho_sublevel d 1
  refine ⟨(volume D).toReal + 1,by positivity,fun r hr => ?_⟩
  have e : {q : XV d | rho q ≤ r} = dilate r⁻¹ ⁻¹' D := by
    ext q; change _ ↔ rho (dilate r⁻¹ q) ≤ 1
    simp [rho_dilate _ (inv_pos.mpr hr),inv_mul_eq_div,div_le_one hr]
  rw [e,← Measure.map_apply (by unfold dilate; fun_prop) hD.measurableSet,map_dilate_volume _ _ (inv_pos.mpr hr),
    inv_inv,Measure.smul_apply,smul_eq_mul,mul_comm _ (r^_),ENNReal.ofReal_mul (by positivity)]
  gcongr; exact (ENNReal.ofReal_toReal hD.measure_lt_top.ne).symm.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

variable (m : ClassicalProfile d α)

theorem measurable_family {p : ℝ} (hd : 1 ≤ d) (hp : 0 < p) (ha : 0 < α)
    (he : 0 < α-2+4*(d:ℝ)/p) : ∃ S : ℝ, 0 < S ∧ MeasurableFamilyStatement d p m.lam m.Lam ⟨0,0,0⟩ S := by
  let k := ((d:ℝ)*m.lam)⁻¹
  have hdl : 0 < (d:ℝ)*m.lam := mul_pos (by exact_mod_cast (show 0 < d by omega)) m.hlam
  have hk := (inv_pos.mpr hdl).le
  obtain ⟨S,hS,hbd⟩ := m.exists_cylinder k hk ha
  let r (j : ℕ) := 1/((j:ℝ)+1)
  have hr j : 0 < r j := by dsimp [r]; positivity
  have hs (j : ℕ) : r j ≤ 1 := (div_le_one (by positivity : 0 < (j:ℝ)+1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hlim : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let U j := m.test S k (r j)
  have hu j := cappedQuad_smooth (1/S^2) (k/S^2) (m.regular_smooth (r j))
  refine ⟨S,hS,m.A,U,m.measurable,m.elliptic,hu,fun j P => timeCutoffTheta_nonneg _,
    fun j => hbd _ (hr j) (hs j),fun j => m.test_height hS k (r j),?_⟩
  obtain ⟨K,hK,herr⟩ := m.core_error
  obtain ⟨V,hV,hvol⟩ := core_volume d
  let C := (volume (Ioo (0-S^2) (0:ℝ))) ^ (1/p)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_Ioo_lt_top.ne
  let L := K * V^(1/p)
  have hp0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hpow := ((continuous_rpow_const he.le).tendsto (0:ℝ)).comp hlim
  have hlim' : Tendsto (fun j => C * ENNReal.ofReal (L * (r j)^(α-2+4*(d:ℝ)/p))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_rpow he.ne',mul_zero,ENNReal.ofReal_zero] using!
      ((ENNReal.continuous_const_mul hC).continuousAt.tendsto.comp (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hpow.const_mul L)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim' (fun _ => bot_le)
  intro j
  let D := {q : XV d | rho q ≤ r j}
  let B := K * (r j)^(α-2)
  let f := D.indicator fun _ => B
  have hB : 0 ≤ B := mul_nonneg hK (rpow_nonneg (hr j).le _)
  have hD : MeasurableSet D := (isClosed_le (continuous_rho _) continuous_const).measurableSet
  have hf : Measurable f := measurable_const.indicator hD
  have hn (q : XV d) : 0 ≤ f q := indicator_nonneg (fun _ _ => hB) _
  have hsp := Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) |>.ae (herr (r j) (hr j))
  have hkin := (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hsp
  have hm := (measurable_backwardOperator_of_joint_smooth m.A m.measurable (U j) (hu j)).max (measurable_const (a := (0 : ℝ)))
  apply (eLpNorm_mono_ae_real (g := fun P : KineticPoint d => f (P.position,P.velocity)) hm.aestronglyMeasurable ?_).trans
  · apply (construction_stationary_norm_le 0 S hS f hf _ hp0 ENNReal.ofReal_ne_top).trans
    simp only [ENNReal.toReal_ofReal hp.le]
    apply mul_le_mul_right
    change eLpNorm (D.indicator fun _ => B) _ _ ≤ _
    rw [eLpNorm_indicator_const hD.nullMeasurableSet hp0 ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp.le,
      ← ofReal_norm,Real.norm_of_nonneg hB]
    apply le_trans _ (source_norm_rpow_identity d α p V K (r j) hp hV hK (hr j)).le
    exact mul_le_mul_right (ENNReal.rpow_le_rpow (hvol _ (hr j)) (one_div_nonneg.mpr hp.le)) _
  · apply ae_restrict_of_ae
    filter_upwards [hkin] with P hP
    have hz : 1/S^2 ≤ k/S^2*2*((d:ℝ)*m.lam) := by
      rw [show k/S^2*2*((d:ℝ)*m.lam) = 2/S^2 by dsimp [k]; field_simp [m.hlam.ne']]
      gcongr; norm_num
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    exact max_le ((cappedQuad_le m _ _ (div_nonneg hk (sq_nonneg _)) hz (m.regular_smooth (r j)) P).trans
      (max_le hP (hn _))) (hn _)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ClassicalProfile
