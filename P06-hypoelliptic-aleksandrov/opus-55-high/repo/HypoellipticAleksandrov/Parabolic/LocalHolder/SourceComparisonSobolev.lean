module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10OrderIdeal
import PDEFoundation.Measure.LpDominatedConvergence
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

/-! # Zero-boundary Sobolev certificates for continuous barriers

Strict positive level truncations have compact interior support. Their strong Sobolev
limit gives the zero-boundary certificate needed for variational source comparison.
-/

@[expose] public section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped ENNReal Topology

variable {d : ℕ} {Ω : Set (PDE.Vec d)}

/-- A continuous nonnegative H1 representative vanishing on the frontier belongs to H10. -/
theorem memH10_of_continuous_nonnegative_zero_frontier  (hΩ : IsOpen Ω) (hcl : IsCompact (closure Ω))
    (f : PDE.H1Function Ω) (hc : Continuous f.toFun)
    (hn : ∀ x ∈ Ω, 0 ≤ f.toFun x)
    (hz : ∀ x ∈ frontier Ω, f.toFun x = 0) : PDE.MemH10 Ω f.toFun := by
  let μ := PDE.volumeOn Ω
  have hμ : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hcl.measure_lt_top⟩
  let δ : ℕ → ℝ := fun n => 1 / (n + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose F hF hFg using fun n =>
    PDE.H1Function.exists_h1PositivePartSubConst_of_isOpen hΩ f _ (hδ n).le
  have hmem : ∀ n, PDE.MemH10 Ω (F n).toFun := by
    intro n
    let K  := closure Ω ∩ {x | δ n ≤ f.toFun x}
    have hK : IsCompact K := hcl.inter_right (isClosed_le continuous_const hc)
    have hKΩ : K ⊆ Ω := by
      intro x hx
      by_contra hxo
      have hxf : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; grind
      grind
    obtain ⟨q, hq⟩ := PDE.H1Function.exists_h10Function_of_ae_zero_outside_compact
      hΩ _ K hK hKΩ (by
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx hxn
        have hlt : f.toFun x < δ n := by
          by_contra hnlt
          exact hxn ⟨subset_closure hx, le_of_not_gt hnlt⟩
        rw [hF]
        exact max_eq_right (sub_nonpos.mpr hlt.le))
    exact ⟨q, congrArg PDE.H1Function.toFun hq⟩
  have hval : Tendsto (fun n => eLpNorm ((F n).toFun - f.toFun) 2 μ)
      atTop (𝓝 0) := by
    apply PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
      (by norm_num) (by norm_num) (fun n => (F n).memL2.aestronglyMeasurable)
      f.memL2 f.memL2
    · intro n
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [hF]
      simp only [Real.norm_eq_abs]
      grind
    · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have ht : Tendsto (fun n => max _ 0) atTop
          (𝓝 (max (f.toFun x - 0) 0)) :=
        (tendsto_const_nhds.sub hδ0).max tendsto_const_nhds
      simp_all
  have hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (F n).grad x i - f.grad x i) 2 μ)
      atTop (𝓝 0) := by
    intro i
    apply PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
      (by norm_num) (by norm_num) (fun n => ((F n).gradMemL2 i).aestronglyMeasurable)
      (f.gradMemL2 i) (f.gradMemL2 i)
    · intro n
      filter_upwards with x
      rw [hFg n]
      change ‖({y | δ n < f.toFun y}.indicator f.grad) x i‖ ≤ ‖f.grad x i‖
      by_cases hx : δ n < f.toFun x
      · simp_all
      simp_all
    · filter_upwards [ae_restrict_mem hΩ.measurableSet,
        f.grad_ae_zero_on_zero_set_of_isOpen hΩ] with x hx hzgrad
      by_cases hp : 0 < f.toFun x
      · have hevent : ∀ᶠ n in atTop, δ n < f.toFun x := hδ0.eventually_lt_const hp
        apply (tendsto_congr' (hevent.mono fun n hnlt => ?_)).2 tendsto_const_nhds
        simp_all
      · have hf0 : f.toFun x = 0 := le_antisymm (not_lt.mp hp) (hn x hx)
        have hg0 := congrFun (hzgrad hf0) i
        have heq : (fun n => (F n).grad x i) = fun _ => f.grad x i := by
          funext n
          rw [hFg]
          have hnot : ¬δ n < f.toFun x := by grind
          simp_all
        simp_all
  apply PDE.memH10_of_tendsto_H1 hΩ f F hmem
  · refine hval.congr (fun n => ?_)
    exact PDE.eLpNorm_sub_swap _ _
  · intro i
    refine (hgrad i).congr (fun n => ?_)
    exact PDE.eLpNorm_sub_swap _ _

/-- A smooth nonnegative zero-frontier barrier has a smooth compact H10 realization. -/
theorem exists_h10_smooth_barrier_eqOn 
    (hΩ : IsOpen Ω) (hcl : IsCompact (closure Ω)) (f : PDE.Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hn : ∀ x ∈ Ω, 0 ≤ f x) (hz : ∀ x ∈ frontier Ω, f x = 0) :
    ∃ q : PDE.H10Function Ω,
      ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
      HasCompactSupport q.toH1Function.toFun ∧
      EqOn q.toH1Function.toFun f (closure Ω) := by
  obtain ⟨χ, hχ, hχc, _, hχn, hχone⟩ :=
    KineticAleksandrov.SectionTwo.exists_smooth_cutoff hcl isOpen_univ (subset_univ _)
  let F  := fun x => χ x * f x
  have hF : ContDiff ℝ _ F := hχ.mul hf
  have hFc : HasCompactSupport F := hχc.mul_right
  let H := (PDE.H10Function.ofContDiff isOpen_univ hF hFc (subset_univ _)).toH1Function
  let HΩ := H.restrict hΩ (subset_univ _)
  have hmem : PDE.MemH10 Ω HΩ.toFun := by
    apply memH10_of_continuous_nonnegative_zero_frontier hΩ hcl HΩ hF.continuous
    · intro x hx
      exact mul_nonneg (hχn x).1 (hn x hx)
    aesop
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_, ?_, ?_⟩
  · aesop
  · aesop
  · intro x hx
    aesop

end HypoellipticAleksandrov.Parabolic.LocalHolder
