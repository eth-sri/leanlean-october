module

public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GeneralOpenH1ZeroLevel
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactInteriorH1ToH10
import PDEFoundation.Measure.LpDominatedConvergence
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure

@[expose] public noncomputable section

namespace PDE
open Filter MeasureTheory Topology
open scoped ENNReal


/-- Commuting the two arguments of a pointwise difference does not change its
`Lᵖ` extended norm. -/
theorem eLpNorm_sub_swap {d : ℕ} {μ : Measure (Vec d)}
    (a b : Vec d → ℝ) {p : ℝ≥0∞} :
    eLpNorm (fun x => a x - b x) p μ =
      eLpNorm (fun x => b x - a x) p μ := by
  rw [show (fun x => a x - b x) = -(fun x => b x - a x) from by
    funext x
    simp only [Pi.neg_apply]
    ring, eLpNorm_neg]

/-- **`H¹₀(U)` is closed under representative-level `H¹` limits.**

If an `H¹` representative is the coordinatewise `L²(volumeOn U)` limit of
representatives admitting supported smooth `H¹₀` approximations, then its
chosen representative belongs to `MemH10 U`. -/
theorem memH10_of_tendsto_H1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (f : H1Function U) (F : ℕ → H1Function U)
    (hmem : ∀ n, MemH10 U (F n).toFun)
    (hfun : Tendsto
      (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x)
        2 (volumeOn U))
      atTop (nhds 0))
    (hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => f.grad x i - (F n).grad x i)
        2 (volumeOn U))
      atTop (nhds 0)) :
    MemH10 U f.toFun := by
  classical
  set μU : Measure (Vec d) := volumeOn U with hμU
  choose W hW using hmem
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hbridge : ∀ n (i : Fin d),
      (fun x => (W n).toH1Function.grad x i) =ᵐ[μU]
        (fun x => (F n).grad x i) := by
    intro n i
    have hw := (W n).toH1Function.hasWeakGradient i
    rw [hW n] at hw
    exact HasWeakPartialDerivOn.ae_eq hU (hloc _ i) (hloc _ i) hw
      ((F n).hasWeakGradient i)
  set ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹ with hε
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simp only [hε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_tendsto : Tendsto ε atTop (nhds 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero).comp (tendsto_add_atTop_nat 1)
  have hex : ∀ n, ∃ k,
      eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x)
          2 μU < ε n ∧
      ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n := by
    intro n
    have e1 :=
      (W n).tendsto_approx.eventually_lt_const (hε_pos n)
    have e2 : ∀ i : Fin d, ∀ᶠ k in atTop,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      fun i => ((W n).tendsto_approx_grad i).eventually_lt_const (hε_pos n)
    have e2' :=
      Filter.eventually_all.2 e2
    exact (e1.and e2').exists
  choose k hk using hex
  set ψ : ℕ → Vec d → ℝ := fun n => (W n).approx (k n) with hψ
  have htf : Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x)
        2 μU) atTop (nhds 0) := by
    refine hfun.congr (fun n => ?_)
    rw [eLpNorm_sub_swap ((W n).toH1Function.toFun) (f.toFun), hW n]
  have hfun_bound : Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU)
      atTop (nhds 0) := by
    simpa using hε_tendsto.add htf
  have hgi : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i)
        2 μU) atTop (nhds 0) := by
    intro i
    refine (hgrad i).congr (fun n => ?_)
    rw [eLpNorm_sub_swap (fun x => (W n).toH1Function.grad x i)
      (fun x => f.grad x i)]
    exact eLpNorm_congr_ae (by
      filter_upwards [hbridge n i] with x hx
      rw [hx])
  have hgrad_bound : ∀ i : Fin d, Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU)
      atTop (nhds 0) := by
    intro i
    simpa using hε_tendsto.add (hgi i)
  refine ⟨{ toH1Function := f
            approx := ψ
            approx_smooth := fun n => (W n).approx_smooth (k n)
            approx_hasCompactSupport := fun n => (W n).approx_hasCompactSupport (k n)
            approx_support_subset := fun n => (W n).approx_support_subset (k n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfun_bound
      (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => ψ n x - f.toFun x) =
          (fun x => ψ n x - (W n).toH1Function.toFun x) +
            (fun x => (W n).toH1Function.toFun x - f.toFun x) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt (hk n).1) le_rfl
  · intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hgrad_bound i) (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - f.grad x i) =
          (fun x => (fderiv ℝ (ψ n) x) (basisVec i) -
            (W n).toH1Function.grad x i) +
            (fun x => (W n).toH1Function.grad x i - f.grad x i) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt ((hk n).2 i)) le_rfl

end PDE

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set
open scoped ENNReal Topology


/-- A smooth nonnegative zero-frontier barrier has a smooth compact H10 realization. -/
theorem exists_h10_smooth_barrier_eqOn {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (hcl : IsCompact (closure Ω)) (f : PDE.Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hn : ∀ x ∈ Ω, 0 ≤ f x) (hz : ∀ x ∈ frontier Ω, f x = 0) :
    ∃ q : PDE.H10Function Ω,
      ContDiff ℝ (⊤ : ℕ∞) q.toH1Function.toFun ∧
      HasCompactSupport q.toH1Function.toFun ∧
      EqOn q.toH1Function.toFun f (closure Ω)  := by
  have memH10_of_continuous_nonnegative_zero_frontier {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (hcl : IsCompact (closure Ω)) (f : PDE.H1Function Ω) (hc : Continuous f.toFun) (hn : ∀ x ∈ Ω, 0 ≤ f.toFun x) (hz : ∀ x ∈ frontier Ω, f.toFun x = 0) :
      PDE.MemH10 Ω f.toFun := by
    let μ := PDE.volumeOn Ω
    have hμ : IsFiniteMeasure μ := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono subset_closure).trans_lt hcl.measure_lt_top⟩
    let δ : ℕ → ℝ := fun n => 1 / (n + 1)
    have hδ : ∀ n, 0 < δ n := fun n => by dsimp [δ]; positivity
    have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    choose F hF hFg using fun n =>
      PDE.H1Function.exists_h1PositivePartSubConst_of_isOpen hΩ f (δ n) (hδ n).le
    have hmem : ∀ n, PDE.MemH10 Ω (F n).toFun := by
      intro n
      let K := closure Ω ∩ {x | δ n ≤ f.toFun x}
      have hK : IsCompact K := hcl.inter_right (isClosed_le continuous_const hc)
      have hKΩ : K ⊆ Ω := by
        intro x hx
        by_contra hxo
        have hxf : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx.1, hxo⟩
        have hh : δ n ≤ f.toFun x := hx.2
        rw [hz x hxf] at hh
        exact (not_le_of_gt (hδ n)) hh
      obtain ⟨q, hq⟩ := PDE.H1Function.exists_h10Function_of_ae_zero_outside_compact
        hΩ (F n) K hK hKΩ (by
          filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx hxn
          have hlt : f.toFun x < δ n := by
            by_contra hnlt
            exact hxn ⟨subset_closure hx, le_of_not_gt hnlt⟩
          rw [hF n]
          exact max_eq_right (sub_nonpos.mpr hlt.le))
      exact ⟨q, congrArg PDE.H1Function.toFun hq⟩
    have hval : Tendsto (fun n => eLpNorm ((F n).toFun - f.toFun) 2 μ)
        atTop (𝓝 0) := by
      apply PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
        (by norm_num) (by norm_num) (fun n => (F n).memL2.aestronglyMeasurable)
        f.memL2 f.memL2
      · intro n
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        rw [hF n]
        simp
        have hlo : 0 ≤ max (f.toFun x - δ n) 0 := le_max_right _ _
        rw [abs_of_nonneg hlo, abs_of_nonneg (hn x hx)]
        exact max_le (sub_le_self _ (hδ n).le) (hn x hx)
      · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        have ht : Tendsto (fun n => max (f.toFun x - δ n) 0) atTop
            (𝓝 (max (f.toFun x - 0) 0)) :=
          (tendsto_const_nhds.sub hδ0).max tendsto_const_nhds
        simpa [hF, max_eq_left (hn x hx)] using ht
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
        · rw [indicator_of_mem (show x ∈ {y | δ n < f.toFun y} from hx)]
        · rw [indicator_of_notMem (show x ∉ {y | δ n < f.toFun y} from hx)]
          simpa using norm_nonneg (f.grad x i)
      · filter_upwards [ae_restrict_mem hΩ.measurableSet,
          f.grad_ae_zero_on_zero_set_of_isOpen hΩ] with x hx hzgrad
        by_cases hp : 0 < f.toFun x
        · have hevent : ∀ᶠ n in atTop, δ n < f.toFun x := hδ0.eventually_lt_const hp
          apply (tendsto_congr' (hevent.mono fun n hnlt => ?_)).2 tendsto_const_nhds
          rw [hFg n]
          change ({y | δ n < f.toFun y}.indicator f.grad) x i = f.grad x i
          rw [indicator_of_mem (show x ∈ {y | δ n < f.toFun y} from hnlt)]
        · have hf0 : f.toFun x = 0 := le_antisymm (not_lt.mp hp) (hn x hx)
          have heq : (fun n => (F n).grad x i) = fun _ => f.grad x i := by
            funext n
            rw [hFg n]
            have hnot : ¬δ n < f.toFun x := by rw [hf0]; exact (hδ n).not_gt
            change ({y | δ n < f.toFun y}.indicator f.grad) x i = f.grad x i
            rw [indicator_of_notMem (show x ∉ {y | δ n < f.toFun y} from hnot), (congrFun (hzgrad hf0) i)]
          rw [heq]
          exact tendsto_const_nhds
    apply PDE.memH10_of_tendsto_H1 hΩ f F hmem
    · refine hval.congr (fun n => ?_)
      exact PDE.eLpNorm_sub_swap _ _
    · intro i
      refine (hgrad i).congr (fun n => ?_)
      exact PDE.eLpNorm_sub_swap _ _
  obtain ⟨χ, hχ, hχc, _, hχn, hχone⟩ :=
    KineticAleksandrov.SectionTwo.exists_smooth_cutoff hcl isOpen_univ (subset_univ _)
  let F : PDE.Vec d → ℝ := fun x => χ x * f x
  have hF := hχ.mul hf
  have hFc : HasCompactSupport F := hχc.mul_right
  let HΩ := ((PDE.H10Function.ofContDiff isOpen_univ hF hFc (subset_univ _)).toH1Function).restrict hΩ (subset_univ _)
  have hmem : PDE.MemH10 Ω HΩ.toFun := by
    apply memH10_of_continuous_nonnegative_zero_frontier hΩ hcl HΩ hF.continuous
    · intro x hx
      exact mul_nonneg (hχn x).1 (hn x hx)
    · intro x hx
      change χ x * f x = 0
      rw [hz x hx, mul_zero]
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_, ?_, ?_⟩
  · rw [hq]
    exact hF
  · rw [hq]
    exact hFc
  · intro x hx
    rw [hq]
    change χ x * f x = f x
    rw [hχone x hx, one_mul]

end HypoellipticAleksandrov.Parabolic.LocalHolder

