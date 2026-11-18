module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceCutoff
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
public import Mathlib.Topology.Algebra.Indicator
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionTraceRepresentation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Function Metric MeasureTheory
open scoped Topology ProbabilityTheory ENNReal


/-- A classical solution restricted to any earlier state slice is continuous on the
closed state fiber. -/
theorem IsClassicalTerminalSolution.continuousOn_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r ≤ τ) :
    ContinuousOn (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (closure (evolutionStateSet Ω γ r)) := by
  refine hu.2.1.comp
    (KineticPoint.continuous_mk continuous_const continuous_fst continuous_snd).continuousOn ?_
  intro x hx
  have hx' : x ∈ closure (movingDomain Ω γ r) ×ˢ (univ : Set (PDE.Vec n)) := by
    simpa only [evolutionStateSet, closure_prod_eq, closure_univ] using hx
  exact ⟨hrτ, hx'.1⟩

/-- Extending an intermediate slice by zero outside its state fiber is continuous. -/
theorem IsClassicalTerminalSolution.continuous_zeroExtended_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r ≤ τ) :
    Continuous ((evolutionStateSet Ω γ r).indicator
      (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)) := by
  apply continuous_indicator ?_ (hu.continuousOn_slice hrτ)
  intro x hx
  have hx' : x ∈ frontier (movingDomain Ω γ r) ×ˢ (univ : Set (PDE.Vec n)) := by
    simpa only [evolutionStateSet, frontier_prod_univ_eq] using hx
  exact hu.2.2.2.2.2 ⟨r, x.1, x.2⟩ ⟨hrτ, hx'.1⟩

/-- A strictly earlier slice is smooth on the open state fiber. -/
theorem IsClassicalTerminalSolution.contDiffOn_slice
    {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r < τ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : EvolutionAmbientState n => u ⟨r, x.1, x.2⟩)
      (evolutionStateSet Ω γ r) := by
  exact hu.2.2.1.comp ((contDiff_const.prodMk contDiff_id).contDiffOn)
    (fun x hx => ⟨hrτ, hx.1⟩)

/-- Multiplying an interior-smooth function by an interior-supported smooth cutoff gives
an ambient smooth function, irrespective of the original function outside the open set. -/
theorem contDiff_mul_of_tsupport_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {χ g : E → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hs : tsupport χ ⊆ U) : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds (hs hx)))
  · have he : χ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    have hz : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : E => (0 : ℝ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]



/-- Sublevel sets of the quadratic norm weight are compact in finite dimension. -/
theorem isCompact_quadratic_weight_sublevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) : IsCompact {x : E | 1 + ‖x‖ ^ 2 ≤ R} := by
  apply (isCompact_closedBall (0 : E) (|R| + 1)).of_isClosed_subset
    (isClosed_le (continuous_const.add (continuous_norm.pow 2)) continuous_const)
  intro x hx
  rw [mem_closedBall_zero_iff]
  have hn := norm_nonneg x
  have hR := le_abs_self R
  have hs := sq_nonneg (‖x‖ - 1)
  have hr := abs_nonneg R
  have hx' : 1 + ‖x‖ ^ 2 ≤ R := hx
  nlinarith only [hn, hR, hs, hr, hx']

/-- The quadratic ambient norm weight is bounded by the actual Euclidean state weight. -/
theorem quadratic_state_weight_le_radial {n : ℕ} (r : ℝ) (x : EvolutionAmbientState n) :
    1 + ‖x‖ ^ 2 ≤ 1 + radialSq (⟨r, x.1, x.2⟩ : KineticPoint n) := by
  have hcomponent (y : PDE.Vec n) : ‖y‖ ^ 2 ≤ PDE.vecNormSq y := by
    rw [← PDE.vecEuclideanNorm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (PDE.vecEuclideanNorm_nonneg _)).mpr
      (PDE.norm_le_vecEuclideanNorm y)
  have h₁ := hcomponent x.1
  have h₂ := hcomponent x.2
  rw [Prod.norm_def]
  dsimp only [radialSq]
  rcases le_total ‖x.1‖ ‖x.2‖ with h | h
  · rw [max_eq_right h]
    linarith only [h₂, PDE.vecNormSq_nonneg x.1]
  · rw [max_eq_left h]
    linarith only [h₁, PDE.vecNormSq_nonneg x.2]



/-- A strictly earlier classical slice has smooth compact interior approximants with
an arbitrarily small Euclidean weighted error and the same uniform bound. -/
theorem IsClassicalTerminalSolution.exists_compact_slice_approximation
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
    {τ r C ε : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hrτ : r < τ)
    (hC0 : 0 ≤ C) (hC : ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C)
    (hε : 0 < ε) :
    ∃ G : BoundedBorel (EvolutionAmbientState n),
      IsSmoothCompactTerminalDatum Ω γ r G ∧ (∀ x, |G x| ≤ C) ∧
      ∀ p ∈ evolutionTerminalClosure Ω γ r,
        |u p - G (p.position, p.velocity)| ≤ ε * (1 + radialSq p) := by
  let U := evolutionStateSet Ω γ r
  let f : EvolutionAmbientState n → ℝ := fun x => u ⟨r, x.1, x.2⟩
  let g := U.indicator f
  have hU : IsOpen U := (isOpen_movingDomain hΩ r).prod isOpen_univ
  have hg : Continuous g := hu.continuous_zeroExtended_slice hrτ.le
  have hgb : ∀ x, |g x| ≤ C := by
    intro x
    dsimp only [g]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      exact hC ⟨r, x.1, x.2⟩ ⟨hrτ.le, subset_closure hx.1⟩
    · rw [indicator_of_notMem hx, abs_zero]
      exact hC0
  obtain ⟨χ, hχ, hc, hs, hr, herr⟩ := exists_smooth_cutoff_weighted_error hU g
    (fun x => 1 + ‖x‖ ^ 2) hg (continuous_const.add (continuous_norm.pow 2))
    (fun x => le_add_of_nonneg_right (sq_nonneg _))
    isCompact_quadratic_weight_sublevel (fun x hx => indicator_of_notMem hx f) hgb hε
  have heq : (fun x => χ x * g x) = (fun x => χ x * f x) := by
    funext x
    dsimp only [g]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
    · have hz : χ x = 0 := notMem_support.mp
        (fun hxχ => hx (hs (subset_closure hxχ)))
      rw [hz, zero_mul, zero_mul]
  have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * g x) := by
    rw [heq]
    exact contDiff_mul_of_tsupport_subset hU hχ (hu.contDiffOn_slice hrτ) hs
  have hbound : ∀ x, |χ x * g x| ≤ C := by
    intro x
    rw [abs_mul, abs_of_nonneg (hr x).1]
    exact (mul_le_mul_of_nonneg_right (hr x).2 (abs_nonneg _)).trans
      (by simpa only [one_mul] using hgb x)
  let G : BoundedBorel (EvolutionAmbientState n) :=
    ⟨fun x => χ x * g x, hprod.continuous.measurable, ⟨C, hC0, hbound⟩⟩
  refine ⟨G, ⟨hprod, hc.mul_right, tsupport_mul_subset_left.trans hs⟩, hbound, ?_⟩
  intro p hp
  have hgp : g (p.position, p.velocity) = u p := by
    dsimp only [g]
    by_cases hx : (p.position, p.velocity) ∈ U
    · rw [indicator_of_mem hx]
      change u ⟨r, p.position, p.velocity⟩ = u p
      congr 1
      exact KineticPoint.ext hp.1.symm rfl rfl
    · have hnot : p.position ∉ movingDomain Ω γ r :=
        fun hy => hx ⟨hy, mem_univ _⟩
      have hfr : p.position ∈ frontier (movingDomain Ω γ r) := by
        rw [(isOpen_movingDomain hΩ r).frontier_eq]
        exact ⟨hp.2, hnot⟩
      rw [indicator_of_notMem hx]
      exact (hu.2.2.2.2.2 p ⟨hp.1.trans_le hrτ.le, hp.1 ▸ hfr⟩).symm
  have hh := herr (p.position, p.velocity)
  rw [hgp] at hh
  have hw := quadratic_state_weight_le_radial r (p.position, p.velocity)
  have hpident : (⟨r, p.position, p.velocity⟩ : KineticPoint n) = p :=
    KineticPoint.ext hp.1.symm rfl rfl
  rw [hpident] at hw
  change |u p - χ (p.position, p.velocity) * g (p.position, p.velocity)| ≤ _
  rw [hgp]
  exact hh.trans (mul_le_mul_of_nonneg_left hw hε.le)



/-- A weighted terminal error between two classical solutions propagates to every
point of the earlier closed cylinder. The first solution may end at a later time. -/
theorem classical_intermediate_sub_le_growth
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {r τ δ : ℝ} (hrτ : r ≤ τ) (hδ : 0 ≤ δ)
    {F G : BoundedBorel (EvolutionAmbientState n)} {u v : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hv : IsClassicalTerminalSolution Ω γ B b r G v)
    (hterm : ∀ p ∈ evolutionTerminalClosure Ω γ r,
      u p - v p ≤ δ * (1 + radialSq p)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ r,
      u p - v p ≤ δ *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) r p := by
  have hu' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  have hv' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b r G v).2 hv
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  let Φ := growthBarrier (n := n) cg r
  have hcg : 0 ≤ cg := by
    dsimp [cg, growthConstant]
    have := PDE.vecEuclideanNorm_nonneg (b 0)
    positivity
  have hΦpos (p : KineticPoint n) : 0 ≤ Φ p := (growthBarrier_pos cg r p).le
  have hΦop (p : KineticPoint n) :
      viscousTransportedOperator B b 0 Φ p ≤ -Φ p :=
    viscousTransportedOperator_growthBarrier_le zero_le_one
      (fun t y z => (hB t y z).2) hb r p
  obtain ⟨C₁, _, hC₁⟩ := hu'.1
  obtain ⟨C₂, _, hC₂⟩ := hv'.1
  intro p₀ hp₀
  have hclosed (p : KineticPoint n) (hp : p ∈ movingClosedSlab Ω γ p₀.time r) :
      p ∈ evolutionPastClosedCylinder Ω γ r := ⟨hp.2.1, hp.2.2⟩
  have hlater (p : KineticPoint n) (hp : p ∈ movingClosedSlab Ω γ p₀.time r) :
      p ∈ evolutionPastClosedCylinder Ω γ τ := ⟨hp.2.1.trans hrτ, hp.2.2⟩
  have hopen (p : KineticPoint n) (hp : p ∈ movingActiveSlab Ω γ p₀.time r) :
      p ∈ evolutionPastOpenCylinder Ω γ r := ⟨hp.2.1, hp.2.2⟩
  have hlateopen (p : KineticPoint n) (hp : p ∈ movingActiveSlab Ω γ p₀.time r) :
      p ∈ evolutionPastOpenCylinder Ω γ τ := ⟨hp.2.1.trans_le hrτ, hp.2.2⟩
  have hureg (p : KineticPoint n) (hp : p ∈ movingActiveSlab Ω γ p₀.time r) :=
    hu'.isSliceRegularAt hΩ hγ (hlateopen p hp)
  have hvreg (p : KineticPoint n) (hp : p ∈ movingActiveSlab Ω γ p₀.time r) :=
    hv'.isSliceRegularAt hΩ hγ (hopen p hp)
  have hmax := growth_comparison hΩ hγ hlam hB hb (le_refl 0) zero_le_one
    (a := p₀.time) (T := r) (u := fun p => u p - v p - δ * Φ p)
    ?_ ?_ ?_ ?_ ?_ ?_ p₀ ⟨le_rfl, hp₀.1, hp₀.2⟩
  · linarith only [hmax]
  · refine ⟨C₁ + C₂, fun p hp => ?_⟩
    have h₁ := (abs_le.mp (hC₁ p (hlater p hp))).2
    have h₂ := (abs_le.mp (hC₂ p (hclosed p hp))).1
    have hnon := mul_nonneg hδ (hΦpos p)
    linarith only [h₁, h₂, hnon]
  · exact ((hu'.2.1.mono (fun p hp => hlater p hp)).sub
      (hv'.2.1.mono (fun p hp => hclosed p hp))).sub
      ((continuous_const.mul (continuous_growthBarrier cg r)).continuousOn)
  · intro p hp
    exact ((hureg p hp).sub (hvreg p hp)).sub
      ((isSliceRegularAt_growthBarrier cg r p).const_mul δ)
  · intro p hp
    rw [viscousTransportedOperator_sub ((hureg p hp).sub (hvreg p hp))
        ((isSliceRegularAt_growthBarrier cg r p).const_mul δ),
      viscousTransportedOperator_sub (hureg p hp) (hvreg p hp),
      hu'.2.2.2.1 p (hlateopen p hp), hv'.2.2.2.1 p (hopen p hp),
      viscousTransportedOperator_const_mul δ (isSliceRegularAt_growthBarrier cg r p)]
    have hnon := mul_nonpos_of_nonneg_of_nonpos hδ
      ((hΦop p).trans (neg_nonpos.mpr (hΦpos p)))
    linarith only [hnon]
  · intro p hp ht
    have he := hterm p ⟨ht, ht ▸ hp.2.2⟩
    have hg := one_add_radialSq_le_growthBarrier hcg hp.2.1
    have hbound := he.trans (mul_le_mul_of_nonneg_left hg hδ)
    linarith only [hbound]
  · intro p hp hfr
    rw [hu'.2.2.2.2.2 p ⟨hp.2.1.trans hrτ, hfr⟩,
      hv'.2.2.2.2.2 p ⟨hp.2.1, hfr⟩, sub_self]
    exact sub_nonpos.mpr (mul_nonneg hδ (hΦpos p))

/-- Absolute weighted terminal errors propagate under the same Euclidean growth barrier. -/
theorem classical_intermediate_abs_sub_le_growth
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam)
    {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B)
    {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n} (hb : HasEuclideanLipschitzDrift Lb b)
    {r τ δ : ℝ} (hrτ : r ≤ τ) (hδ : 0 ≤ δ)
    {F G : BoundedBorel (EvolutionAmbientState n)} {u v : KineticPoint n → ℝ}
    (hu : IsClassicalTerminalSolution Ω γ B b τ F u)
    (hv : IsClassicalTerminalSolution Ω γ B b r G v)
    (hterm : ∀ p ∈ evolutionTerminalClosure Ω γ r,
      |u p - v p| ≤ δ * (1 + radialSq p)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ r,
      |u p - v p| ≤ δ *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) r p := by
  have hupper := classical_intermediate_sub_le_growth hΩ hγ hlam hB hb hrτ hδ hu hv
    (fun p hp => (le_abs_self _).trans (hterm p hp))
  have hlower := classical_intermediate_sub_le_growth hΩ hγ hlam hB hb hrτ hδ
    (hu.smul hΩ hγ (-1)) (hv.smul hΩ hγ (-1)) (fun p hp => by
      have hh := (abs_le.mp (hterm p hp)).1
      linarith only [hh])
  intro p hp
  have hh := hlower p hp
  exact abs_le.mpr ⟨by linarith only [hh], hupper p hp⟩

section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal integral operators compose on smooth compact terminal data. -/
theorem terminalOperators_comp_smooth
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    P₀ σ τ (hσr.trans hrτ) (terminalStateDatum F) =
      P₀ σ r hσr (P₀ r τ hrτ (terminalStateDatum F)) := by
  have hself (t : ℝ) := (terminalOperators_basic n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx).1 t
  by_cases heq : r = τ
  · subst τ
    rw [hself]
    rfl
  have hrt : r < τ := lt_of_le_of_ne hrτ heq
  obtain ⟨C, hC0, hCF⟩ := F.exists_bound
  obtain ⟨u, hu, hCu, _⟩ := hEx τ F hF
  have hC := hCu C hC0 hCF
  have hrep (s : ℝ) (hst : s ≤ τ) (p : EvolutionState Ω γ s) :
      P₀ s τ hst (terminalStateDatum F) p = u ⟨s, p.1.1, p.1.2⟩ := by
    rw [terminalOperators_apply_smooth]
    exact terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      s τ hst p F hF u hu
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (j : ℕ) := hu.exists_compact_slice_approximation
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hrt hC0 hC (hε j)
  choose G hG hGC hGerr using hex
  have hvex (j : ℕ) := hEx r (G j) (hG j)
  choose v hv hvbound hvuniq using hvex
  have herr (j : ℕ) (p : KineticPoint n) (hp : p ∈ evolutionPastClosedCylinder Ω γ r) :
      |u p - v j p| ≤ ε j *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) L_b) r p := by
    apply classical_intermediate_abs_sub_le_growth
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hlam hB_ell hb_lipschitz
      hrτ (hε j).le hu (hv j) ?_ p hp
    intro q hq
    rw [(hv j).2.2.2.2.1 q hq]
    exact hGerr j q hq
  apply BoundedBorel.ext
  intro p
  have hp : (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n) ∈
      evolutionPastClosedCylinder Ω γ r := mk_mem_evolutionPastClosedCylinder hσr p
  have hvalues : Tendsto (fun j => v j ⟨σ, p.1.1, p.1.2⟩) atTop
      (𝓝 (u ⟨σ, p.1.1, p.1.2⟩)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs, abs_sub_comm]
    apply squeeze_zero (fun j => abs_nonneg _) (fun j => herr j _ hp)
    simpa only [zero_mul] using hεlim.mul_const
      (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) L_b)
        r (⟨σ, p.1.1, p.1.2⟩ : KineticPoint n))
  have hpoint (x : EvolutionState Ω γ r) :
      Tendsto (fun j => G j x.1) atTop (𝓝 (u ⟨r, x.1.1, x.1.2⟩)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [Real.norm_eq_abs, abs_sub_comm]
    apply squeeze_zero (fun j => abs_nonneg _)
      (fun j => hGerr j ⟨r, x.1.1, x.1.2⟩ ⟨rfl, subset_closure x.2.1⟩)
    simpa only [zero_mul] using hεlim.mul_const
      (1 + radialSq (⟨r, x.1.1, x.1.2⟩ : KineticPoint n))
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have hint := tendsto_integral_of_dominated_convergence (μ := κ σ r hσr p)
    (fun _ => C)
    (fun j => ((G j).measurable.comp measurable_subtype_coe).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using hGC j x.1)
    (Eventually.of_forall hpoint)
  have hlim : Tendsto (fun j => v j ⟨σ, p.1.1, p.1.2⟩) atTop
      (𝓝 (∫ x : EvolutionState Ω γ r, u ⟨r, x.1.1, x.1.2⟩ ∂(κ σ r hσr p))) := by
    have heval (j : ℕ) : v j ⟨σ, p.1.1, p.1.2⟩ =
        ∫ x : EvolutionState Ω γ r, G j x.1 ∂(κ σ r hσr p) := by
      rw [← terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ r hσr p (G j) (hG j) (v j) (hv j), ← terminalOperators_apply_smooth,
        terminalOperators_apply]
      rfl
    simpa only [heval, Function.comp_apply] using hint
  rw [hrep, terminalOperators_apply]
  have heq := tendsto_nhds_unique hvalues hlim
  exact heq.trans (integral_congr_ae (Eventually.of_forall fun x => (hrep r hrτ x).symm))

end EvolutionData

end


section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
variable (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω)
variable (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
variable (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
variable (hEx : ClassicalTerminalExistence Ω γ B b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive hEx

local notation "μ" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal fiber kernels satisfy pointwise composition. -/
theorem terminalFiberKernel_comp
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    κ σ τ (hσr.trans hrτ) = κ r τ hrτ ∘ₖ κ σ r hσr := by
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ
  apply ProbabilityTheory.Kernel.ext
  intro p
  let q := evolutionQueryOfState Ω γ σ τ (hσr.trans hrτ) p
  let ν := (κ r τ hrτ ∘ₖ κ σ r hσr) p
  let νa := ν.map ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)
  have hmass : νa univ ≤ 1 := by
    rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ]
    change (κ r τ hrτ ∘ₖ κ σ r hσr) p univ ≤ 1
    rw [ProbabilityTheory.Kernel.comp_apply' _ _ _ MeasurableSet.univ]
    calc
      (∫⁻ x, κ r τ hrτ x univ ∂(κ σ r hσr p)) ≤ ∫⁻ _x, 1 ∂(κ σ r hσr p) :=
        lintegral_mono fun x => terminalFiberKernel_univ_le_one n hn lam Lam m L_b
          hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
          hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ x
      _ = κ σ r hσr p univ := by rw [lintegral_const, one_mul]
      _ ≤ 1 := terminalFiberKernel_univ_le_one n hn lam Lam m L_b
        hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
        hb_smooth hb_lipschitz hb_coercive hEx σ r hσr p
  have hsupp : νa.restrict (evolutionStateSet Ω γ τ) = νa :=
    map_subtype_val_restrict (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ)) ν
  have hint (F : BoundedBorel (EvolutionAmbientState n))
      (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
      (∫ x, F x ∂νa) = terminalValue n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ τ (hσr.trans hrτ) p F hF := by
    rw [(MeasurableEmbedding.subtype_coe
      (measurableSet_evolutionStateSet_of_isOpen
        (isOpen_of_isAdmissibleEvolutionDomain hΩ))).integral_map]
    change (∫ x, terminalStateDatum F x ∂((κ r τ hrτ ∘ₖ κ σ r hσr) p)) = _
    rw [ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel (terminalStateDatum F) _)]
    simp_rw [← terminalOperators_apply]
    have hc := congrArg (fun f : BoundedBorel (EvolutionState Ω γ σ) => f p)
      (terminalOperators_comp_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
        hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
        σ r τ hσr hrτ F hF)
    rw [← hc]
    exact terminalOperators_apply_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      σ τ (hσr.trans hrτ) p F hF
  have heq := terminalMeasure_eq_of_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    q νa hmass hsupp hint
  have hm := congrArg (Measure.comap ((↑) : EvolutionState Ω γ τ → EvolutionAmbientState n)) heq
  rw [(MeasurableEmbedding.subtype_coe
    (measurableSet_evolutionStateSet_of_isOpen
      (isOpen_of_isAdmissibleEvolutionDomain hΩ))).comap_map] at hm
  exact hm.symm

/-- The terminal operators compose on every bounded Borel datum. -/
theorem terminalOperators_comp
    (σ r τ : ℝ) (hσr : σ ≤ r) (hrτ : r ≤ τ) :
    P₀ σ τ (hσr.trans hrτ) = (P₀ σ r hσr).comp (P₀ r τ hrτ) := by
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r hσr
  have := isFiniteKernel_terminalFiberKernel n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx r τ hrτ
  apply LinearMap.ext
  intro f
  apply BoundedBorel.ext
  intro p
  rw [terminalOperators_apply, terminalFiberKernel_comp n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx σ r τ hσr hrτ,
    ProbabilityTheory.Kernel.integral_comp (integrable_boundedBorel f _)]
  change _ = P₀ σ r hσr (P₀ r τ hrτ f) p
  rw [terminalOperators_apply]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (terminalOperators_apply n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      r τ hrτ f x).symm)

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

