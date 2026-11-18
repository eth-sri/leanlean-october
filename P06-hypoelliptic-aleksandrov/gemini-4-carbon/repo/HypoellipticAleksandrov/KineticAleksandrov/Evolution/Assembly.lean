module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBall
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyParameters
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSequence
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluing
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal
import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriers
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelSmoothTest
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelDense
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.AssemblyAssembly
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionKernel

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
open HypoellipticAleksandrov Set Filter MeasureTheory Evolution
open scoped Topology MatrixOrder
section

open HypoellipticAleksandrov Set Filter
open scoped Topology MatrixOrder

/-- A Euclidean radial cutoff lies strictly inside every larger diffused ball. -/
theorem mem_movingBall_of_radialSq_le {n : ℕ} {S r : ℝ} (hS : 0 ≤ S) (hr : S < r)
    {p : KineticPoint n} (hp : radialSq p ≤ S ^ 2) :
    p.position ∈ movingDomain (PDE.euclideanBall 0 r) (fun _ => 0) p.time := by
  have hsq : PDE.vecNormSq p.position ≤ S ^ 2 := by
    dsimp only [radialSq] at hp
    linarith [PDE.vecNormSq_nonneg p.velocity]
  have hn : PDE.vecEuclideanNorm p.position ≤ S := Real.sqrt_le_iff.mpr ⟨hS, hsq⟩
  apply (mem_movingBall_iff_norm_lt (hS.trans_lt hr)).mpr
  simpa using hn.trans_lt hr

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Actual expanding-ball solutions are uniformly Cauchy on every fixed bounded whole-space
cylinder, by the proved pure-growth comparison estimate. -/
theorem uniformCauchySeqOn_wholeSpace_ball_solutions :
    UniformCauchySeqOn v atTop
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2})  := by
  have abs_sub_le_growth_ball_solutions {n : ℕ} {lam : ℝ} {Lam : ℝ} {Lb : ℝ} {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam) (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b) {ε τ α S C : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hS : 0 ≤ S) (hC : 0 ≤ C) (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C) (r : Fin 2 → ℝ) (hr : ∀ i, S < r i) (v : Fin 2 → KineticPoint n → ℝ) (hv : ∀ i, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r i))
      (fun _ => 0) B b ε τ F (v i)) :
      ∀ p ∈ movingClosedSlab Set.univ (fun _ => 0) α τ ∩ {q | radialSq q ≤ S ^ 2},
      |v 0 p - v 1 p| ≤ 2 * C *
        (growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) τ p /
          (1 + S ^ 2)) := by
    let K := movingClosedSlab Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
      {q | radialSq q ≤ S ^ 2}
    let A := movingActiveSlab Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
      {q | radialSq q < S ^ 2}
    let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
    let Φ := growthBarrier (n := n) cg τ
    let k := 2 * C / (1 + S ^ 2)
    have hk : 0 ≤ k := by dsimp [k]; positivity
    have hcg : 0 ≤ cg := by
      dsimp [cg, growthConstant]
      have := PDE.vecEuclideanNorm_nonneg (b 0)
      positivity
    have hmem (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
        p.position ∈ movingDomain (PDE.euclideanBall 0 (r i)) (fun _ => 0) p.time := by
      have hsq : PDE.vecNormSq p.position ≤ S ^ 2 := by
        have ht : radialSq p ≤ S ^ 2 := hp.2
        dsimp only [radialSq] at ht
        linarith [PDE.vecNormSq_nonneg p.velocity]
      have hn : PDE.vecEuclideanNorm p.position ≤ S := Real.sqrt_le_iff.mpr ⟨hS, hsq⟩
      apply (mem_movingBall_iff_norm_lt (hS.trans_lt (hr i))).mpr
      simpa using hn.trans_lt (hr i)
    have hclosed (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) :
        p ∈ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r i)) (fun _ => 0) τ :=
      ⟨hp.1.2.1, subset_closure (hmem i p hp)⟩
    have hvc (i : Fin 2) : ContinuousOn (v i) K := (hv i).2.1.mono (hclosed i)
    have hAK : A ⊆ K := fun p hp =>
      ⟨⟨hp.1.1, hp.1.2.1.le, subset_closure hp.1.2.2⟩,
        (show radialSq p < S ^ 2 from hp.2).le⟩
    have hopen (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) :
        p ∈ evolutionPastOpenCylinder (PDE.euclideanBall 0 (r i)) (fun _ => 0) τ :=
      ⟨hp.1.2.1, hmem i p (hAK hp)⟩
    have hreg (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) : IsSliceRegularAt (v i) p :=
      (hv i).isSliceRegularAt (PDE.isOpen_euclideanBall 0 (r i)) continuous_const
        (hopen i p hp)
    have hop (i : Fin 2) (p : KineticPoint n) (hp : p ∈ A) :
        viscousTransportedOperator B b ε (v i) p = 0 := (hv i).2.2.2.1 p (hopen i p hp)
    have hbound (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) : |v i p| ≤ C :=
      classical_abs_le_const (PDE.isOpen_euclideanBall 0 (r i)) continuous_const
        hlam hB hb hε hε1 (hv i) hFC p (hclosed i p hp)
    have hterm (i : Fin 2) (p : KineticPoint n) (hp : p ∈ K) (ht : p.time = τ) :
        v i p = F (p.position, p.velocity) :=
      (hv i).2.2.2.2.1 p ⟨ht, by simpa only [ht] using (hclosed i p hp).2⟩
    have hΦreg (p : KineticPoint n) := isSliceRegularAt_growthBarrier cg τ p
    have hΦop (p : KineticPoint n) : viscousTransportedOperator B b ε Φ p ≤ -Φ p :=
      viscousTransportedOperator_growthBarrier_le hε1 (fun t y z => (hB t y z).2) hb τ p
    have hΦpos (p : KineticPoint n) : 0 < Φ p := growthBarrier_pos cg τ p
    have hwhole (t : ℝ) : movingDomain Set.univ (fun _ : ℝ => (0 : PDE.Vec n)) t = univ := by
      ext y
      rw [mem_movingDomain_iff]
      simp
    have side (s : ℝ) (hs : s = 1 ∨ s = -1) : ∀ p ∈ K,
        s * (v 0 p - v 1 p) ≤ k * Φ p := by
      have hmax := bounded_comparison (b := b) isOpen_univ continuous_const hlam hB hε
        (Ω := univ) (γ := fun _ => 0) (a := α) (T := τ) (R := S)
        (u := fun p => s * (v 0 p - v 1 p) - k * Φ p)
        ((((hvc 0).sub (hvc 1)).const_smul s).sub
          ((continuous_const.mul (continuous_growthBarrier cg τ)).continuousOn))
        ?_ ?_ ?_ ?_ ?_
      · intro p hp
        have := hmax p hp
        linarith
      · intro p hp
        exact (((hreg 0 p hp).sub (hreg 1 p hp)).const_mul s).sub ((hΦreg p).const_mul k)
      · intro p hp
        rw [viscousTransportedOperator_sub
            (((hreg 0 p hp).sub (hreg 1 p hp)).const_mul s) ((hΦreg p).const_mul k),
          viscousTransportedOperator_const_mul s ((hreg 0 p hp).sub (hreg 1 p hp)),
          viscousTransportedOperator_sub (hreg 0 p hp) (hreg 1 p hp), hop 0 p hp, hop 1 p hp,
          viscousTransportedOperator_const_mul k (hΦreg p)]
        have hn := mul_nonpos_of_nonneg_of_nonpos hk
          ((hΦop p).trans (by linarith [hΦpos p]))
        linarith
      · intro p hp ht
        rw [hterm 0 p hp ht, hterm 1 p hp ht, sub_self, mul_zero]
        simpa using neg_nonpos.mpr (mul_nonneg hk (hΦpos p).le)
      · intro p _ hfr
        rw [hwhole, frontier_univ] at hfr
        exact hfr.elim
      · intro p hp he
        have h0 := abs_le.mp (hbound 0 p hp)
        have h1 := abs_le.mp (hbound 1 p hp)
        have hdom := one_add_radialSq_le_growthBarrier hcg hp.1.2.1
        rw [he] at hdom
        have hb' : 2 * C ≤ k * Φ p := by
          dsimp only [k]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hdom (by positivity)
        rcases hs with rfl | rfl <;> linarith
    intro p hp
    have h0 := side 1 (Or.inl rfl) p hp
    have h1 := side (-1) (Or.inr rfl) p hp
    have he : k * Φ p = 2 * C * (Φ p / (1 + S ^ 2)) := by dsimp [k]; ring
    rw [he] at h0 h1
    exact abs_le.mpr ⟨by linarith, by simpa using h0⟩
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb
  obtain ⟨M0, hM0⟩ := (isCompact_movingClosedSlab_inter (Ω := univ)
    (γ := fun _ : ℝ => 0) continuous_const α τ S0).bddAbove_image
    (continuous_growthBarrier cg τ).continuousOn
  let M := max M0 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ : ∀ p ∈ (movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩ {p | radialSq p ≤ S0 ^ 2}), growthBarrier cg τ p ≤ M :=
    fun p hp => (hM0 ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro e he
  obtain ⟨δ, A, S, hδ, -, -, hA, -, -, hS, herr⟩ :=
    exists_small_dirichlet_comparison_parameters (κ := 1) (d := 1) (δ0 := 1) (r0 := 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num) (by norm_num) (by norm_num) hC hM he S0
  have hw : 0 ≤ barrierW 1 (δ + 3 / 2 * A) / barrierW 1 1 :=
    div_nonneg (barrierW_pos (by norm_num) (by linarith)).le
      (barrierW_pos (by norm_num) (by norm_num)).le
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hrlim.eventually (eventually_gt_atTop |S|))
  refine ⟨N, ?_⟩
  intro j hj k hk p hp
  let ix (i : Fin 2) := if i = 0 then j else k
  have hix (i : Fin 2) : N ≤ ix i := by dsimp [ix]; split_ifs <;> assumption
  have hpS : p ∈ movingClosedSlab univ (fun _ => 0) α τ ∩
      {q | radialSq q ≤ |S| ^ 2} := ⟨hp.1, by
        rw [sq_abs]
        exact (show radialSq p ≤ S0 ^ 2 from hp.2).trans hS⟩
  have hden : 0 ≤ 1 + S ^ 2 := by positivity
  have hfinal := (abs_sub_le_growth_ball_solutions hlam hB hb hε hε1 (abs_nonneg S) hC F hFC (fun i => r (ix i)) (fun i => hN _ (hix i)) (fun i => v (ix i)) (fun i => hv _) p hpS).trans_lt (by
    rw [sq_abs]
    exact (mul_le_mul_of_nonneg_left
      ((div_le_div_of_nonneg_right (hΦ p hp) hden).trans (le_add_of_nonneg_right hw)) (by positivity)).trans_lt herr)
  have h10 : 1 ≠ 0 := by decide
  simpa [ix, h10, Real.dist_eq] using hfinal

/-- Actual expanding-ball solutions converge uniformly to one bounded continuous limit
on every fixed whole-space cylinder. -/
theorem tendstoUniformlyOn_wholeSpace_ball_solutions :
    TendstoUniformlyOn v (fun p => limUnder atTop (fun j => v j p)) atTop
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) ∧
    ContinuousOn (fun p => limUnder atTop (fun j => v j p))
      (movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) ∧
    ∀ p ∈ movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2},
      |limUnder atTop (fun j => v j p)| ≤ C := by
  have hCau := uniformCauchySeqOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv
  have hU := hCau.tendstoUniformlyOn_of_tendsto
    (f := fun p => limUnder atTop (fun j => v j p))
    (fun p hp => (hCau.cauchySeq hp).tendsto_limUnder)
  have hnear :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hclosed (j : ℕ) (hj : |S0| < r j) :
      (movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩ {p | radialSq p ≤ S0 ^ 2}) ⊆ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r j)) (fun _ => 0) τ :=
    fun p hp => ⟨hp.1.2.1, subset_closure (mem_movingBall_of_radialSq_le
      (abs_nonneg S0) hj (by simpa using (show radialSq p ≤ S0 ^ 2 from hp.2)))⟩
  refine ⟨hU, hU.continuousOn ?_, fun p hp => ?_⟩
  · exact (hnear.mono fun j hj => (hv j).2.1.mono (hclosed j hj)).frequently
  · apply le_of_tendsto (hU.tendsto_at hp |>.abs)
    exact hnear.mono fun j hj => classical_abs_le_const
      (PDE.isOpen_euclideanBall 0 (r j)) continuous_const hlam hB hb hε hε1
      (hv j) hFC p (hclosed j hj hp)

end Data

end


/-- A strict bounded whole-space cylinder, using the explicit Euclidean radial cutoff. -/
def wholeSpaceInnerCylinder {n : ℕ} (α τ S : ℝ) : Set (KineticPoint n) :=
  {p | α < p.time ∧ p.time < τ ∧ radialSq p < S ^ 2}

/-- Strict bounded whole-space cylinders are open. -/
theorem isOpen_wholeSpaceInnerCylinder {n : ℕ} (α τ S : ℝ) :
    IsOpen (wholeSpaceInnerCylinder (n := n) α τ S) :=
  (isOpen_lt continuous_const continuous_time).inter
    ((isOpen_lt continuous_time continuous_const).inter
      (isOpen_lt continuous_radialSq continuous_const))

/-- The strict whole-space cylinder lies in its compact closed counterpart. -/
theorem wholeSpaceInnerCylinder_subset_closed {n : ℕ} (α τ S : ℝ) :
    wholeSpaceInnerCylinder (n := n) α τ S ⊆
      movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S ^ 2} := by
  intro p hp
  have hm : p.position ∈ movingDomain univ (fun _ : ℝ => 0) p.time :=
    mem_movingDomain_iff.mpr (mem_univ _)
  exact ⟨⟨hp.1.le, hp.2.1.le, subset_closure hm⟩, hp.2.2.le⟩

/-- Compact radial cylinders are relative neighbourhoods of all points of a whole-space
closed slab, including its time faces. -/
theorem exists_wholeSpace_closedCylinder_mem_nhdsWithin {n : ℕ} {α τ : ℝ}
    {p : KineticPoint n}
    (_hp : p ∈ movingClosedSlab univ (fun _ => 0) α τ) :
    ∃ S : ℝ, 0 < S ∧ radialSq p < S ^ 2 ∧
      (movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
        {p | radialSq p ≤ S ^ 2}) ∈
        𝓝[movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ] p := by
  let S := radialSq p + 1
  have hrad0 : 0 ≤ radialSq p :=
    add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
  have hS : 0 < S := by dsimp [S]; linarith
  have hrad : radialSq p < S ^ 2 := by dsimp [S]; nlinarith
  refine ⟨S, hS, hrad, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    (continuous_radialSq.continuousAt.eventually (gt_mem_nhds hrad)).filter_mono
      nhdsWithin_le_nhds] with q hq hrq
  exact ⟨hq, hrq.le⟩

section

open HypoellipticAleksandrov Set Filter MeasureTheory
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Integration against a continuous test on a fixed bounded whole-space cylinder
commutes with the actual expanding-ball limit. -/
theorem tendsto_setIntegral_mul_wholeSpace_ball_solutions
    (φ : KineticPoint n → ℝ) (hφ : Continuous φ) :
    Tendsto (fun j => ∫ p in movingClosedSlab univ (fun _ => 0) α τ ∩
      {p | radialSq p ≤ S0 ^ 2}, v j p * φ p) atTop
      (𝓝 (∫ p in movingClosedSlab univ (fun _ => 0) α τ ∩ {p | radialSq p ≤ S0 ^ 2},
        limUnder atTop (fun j => v j p) * φ p)) := by
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hK : IsCompact K := isCompact_movingClosedSlab_inter continuous_const α τ S0
  have hnear :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hclosed (j : ℕ) (hj : |S0| < r j) :
      K ⊆ evolutionPastClosedCylinder (PDE.euclideanBall 0 (r j)) (fun _ => 0) τ :=
    fun p hp => ⟨hp.1.2.1, subset_closure (mem_movingBall_of_radialSq_le
      (abs_nonneg S0) hj (by simpa using (show radialSq p ≤ S0 ^ 2 from hp.2)))⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun p => C * |φ p|)
  · exact hnear.mono fun j hj => ((hv j).2.1.mono (hclosed j hj) |>.mul
      hφ.continuousOn).aestronglyMeasurable hK.measurableSet
  · refine hnear.mono fun j hj => ?_
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (classical_abs_le_const (PDE.isOpen_euclideanBall 0 (r j)) continuous_const hlam hB hb hε hε1 (hv j) hFC p (hclosed j hj hp)) (abs_nonneg _)
  · exact (continuous_const.mul hφ.abs).continuousOn.integrableOn_compact hK
  · filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact (((tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0) hlam hB hb hε hε1 hC F hFC r hrlim v hv).1).tendsto_at hp).mul tendsto_const_nhds

end Data

end
section

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- The actual expanding-ball limit satisfies the regularized weak equation on
strict bounded whole-space cylinders. No weak equation or limit estimate is assumed. -/
theorem weakRegularized_wholeSpace_ball_limit :
    IsKineticWeakRegularizedSolution B b ε (wholeSpaceInnerCylinder α τ S0)
      (fun p => limUnder atTop (fun j => v j p)) (fun _ => 0) := by
  let U := wholeSpaceInnerCylinder (n := n) α τ S0
  let K := movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
    {p | radialSq p ≤ S0 ^ 2}
  have hU : IsOpen U := isOpen_wholeSpaceInnerCylinder α τ S0
  have hUK : U ⊆ K := wholeSpaceInnerCylinder_subset_closed α τ S0
  refine ⟨((tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0) hlam hB hb hε.le hε1 hC F hFC r hrlim v hv).2.1.mono hUK).locallyIntegrableOn hU.measurableSet, ?_⟩
  intro ψ hψ hc hs
  let φ (p : KineticPoint n) := regularizedAdjoint B b ε ψ
    ((evolutionHomeomorph n).symm p)
  have hφ : Continuous φ := (contDiff_regularizedAdjoint hBs hbs hψ ε).continuous.comp
    (evolutionHomeomorph n).symm.continuous
  have hzeroU (p : KineticPoint n) (hp : p ∉ U) : φ p = 0 := by
    apply regularizedAdjoint_eq_zero_of_notMem_tsupport
    intro hx
    exact hp (by simpa using hs hx)
  have hzeroK (p : KineticPoint n) (hp : p ∉ K) : φ p = 0 :=
    hzeroU p (fun h => hp (hUK h))
  have hnear : ∀ᶠ j : ℕ in atTop, |S0| < r j :=
    hrlim.eventually (eventually_gt_atTop |S0|)
  have hIz : ∀ᶠ j : ℕ in atTop, (∫ p in K, v j p * φ p) = 0 := by
    filter_upwards [hnear] with j hj
    let V := evolutionHomeomorph n ⁻¹' U
    have hV : IsOpen V := hU.preimage (evolutionHomeomorph n).continuous
    have hball (p : KineticPoint n) (hp : p ∈ U) :
        p.position ∈ movingDomain (PDE.euclideanBall 0 (r j)) (fun _ => 0) p.time :=
      mem_movingBall_of_radialSq_le (abs_nonneg S0) hj
        (by simpa using (show radialSq p < S0 ^ 2 from hp.2.2).le)
    have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (v j ∘ evolutionHomeomorph n) V := by
      exact (hv j).2.2.1.comp (evolutionProdCLE n).contDiff.contDiffOn
        (fun x hx => ⟨hx.2.1, hball _ hx⟩)
    have hop : ∀ x ∈ V, regularizedOperator B b ε (v j ∘ evolutionHomeomorph n) x = 0 := by
      intro x hx
      have hc2 : ContDiffAt ℝ 2 (v j ∘ evolutionHomeomorph n) x :=
        (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
      rw [regularizedOperator_comp ε hc2]
      exact (hv j).2.2.2.1 _ ⟨hx.2.1, hball _ hx⟩
    have hePack : (∫ x in V, v j (evolutionHomeomorph n x) *
        regularizedAdjoint B b ε ψ x) = 0 := by
      change (∫ x in V, (v j ∘ evolutionHomeomorph n) x *
        regularizedAdjoint B b ε ψ x) = 0
      rw [integral_regularizedAdjoint_contDiffOn hV hBs hBsym hbs ε hsm ψ hψ hc hs]
      have he : (∫ x in V, regularizedOperator B b ε
          (v j ∘ evolutionHomeomorph n) x * ψ x) = ∫ x in V, 0 :=
        setIntegral_congr_fun hV.measurableSet
        (fun x hx => by rw [hop x hx, zero_mul])
      exact he.trans (by simp)
    have heU : (∫ p in U, v j p * φ p) = 0 := by
      have ht := setIntegral_comp_evolutionHomeomorph (fun p => v j p * φ p) U
      simp only [φ, Homeomorph.symm_apply_apply] at ht
      exact ht.symm.trans hePack
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroK p hp, mul_zero])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun p hp => by rw [hzeroU p hp, mul_zero])] at heU
    exact heU
  have heLim : (∫ p in K, limUnder atTop (fun j => v j p) * φ p) = 0 :=
    tendsto_nhds_unique (tendsto_setIntegral_mul_wholeSpace_ball_solutions (α := α) (S0 := S0) hlam hB hb hε.le hε1 hC F hFC r hrlim v hv φ hφ) (tendsto_const_nhds.congr' (hIz.mono fun j hj => hj.symm))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroK p hp, mul_zero])] at heLim
  simp
  change (∫ p in U, limUnder atTop (fun j => v j p) * φ p) = 0
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun p hp => by rw [hzeroU p hp, mul_zero])]
  exact heLim

end Data

end
section

open HypoellipticAleksandrov Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- Relative to the explicit Hörmander input, the actual whole-space ball limit
is smooth and satisfies the pointwise viscous equation on each bounded inner cylinder. -/
theorem classical_wholeSpace_ball_limit (hH : HormanderHypoellipticityStatement) :
    ContDiffOn ℝ (⊤ : ℕ∞) ((fun p => limUnder atTop (fun j => v j p)) ∘
      evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' wholeSpaceInnerCylinder α τ S0) ∧
    ∀ p ∈ wholeSpaceInnerCylinder α τ S0,
      viscousTransportedOperator B b ε (fun p => limUnder atTop (fun j => v j p)) p = 0 := by
  let U := wholeSpaceInnerCylinder (n := n) α τ S0
  let f (p : KineticPoint n) := limUnder atTop (fun j => v j p)
  have hU : IsOpen U := isOpen_wholeSpaceInnerCylinder α τ S0
  have hV : IsOpen (evolutionHomeomorph n ⁻¹' U) := hU.preimage
    (evolutionHomeomorph n).continuous
  have hw := weakRegularized_wholeSpace_ball_limit (α := α) (S0 := S0)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs
  obtain ⟨w, hws, hae⟩ := exists_smooth_viscous_kinetic_representative
    hH hlam hBs hB hbs U hU ε hε f hw
  have hcf : ContinuousOn f U :=
    (tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S0)
      hlam hB hb hε.le hε1 hC F hFC r hrlim v hv).2.1.mono
        (wholeSpaceInnerCylinder_subset_closed α τ S0)
  have hcPack : ContinuousOn (f ∘ evolutionHomeomorph n) (evolutionHomeomorph n ⁻¹' U) :=
    hcf.comp (evolutionHomeomorph n).continuous.continuousOn (fun _ hx => hx)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ evolutionHomeomorph n)
      (evolutionHomeomorph n ⁻¹' U) := hws.congr (fun _ hx => (eqOn_of_ae_eq_of_continuousOn_kinetic hU hcPack hws.continuousOn hae) hx)
  have hOp := regularizedOperator_eq_zero_of_smooth_weak hV hBs hBsym hbs ε hsm ((isWeakRegularizedSolution_comp_iff B b ε U f (fun _ => 0)).mpr hw)
  refine ⟨hsm, ?_⟩
  intro p hp
  let x := (evolutionHomeomorph n).symm p
  have hx : x ∈ evolutionHomeomorph n ⁻¹' U := by
    change evolutionHomeomorph n x ∈ U
    simpa only [x, Homeomorph.apply_symm_apply] using hp
  have hc2 : ContDiffAt ℝ 2 (f ∘ evolutionHomeomorph n) x :=
    (hsm.contDiffAt (hV.mem_nhds hx)).of_le (by norm_num)
  have hz := hOp x hx
  rw [regularizedOperator_comp ε hc2] at hz
  simpa only [x, Homeomorph.apply_symm_apply, viscousTransportedOperator] using hz

end Data

end


/-- Translating the whole diffused space leaves the actual moving domain equal to univ. -/
theorem movingDomain_univ_eq {n : ℕ} (Γ : ℝ → PDE.Vec n) (t : ℝ) :
    movingDomain univ Γ t = univ := by
  ext y
  rw [mem_movingDomain_iff]
  simp

section Data

variable {n : ℕ} {lam Lam Lb : ℝ} {B : FullKineticCoefficient n}
variable {b : PDE.Vec n → PDE.Vec n} (hlam : 0 < lam)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hb : HasEuclideanLipschitzDrift Lb b)
variable {ε τ α S0 C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 ≤ C)
variable (F : BoundedBorel (EvolutionAmbientState n)) (hFC : ∀ q, |F q| ≤ C)
variable (r : ℕ → ℝ) (hrlim : Tendsto r atTop atTop) (v : ℕ → KineticPoint n → ℝ)
variable (hv : ∀ j, IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
  (fun _ => 0) B b ε τ F (v j))
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hbs : IsSmoothDrift b)
include hBs hBsym hbs
include hlam hB hb hε hε1 hC hFC hrlim hv

/-- The actual expanding-ball limit is a bounded classical whole-space solution,
including its exact terminal values, relative to the explicit Hörmander input. -/
theorem isClassicalViscousTerminalSolution_wholeSpace_ball_limit
    (hH : HormanderHypoellipticityStatement) :
    IsClassicalViscousTerminalSolution univ (fun _ => 0) B b ε τ F
      (fun p => limUnder atTop (fun j => v j p)) ∧
    ∀ p ∈ evolutionPastClosedCylinder univ (fun _ => 0) τ,
      |limUnder atTop (fun j => v j p)| ≤ C := by
  let f (p : KineticPoint n) := limUnder atTop (fun j => v j p)
  have hUnif (α S : ℝ) := tendstoUniformlyOn_wholeSpace_ball_solutions (α := α) (S0 := S)
    hlam hB hb hε.le hε1 hC F hFC r hrlim v hv
  have hLocal (α S : ℝ) := classical_wholeSpace_ball_limit (α := α) (S0 := S)
    hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs hH
  have hcl (p : KineticPoint n) (hp : p.time ≤ τ) :
      p ∈ movingClosedSlab univ (fun _ => 0) (p.time - 1) τ := by
    refine ⟨by linarith, hp, ?_⟩
    rw [movingDomain_univ_eq, closure_univ]
    trivial
  have hbnd : ∀ p ∈ evolutionPastClosedCylinder univ (fun _ => 0) τ, |f p| ≤ C := by
    intro p hp
    obtain ⟨S, -, hrad, -⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin (hcl p hp.1)
    exact (hUnif (p.time - 1) S).2.2 p ⟨hcl p hp.1, hrad.le⟩
  refine ⟨⟨⟨C, hC, hbnd⟩, ?_, ?_, ?_, ?_, ?_⟩, hbnd⟩
  · intro p hp
    let α := p.time - 1
    obtain ⟨S, -, hrad, hKmem⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin (hcl p hp.1)
    have hc := (hUnif α S).2.1 p ⟨hcl p hp.1, hrad.le⟩
    have hslab : movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∈
        𝓝[evolutionPastClosedCylinder univ (fun _ => 0) τ] p := by
      filter_upwards [self_mem_nhdsWithin,
        (continuous_time.continuousAt.eventually (lt_mem_nhds (by
          dsimp [α]; linarith : α < p.time))).filter_mono nhdsWithin_le_nhds]
        with q hq ht
      exact ⟨ht.le, hq.1, hq.2⟩
    have hKe : ∀ᶠ q in 𝓝[movingClosedSlab univ
        (fun _ : ℝ => (0 : PDE.Vec n)) α τ] p,
        q ∈ movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
          {p | radialSq p ≤ S ^ 2} := hKmem
    exact hc.mono_of_mem_nhdsWithin (hKe.filter_mono (nhdsWithin_le_of_mem hslab))
  · intro q hq
    let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
    let α := p.time - 1
    let S := radialSq p + 1
    have hrad0 : 0 ≤ radialSq p :=
      add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    have hpU : p ∈ wholeSpaceInnerCylinder α τ S :=
      ⟨by dsimp [α]; linarith, hq.1, by dsimp [S]; nlinarith⟩
    let x := (evolutionProdCLE n).symm q
    have hxp : evolutionHomeomorph n x = p := by
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    have hx : x ∈ evolutionHomeomorph n ⁻¹' wholeSpaceInnerCylinder α τ S := by
      change evolutionHomeomorph n x ∈ wholeSpaceInnerCylinder α τ S
      rw [hxp]
      exact hpU
    have hc := ((hLocal α S).1.contDiffAt (((isOpen_wholeSpaceInnerCylinder (n := n) α τ S).preimage (evolutionHomeomorph n).continuous).mem_nhds hx)).comp q
      (evolutionProdCLE n).symm.contDiff.contDiffAt
    have hfun : (f ∘ evolutionHomeomorph n) ∘ (evolutionProdCLE n).symm =
        fun q => f ⟨q.1, q.2.1, q.2.2⟩ := by
      funext q
      change f (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) = f ⟨q.1, q.2.1, q.2.2⟩
      apply congrArg f
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    change ContDiffAt ℝ (⊤ : ℕ∞) ((f ∘ evolutionHomeomorph n) ∘
      (evolutionProdCLE n).symm) q at hc
    rw [hfun] at hc
    exact hc.contDiffWithinAt
  · intro p hp
    let S := radialSq p + 1
    have hrad0 : 0 ≤ radialSq p :=
      add_nonneg (PDE.vecNormSq_nonneg _) (PDE.vecNormSq_nonneg _)
    exact (hLocal (p.time - 1) S).2 p
      ⟨by linarith, hp.1, by dsimp [S]; nlinarith⟩
  · intro p hp
    let α := τ - 1
    obtain ⟨S, -, hrad, -⟩ := exists_wholeSpace_closedCylinder_mem_nhdsWithin
      (hcl p hp.1.le)
    have hpK : p ∈ movingClosedSlab univ (fun _ : ℝ => (0 : PDE.Vec n)) α τ ∩
        {p | radialSq p ≤ S ^ 2} := by
      refine ⟨⟨by dsimp [α]; rw [hp.1]; linarith, hp.1.le, ?_⟩, hrad.le⟩
      rw [movingDomain_univ_eq, closure_univ]
      trivial
    have he : ∀ᶠ j : ℕ in atTop, v j p = F (p.position, p.velocity) := by
      filter_upwards [hrlim.eventually (eventually_gt_atTop |S|)] with j hj
      have hi := mem_movingBall_of_radialSq_le (abs_nonneg S) hj
        (by simpa using hrad.le)
      exact (hv j).2.2.2.2.1 p
        ⟨hp.1, by simpa only [hp.1] using subset_closure hi⟩
    exact tendsto_nhds_unique ((hUnif α S).1.tendsto_at hpK)
      (tendsto_const_nhds.congr' (he.mono fun j hj => hj.symm))
  · intro p hp
    have hfr := hp.2
    rw [movingDomain_univ_eq, frontier_univ] at hfr
    exact hfr.elim

end Data

end
section
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder


/-- A moving ball with centre c is the zero-centred ball moved by the curve Γ + c. -/
theorem movingDomain_ball_add_const {n : ℕ} (c : PDE.Vec n) (r0 : ℝ)
    (Γ : ℝ → PDE.Vec n) (σ : ℝ) :
    movingDomain (PDE.euclideanBall c r0) Γ σ =
      movingDomain (PDE.euclideanBall 0 r0) (fun s => Γ s + c) σ := by
  ext y
  simp [mem_movingDomain_euclideanBall_iff]

/-- Moving the constant ball centre into the centre curve preserves the entire
classical viscous terminal-solution predicate, with coefficients and operator unchanged. -/
theorem isClassicalViscousTerminalSolution_ball_add_const_iff {n : ℕ}
    (c : PDE.Vec n) (r0 : ℝ) (Γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) (v : KineticPoint n → ℝ) :
    IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F v ↔
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 r0)
        (fun s => Γ s + c) B b ε τ F v := by
  simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
    evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
    evolutionLateralFrontier, movingDomain_ball_add_const c r0 Γ]

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {c : PDE.Vec n}
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) {r0 : ℝ} (hr0 : 0 < r0)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ hr0

/-- The ball branch of the exhaustion limit with arbitrary centre: actual bounded classical
viscous evolution and uniqueness, relative to explicit Lieberman and Hörmander inputs. -/
theorem exists_viscous_terminalSolution_ball
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r0) Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution (PDE.euclideanBall c r0) Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ))  := by
  have piecewiseC1_add_const {n : ℕ} {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ) (c : PDE.Vec n) :
      IsContinuousPiecewiseC1 (fun t => Γ t + c) := by
    refine ⟨hΓ.1.add continuous_const, fun a b hab => ?_⟩
    obtain ⟨N, t, ht, h0, hl, hpiece⟩ := hΓ.2 a b hab
    exact ⟨N, t, ht, h0, hl, fun i => (hpiece i).add contDiffOn_const⟩
  have hF0 : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 r0)
      (fun s => Γ s + c) τ F := by
    simpa only [IsSmoothCompactTerminalDatum, evolutionStateSet,
      movingDomain_ball_add_const c r0 Γ] using hF
  obtain ⟨v, hv, hbound, huniq⟩ := exists_viscous_terminalSolution_innerBall
    hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco (piecewiseC1_add_const hΓ c) hr0
    τ F hF0 ε hε hε1 C hC hFC
  have hK : evolutionPastClosedCylinder (PDE.euclideanBall c r0) Γ τ =
      evolutionPastClosedCylinder (PDE.euclideanBall 0 r0) (fun s => Γ s + c) τ := by
    simp only [evolutionPastClosedCylinder, movingDomain_ball_add_const c r0 Γ]
  refine ⟨v, (isClassicalViscousTerminalSolution_ball_add_const_iff
    c r0 Γ B b ε τ F v).mpr hv, ?_, ?_⟩
  · simpa only [hK] using hbound
  · intro w hw
    simpa only [hK] using huniq w ((isClassicalViscousTerminalSolution_ball_add_const_iff c r0 Γ B b ε τ F w).mp hw)

end Data

end
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ

/-- The interval branch of the exhaustion limit follows from its exact Euclidean-ball
identification, with the source constants, operator and terminal datum preserved. -/
theorem exists_viscous_terminalSolution_interval
    (hN : n = 1) (Ω : Set (PDE.Vec n)) (lo hi : ℝ) (hlohi : lo < hi)
    (hΩ : hN ▸ Ω = PDE.oneDimensionalAxisBox lo hi)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution Ω Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder Ω Γ τ)) := by
  cases hN
  have hΩ' : Ω = PDE.oneDimensionalAxisBox lo hi := by simpa using hΩ
  rw [hΩ', oneDimensionalAxisBox_eq_euclideanBall hlohi] at hF ⊢
  exact exists_viscous_terminalSolution_ball hLE hH hn hlam hlamLam hm hmLb
    hBs hBsym hB hbs hb hbco hΓ (show 0 < (hi - lo) / 2 by linarith)
    τ F hF ε hε hε1 C hC hFC

end Data

end
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter Evolution
open scoped Topology MatrixOrder

section Data

variable (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
variable {n : ℕ} (hn : 1 ≤ n) {lam Lam m Lb : ℝ}
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ Lb)
variable {B : FullKineticCoefficient n} {b : PDE.Vec n → PDE.Vec n}
variable (hBs : IsSmoothFullKineticCoefficient B) (hBsym : IsSymmetricFullKineticCoefficient B)
variable (hB : HasEverywhereLoewnerBounds lam Lam B) (hbs : IsSmoothDrift b)
variable (hb : HasEuclideanLipschitzDrift Lb b) (hbco : HasUnitDirectionDriftCoercivity m b)
variable {Γ : ℝ → PDE.Vec n} (hΓ : IsContinuousPiecewiseC1 Γ)

include hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ

/-- The whole-space branch of Actual bounded classical viscous evolution,
relative only to the two analytic hypotheses. -/
theorem exists_viscous_terminalSolution_wholeSpace
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum univ Γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution univ Γ B b ε τ F v ∧
      (∀ p ∈ evolutionPastClosedCylinder univ Γ τ, |v p| ≤ C) ∧
      (∀ w : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution univ Γ B b ε τ F w →
          EqOn w v (evolutionPastClosedCylinder univ Γ τ)) := by
  obtain ⟨Z0, hZ0⟩ := hF.2.1.bddAbove_image
    (PDE.continuous_vecEuclideanNorm.comp continuous_fst).continuousOn
  let Z := max Z0 0
  have hZ : 0 ≤ Z := le_max_right _ _
  let r (j : ℕ) := Z + (j : ℝ) + 1
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrZ (j : ℕ) : Z < r j := by
    dsimp [r]
    have := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hrlim : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun j => by dsimp [r]; linarith) tendsto_natCast_atTop_atTop
  have hΓ0 : IsContinuousPiecewiseC1 (fun _ : ℝ => (0 : PDE.Vec n)) :=
    isContinuousPiecewiseC1_of_contDiff contDiff_const
  have hex (j : ℕ) : ∃ v : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution (PDE.euclideanBall 0 (r j))
        (fun _ => 0) B b ε τ F v := by
    have hFj : IsSmoothCompactTerminalDatum (PDE.euclideanBall 0 (r j))
        (fun _ => 0) τ F := by
      refine ⟨hF.1, hF.2.1, fun q hq => ⟨?_, mem_univ _⟩⟩
      apply (mem_movingBall_iff_norm_lt (hr j)).mpr
      simp
      exact ((hZ0 ⟨q, hq, rfl⟩).trans (le_max_left _ _)).trans_lt (hrZ j)
    obtain ⟨v, hv, -, -⟩ := exists_viscous_terminalSolution_innerBall
      hLE hH hn hlam hlamLam hm hmLb hBs hBsym hB hbs hb hbco hΓ0 (hr j)
      τ F hFj ε hε hε1 C hC hFC
    exact ⟨v, hv⟩
  choose v hv using hex
  obtain ⟨hf, hbound⟩ := isClassicalViscousTerminalSolution_wholeSpace_ball_limit
    hlam hB hb hε hε1 hC F hFC r hrlim v hv hBs hBsym hbs hH
  have hsame (w : KineticPoint n → ℝ) :
      IsClassicalViscousTerminalSolution univ Γ B b ε τ F w ↔
        IsClassicalViscousTerminalSolution univ (fun _ => 0) B b ε τ F w := by
    simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
      evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
      evolutionLateralFrontier, movingDomain_univ_eq]
  have hK : evolutionPastClosedCylinder univ Γ τ =
      evolutionPastClosedCylinder univ (fun _ : ℝ => (0 : PDE.Vec n)) τ := by
    simp only [evolutionPastClosedCylinder, movingDomain_univ_eq]
  have hfΓ := (hsame _).mpr hf
  refine ⟨fun p => limUnder atTop (fun j => v j p), hfΓ, ?_, ?_⟩
  · simpa only [hK] using hbound
  · intro w hw
    exact classical_unique isOpen_univ hΓ.1 hlam hB hb hε.le hε1 hw hfΓ

end Data

end

open HypoellipticAleksandrov Set
open scoped MatrixOrder

section EvolutionData

variable (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
variable (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
variable (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
variable (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
variable (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
variable (hB_smooth : IsSmoothFullKineticCoefficient B)
variable (hB_symm : IsSymmetricFullKineticCoefficient B)
variable (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b)
variable (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
variable (hb_coercive : HasUnitDirectionDriftCoercivity m b)
include hn hlam hlamLam hm hmLb hΩ hγ hB_smooth hB_symm hB_ell
include hb_smooth hb_lipschitz hb_coercive

/-- **Exhaustion limit.** Actual bounded classical viscous terminal
solutions exist and are unique on every admissible moving domain, relative
only to the two explicit hypotheses. -/
theorem exists_viscous_terminalSolution
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) (hFC : ∀ q, |F q| ≤ C) :
    ∃ u : KineticPoint n → ℝ,
      IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
      (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
  rcases hΩ with hWhole | ⟨c, r, hr, hBall⟩ | ⟨hN, lo, hi, hlohi, hInterval⟩
  · rw [hWhole] at hF ⊢
    exact exists_viscous_terminalSolution_wholeSpace hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ
      τ F hF ε hε hε1 C hC hFC
  · rw [hBall] at hF ⊢
    exact exists_viscous_terminalSolution_ball hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ hr
      τ F hF ε hε hε1 C hC hFC
  · exact exists_viscous_terminalSolution_interval hLE hH hn hlam hlamLam hm hmLb
      hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hγ
      hN Ω lo hi hlohi hInterval τ F hF ε hε hε1 C hC hFC

end EvolutionData

end
open HypoellipticAleksandrov Set Filter Classical HypoellipticAleksandrov.Parabolic MeasureTheory Evolution
open scoped Topology MatrixOrder ProbabilityTheory

/-- An interior continuous function extends continuously when its boundary traces converge
uniformly to a supplied continuous boundary function. -/
theorem continuousOn_interior_patch {α : Type*} [TopologicalSpace α]
    (U S : Set α) (hU : IsOpen U) (hUS : U ⊆ S) (V w : α → ℝ)
    (hV : ContinuousOn V U) (hw : ContinuousOn w S)
    (htrace : ∀ p ∈ S, p ∉ U → ∀ η : ℝ, 0 < η →
      ∃ O : Set α, IsOpen O ∧ p ∈ O ∧ ∀ q ∈ O ∩ U, |V q - w p| ≤ η) :
    ContinuousOn (fun p => if p ∈ U then V p else w p) S := by
  classical
  intro p hp
  by_cases hi : p ∈ U
  · have he : (fun q => if q ∈ U then V q else w q) =ᶠ[𝓝 p] V := by
      filter_upwards [hU.mem_nhds hi] with q hq
      simp only [ite_eq_left hq]
    exact ((hV p hi).continuousAt (hU.mem_nhds hi)).continuousWithinAt.congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) (by simp [hi])
  · have _hUS := hUS
    change Tendsto _ (𝓝[S] p) (𝓝 _)
    simp only [ite_eq_right hi]
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨O, hO, hpO, hbound⟩ := htrace p hp hi (η / 2) (by positivity)
    have hw' := Metric.tendsto_nhds.mp (hw p hp) η hη
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hpO), hw'] with q hq hqw
    by_cases hqi : q ∈ U
    · rw [ite_eq_left hqi, Real.dist_eq]
      exact (hbound q ⟨hq, hqi⟩).trans_lt (by linarith)
    · simpa only [ite_eq_right hqi] using hqw



/-- The moving domain over the whole space is the whole space. -/
theorem movingDomain_univ {n : ℕ} (γ : ℝ → PDE.Vec n) (σ : ℝ) :
    movingDomain (Set.univ : Set (PDE.Vec n)) γ σ = Set.univ := by
  ext y
  simp [mem_movingDomain_iff]

/-- Over the whole space the viscous classical-solution predicate does not depend on the curve. -/
theorem isClassicalViscousTerminalSolution_univ_curve_congr {n : ℕ} (γ γ' : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (ε τ : ℝ)
    (F : BoundedBorel (EvolutionAmbientState n)) (u : KineticPoint n → ℝ) :
    IsClassicalViscousTerminalSolution (Set.univ : Set (PDE.Vec n)) γ B b ε τ F u ↔
      IsClassicalViscousTerminalSolution (Set.univ : Set (PDE.Vec n)) γ' B b ε τ F u := by
  simp only [IsClassicalViscousTerminalSolution, evolutionPastClosedCylinder,
    evolutionPastInteriorRaw, evolutionPastOpenCylinder, evolutionTerminalClosure,
    evolutionLateralFrontier, movingDomain_univ]

/-- Over the whole space the closed moving slab does not depend on the curve. -/
theorem movingClosedSlab_univ_curve_congr {n : ℕ} (γ γ' : ℝ → PDE.Vec n) (a τ : ℝ) :
    movingClosedSlab (Set.univ : Set (PDE.Vec n)) γ a τ =
      movingClosedSlab (Set.univ : Set (PDE.Vec n)) γ' a τ := by
  simp only [movingClosedSlab, movingDomain_univ]

/-- **Two barriers** (companion paper, (A.1), `Ω = ℝⁿ`).  Whole-space terminal comparison on a
finite slab: `|u_ε - F| ≤ (τ - σ) M` wherever `|L_ε F| ≤ M` on the slab.  There is no lateral
clause. -/
theorem wholeSpace_terminalDatum_bound {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b)
    (hwhole : Ω = Set.univ) (a τ : ℝ) (haτ : a < τ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ movingClosedSlab Ω γ a τ,
      |viscousTransportedOperator B b ε
        (fun q => F (q.position, q.velocity)) p| ≤ M)
    (u : KineticPoint n → ℝ)
    (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) :
    ∀ p ∈ movingClosedSlab Ω γ a τ,
      |u p - F (p.position, p.velocity)| ≤ (τ - p.time) * M := by
  subst hwhole
  obtain ⟨FB, -, hFB⟩ := F.exists_bound
  have hS := movingClosedSlab_univ_curve_congr (n := n) γ (fun _ => 0) a τ
  have hfr : ∀ q : KineticPoint n,
      q.position ∉ frontier (movingDomain (Set.univ : Set (PDE.Vec n)) (fun _ => 0) q.time) := by
    intro q
    rw [movingDomain_univ, frontier_univ]
    exact notMem_empty _
  rw [hS]
  exact classical_sub_terminalDatum_le_core_of_slab isOpen_univ continuous_const hlam hB hb hε
    hε1 hF.1 hFB (a := a) (by rw [hS] at hM; exact hM) ((isClassicalViscousTerminalSolution_univ_curve_congr γ (fun _ => 0) B b ε τ F u).mp hu) (fun q _ hq => absurd hq (hfr q))




/-- Terminal trace from a uniform terminal window: if `|u_i - F| ≤ (τ - σ) M` for all `i` on the
past cylinder near the terminal time, then the terminal trace at a terminal point is uniform. -/
theorem terminal_trace_of_window {n : ℕ} {ι : Type*} {Ω : Set (PDE.Vec n)}
    {γ : ℝ → PDE.Vec n} {τ : ℝ} (F : BoundedBorel (EvolutionAmbientState n))
    (hF : Continuous (F : EvolutionAmbientState n → ℝ)) (u : ι → KineticPoint n → ℝ)
    {M δ₀ : ℝ} (hM0 : 0 ≤ M) (hδ₀ : 0 < δ₀)
    (hwin : ∀ i, ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, τ - δ₀ < p.time →
      |u i p - F (p.position, p.velocity)| ≤ (τ - p.time) * M)
    {p₀ : KineticPoint n} (hp₀ : p₀.time = τ) {η : ℝ} (hη : 0 < η) :
    ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
      ∀ i, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
        |u i p - F (p₀.position, p₀.velocity)| ≤ η := by
  have hK : 0 < η / (2 * (M + 1)) := by positivity
  set δ := min δ₀ (η / (2 * (M + 1))) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ hK
  have hFe : Continuous (fun p : KineticPoint n => F (p.position, p.velocity)) :=
    hF.comp (continuous_position.prodMk continuous_velocity)
  refine ⟨{p | τ - δ < p.time} ∩
    {p | |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2}, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_time).inter
      (isOpen_lt ((hFe.sub continuous_const).abs) continuous_const)
  · refine ⟨?_, ?_⟩
    · show τ - δ < p₀.time
      rw [hp₀]
      linarith
    · show |F (p₀.position, p₀.velocity) - F (p₀.position, p₀.velocity)| < η / 2
      simp
      linarith
  · rintro i p ⟨⟨hpt, hpF⟩, hcyl⟩
    have hpt' : τ - δ < p.time := hpt
    have hpF' : |F (p.position, p.velocity) - F (p₀.position, p₀.velocity)| < η / 2 := hpF
    have hδ₀le : δ ≤ δ₀ := min_le_left _ _
    have hδKle : δ ≤ η / (2 * (M + 1)) := min_le_right _ _
    have h1 := hwin i p hcyl (by linarith)
    have h2 : (τ - p.time) * M ≤ δ * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    have h3 : δ * M ≤ η / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right hδKle hM0
    have h4 : η / (2 * (M + 1)) * M ≤ η / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h5 := abs_sub_le (u i p) (F (p.position, p.velocity)) (F (p₀.position, p₀.velocity))
    linarith

/-- **Uniform traces** (companion paper, (A.1), zero-viscosity part).  Uniform terminal and lateral
traces for the family of actual viscous solutions: for every terminal point `p₀` and tolerance `η`
there is a neighbourhood `O` of `p₀`, independent of `ε ∈ (0, 1]`, on which `|u_ε - F(p₀)| ≤ η`
(past cylinder), and likewise `|u_ε| ≤ η` near every lateral frontier point.  The standing premises
(`Ω` admissible, `γ` continuous piecewise `C¹`, the Loewner bounds of `B`, the Lipschitz drift)
are explicit. -/
theorem uniform_viscous_boundary_traces {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n}
    (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.Vec n → PDE.Vec n}
    (hb : HasEuclideanLipschitzDrift Lb b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F)
    (u : {ε : ℝ // 0 < ε ∧ ε ≤ 1} → KineticPoint n → ℝ)
    (hu : ∀ ε, IsClassicalViscousTerminalSolution Ω γ B b ε.1 τ F (u ε)) :
    (∀ p₀ ∈ evolutionTerminalClosure Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |u ε p - F (p₀.position, p₀.velocity)| ≤ η) ∧
    (∀ p₀ ∈ evolutionLateralFrontier Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |u ε p| ≤ η)  := by
  have exists_collar_scale {c : PDE.Vec n} {r : ℝ} (hr : 0 < r) {γ : ℝ → PDE.Vec n} {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} (hF : IsSmoothCompactTerminalDatum (PDE.euclideanBall c r) γ τ F) :
      ∃ d : ℝ, 0 < d ∧ d < r / 4 ∧ ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
      2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - (γ τ + c)) := by
    have hcpt : IsCompact (tsupport (F : EvolutionAmbientState n → ℝ)) := hF.2.1.isCompact
    have hcont : Continuous (fun q : EvolutionAmbientState n =>
        r - PDE.vecEuclideanNorm (q.1 - (γ τ + c))) :=
      continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
        (continuous_fst.sub continuous_const))
    obtain ⟨m, hm, hmle⟩ := hcpt.exists_forall_le' (a := 0) hcont.continuousOn (fun q hq => by
      have h1 : q.1 ∈ movingDomain (PDE.euclideanBall c r) γ τ := (hF.2.2 hq).1
      have h2 := mem_movingDomain_euclideanBall_iff.mp h1
      have h3 : PDE.vecEuclideanNorm (q.1 - (γ τ + c)) < r := by
        unfold PDE.vecEuclideanNorm
        exact (Real.sqrt_lt' hr).mpr h2
      linarith)
    refine ⟨min (m / 2) (r / 8), lt_min (by linarith) (by linarith),
      lt_of_le_of_lt (min_le_right _ _) (by linarith), fun q hq => ?_⟩
    have := hmle q hq
    have h2 : min (m / 2) (r / 8) ≤ m / 2 := min_le_left _ _
    linarith
  obtain ⟨M, hM0, hM⟩ := exists_uniform_terminalDatum_operator_bound hlam hB hb τ F hF
  obtain ⟨C, -, hC⟩ := F.exists_bound
  have hFc : Continuous (F : EvolutionAmbientState n → ℝ) := hF.1.continuous
  rcases eq_univ_or_exists_euclideanBall_of_isAdmissibleEvolutionDomain hΩ with
    rfl | ⟨c, r, hr, rfl⟩
  · refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
    · refine terminal_trace_of_window F hFc u hM0 one_pos (fun i p hp ht => ?_) hp₀.1 hη
      exact wholeSpace_terminalDatum_bound hlam hB hb rfl (τ - 1) τ (by linarith) F hF i.1
        i.2.1.le i.2.2 M hM0 (fun q _ => hM i.1 i.2.1.le i.2.2 q) (u i) (hu i) p
        ⟨by linarith, hp.1, hp.2⟩
    · exfalso
      have h := hp₀.2
      rw [movingDomain_univ, frontier_univ] at h
      exact notMem_empty _ h
  · obtain ⟨d, hd, hdr, hsupp⟩ := exists_collar_scale hr hF
    refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
    · obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ (τ - 1) τ (by linarith)
      have hL1 : 0 < d / (1 + L) := div_pos hd (by linarith)
      refine terminal_trace_of_window F hFc u hM0 (lt_min one_pos hL1)
        (fun i p hp ht => ?_) hp₀.1 hη
      have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (τ - 1) τ :=
        ⟨by linarith [min_le_left (1 : ℝ) (d / (1 + L))], hp.1, hp.2⟩
      exact (two_barriers_on_finite_slab hr hγ (τ - 1) τ (by linarith) L hL hγL hlam hB hb
        i.2.1.le i.2.2 hF d hd hdr hsupp C M hC (fun q _ => hM i.1 i.2.1.le i.2.2 q)
        (hu i)).2 p hslab (by linarith [min_le_right (1 : ℝ) (d / (1 + L))])
    · have hpτ : p₀.time ≤ τ := hp₀.1
      obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ (p₀.time - 1) τ
        (by linarith)
      have hκ : 0 < collarKappa L lam := div_pos (by linarith) hlam
      have hW : 0 < barrierW (collarKappa L lam) d := barrierW_pos hκ hd
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
      have hDc : Continuous (fun p : KineticPoint n =>
          r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) :=
        continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
          (continuous_position.sub ((hγ.1.comp continuous_time).add continuous_const)))
      have hwc : Continuous (barrierW (collarKappa L lam)) := by
        unfold barrierW
        fun_prop
      have hD0 : r - PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c)) = 0 := by
        have hS := vecNormSq_eq_of_mem_frontier_movingDomain hp₀.2
        have : PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c)) = r := by
          unfold PDE.vecEuclideanNorm
          rw [hS, Real.sqrt_sq hr.le]
        linarith
      have hw0 : barrierW (collarKappa L lam) 0 = 0 := by simp [barrierW]
      refine ⟨{p | p₀.time - 1 < p.time} ∩
        {p | C * barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) <
            η * barrierW (collarKappa L lam) d}, ?_,
        ⟨(by show p₀.time - 1 < p₀.time; linarith), ?_⟩, ?_⟩
      · exact (isOpen_lt continuous_const continuous_time).inter
          (isOpen_lt (continuous_const.mul (hwc.comp hDc)) continuous_const)
      · show C * barrierW (collarKappa L lam)
          (r - PDE.vecEuclideanNorm (p₀.position - (γ p₀.time + c))) <
            η * barrierW (collarKappa L lam) d
        rw [hD0, hw0, mul_zero]
        exact mul_pos hη hW
      · rintro i p ⟨⟨hpt, hpD⟩, hcyl⟩
        have hpt' : p₀.time - 1 < p.time := hpt
        have hpD' : C * barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) <
              η * barrierW (collarKappa L lam) d := hpD
        have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (p₀.time - 1) τ :=
          ⟨hpt'.le, hcyl.1, hcyl.2⟩
        have h1 := (two_barriers_on_finite_slab hr hγ (p₀.time - 1) τ (by linarith) L hL hγL
          hlam hB hb i.2.1.le i.2.2 hF d hd hdr hsupp C M hC
          (fun q _ => hM i.1 i.2.1.le i.2.2 q) (hu i)).1 p hslab
        have h2 : C * min 1 (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) ≤
            C * (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hC0
        have h3 : C * (barrierW (collarKappa L lam)
            (r - PDE.vecEuclideanNorm (p.position - (γ p.time + c))) /
              barrierW (collarKappa L lam) d) < η := by
          rw [← mul_div_assoc, div_lt_iff₀ hW]
          exact hpD'
        linarith





/-- The existence premise used for the terminal point value and its consumers is discharged
by the existence theorem above, with only the same two hypotheses. -/
theorem classicalTerminalExistence_holds
    (n : ℕ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement)
    : ClassicalTerminalExistence Ω γ B b   := by
  have exists_classical_terminalSolution_of_viscous (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) (hB_smooth : IsSmoothFullKineticCoefficient B) (hB_symm : IsSymmetricFullKineticCoefficient B) (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b) (hb_coercive : HasUnitDirectionDriftCoercivity m b) (hvisc : ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
      IsSmoothCompactTerminalDatum Ω γ τ F → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (C : ℝ), 0 ≤ C → (∀ q, |F q| ≤ C) →
      ∃ u : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
        (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
        (∀ v : KineticPoint n → ℝ,
          IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
            EqOn v u (evolutionPastClosedCylinder Ω γ τ))) (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
      ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
    let : SecondCountableTopology (KineticPoint n) :=
      (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
    obtain ⟨C, hC, hFC⟩ := F.exists_bound
    let family (ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}) :=
      (hvisc τ F hF ε.1 ε.2.1 ε.2.2 C hC hFC).choose
    have hfamily (ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}) :=
      (hvisc τ F hF ε.1 ε.2.1 ε.2.2 C hC hFC).choose_spec
    let seqε (j : ℕ) : {ε : ℝ // 0 < ε ∧ ε ≤ 1} :=
      ⟨1 / ((j : ℝ) + 1), by
        constructor
        · positivity
        · exact (div_le_one (by positivity)).mpr (by
            have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            linarith)⟩
    let v := fun j => family (seqε j)
    let w := family ⟨1, one_pos, le_rfl⟩
    have hw : IsClassicalViscousTerminalSolution Ω γ B b 1 τ F w := (hfamily _).1
    have hΩo := isOpen_of_isAdmissibleEvolutionDomain hΩ
    let U := evolutionPastOpenCylinder Ω γ τ
    let S := evolutionPastClosedCylinder Ω γ τ
    have hU := isOpen_evolutionPastOpenCylinder hΩo hγ.1 τ
    have hUS : U ⊆ S := fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
    obtain ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, hVC, hVE⟩ :=
      exists_smooth_viscosity_sequence_limit hH n hn lam Lam m L_b
        hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
        hb_lipschitz hb_coercive τ F C hC v
        (fun j => (hfamily (seqε j)).1) (fun j => (hfamily (seqε j)).2.1)
    have hva : ∀ j, AEStronglyMeasurable (v (ν j)) (volume.restrict U) := fun j =>
      (((hfamily (seqε (ν j))).1.2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
    have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v (ν j) p| ≤ C := fun j => by
      filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      exact (hfamily (seqε (ν j))).2.1 p (hUS hp)
    have hcV : ContinuousOn V U := by
      have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
        (fun p hp => by simpa using hp)
      simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
    have ht := uniform_viscous_boundary_traces hΩ hγ hlam hB_ell hb_lipschitz τ F hF
      family (fun ε => (hfamily ε).1)
    have htrace : ∀ p ∈ S, p ∉ U → ∀ η : ℝ, 0 < η →
        ∃ O : Set (KineticPoint n), IsOpen O ∧ p ∈ O ∧
          ∀ q ∈ O ∩ U, |V q - w p| ≤ η := by
      intro p hp hpi η hη
      have hfaces : p ∈ evolutionTerminalClosure Ω γ τ ∨
          p ∈ evolutionLateralFrontier Ω γ τ := by
        by_cases he : p.time = τ
        · exact Or.inl ⟨he, by simpa only [← he] using hp.2⟩
        · right
          refine ⟨hp.1, ?_⟩
          rw [(isOpen_movingDomain hΩo p.time).frontier_eq]
          refine ⟨hp.2, ?_⟩
          intro hi
          exact hpi ⟨lt_of_le_of_ne hp.1 he, hi⟩
      rcases hfaces with hterm | hlat
      · obtain ⟨O, hO, hpO, hbO⟩ := ht.1 p hterm η hη
        refine ⟨O, hO, hpO, ?_⟩
        have hh := bounded_weak_limit_abs_sub_le_on_open U (O ∩ U) (hO.inter hU)
          inter_subset_right (fun j => v (ν j)) u V C
          (F (p.position, p.velocity)) η hva hba hua hub hlim hcV hrep
          (fun j q hq => hbO (seqε (ν j)) q ⟨hq.1, hUS hq.2⟩)
        simpa only [hw.2.2.2.2.1 p hterm] using hh
      · obtain ⟨O, hO, hpO, hbO⟩ := ht.2 p hlat η hη
        refine ⟨O, hO, hpO, ?_⟩
        have hh := bounded_weak_limit_abs_sub_le_on_open U (O ∩ U) (hO.inter hU)
          inter_subset_right (fun j => v (ν j)) u V C 0 η hva hba hua hub hlim hcV hrep
          (fun j q hq => by
            simpa using (hbO (seqε (ν j)) q ⟨hq.1, hUS hq.2⟩))
        simpa only [hw.2.2.2.2.2 p hlat] using hh
    let candidate := fun p => if p ∈ U then V p else w p
    have hgerm : ∀ p ∈ U, candidate =ᶠ[𝓝 p] V := by
      intro p hp
      filter_upwards [hU.mem_nhds hp] with q hq
      change (if q ∈ U then V q else w q) = V q
      exact ite_eq_left (show q ∈ U from hq)
    have hclass : IsClassicalTerminalSolution Ω γ B b τ F candidate := by
      refine ⟨⟨C, hC, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        by_cases hi : p ∈ U
        · simpa only [candidate, ite_eq_left hi] using hVC p hi
        · simpa only [candidate, ite_eq_right hi] using (hfamily ⟨1, one_pos, le_rfl⟩).2.1 p hp
      · exact continuousOn_interior_patch U S hU hUS V w hcV hw.2.1 htrace
      · rw [evolutionPastInteriorRaw_eq_image]
        apply contDiffOn_comp_evolutionHomeomorph_iff.mp
        apply hV.congr
        intro x hx
        change (if evolutionHomeomorph n x ∈ U then _ else _) = _
        exact ite_eq_left (show evolutionHomeomorph n x ∈ U from hx)
      · intro p hp
        have he := viscousTransportedOperator_congr_germ B b 0 (hgerm p hp)
        simpa only [viscousTransportedOperator_zero, hVE p hp] using he
      · intro p hp
        have hi : p ∉ U := fun h => (ne_of_lt h.1) hp.1
        simpa only [candidate, ite_eq_right hi] using hw.2.2.2.2.1 p hp
      · intro p hp
        have hf := hp.2
        rw [(isOpen_movingDomain hΩo p.time).frontier_eq] at hf
        have hi : p ∉ U := fun h => hf.2 h.2
        simpa only [candidate, ite_eq_right hi] using hw.2.2.2.2.2 p hp
    have hzero := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F candidate).mpr hclass
    refine ⟨candidate, hclass, ?_, ?_⟩
    · intro D hD hFD
      have _hD := hD
      exact classical_abs_le_const hΩo hγ.1 hlam hB_ell hb_lipschitz
        le_rfl zero_le_one hzero hFD
    · intro z hz
      exact classical_unique hΩo hγ.1 hlam hB_ell hb_lipschitz le_rfl zero_le_one
        ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F z).mpr hz) hzero
  have exists_classical_terminalSolution (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n) (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n) (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) (hB_smooth : IsSmoothFullKineticCoefficient B) (hB_symm : IsSymmetricFullKineticCoefficient B) (hB_ell : HasEverywhereLoewnerBounds lam Lam B) (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b) (hb_coercive : HasUnitDirectionDriftCoercivity m b) (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement) (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
      ∃ u : KineticPoint n → ℝ,
      IsClassicalTerminalSolution Ω γ B b τ F u ∧
      (∀ C : ℝ, 0 ≤ C → (∀ q, |F q| ≤ C) →
        ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
      (∀ v : KineticPoint n → ℝ,
        IsClassicalTerminalSolution Ω γ B b τ F v →
          EqOn v u (evolutionPastClosedCylinder Ω γ τ)) := by
    apply exists_classical_terminalSolution_of_viscous Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
      hb_lipschitz hb_coercive
      (fun τ F hF ε hε hε1 C hC hFC => ?_) τ F hF
    exact exists_viscous_terminalSolution
      (n := n) (hn := hn) (lam := lam) (Lam := Lam) (m := m) (L_b := L_b)
      (hlam := hlam) (hlamLam := hlamLam) (hm := hm) (hmLb := hmLb)
      (Ω := Ω) (γ := γ) (B := B) (b := b) (hΩ := hΩ) (hγ := hγ)
      (hB_smooth := hB_smooth) (hB_symm := hB_symm) (hB_ell := hB_ell)
      (hb_smooth := hb_smooth) (hb_lipschitz := hb_lipschitz) (hb_coercive := hb_coercive)
      hLE hH τ F hF ε hε hε1 C hC hFC
  exact exists_classical_terminalSolution
    Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH

section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set
open scoped CompactlySupported

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

local notation "μT" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- The terminal measure family is jointly Borel on the actual valid
query subtype, including the equal-time endpoint. -/
theorem measurable_terminalMeasure : Measurable (fun q : EvolutionQuery Ω γ => μT q) := by
  have hmass (q : EvolutionQuery Ω γ) : μT q univ ≤ 1 :=
    (terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).1
  have (q : EvolutionQuery Ω γ) : IsFiniteMeasure (μT q) :=
    ⟨(hmass q).trans_lt ENNReal.one_lt_top⟩
  apply measurable_measure_family_of_smooth_tests μT hmass
  intro f hf
  exact measurable_integral_terminal_smooth n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx (compactProbeDatum f) hf

end EvolutionData

end

theorem exists_terminalEvolution_of_classical
    (hLE : LiebermanEllipsoidDirichletStatement) (hH : HormanderHypoellipticityStatement) :
    SectionTwo.TerminalEvolutionConclusion := by
  intro n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive
  let hEx := classicalTerminalExistence_holds n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hLE hH
  exact construction_terminalEvolution_assembly n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx hH
    (terminalOperators_comp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx)
    (terminalFiberKernel_comp n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx)
    (measurable_terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx)

end HypoellipticAleksandrov.KineticAleksandrov

