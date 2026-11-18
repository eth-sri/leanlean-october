module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CompositionKernel
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriersTerminal
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.JointQueryBorelCutoffSequence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
section
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open scoped Topology


/-- The time-state set of interior terminal states is open for a continuous motion. -/
theorem isOpen_terminal_state_graph {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) :
    IsOpen {q : ℝ × EvolutionAmbientState n | q.2 ∈ evolutionStateSet Ω γ q.1} := by
  have hc : Continuous (fun q : ℝ × EvolutionAmbientState n => q.2.1 - γ q.1) :=
    (continuous_fst.comp continuous_snd).sub (hγ.comp continuous_fst)
  convert hΩ.preimage hc using 1
  ext q
  exact and_iff_left (mem_univ _ ) |>.trans mem_movingDomain_iff

/-- A compact interior terminal support remains interior for all nearby terminal times. -/
theorem IsCompact.eventually_subset_terminal_state
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {K : Set (EvolutionAmbientState n)} (hK : IsCompact K) {τ : ℝ}
    (hKT : K ⊆ evolutionStateSet Ω γ τ) :
    ∀ᶠ t in 𝓝 τ, K ⊆ evolutionStateSet Ω γ t := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  exact (isOpen_terminal_state_graph hΩ hγ).mem_nhds (hKT hx)

/-- The times at which a fixed compact set is an interior terminal support form an open set. -/
theorem IsCompact.isOpen_terminal_support_times
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)
    {K : Set (EvolutionAmbientState n)} (hK : IsCompact K) :
    IsOpen {τ : ℝ | K ⊆ evolutionStateSet Ω γ τ} := by
  apply isOpen_iff_mem_nhds.mpr
  intro τ hτ
  exact IsCompact.eventually_subset_terminal_state hΩ hγ hK hτ


/-- A compact interior datum remains a valid terminal datum on a whole time window. -/
theorem IsSmoothCompactTerminalDatum.exists_terminal_window
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω)
    {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {τ : ℝ}
    {F : BoundedBorel (EvolutionAmbientState n)}
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, dist t τ < δ →
      IsSmoothCompactTerminalDatum Ω γ t F := by
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp
    (IsCompact.eventually_subset_terminal_state hΩ hγ hF.2.1 hF.2.2)
  exact ⟨δ, hδ, fun t ht => ⟨hF.1, hF.2.1, hb ht⟩⟩

/-- If a fixed datum is supported inside every fiber of a slab, it vanishes on each
lateral frontier of that slab. -/
theorem terminalDatum_zero_lateral_of_support
    {n : ℕ} {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    {a T : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    (hs : ∀ t ∈ Icc a T, tsupport F ⊆ evolutionStateSet Ω γ t) :
    ∀ p ∈ movingClosedSlab Ω γ a T,
      p.position ∈ frontier (movingDomain Ω γ p.time) → F (p.position, p.velocity) = 0 := by
  intro p hp hfr
  apply Function.notMem_support.mp
  intro hnon
  rw [(isOpen_movingDomain hΩ p.time).frontier_eq] at hfr
  exact hfr.2 (hs p.time ⟨hp.1, hp.2.1⟩ (subset_closure hnon)).1

/-- The actual kinetic starting point of a valid evolution query. -/
def evolutionQueryPoint {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n}
    (q : EvolutionQuery Ω γ) : KineticPoint n := ⟨q.1.1, q.1.2.2.1, q.1.2.2.2⟩




/-- The integer index of the upper mesh approximation of a terminal time. -/
def terminalTimeMeshIndex (j : ℕ) (τ : ℝ) : ℤ := Int.ceil (τ * ((j : ℝ) + 1))

/-- The upper mesh approximation, with mesh size `1 / (j + 1)`. -/
def terminalTimeMesh (j : ℕ) (τ : ℝ) : ℝ :=
  (terminalTimeMeshIndex j τ : ℝ) / ((j : ℝ) + 1)

/-- The mesh index is Borel measurable. -/
theorem measurable_terminalTimeMeshIndex (j : ℕ) : Measurable (terminalTimeMeshIndex j) :=
  Int.measurable_ceil.comp (measurable_id.mul_const _)

/-- Every upper mesh approximation is at least the original time. -/
theorem le_terminalTimeMesh (j : ℕ) (τ : ℝ) : τ ≤ terminalTimeMesh j τ := by
  rw [terminalTimeMesh, le_div_iff₀ (by positivity : 0 < (j : ℝ) + 1)]
  exact Int.le_ceil _

/-- The upper mesh error is at most the mesh size. -/
theorem terminalTimeMesh_sub_le (j : ℕ) (τ : ℝ) :
    terminalTimeMesh j τ - τ ≤ 1 / ((j : ℝ) + 1) := by
  dsimp only [terminalTimeMesh, terminalTimeMeshIndex]
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : 0 < (j : ℝ) + 1)]
  field_simp
  linarith only [(Int.ceil_lt_add_one (τ * ((j : ℝ) + 1)))]

/-- Upper mesh times tend to their original terminal time. -/
theorem tendsto_terminalTimeMesh (τ : ℝ) :
    Tendsto (fun j => terminalTimeMesh j τ) atTop (𝓝 τ) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnorm (j : ℕ) : ‖terminalTimeMesh j τ - τ‖ = terminalTimeMesh j τ - τ :=
    Real.norm_of_nonneg (sub_nonneg.mpr (le_terminalTimeMesh j τ))
  simp only [hnorm]
  exact squeeze_zero (fun j => sub_nonneg.mpr (le_terminalTimeMesh j τ))
    (fun j => terminalTimeMesh_sub_le j τ) tendsto_one_div_add_atTop_nhds_zero_nat

section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set

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

/-- A fixed smooth compact probe has a uniform terminal-time error on every slab
where it vanishes on the lateral frontier. -/
theorem terminalOperators_terminal_time_error
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (q : ℝ) (hτq : τ ≤ q)
      (hFq : IsSmoothCompactTerminalDatum Ω γ q F),
      (∀ z ∈ movingClosedSlab Ω γ τ q,
        z.position ∈ frontier (movingDomain Ω γ z.time) →
          F (z.position, z.velocity) = 0) →
      ∀ (σ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ),
        |P₀ σ q (hστ.trans hτq) (terminalStateDatum F) p -
          P₀ σ τ hστ (terminalStateDatum F) p| ≤ (q - τ) * M := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_terminalDatum_operator_bound
    hlam hB_ell hb_lipschitz τ F hF
  refine ⟨M, hM0, ?_⟩
  intro q hτq hFq hlat σ hστ p
  obtain ⟨u, hu, hrep, _⟩ := terminalOperators_classical n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q F hFq
  obtain ⟨C, _, hC⟩ := F.exists_bound
  have herr (x : EvolutionState Ω γ τ) :
      |P₀ τ q hτq (terminalStateDatum F) x - terminalStateDatum F x| ≤ (q - τ) * M := by
    rw [← hrep τ hτq x]
    exact classical_sub_terminalDatum_le_core_of_slab
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hlam hB_ell hb_lipschitz
      (le_refl 0) zero_le_one hF.1 hC (fun z _ => hM 0 (le_refl 0) zero_le_one z)
      ((isClassicalViscousTerminalSolution_zero_iff Ω γ B b q F u).2 hu)
      hlat ⟨τ, x.1.1, x.1.2⟩ ⟨le_rfl, hτq, subset_closure x.2.1⟩
  let D := P₀ τ q hτq (terminalStateDatum F) - terminalStateDatum F
  have heq : P₀ σ q (hστ.trans hτq) (terminalStateDatum F) p -
      P₀ σ τ hστ (terminalStateDatum F) p = P₀ σ τ hστ D p := by
    rw [terminalOperators_comp_smooth n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
      σ τ q hστ hτq F hFq]
    exact (congrArg (fun f : BoundedBorel (EvolutionState Ω γ σ) => f p)
      ((P₀ σ τ hστ).map_sub (P₀ τ q hτq (terminalStateDatum F))
        (terminalStateDatum F))).symm
  rw [heq, terminalOperators_apply]
  exact abs_integral_boundedBorel_le D _
    (terminalFiberKernel_univ_le_one n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx σ τ hστ p)
    (mul_nonneg (sub_nonneg.mpr hτq) hM0) herr

end EvolutionData

end





/-- Evaluating a countable measurable family at a measurable index is measurable. -/
theorem measurable_countable_lookup {X : Type*} [MeasurableSpace X]
    (I : X → ℤ) (v : ℤ → X → ℝ) (hv : ∀ k, Measurable (v k)) (hI : Measurable I) :
    Measurable (fun x => v (I x) x) := by
  have hLookup : Measurable (fun z : ℤ × X => v z.1 z.2) :=
    measurable_from_prod_countable_right hv
  exact hLookup.comp (hI.prodMk measurable_id)

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

/-- A fixed terminal probe solution, extended by zero outside its past closed cylinder.
For a datum not supported in the terminal fiber the auxiliary function is zero. -/
def extendedTerminalProbe (n : ℕ) (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hEx : ClassicalTerminalExistence Ω γ B b)
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) : KineticPoint n → ℝ := by
  classical
  exact if hF : IsSmoothCompactTerminalDatum Ω γ τ F then
    (evolutionPastClosedCylinder Ω γ τ).indicator (hEx τ F hF).choose
  else 0

/-- The auxiliary fixed-terminal extension is Borel measurable. -/
theorem measurable_extendedTerminalProbe
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (extendedTerminalProbe n Ω γ B b hEx τ F) := by
  classical
  unfold extendedTerminalProbe
  split_ifs with hF
  · have hu := (hEx τ F hF).choose_spec.1
    have hs : IsClosed (evolutionPastClosedCylinder Ω γ τ) :=
      (isClosed_le continuous_time continuous_const).inter
        (isClosed_setOf_mem_closure_movingDomain hγ.1)
    exact hu.2.1.measurable_piecewise continuousOn_const hs.measurableSet
  · exact measurable_const

/-- On a valid earlier source the extension is exactly the terminal integral operator. -/
theorem extendedTerminalProbe_eq_operator
    (σ τ : ℝ) (hστ : σ ≤ τ) (p : EvolutionState Ω γ σ)
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
    extendedTerminalProbe n Ω γ B b hEx τ F
      ⟨σ, p.1.1, p.1.2⟩ = P₀ σ τ hστ (terminalStateDatum F) p := by
  rw [extendedTerminalProbe, dite_eq_left hF,
    indicator_of_mem (mk_mem_evolutionPastClosedCylinder hστ p), terminalOperators_apply_smooth]
  exact (terminalValue_eq_of_solution n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
    hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
    σ τ hστ p F hF _ (hEx τ F hF).choose_spec.1).symm

/-- The upper-time countable probe approximation is measurable on valid queries. -/
theorem measurable_upper_terminal_probe
    (j : ℕ) (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (fun q : EvolutionQuery Ω γ =>
      extendedTerminalProbe n Ω γ B b hEx
        (terminalTimeMesh j q.1.2.1) F (evolutionQueryPoint q))  := by
  have measurable_mesh_query_lookup {n : ℕ} {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} (v : ℤ → KineticPoint n → ℝ) (hv : ∀ k, Measurable (v k)) :
      Measurable (fun q : EvolutionQuery Ω γ =>
      v (terminalTimeMeshIndex j q.1.2.1) (evolutionQueryPoint q)) := by
    have continuous_evolutionQueryPoint {Ω : Set (PDE.Vec n)} {γ : ℝ → PDE.Vec n} :
        Continuous (@evolutionQueryPoint n Ω γ) := by
      exact KineticPoint.continuous_mk (continuous_fst.comp continuous_subtype_val)
        (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
        (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))
    have hm : Measurable (fun z : ℤ × KineticPoint n => v z.1 z.2) :=
      measurable_from_prod_countable_right hv
    exact hm.comp (((measurable_terminalTimeMeshIndex j).comp
      (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))).prodMk
      continuous_evolutionQueryPoint.measurable)
  exact measurable_mesh_query_lookup
    (fun k => extendedTerminalProbe n Ω γ B b hEx ((k : ℝ) / ((j : ℝ) + 1)) F)
    (fun k => measurable_extendedTerminalProbe n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx ((k : ℝ) / ((j : ℝ) + 1)) F)

end EvolutionData

end
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Function Filter
open scoped Topology
section

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic MeasureTheory Set Filter
open scoped Topology


/-- The integral of a fixed probe at admissible terminal times, and zero at the other times. -/
def validTerminalProbeIntegral (n : ℕ) (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (μ : EvolutionQuery Ω γ → Measure (EvolutionAmbientState n))
    (F : BoundedBorel (EvolutionAmbientState n)) (q : EvolutionQuery Ω γ) : ℝ := by
  classical
  exact if IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F then ∫ x, F x ∂(μ q) else 0

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

/-- At every query where a fixed smooth compact datum is admissible, its upper-time
measurable probe approximations converge to the terminal measure integral. -/
theorem tendsto_upper_terminal_probe
    (q : EvolutionQuery Ω γ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F) :
    Tendsto (fun j => extendedTerminalProbe n Ω γ B b hEx
      (terminalTimeMesh j q.1.2.1) F (evolutionQueryPoint q)) atTop
      (𝓝 (∫ x, F x ∂(μT q))) := by
  let τ := q.1.2.1
  let σ := q.1.1
  let p : EvolutionState Ω γ σ := ⟨q.1.2.2, q.2.2⟩
  obtain ⟨δ, hδ, hwindow⟩ := hF.exists_terminal_window
    (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1
  obtain ⟨M, hM0, herr⟩ := terminalOperators_terminal_time_error n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx τ F hF
  have hevent : ∀ᶠ j in atTop,
      |extendedTerminalProbe n Ω γ B b hEx (terminalTimeMesh j τ) F (evolutionQueryPoint q) -
        P₀ σ τ q.2.1 (terminalStateDatum F) p| ≤ (terminalTimeMesh j τ - τ) * M := by
    filter_upwards [(tendsto_terminalTimeMesh τ).eventually (Metric.ball_mem_nhds τ hδ)] with j hj
    have hτj := le_terminalTimeMesh j τ
    have hFj := hwindow (terminalTimeMesh j τ) hj
    have hs : ∀ t ∈ Icc τ (terminalTimeMesh j τ),
        tsupport F ⊆ evolutionStateSet Ω γ t := by
      intro t ht
      have hd : dist t τ ≤ dist (terminalTimeMesh j τ) τ := by
        rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
          abs_of_nonneg (sub_nonneg.mpr hτj)]
        exact sub_le_sub_right ht.2 τ
      exact (hwindow t (hd.trans_lt hj)).2.2
    change |extendedTerminalProbe n Ω γ B b hEx (terminalTimeMesh j τ) F
      ⟨σ, p.1.1, p.1.2⟩ - P₀ σ τ q.2.1 (terminalStateDatum F) p| ≤ _
    rw [extendedTerminalProbe_eq_operator n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx σ (terminalTimeMesh j τ)
      (q.2.1.trans hτj) p F hFj]
    exact herr (terminalTimeMesh j τ) hτj hFj (terminalDatum_zero_lateral_of_support (isOpen_of_isAdmissibleEvolutionDomain hΩ) hs) σ q.2.1 p
  have hlim : Tendsto (fun j => extendedTerminalProbe n Ω γ B b hEx
      (terminalTimeMesh j τ) F (evolutionQueryPoint q)) atTop
      (𝓝 (P₀ σ τ q.2.1 (terminalStateDatum F) p)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp
    apply squeeze_zero' (Eventually.of_forall fun j => abs_nonneg _) hevent
    simpa using ((tendsto_terminalTimeMesh τ).sub_const τ).mul_const M
  have heq : P₀ σ τ q.2.1 (terminalStateDatum F) p = ∫ x, F x ∂(μT q) := by
    rw [terminalOperators_apply_smooth]
    exact ((terminalMeasure_spec n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
      hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx q).2.2 F hF).symm
  rw [heq] at hlim
  exact hlim

/-- Fixed compact smooth test integrals are jointly measurable on the subtype of queries
where the test datum is supported in the terminal fiber. -/
theorem measurable_terminal_probe_on_admissible_queries
    (F : BoundedBorel (EvolutionAmbientState n)) :
    Measurable (fun q : {q : EvolutionQuery Ω γ //
      IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F} => ∫ x, F x ∂(μT q.1)) := by
  apply measurable_of_tendsto_metrizable
    (fun j => (measurable_upper_terminal_probe n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx j F).comp measurable_subtype_coe)
  apply tendsto_pi_nhds.mpr
  intro q
  exact tendsto_upper_terminal_probe n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q.1 F q.2

/-- A fixed smooth compact test integral, taken as zero when the test is not admissible,
is jointly measurable on the entire valid query space. -/
theorem measurable_valid_terminal_probe
    (F : BoundedBorel (EvolutionAmbientState n))
    (hFs : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) :
    Measurable (validTerminalProbeIntegral n Ω γ μT F) := by
  classical
  unfold validTerminalProbeIntegral
  let D : Set (EvolutionQuery Ω γ) :=
    {q | IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F}
  have hs : MeasurableSet D := by
    have hm : Measurable (fun q : EvolutionQuery Ω γ => q.1.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
    simpa [D, IsSmoothCompactTerminalDatum, hFs, hFc, Set.preimage] using
      (IsCompact.isOpen_terminal_support_times (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hFc).measurableSet.preimage hm
  apply measurable_of_restrict_of_restrict_compl hs
  · convert measurable_terminal_probe_on_admissible_queries n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx F using 1
    funext q
    exact ite_eq_left q.2
  · have hf : Dᶜ.domRestrict (fun q =>
        if IsSmoothCompactTerminalDatum Ω γ q.1.2.1 F then ∫ x, F x ∂(μT q) else 0) =
        (fun _ => (0 : ℝ)) := by
      funext q
      exact ite_eq_right q.2
    rw [hf]
    exact measurable_const

end EvolutionData

end


/-- Restrict a bounded Borel time-state probe to a terminal time. -/
def jointTerminalProbeSlice {n : ℕ}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n)) (τ : ℝ) :
    BoundedBorel (EvolutionAmbientState n) :=
  ⟨fun x => Φ (τ, x), Φ.measurable.comp (measurable_const.prodMk measurable_id), by
    obtain ⟨C, hC0, hC⟩ := Φ.exists_bound
    exact ⟨C, hC0, fun x => hC (τ, x)⟩⟩

/-- Every slice of a smooth compact time-state probe is smooth and compactly supported. -/
theorem jointTerminalProbeSlice_regular {n : ℕ}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) (τ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (jointTerminalProbeSlice Φ τ) ∧
      HasCompactSupport (jointTerminalProbeSlice Φ τ) := by
  refine ⟨hΦ.comp (contDiff_const.prodMk contDiff_id), ?_⟩
  apply HasCompactSupport.intro (hc.image continuous_snd)
  intro x hx
  apply notMem_support.mp
  intro hnon
  exact hx ⟨(τ, x), subset_closure hnon, rfl⟩

/-- Near a fixed terminal time, all neighboring slices of a compact graph-supported
probe are supported inside that fixed terminal fiber. -/
theorem eventually_jointTerminalProbeSlice_admissible {n : ℕ}
    {Ω : Set (PDE.Vec n)} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n}
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ {q : ℝ × EvolutionAmbientState n |
      q.2 ∈ evolutionStateSet Ω γ q.1}) (τ : ℝ) :
    ∀ᶠ t in 𝓝 τ, IsSmoothCompactTerminalDatum Ω γ τ (jointTerminalProbeSlice Φ t) := by
  let K :=
    tsupport Φ ∩ {z | z.2 ∉ evolutionStateSet Ω γ τ}
  have hK : IsCompact K := hc.inter_right
    (((isOpen_movingDomain hΩ τ).prod isOpen_univ).isClosed_compl.preimage continuous_snd)
  have hnot : τ ∉ Prod.fst '' K := by
    rintro ⟨z, hz, hzt⟩
    have hi := hs hz.1
    change z.2 ∈ evolutionStateSet Ω γ z.1 at hi
    rw [hzt] at hi
    exact hz.2 hi
  have hnear := ((hK.image continuous_fst).isClosed).isOpen_compl.mem_nhds hnot
  filter_upwards [hnear] with t ht
  obtain ⟨hr, hcompact⟩ := jointTerminalProbeSlice_regular Φ hΦ hc t
  refine ⟨hr, hcompact, ?_⟩
  intro x hx
  by_contra hxu
  exact ht ⟨(t, x), ⟨(tsupport_comp_subset_preimage Φ (continuous_const.prodMk continuous_id) hx), hxu⟩, rfl⟩

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

local notation "μT" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Integrating a smooth compact graph-supported time-state probe against the terminal
measure at its own terminal time is jointly Borel measurable. -/
theorem measurable_joint_terminal_probe
    (Φ : BoundedBorel (ℝ × EvolutionAmbientState n))
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hs : tsupport Φ ⊆ {z : ℝ × EvolutionAmbientState n |
      z.2 ∈ evolutionStateSet Ω γ z.1}) :
    Measurable (fun q : EvolutionQuery Ω γ => ∫ x, Φ (q.1.2.1, x) ∂(μT q)) := by
  let A (j : ℕ) (q : EvolutionQuery Ω γ) := validTerminalProbeIntegral n Ω γ μT
    (jointTerminalProbeSlice Φ (terminalTimeMesh j q.1.2.1)) q
  have hA (j : ℕ) : Measurable (A j) := by
    apply measurable_countable_lookup
      (fun q => terminalTimeMeshIndex j q.1.2.1)
      (fun k q => validTerminalProbeIntegral n Ω γ μT
        (jointTerminalProbeSlice Φ ((k : ℝ) / ((j : ℝ) + 1))) q)
    · intro k
      obtain ⟨hr, hcompact⟩ := jointTerminalProbeSlice_regular Φ hΦ hc
        ((k : ℝ) / ((j : ℝ) + 1))
      exact measurable_valid_terminal_probe n hn lam Lam m L_b
        hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
        hb_smooth hb_lipschitz hb_coercive hEx _ hr hcompact
    · exact (measurable_terminalTimeMeshIndex j).comp
        (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
  apply measurable_of_tendsto_metrizable hA
  apply tendsto_pi_nhds.mpr
  intro q
  have : IsFiniteMeasure (μT q) := ⟨(terminalMeasure_spec n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q).1.trans_lt ENNReal.one_lt_top⟩
  obtain ⟨C, _, hC⟩ := Φ.exists_bound
  have hlim := tendsto_integral_of_dominated_convergence (μ := μT q)

    (f := fun x => Φ (q.1.2.1, x)) (fun _ => C)
    (fun j => (Φ.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      simpa using hC (terminalTimeMesh j q.1.2.1, x))
    (Eventually.of_forall fun x => hΦ.continuous.continuousAt.tendsto.comp
      ((tendsto_terminalTimeMesh q.1.2.1).prodMk_nhds tendsto_const_nhds))
  apply hlim.congr'
  filter_upwards [(tendsto_terminalTimeMesh q.1.2.1).eventually (eventually_jointTerminalProbeSlice_admissible (isOpen_of_isAdmissibleEvolutionDomain hΩ) Φ hΦ hc hs q.1.2.1)] with j hj
  exact (ite_eq_left hj).symm

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

local notation "μT" => terminalMeasure n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx
local notation "κ" => terminalFiberKernel n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

local notation "P₀" => terminalOperators n hn lam Lam m L_b hlam hlamLam hm hmLb Ω γ B b
  hΩ hγ hB_smooth hB_symm hB_ell hb_smooth hb_lipschitz hb_coercive hEx

/-- Integrals of arbitrary bounded ambient smooth probes against the terminal measures
are jointly measurable, without any terminal-support premise on the probe. -/
theorem measurable_integral_terminal_smooth
    (F : BoundedBorel (EvolutionAmbientState n))
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Measurable (fun q : EvolutionQuery Ω γ => ∫ x, F x ∂(μT q)) := by
  obtain ⟨χ, hχ, hb, _, hcover⟩ := exists_increasing_smooth_interior_cutoffs
    (isOpen_terminal_state_graph (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1)
  obtain ⟨C, hC0, hC⟩ := F.exists_bound
  have hbound (j : ℕ) (z : ℝ × EvolutionAmbientState n) : |χ j z * F z.2| ≤ C := by
    rw [abs_mul, abs_of_nonneg (hb j z).1]
    exact (mul_le_mul_of_nonneg_right (hb j z).2 (abs_nonneg _)).trans
      (by simpa using hC z.2)
  let Φ (j : ℕ) : BoundedBorel (ℝ × EvolutionAmbientState n) :=
    ⟨fun z => χ j z * F z.2,
      ((hχ j).1.continuous.measurable.mul (F.measurable.comp measurable_snd)),
      ⟨C, hC0, hbound j⟩⟩
  have hΦr (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Φ j) :=
    (hχ j).1.mul (hF.comp contDiff_snd)
  have hΦc (j : ℕ) : HasCompactSupport (Φ j) := (hχ j).2.1.mul_right
  have hΦs (j : ℕ) : tsupport (Φ j) ⊆
      {z : ℝ × EvolutionAmbientState n | z.2 ∈ evolutionStateSet Ω γ z.1} :=
    tsupport_mul_subset_left.trans (hχ j).2.2
  apply measurable_of_tendsto_metrizable
    (fun j => measurable_joint_terminal_probe n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
      hb_smooth hb_lipschitz hb_coercive hEx (Φ j) (hΦr j) (hΦc j) (hΦs j))
  apply tendsto_pi_nhds.mpr
  intro q
  have hspec := terminalMeasure_spec n hn lam Lam m L_b
    hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell
    hb_smooth hb_lipschitz hb_coercive hEx q
  have : IsFiniteMeasure (μT q) := ⟨hspec.1.trans_lt ENNReal.one_lt_top⟩
  have hU : MeasurableSet (evolutionStateSet Ω γ q.1.2.1) :=
    measurableSet_evolutionStateSet_of_isOpen (isOpen_of_isAdmissibleEvolutionDomain hΩ)
  have ha : ∀ᵐ x ∂(μT q), x ∈ evolutionStateSet Ω γ q.1.2.1 := by
    apply ae_iff.mpr
    change (μT q) (evolutionStateSet Ω γ q.1.2.1)ᶜ = 0
    rw [← hspec.2.1, Measure.restrict_apply hU.compl]
    simp only [Set.compl_inter_self, measure_empty]
  apply tendsto_integral_of_dominated_convergence
    (F := fun j x => Φ j (q.1.2.1, x)) (fun _ => C)
    (fun j => ((Φ j).measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_const C)
    (fun j => Eventually.of_forall fun x => by
      change |χ j (q.1.2.1, x) * F x| ≤ C
      exact hbound j (q.1.2.1, x))
  filter_upwards [ha] with x hx
  obtain ⟨N, hN⟩ := hcover (q.1.2.1, x) hx
  apply tendsto_const_nhds.congr'
  apply eventually_atTop.mpr
  refine ⟨N, fun j hj => ?_⟩
  change F x = χ j (q.1.2.1, x) * F x
  rw [hN j hj, one_mul]

end EvolutionData

end HypoellipticAleksandrov.KineticAleksandrov

