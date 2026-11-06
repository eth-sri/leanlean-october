module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalPatch
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationBarriersTraces
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
import Mathlib.Tactic.Linarith
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalOrder
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeOperator
import Mathlib.Analysis.SpecificLimits.Basic
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierIntervalGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.CurveLipschitz
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.FiniteSlabBarriers
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationBarriers
import HypoellipticAleksandrov.KineticAleksandrov.EvolutionProblem
import Mathlib.Tactic.Positivity

/-! # Classical terminal solutions conditional on viscous existence

The additional premise is the existence of bounded classical viscous terminal solutions
on the moving domains.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov Set Filter MeasureTheory Evolution Classical
open scoped Topology MatrixOrder
open HypoellipticAleksandrov.Parabolic

/- Existence of a classical terminal solution, derived from viscous existence.  Hörmander's
hypoellipticity theorem and viscous existence are explicit hypotheses. -/
theorem exists_classical_terminalSolution_of_viscous
    (hH : HormanderHypoellipticityStatement)
    (n ) (hn : 1 ≤ n) (lam Lam m L_b : ℝ)
    (hlam : 0 < lam) (hlamLam : lam ≤ Lam) (hm : 0 < m) (hmLb : m ≤ L_b)
    (Ω : Set (PDE.Vec n)) (γ : ℝ → PDE.Vec n)
    (B : FullKineticCoefficient n) (b : PDE.Vec n → PDE.Vec n)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ)
    (hB_smooth : IsSmoothFullKineticCoefficient B)
    (hB_symm : IsSymmetricFullKineticCoefficient B)
    (hB_ell : HasEverywhereLoewnerBounds lam Lam B)
    (hb_smooth : IsSmoothDrift b) (hb_lipschitz : HasEuclideanLipschitzDrift L_b b)
    (hb_coercive : HasUnitDirectionDriftCoercivity m b)
    (hvisc : ∀ (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n)),
      IsSmoothCompactTerminalDatum Ω γ τ F → ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (C : ℝ), 0 ≤ C → (∀ q, |F q| ≤ C) →
      ∃ u : KineticPoint n → ℝ,
        IsClassicalViscousTerminalSolution Ω γ B b ε τ F u ∧
        (∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ C) ∧
        (∀ v : KineticPoint n → ℝ,
          IsClassicalViscousTerminalSolution Ω γ B b ε τ F v →
            EqOn v u (evolutionPastClosedCylinder Ω γ τ)))
    (τ : ℝ) (F : BoundedBorel (EvolutionAmbientState n))
    (hF : IsSmoothCompactTerminalDatum Ω γ τ F) :
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
  obtain ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, hVC, hVE⟩ : ∃ (u V : KineticPoint n → ℝ) (ν : ℕ → ℕ), StrictMono ν ∧
      AEStronglyMeasurable u (volume.restrict (evolutionPastOpenCylinder Ω γ τ)) ∧
      (∀ᵐ p ∂volume.restrict (evolutionPastOpenCylinder Ω γ τ), |u p| ≤ C) ∧
      (∀ ψ : KineticPoint n → ℝ,
        IntegrableOn ψ (evolutionPastOpenCylinder Ω γ τ) volume →
        Tendsto (fun j => ∫ p in evolutionPastOpenCylinder Ω γ τ, v (ν j) p * ψ p)
          atTop (𝓝 (∫ p in evolutionPastOpenCylinder Ω γ τ, u p * ψ p))) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph n)
        (evolutionHomeomorph n ⁻¹' evolutionPastOpenCylinder Ω γ τ) ∧
      u =ᵐ[volume.restrict (evolutionPastOpenCylinder Ω γ τ)] V ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, |V p| ≤ C) ∧
      (∀ p ∈ evolutionPastOpenCylinder Ω γ τ, transportedForwardOperator B b V p = 0) := by
    have hv := (fun j => (hfamily (seqε j)).1)
    have hb := (fun j => (hfamily (seqε j)).2.1)
    let : SecondCountableTopology (KineticPoint n) :=
      (KineticPoint.homeomorphProd n).isEmbedding.secondCountableTopology
    let U := evolutionPastOpenCylinder Ω γ τ
    have hU := isOpen_evolutionPastOpenCylinder
      (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 τ
    have hUS : U ⊆ evolutionPastClosedCylinder Ω γ τ :=
      fun p hp => ⟨hp.1.le, subset_closure hp.2⟩
    have hva : ∀ j, AEStronglyMeasurable (v j) (volume.restrict U) := fun j =>
      (((hv j).2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
    have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v j p| ≤ C := fun j => by
      filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
      exact hb j p (hUS hp)
    obtain ⟨u, ν, hν, hua, hub, hlim⟩ := exists_sigmaFinite_bounded_weak_subsequence
      (volume.restrict U) v C hC hva hba
    have hε : Tendsto (fun j => 1 / ((ν j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hν.tendsto_atTop
    have hw := weak_transport_equation_of_vanishing_viscosity n hn lam Lam m L_b
      hlam hlamLam hm hmLb Ω γ B b hΩ hγ hB_smooth hB_symm hB_ell hb_smooth
      hb_lipschitz hb_coercive τ (fun j => 1 / ((ν j : ℝ) + 1))
      (fun j => by positivity) hε (fun j => v (ν j)) u C hC
      (fun j => classical_viscous_terminalSolution_isWeak
        (isOpen_of_isAdmissibleEvolutionDomain hΩ) hγ.1 hB_smooth hB_symm hb_smooth (hv (ν j)))
      (fun j => hba (ν j)) hua hub hlim
    obtain ⟨V, hV, hrep⟩ := exists_smooth_kinetic_representative hH hlam hB_smooth hB_ell
      hb_smooth hm hb_coercive U hU u hw
    have hc : ContinuousOn V U := by
      have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
        (fun p hp => by simpa using hp)
      simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
    refine ⟨u, V, ν, hν, hua, hub, hlim, hV, hrep, ?_, ?_⟩
    · have hh := bounded_weak_limit_abs_sub_le_on_open U U hU Subset.rfl
        (fun j => v (ν j)) u V C 0 C (fun j => hva (ν j)) (fun j => hba (ν j))
        hua hub hlim hc hrep (fun j p hp => by simpa using hb (ν j) p (hUS hp))
      simpa only [sub_zero] using hh
    · exact transportedForwardOperator_eq_zero_of_smooth_weak hB_smooth hB_symm
        hb_smooth hU hw hV hrep
  have hva : ∀ j, AEStronglyMeasurable (v (ν j)) (volume.restrict U) := fun j =>
    (((hfamily (seqε (ν j))).1.2.1.mono hUS).aestronglyMeasurable hU.measurableSet)
  have hba : ∀ j, ∀ᵐ p ∂volume.restrict U, |v (ν j) p| ≤ C := fun j => by
    filter_upwards [ae_restrict_mem hU.measurableSet] with p hp
    exact (hfamily (seqε (ν j))).2.1 p (hUS hp)
  have hcV : ContinuousOn V U := by
    have hc := hV.continuousOn.comp (evolutionHomeomorph n).symm.continuous.continuousOn
      (fun p hp => by simpa using hp)
    simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hc
  have ht : (∀ p₀ ∈ evolutionTerminalClosure Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |family ε p - F (p₀.position, p₀.velocity)| ≤ η) ∧
    (∀ p₀ ∈ evolutionLateralFrontier Ω γ τ, ∀ η : ℝ, 0 < η →
      ∃ O : Set (KineticPoint n), IsOpen O ∧ p₀ ∈ O ∧
        ∀ ε, ∀ p ∈ O ∩ evolutionPastClosedCylinder Ω γ τ,
          |family ε p| ≤ η) := by
    have hu := (fun ε => (hfamily ε).1)
    obtain ⟨M, hM0, hM⟩ := exists_uniform_terminalDatum_operator_bound hlam hB_ell hb_lipschitz τ F hF
    obtain ⟨C, -, hC⟩ := F.exists_bound
    have hFc : Continuous (F : EvolutionAmbientState n → ℝ) := hF.1.continuous
    have _h_xinl_0 : Ω = Set.univ ∨ ∃ (c : PDE.Vec n) (r : ℝ), 0 < r ∧ Ω = PDE.euclideanBall c r := by
      rcases hΩ with h | h | ⟨hn, lo, hi, hlohi, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · cases hn
        have h' : Ω = PDE.oneDimensionalAxisBox lo hi := by simpa using h
        exact Or.inr ⟨intervalCentre lo hi, (hi - lo) / 2, by linarith,
          h'.trans (oneDimensionalAxisBox_eq_euclideanBall hlohi)⟩
    rcases _h_xinl_0 with
      rfl | ⟨c, r, hr, rfl⟩
    · refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
      · refine terminal_trace_of_window F hFc family hM0 one_pos (fun i p hp ht => ?_) hp₀.1 hη
        exact wholeSpace_terminalDatum_bound hlam hB_ell hb_lipschitz rfl (τ - 1) τ (by linarith) F hF i.1
          i.2.1.le i.2.2 M hM0 (fun q _ => hM i.1 i.2.1.le i.2.2 q) (family i) (hu i) p
          ⟨by linarith, hp.1, hp.2⟩
      · exfalso
        have h := hp₀.2
        rw [movingDomain_univ, frontier_univ] at h
        exact notMem_empty _ h
    · obtain ⟨d, hd, hdr, hsupp⟩ : ∃ d : ℝ, 0 < d ∧ d < r / 4 ∧ ∀ q ∈ tsupport (F : EvolutionAmbientState n → ℝ),
        2 * d ≤ r - PDE.vecEuclideanNorm (q.1 - (γ τ + c)) := by
            have hcpt := hF.2.1.isCompact
            have hcont : Continuous (fun q : EvolutionAmbientState n =>
                r - PDE.vecEuclideanNorm (q.1 - (γ τ + c))) :=
              continuous_const.sub (PDE.continuous_vecEuclideanNorm.comp
                (continuous_fst.sub continuous_const))
            obtain ⟨m, hm, hmle⟩ := hcpt.exists_forall_le' (a := 0) hcont.continuousOn (fun q hq => by
              have h1 := (hF.2.2 hq).1
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

          /- Terminal trace from a uniform terminal window: if `|u_i - F| ≤ (τ - σ) M` for all `i` on the
          past cylinder near the terminal time, then the terminal trace at a terminal point is uniform. -/
      refine ⟨fun p₀ hp₀ η hη => ?_, fun p₀ hp₀ η hη => ?_⟩
      · obtain ⟨L, hL, hγL⟩ := exists_evolution_curve_lipschitzOn hγ (τ - 1) τ (by linarith)
        have hL1 : 0 < d / (1 + L) := div_pos hd (by linarith)
        refine terminal_trace_of_window F hFc family hM0 (lt_min one_pos hL1)
          (fun i p hp ht => ?_) hp₀.1 hη
        have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (τ - 1) τ :=
          ⟨by linarith [min_le_left (1 : ℝ) (d / (1 + L))], hp.1, hp.2⟩
        exact (two_barriers_on_finite_slab hr hγ (τ - 1) τ (by linarith) L hL hγL hlam hB_ell hb_lipschitz
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
          have hpt' := hpt
          have hpD' := hpD
          have hslab : p ∈ movingClosedSlab (PDE.euclideanBall c r) γ (p₀.time - 1) τ :=
            ⟨hpt'.le, hcyl.1, hcyl.2⟩
          have h1 := (two_barriers_on_finite_slab hr hγ (p₀.time - 1) τ (by linarith) L hL hγL
            hlam hB_ell hb_lipschitz i.2.1.le i.2.2 hF d hd hdr hsupp C M hC
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
          simpa only [sub_zero] using (hbO (seqε (ν j)) q ⟨hq.1, hUS hq.2⟩))
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

end HypoellipticAleksandrov.KineticAleksandrov
