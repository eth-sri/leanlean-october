module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.RCMProof.XiLower

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open FK Duality CorrLength

def routeBRotatedBoundaryEvent (n : ℕ)  :=
  ⋃ v : {v : CorrLength.RotatedVertex //
      max v.1.1.natAbs v.1.2.natAbs = n},
    CorrLength.rotatedConnectionEvent CorrLength.rotatedLatticeOrigin v.1

def routeBSquareBoundaryEvent (n : ℕ)  :=
  ⋃ v : {v : CorrLength.RotatedVertex //
      max v.1.1.natAbs v.1.2.natAbs = n},
    CorrLength.connectionEvent (0, 0) (CorrLength.rotatedVertexEquiv v.1)

def routeBSquareBoundaryTail (N : ℕ)  :=
  ⋃ k : {k : ℕ // N ≤ k}, routeBSquareBoundaryEvent k.1

private theorem routeBSquareBoundaryEvent_measurable (n : ℕ) :
    MeasurableSet (routeBSquareBoundaryEvent n) := by
  apply MeasurableSet.iUnion
  intro v
  exact CorrLength.connectionEvent_isMeasurableSet _ _

private theorem routeBSquareBoundaryTail_measurable (n : ℕ) :
    MeasurableSet (routeBSquareBoundaryTail n) := MeasurableSet.iUnion fun k => routeBSquareBoundaryEvent_measurable ↑k

private theorem routeBSquareBoundaryTail_antitone :
    Antitone routeBSquareBoundaryTail := by
  intro m n hmn ω hω
  rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
  exact Set.mem_iUnion.mpr ⟨⟨k.1, hmn.trans k.2⟩, hk⟩

private theorem routeBSquareBoundaryTail_inter_finiteCluster_empty
    (ω : FK.LatticeConfiguration) (hfinite : (Duality.cluster ω (0, 0)).Finite) :
    ω ∉ ⋂ n, routeBSquareBoundaryTail n := by
  
  
  have hSfinite : ((fun x  => max x.1.natAbs x.2.natAbs) ''
                     Duality.cluster ω (0, 0)).Finite := hfinite.image _
  obtain ⟨K, hK⟩ := hSfinite.bddAbove
  intro hω
  
  rcases Set.mem_iUnion.mp (Set.mem_iInter.mp hω (2 * K + 1)) with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨v, hv⟩
  let x := CorrLength.rotatedVertexEquiv v.1
  
  have hcoords := congrArg Subtype.val
      (CorrLength.squareToRotated_rotatedToSquare v.1)
  have hfirst : v.1.1.1 = x.1 - x.2 := Eq.symm (congrArg Prod.fst hcoords)
  have hsecond : v.1.1.2 = x.1 + x.2 := Eq.symm (congrArg Prod.snd hcoords)
  
  
  
  
  have hxK : max x.1.natAbs x.2.natAbs ≤ K := hK (Exists.intro x ⟨ (CorrLength.connectionEvent_iff_rcInfiniteReachable (0, 0) x ω).1 hv , rfl⟩)
  
  omega

/-- A free rotated boundary connection tends to zero when the square-lattice
free origin cluster is almost surely finite. The proof uses continuity from
above on the union of all shell events beyond a given radius. -/
theorem rotatedBoundaryConnectionProbability_tendsto_zero_of_ae_finite_cluster
    (θ : FK.Parameters) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (hfinite : ∀ᵐ ω ∂μ, (Duality.cluster ω (0, 0)).Finite) :
    Filter.Tendsto (fun n : ℕ =>
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
        (routeBRotatedBoundaryEvent n)) Filter.atTop (nhds 0) := by
  have := hμ.1
  let ν  :=
    Classical.choose (FK.freeBoxLimit_existsUnique θ)
  
  
  have hμν  :=
    PottsDiscontinuity.rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ (FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν ((Classical.choose_spec (FK.freeBoxLimit_existsUnique θ)).1
                                                                                                                                (fun _ => (0, 0)) (fun n => n)
                                                                                                                                FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive))
  let H := CorrLength.rotatedConfigurationHomeomorph
  have hrotMeas (n : ℕ) : MeasurableSet (routeBRotatedBoundaryEvent n) := MeasurableSet.iUnion fun v => rotatedConnectionEvent_isMeasurableSet rotatedLatticeOrigin ↑v
  have hpre (n : ℕ) : H.toFun ⁻¹' routeBRotatedBoundaryEvent n =
      routeBSquareBoundaryEvent n := by
    ext ω
    simp [routeBRotatedBoundaryEvent, routeBSquareBoundaryEvent, H,
      CorrLength.rotatedConnectionEvent, CorrLength.rotatedLatticeOrigin,
      CorrLength.rotatedVertexEquiv, CorrLength.rotatedToSquareVertex]
  have hprob (n : ℕ) :
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
          (routeBRotatedBoundaryEvent n) =
        μ.real (routeBSquareBoundaryEvent n) := by
    have hmap := ProbabilityMeasure.map_apply ν
      H.continuous_toFun.measurable.aemeasurable (hrotMeas n)
    rw [hpre n] at hmap
    calc
      (CorrLength.rotatedFreeBoxLimit θ).toMeasure.real
          (routeBRotatedBoundaryEvent n) =
         (CorrLength.rotatedFreeBoxLimit θ)
          (routeBRotatedBoundaryEvent n)  :=
        ProbabilityMeasure.measureReal_eq_coe_coeFn _ _
      _ =  ν (routeBSquareBoundaryEvent n)  := by
        simpa [CorrLength.rotatedFreeBoxLimit, H, ν] using hmap
      _ = μ.real (routeBSquareBoundaryEvent n) := by
        simp_all
  
  
  have htailENN : Filter.Tendsto (fun n => μ (routeBSquareBoundaryTail n))
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def,  by
                                                                                         exact measure_mono_null (fun ⦃ω⦄ hω hfiniteω => routeBSquareBoundaryTail_inter_finiteCluster_empty ω hfiniteω hω)
                                                                                                 (Eq.mpr (congrArg (fun _a => _a) (Eq.symm (propext ae_iff))) hfinite) ] using  MeasureTheory.tendsto_measure_iInter_atTop
                                              (μ := μ) (s := routeBSquareBoundaryTail)
                                              (fun n => (routeBSquareBoundaryTail_measurable n).nullMeasurableSet)
                                              routeBSquareBoundaryTail_antitone
                                              ⟨0, measure_ne_top μ _⟩ 
  
  have hprobSmall : Filter.Tendsto
      (fun n => μ.real (routeBSquareBoundaryEvent n))
      Filter.atTop (nhds 0) := by
                                 exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (((ENNReal.continuousAt_toReal (by simp)).tendsto.comp htailENN)) (fun n => measureReal_nonneg) fun n =>
                                         measureReal_mono (fun ⦃ω⦄ hω => Set.mem_iUnion.mpr (Exists.intro ⟨n, le_rfl⟩ hω))
                                           (measure_ne_top μ (routeBSquareBoundaryTail n))
  
  rw [ funext hprob ]
  exact hprobSmall

/-- Absence of percolation for the critical free measure, derived from the positive lower
bound on the inverse correlation length, as the input of Lemma 3.14: (3.24) and Identity (4.4)
give a positive rate;
the resulting exponential decay makes the free origin cluster finite a.s.,
and the rotated boundary connection probability tends to zero. -/
theorem routeB_free_nonpercolation_and_boundary_decay
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW21 : contract_eq315)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ∃ S : ℝ,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S ∧
      μ (Duality.infiniteClusterAt (0, 0)) = 0 ∧
      Filter.Tendsto (fun n : ℕ =>
        (CorrLength.rotatedFreeBoxLimit (FK.criticalParameters q)).toMeasure.real
          (routeBRotatedBoundaryEvent n)) Filter.atTop (nhds 0) := by
  have := hμ.1
  obtain ⟨S, hS, hxi⟩ := xi_inverse_ge_critical_rate
    hW12i hW12ii hW21 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam (by
                                         
                                         apply Real.arcosh_pos
                                         have hqpos : 0 < q.val := by linarith
                                         have hsquare := Real.sq_sqrt (le_of_lt hqpos)
                                         have hsqrt : 2 < Real.sqrt q.val := by
                                           nlinarith [Real.sqrt_nonneg q.val]
                                         linarith)
  have hS_eq  := tendsto_nhds_unique hS hS₀
  
  
  
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    Duality.free_exponential_decay_of_pos_diagonal_rate
      (FK.criticalParameters q) μ hμ ξinv (by
                                             linarith) (by
                                                         refine hRate.congr' ?_
                                                         filter_upwards with n
                                                         have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
                                                             Duality.connectionEvent (0, 0) (diagonalSite n) := by
                                                           ext ω
                                                           rw [CorrLength.connectionEvent_iff_rcInfiniteReachable]
                                                           rfl
                                                         rw [hevent]
                                                         simp only [Duality.twoPoint]
                                                         rw [show Duality.connectionEvent (0, 0) (diagonalSite n) =
                                                           Duality.connectionEvent 0 (diagonalSite n) by rfl]
                                                         
                                                         ring)
  
  have hfinite  :=
    Duality.ae_finite_cluster_of_exponential_decay μ (0, 0) C c hc (by
                                                                      intro x
                                                                      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
                                                                      apply ENNReal.ofReal_le_ofReal
                                                                      
                                                                      exact hdecay x)
  have hno  :=
    Duality.infiniteClusterAt_zero_of_exponential_decay μ C c hc (by
                                                                    intro x
                                                                    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
                                                                    apply ENNReal.ofReal_le_ofReal
                                                                    
                                                                    exact hdecay x)
  have hboundary := rotatedBoundaryConnectionProbability_tendsto_zero_of_ae_finite_cluster
    (FK.criticalParameters q) μ hμ hfinite
  exact ⟨S, hS, hxi, hno, hboundary⟩

end PottsDiscontinuity.RCMProof
