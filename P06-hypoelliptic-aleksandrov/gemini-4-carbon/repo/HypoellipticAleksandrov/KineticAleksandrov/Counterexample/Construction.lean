module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ExtensionGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Height
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHolds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Setting
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Geometry
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.MollifyApproximateIdentity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSourceIdentity
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyOperator
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFunctions
import Mathlib.Topology.MetricSpace.Thickening
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.SmoothFamilyGeometry
import HypoellipticAleksandrov.Coefficients.ParabolicRegularization
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Every exponent below the kinetic threshold admits a positive source-decay exponent. -/
theorem exists_subcritical_alpha (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < alpha - 2 + 4 * (d : ℝ) / p := by
  have hp0 := lt_of_lt_of_le zero_lt_one hp
  have hratio : 1 < 4 * (d : ℝ) / p := (lt_div_iff₀ hp0).2 (by simpa using hpd)
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  obtain ⟨alpha, ha, ha1⟩ := exists_between
    (show max 0 (2 - 4 * (d : ℝ) / p) < 1 from
      max_lt zero_lt_one (by linarith only [hratio]))
  refine ⟨alpha, lt_of_le_of_lt (le_max_left _ _) ha, ha1, ?_⟩
  linarith only [(lt_of_le_of_lt (le_max_right 0 (2 - 4 * (d : ℝ) / p)) ha), (div_pos (by positivity) hp0)]


open Set

/-- With a stationary spatial base point, the cylinder is the literal product cylinder. -/
theorem construction_mem_cylinder_iff {d : ℕ} (T S : ℝ) (hS : 0 < S) (P : KineticPoint d) :
    P ∈ backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ↔
      T - S ^ 2 < P.time ∧ P.time < T ∧
      PDE.vecEuclideanNorm P.velocity < S ∧ PDE.vecEuclideanNorm P.position < S ^ 3 := by
  simp [backwardCylinder, relativePosition,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hS,
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hS 3)]

/-- A positive earlier time at the spatial origin belongs to the chosen fixed cylinder. -/
theorem construction_origin_mem_cylinder {d : ℕ} (T S t : ℝ)
    (hS : 0 < S) (hTS : T < S ^ 2) (ht : 0 < t) (htT : t < T) :
    (⟨t, 0, 0⟩ : KineticPoint d) ∈ backwardCylinder ⟨T, 0, 0⟩ S := by
  rw [construction_mem_cylinder_iff T S hS]
  refine ⟨by linarith, htT, ?_, ?_⟩
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using hS
  · simpa [PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] using pow_pos hS 3

/-- Barrier and cylinder radii are chosen once, independently of all flattening scales. -/
theorem construction_fixed_geometry_of_profile {d : ℕ} (hd : 1 ≤ d) {alpha : ℝ}
    (ha : 0 < alpha) (h : CounterProfileStatement d alpha) :
    ∃ R mu S : ℝ, 0 < R ∧ 0 < mu ∧ 0 < S ∧
      mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2 ∧
      barrierTime mu < S ^ 2 ∧
      (∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) ∧
      (∀ q, profileFunction h q ≤ 1 →
        PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) ∧
      (∀ P, 0 ≤ backwardOperator (fun _t x v => profileMatrix h (x, v))
        (barrier mu R) P) := by
  obtain ⟨R, hR, hv⟩ := exists_profile_barrier_radius ha h
  let mu := (d : ℝ) * profileLowerEllipticity h / R ^ 2
  have hd0 : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hlam := (selectedProfile_spec h).1
  obtain ⟨S, hS, hTS, hgeom⟩ := exists_profile_cylinder_radius ha h (barrierTime mu)
  refine ⟨R, mu, S, hR, (div_pos (mul_pos hd0 hlam) (sq_pos_of_pos hR)), hS, rfl, hTS, hv, hgeom, ?_⟩
  intro P
  exact barrier_operator_nonneg hd (profileMatrix h) (profileLowerEllipticity h)
    R hlam hR (fun q => ((selectedProfile_spec h).2.2.2.2.2.1 q).1) P

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

section


/-! # Sequence-constructor interface for the Appendix C construction

The family propositions are the two conjuncts of the construction's conclusion. Parameters
are selected from the internally proved profile and fixed-cylinder geometry.
-/


namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open Filter MeasureTheory
open scoped MatrixOrder

/-- The subcritical exponent is fixed before all profile and sequence choices. -/
noncomputable def counterAlpha (d : ℕ) (p : ℝ) : ℝ := by
  classical
  exact if h : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * (d : ℝ) then
    (exists_subcritical_alpha d h.1 p h.2.1 h.2.2).choose else 1 / 2

/-- The selected exponent satisfies the full source range and positive norm exponent. -/
theorem counterAlpha_spec (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    0 < counterAlpha d p ∧ counterAlpha d p < 1 ∧
      0 < counterAlpha d p - 2 + 4 * (d : ℝ) / p := by
  classical
  simp only [counterAlpha, dite_eq_left (And.intro hd (And.intro hp hpd))]
  exact (exists_subcritical_alpha d hd p hp hpd).choose_spec

/-- The internally proved profile at the one fixed selected exponent. -/
theorem counterProfileFor (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    CounterProfileStatement d (counterAlpha d p) :=
  counterProfile_holds d hd (counterAlpha d p)
    (counterAlpha_spec d hd p hp hpd).1 (counterAlpha_spec d hd p hp hpd).2.1

/-- Joint ellipticity bounds and cylinder parameters, independent of the sequence index. -/
noncomputable def counterParameters (d : ℕ) (p : ℝ) : ℝ × ℝ × KineticPoint d × ℝ := by
  classical
  exact if hvalid : 1 ≤ d ∧ 1 ≤ p ∧ p < 4 * (d : ℝ) then
    let h := counterProfileFor d hvalid.1 p hvalid.2.1 hvalid.2.2
    let geom := construction_fixed_geometry_of_profile hvalid.1
      (counterAlpha_spec d hvalid.1 p hvalid.2.1 hvalid.2.2).1 h
    let mu := geom.choose_spec.choose
    let S := geom.choose_spec.choose_spec.choose
    (profileLowerEllipticity h, profileUpperEllipticity h, ⟨barrierTime mu, 0, 0⟩, S)
  else (1, 1, ⟨0, 0, 0⟩, 1)

/-- The selected joint parameters have the required positive bounds and cylinder radius. -/
theorem counterParameters_pos (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    0 < (counterParameters d p).1 ∧
      (counterParameters d p).1 ≤ (counterParameters d p).2.1 ∧
      0 < (counterParameters d p).2.2.2 := by
  classical
  let h := counterProfileFor d hd p hp hpd
  have hs := (construction_fixed_geometry_of_profile hd (counterAlpha_spec d hd p hp hpd).1 h).choose_spec.choose_spec.choose_spec
  simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using
    And.intro ((selectedProfile_spec h).1) (And.intro ((selectedProfile_spec h).2.1) hs.2.2.1)

/-- The measurable-coefficient family statement. -/
def MeasurableFamilyStatement (d : ℕ) (p lam Lam : ℝ) (P₀ : KineticPoint d)
    (R : ℝ) : Prop :=
  ∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)

/-- The smooth-coefficient family statement. -/
def SmoothFamilyStatement (d : ℕ) (p lam Lam : ℝ) (P₀ : KineticPoint d)
    (R : ℝ) : Prop :=
  ∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

namespace HypoellipticAleksandrov.KineticAleksandrov

open Counterexample Filter MeasureTheory
open scoped MatrixOrder

/-- The two family statements at the one selected tuple give the construction. -/
theorem construction_of_families
    (hfamilies : ∀ d : ℕ, 1 ≤ d → ∀ p : ℝ, 1 ≤ p → p < 4 * (d : ℝ) →
      let params := counterParameters d p
      MeasurableFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2 ∧
      SmoothFamilyStatement d p params.1 params.2.1 params.2.2.1 params.2.2.2)
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  have hpos := counterParameters_pos d hd p hp hpd
  have hf := hfamilies d hd p hp hpd
  exact ⟨(counterParameters d p).1, (counterParameters d p).2.1,
    (counterParameters d p).2.2.1, (counterParameters d p).2.2.2,
    hpos.1, hpos.2.1, hpos.2.2, hf.1, hf.2⟩

end HypoellipticAleksandrov.KineticAleksandrov
end

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set Filter MeasureTheory HypoellipticAleksandrov.Parabolic
open scoped Topology ENNReal

/-- Continuous scalar functions are bounded on any compact carrier. -/
theorem construction_compact_scalar_bound {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C := by
  obtain ⟨C, hb⟩ := hK.bddAbove_image hf.abs.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

/-- Uniform scalar bounds are preserved by subtraction. -/
theorem construction_scalar_bound_sub {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x - g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hf x hx) (hg x hx))⟩

/-- Uniform scalar bounds are preserved by multiplication. -/
theorem construction_scalar_bound_mul {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x * g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hC

/-- The packed barrier gradient depends continuously on time and space together. -/
theorem construction_barrier_gradient_joint_continuous (d : ℕ) (mu R : ℝ)
    (i : Fin (d + d)) : Continuous (fun z : ℝ × PDE.Vec (d + d) =>
      PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [spatialPackedBarrier_positionGradient]
    exact continuous_const
  · simp only [spatialPackedBarrier_velocityGradient]
    exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
      (R ^ 2)).neg).mul
      ((continuous_apply j).comp ((spatialCoordinateCLE d).continuous.comp
        continuous_snd).snd)


/-- First raw representatives have bounds uniform over both compact time and compact space. -/
theorem construction_rawGradient_uniform_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R a b : ℝ)
    (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) (i : Fin (d + d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      |spatialPackedCutoffGradient h r mu R t x i| ≤ C := by
  let D := Icc a b ×ˢ K
  have hD : IsCompact D := isCompact_Icc.prod hK
  obtain ⟨C, hC, hb⟩ := construction_packedGradient_compact_bound h r hr i K hK
  have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |spatialPackedGradient (flatProfilePositionJet h r)
        (flatProfileVelocityJet h r) z.2 i| ≤ C :=
    ⟨C, hC, fun z hz => hb z.2 hz.2⟩
  obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hf (construction_compact_scalar_bound D hD _ (construction_barrier_gradient_joint_continuous d mu R i))
  refine ⟨N, hN, fun t ht x hx => ?_⟩
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
  rw [spatialPackedCutoffGradient, abs_mul, abs_of_nonneg htheta.1]
  exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
    (by simpa using hbN (t, x) ⟨ht, hx⟩)

/-- Second raw representatives have bounds uniform over compact time and compact space. -/
theorem construction_rawHessian_uniform_bound {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r : ℝ) (hr : 0 < r) (mu R a b : ℝ)
    (K : Set (PDE.Vec (d + d))) (hK : IsCompact K) (i k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x ∈ K,
      |spatialPackedCutoffVelocityHessian h r mu R t x i k| ≤ C  := by
  have construction_barrier_hessian_joint_continuous :
      Continuous (fun z : ℝ × PDE.Vec (d + d) =>
      PDE.classicalGradient (fun y => PDE.classicalGradient
        (spatialPackedBarrier d mu R z.1) y (Fin.natAdd d k)) z.2 (Fin.natAdd d i)) := by
    simp only [spatialPackedBarrier_velocityHessian]
    exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
      (R ^ 2)).neg).mul continuous_const
  let D := Icc a b ×ˢ K
  have hD : IsCompact D := isCompact_Icc.prod hK
  obtain ⟨M, hM, hbM⟩ := flatProfile_jets_compact_bound_of_profile h r hr
    ((spatialCoordinateCLE d) '' K) (hK.image (spatialCoordinateCLE d).continuous)
  have hh : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |flatProfileHessian h r (spatialCoordinateCLE d z.2) i k| ≤ C :=
    ⟨M, hM, fun z hz => (hbM _ ⟨z.2, hz.2, rfl⟩).2.2 i k⟩
  have hg (j : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
      |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j -
        PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 (Fin.natAdd d j)|
        ≤ C := by
    have hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ D,
        |flatProfileVelocityJet h r (spatialCoordinateCLE d z.2) j| ≤ C :=
      ⟨M, hM, fun z hz => by
        simpa using
          (norm_le_pi_norm _ j).trans (hbM _ ⟨z.2, hz.2, rfl⟩).2.1⟩
    exact construction_scalar_bound_sub D _ _ hf
      (construction_compact_scalar_bound D hD _
        (construction_barrier_gradient_joint_continuous d mu R (Fin.natAdd d j)))
  obtain ⟨N, hN, hbN⟩ := construction_scalar_bound_sub D _ _ hh
    (construction_compact_scalar_bound D hD _
      (construction_barrier_hessian_joint_continuous))
  obtain ⟨C, hC, hbC⟩ := construction_scalar_bound_mul D _ _ (hg i) (hg k)
  obtain ⟨L, hL, hbL⟩ := timeCutoffTheta_deriv2_abs_bound
  refine ⟨N + L * C, add_nonneg hN (mul_nonneg hL.le hC), fun t ht x hx => ?_⟩
  have htheta := timeCutoffTheta_deriv_bounds
    (selectedFlatProfile h r (spatialCoordinateCLE d x) - spatialPackedBarrier d mu R t x)
  unfold spatialPackedCutoffVelocityHessian
  apply (abs_add_le _ _).trans
  apply add_le_add
  · rw [abs_mul, abs_of_nonneg htheta.1]
    exact (mul_le_mul_of_nonneg_right htheta.2 (abs_nonneg _)).trans
      (by simpa using hbN (t, x) ⟨ht, hx⟩)
  · rw [mul_assoc, abs_mul]
    exact mul_le_mul (hbL _) (hbC (t, x) ⟨ht, hx⟩) (abs_nonneg _) hL.le


/-- Measurable convergence at almost every spatial point at each time yields convergence
in the literal kinetic product-volume carrier. -/
theorem construction_fixed_time_tendsto_ae_spacetime {d : ℕ}
    (F : ℕ → ℝ × XV d → ℝ) (g : ℝ × XV d → ℝ)
    (hF : ∀ n, Measurable (F n)) (hg : Measurable g)
    (ht : ∀ t : ℝ, ∀ᵐ q ∂volume,
      Tendsto (fun n => F n (t, q)) atTop (𝓝 (g (t, q)))) :
    ∀ᵐ P : KineticPoint d ∂volume,
      Tendsto (fun n => F n (KineticPoint.equivProd d P)) atTop
        (𝓝 (g (KineticPoint.equivProd d P))) := by
  have he : ∀ᵐ z : ℝ × XV d ∂volume,
      Tendsto (fun n => F n z) atTop (𝓝 (g z)) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_tendsto_fun (l := atTop) hF hg)).mpr (Eventually.of_forall ht)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae he

/-- Uniformly bounded measurable convergence controls the positive-part source error in
any finite exponent on a finite-measure cylinder. -/
theorem construction_positive_part_error_tendsto {X : Type*} [MeasurableSpace X]
    (nu : Measure X) [IsFiniteMeasure nu] (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (F : ℕ → X → ℝ) (g : X → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) nu) (hg : AEStronglyMeasurable g nu)
    (C : ℝ) (hC : 0 ≤ C)
    (hFb : ∀ n, ∀ᵐ x ∂nu, |F n x| ≤ C) (hgb : ∀ᵐ x ∂nu, |g x| ≤ C)
    (hlim : ∀ᵐ x ∂nu, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (fun x => max (F n x) 0 - max (g x) 0) p nu)
      atTop (𝓝 0) := by
  apply bounded_convergence_eLpNorm nu p hp0 hpTop _
    (fun n => ((hF n).aemeasurable.max aemeasurable_const).aestronglyMeasurable.sub
      (hg.aemeasurable.max aemeasurable_const).aestronglyMeasurable) (2 * C)
  · intro n
    filter_upwards [hFb n, hgb] with x hx hy
    have hbF : |max (F n x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hx) hC
    have hbg : |max (g x) 0| ≤ C := by
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _ |>.trans hy) hC
    simpa using!
      (abs_sub _ _).trans (show |max (F n x) 0| + |max (g x) 0| ≤ 2 * C by
        linarith only [hbF, hbg])
  · filter_upwards [hlim] with x hx
    simpa using! (hx.max (tendsto_const_nhds (x := 0))).sub_const (max (g x) 0)


/-- The explicit raw time representative is continuous jointly in time and native space. -/
theorem construction_rawTimeJet_joint_continuous {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Continuous (fun z : ℝ × XV d => kineticTimeDerivative
      (timeCutoffProfile (profileFunction h) alpha r mu R) ⟨z.1, z.2.1, z.2.2⟩) := by
  simp_rw [timeCutoffProfile_timeDerivative, barrier_timeDerivative]
  have hv : Continuous (fun z : ℝ × XV d => PDE.vecNormSq z.2.2) :=
    PDE.contDiff_vecNormSq.continuous.comp continuous_snd.snd
  have he : Continuous (fun z : ℝ × XV d => Real.exp (-mu * z.1)) :=
    (continuous_const.mul continuous_fst).rexp
  have hb : Continuous (fun z : ℝ × XV d => barrier mu R ⟨z.1, z.2.1, z.2.2⟩) :=
    he.mul (continuous_const.sub (hv.div_const _))
  exact ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp (((continuous_selectedFlatProfile h r).comp continuous_snd).sub hb)).neg.mul
    ((continuous_const.mul he).mul (continuous_const.sub (hv.div_const _)))


/-- A measurable representative of the full extended source, including the boundary. -/
def constructionIndicatorSource {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) (z : ℝ × XV d) : ℝ :=
  {y | profileFunction h y.2 < 1}.indicator
    (fun y => timeCutoffSourceRepresentative h r mu R ⟨y.1, y.2.1, y.2.2⟩) z

/-- The selected zero-extended source is jointly measurable. -/
theorem construction_indicatorSource_measurable {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R : ℝ) :
    Measurable (constructionIndicatorSource h r mu R)  := by
  have construction_rawSource_joint_measurable :
      Measurable (fun z : ℝ × XV d =>
      timeCutoffSourceRepresentative h r mu R ⟨z.1, z.2.1, z.2.2⟩) := by
    obtain ⟨hx, hv, hh⟩ := measurable_flatProfile_jets h r
    have he : Continuous (fun z : ℝ × XV d => Real.exp (-mu * z.1)) :=
      (continuous_const.mul continuous_fst).rexp
    have hvs : Continuous (fun z : ℝ × XV d => PDE.vecNormSq z.2.2) :=
      PDE.contDiff_vecNormSq.continuous.comp continuous_snd.snd
    have hb : Continuous (fun z : ℝ × XV d => barrier mu R ⟨z.1, z.2.1, z.2.2⟩) :=
      he.mul (continuous_const.sub (hvs.div_const _))
    have hs := ((continuous_selectedFlatProfile h r).comp continuous_snd).sub hb
    have ht := ((contDiff_timeCutoffTheta.continuous_deriv (by simp)).comp hs).measurable
    have ht2 : Measurable (fun z : ℝ × XV d => deriv (deriv timeCutoffTheta)
        (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩)) := by
      simp_rw [deriv2_timeCutoffTheta]
      exact measurable_const.mul
        (((contDiff_flatteningSlope.continuous_deriv (by simp)).comp
          ((continuous_const.mul hs).add continuous_const)).measurable)
    have hBG (i : Fin d) : Measurable (fun z : ℝ × XV d =>
        kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i) := by
      simp_rw [barrier_velocityGradient]
      exact (((continuous_const.mul he).div_const _).neg.mul
        ((continuous_apply i).comp continuous_snd.snd)).measurable
    have hBH (i k : Fin d) : Measurable (fun z : ℝ × XV d =>
        kineticVelocityHessian (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i k) := by
      simp only [barrier_velocityHessian, Matrix.smul_apply, smul_eq_mul]
      exact (((continuous_const.mul he).div_const _).neg.mul continuous_const).measurable
    have hpos (i : Fin d) : Measurable (fun z : ℝ × XV d =>
        flatProfilePositionJet h r z.2 i) :=
      (((measurable_pi_apply i).comp hx).comp measurable_snd)
    have hvel (i : Fin d) : Measurable (fun z : ℝ × XV d =>
        flatProfileVelocityJet h r z.2 i) :=
      (((measurable_pi_apply i).comp hv).comp measurable_snd)
    have htransport : Measurable (fun z : ℝ × XV d => PDE.vecDot z.2.2
        (fun i => deriv timeCutoffTheta
          (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
            flatProfilePositionJet h r z.2 i)) := by
      unfold PDE.vecDot
      exact Finset.measurable_sum _ (fun i _ =>
        ((measurable_pi_apply i).comp measurable_snd.snd).mul (ht.mul (hpos i)))
    have hcontraction : Measurable (fun z : ℝ × XV d => matrixContraction
        (profileMatrix h z.2) (fun i k =>
          deriv timeCutoffTheta
            (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
              (flatProfileHessian h r z.2 i k -
                kineticVelocityHessian (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i k) +
          deriv (deriv timeCutoffTheta)
            (selectedFlatProfile h r z.2 - barrier mu R ⟨z.1, z.2.1, z.2.2⟩) *
              (flatProfileVelocityJet h r z.2 i -
                kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ i) *
              (flatProfileVelocityJet h r z.2 k -
                kineticVelocityGradient (barrier mu R) ⟨z.1, z.2.1, z.2.2⟩ k))) := by
      unfold matrixContraction
      exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun k _ =>
        ((((selectedProfile_spec h).2.2.2.2.1) i k).comp measurable_snd).mul
          ((ht.mul (((hh i k).comp measurable_snd).sub (hBH i k))).add
            ((ht2.mul ((hvel i).sub (hBG i))).mul ((hvel k).sub (hBG k))))))
    simpa [timeCutoffSourceRepresentative, timeCutoffProfile_timeDerivative] using! (((construction_rawTimeJet_joint_continuous h r mu R).measurable).add htransport).sub hcontraction
  exact (construction_rawSource_joint_measurable).indicator
    (isOpen_lt (((selectedProfile_spec h).2.2.2.2.2.2.1).comp continuous_snd) continuous_const).measurableSet




/-- The spacetime indicator uses exactly the fixed-time profile domain. -/
theorem constructionIndicatorSource_apply {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R t : ℝ) (q : XV d) :
    constructionIndicatorSource h r mu R (t, q) =
      {y | profileFunction h y < 1}.indicator
        (fun y => timeCutoffSourceRepresentative h r mu R ⟨t, y.1, y.2⟩) q := by
  by_cases hp : profileFunction h q < 1 <;> simp [constructionIndicatorSource, hp]


/-- Jointly measurable fixed-time almost-everywhere inequalities lift to spacetime. -/
theorem construction_fixed_time_le_ae_spacetime {d : ℕ} (f g : ℝ × XV d → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ t : ℝ, ∀ᵐ q ∂volume, f (t, q) ≤ g (t, q)) :
    ∀ᵐ P : KineticPoint d ∂volume,
      f (KineticPoint.equivProd d P) ≤ g (KineticPoint.equivProd d P) := by
  have hs : MeasurableSet {z | f z ≤ g z} := measurableSet_le hf hg
  have hp : ∀ᵐ z : ℝ × XV d ∂volume, f z ≤ g z :=
    (Measure.ae_prod_iff_ae_ae hs).mpr (Eventually.of_forall hfg)
  exact (KineticPoint.measurePreserving_equivProd d).quasiMeasurePreserving.ae hp


/-- A stationary spatial field acquires precisely the finite time-measure factor. -/
theorem construction_eLpNorm_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y) [SFinite nu] (f : Y → ℝ) (hf : Measurable f)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun q : X × Y => f q.2) p (mu.prod nu) =
      (mu Set.univ) ^ (1 / p.toReal) * eLpNorm f p nu := by
  have hm : Measurable (fun q : X × Y => f q.2) := hf.comp measurable_snd
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hm.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable]
  rw [lintegral_prod _ (hm.enorm.pow_const p.toReal).aemeasurable]
  simp only [lintegral_const]
  rw [ENNReal.mul_rpow_of_nonneg]
  · rw [mul_comm]
  · exact (one_div_pos.mpr (ENNReal.toReal_pos hp0 hpTop)).le





/-- A concrete positive sequence stays strictly below a prescribed positive threshold. -/
theorem construction_exists_scales (r0 : ℝ) (hr0 : 0 < r0) :
    ∃ r : ℕ → ℝ, (∀ j, 0 < r j ∧ r j < r0) ∧ Tendsto r atTop (nhds 0) := by
  let r : ℕ → ℝ := fun j => r0 * (1 / ((j : ℝ) + 2))
  refine ⟨r, ?_, ?_⟩
  · intro j
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    constructor
    · exact mul_pos hr0 (div_pos zero_lt_one (by linarith))
    · change r0 * (1 / ((j : ℝ) + 2)) < r0
      have hi : 1 / ((j : ℝ) + 2) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
      simpa using mul_lt_mul_of_pos_left hi hr0
  · have hh := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh' : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 2)) atTop (nhds 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hh
    simpa only [mul_zero] using hh'.const_mul r0


/-- Shell domination lifts to the literal spacetime source norm, with the finite time
factor and no change to the selected profile witnesses. -/
theorem construction_indicatorSource_norm_le {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict {q | profileFunction h q < 1})   := by
  have construction_extended_positive_source_le_shell_ae (t : ℝ) :
      ∀ᵐ q : XV d ∂volume,
      max (constructionExtendedSource h r mu R m (profileMatrix h) ⟨t, q.1, q.2⟩) 0 ≤
        {y | profileFunction h y < 1}.indicator
          (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r) q := by
    have he := construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m
      hr hmu hR hm hscale hmargin t
    have hb := timeCutoff_source_le_of_profile hd h r hr R hR t
    have hn := flatSource_nonneg_ae_of_profile h r hr
    filter_upwards [he, hb, hn] with q hq hbq hnq
    rw [hq]
    by_cases hprof : q ∈ {y | profileFunction h y < 1}
    · rw [indicator_of_mem hprof, indicator_of_mem hprof]
      rw [hrate]
      exact max_le hbq hnq
    · rw [indicator_of_notMem hprof, indicator_of_notMem hprof, max_self]
  have construction_stationary_indicator_norm_le {d : ℕ} (D : Set (XV d)) (hD : MeasurableSet D) (f : XV d → ℝ) (hf : Measurable f) :
      eLpNorm (fun P : KineticPoint d => D.indicator f (P.position, P.velocity)) p
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
      (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) *
        eLpNorm f p (volume.restrict D) := by
    have construction_stationary_norm_le {d : ℕ} (f : XV d → ℝ) (hf : Measurable f) :
        eLpNorm (fun P : KineticPoint d => f (P.position, P.velocity)) p
        (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)) ≤
        (volume (Ioo (T - S ^ 2) T)) ^ (1 / p.toReal) * eLpNorm f p volume := by
      let D : Set (ℝ × XV d) := Ioo (T - S ^ 2) T ×ˢ univ
      let e := KineticPoint.equivProd d
      have hD : MeasurableSet D := measurableSet_Ioo.prod MeasurableSet.univ
      have hsub : backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S ⊆ e ⁻¹' D := by
        intro P hP
        have hh := (construction_mem_cylinder_iff T S hS P).mp hP
        exact ⟨⟨hh.1, hh.2.1⟩, mem_univ _⟩
      apply (eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hsub)).trans_eq
      have he := eLpNorm_comp_measurePreserving (p := p)
        (hf.comp measurable_snd).aestronglyMeasurable.restrict ((KineticPoint.measurePreserving_equivProd d).restrict_preimage hD)
      change eLpNorm ((fun z : ℝ × XV d => f z.2) ∘ e) p
        (volume.restrict (e ⁻¹' D)) = _
      apply he.trans
      rw [Measure.volume_eq_prod, ← Measure.restrict_prod_eq_prod_univ]
      simpa only [Function.comp_def, Measure.restrict_apply_univ] using
        construction_eLpNorm_snd (volume.restrict (Ioo (T - S ^ 2) T)) volume f hf p hp0 hpTop
    simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hD] using
      construction_stationary_norm_le (D.indicator f) (hf.indicator hD)
  obtain ⟨_, _, _, _, hAm, _, hH, _, _, _, _, hgv, _⟩ := selectedProfile_spec h
  let f := flatSourceWithJet (profileMatrix h) (profileFunction h)
    (profileVelocityJet h) alpha r
  let D := {q | profileFunction h q < 1}
  have hD : MeasurableSet D := (isOpen_lt hH continuous_const).measurableSet
  have hf : Measurable f := measurable_flatSourceWithJet _ _ _ _ _ hAm hH.measurable hgv
  have hbound := construction_fixed_time_le_ae_spacetime
    (fun z => max (constructionIndicatorSource h r mu R z) 0)
    (fun z => D.indicator f z.2)
    ((construction_indicatorSource_measurable h r mu R).max measurable_const)
    ((hf.indicator hD).comp measurable_snd) ?_
  · have hm := ((construction_indicatorSource_measurable h r mu R).comp
        (KineticPoint.measurable_equivProd d)).max (measurable_const (a := 0))
    have hn := eLpNorm_mono_ae_real (p := p)
      (g := fun P : KineticPoint d => D.indicator f (P.position, P.velocity))
      (μ := volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S))
      hm.aestronglyMeasurable.restrict
      (ae_restrict_of_ae (hbound.mono (fun P hP => by
        simpa only [Real.norm_of_nonneg (le_max_right _ _)] using! hP)))
    apply hn.trans
    have he : eLpNorm f p (volume.restrict D) =
        eLpNorm (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha r)
          p (volume.restrict D) :=
      eLpNorm_congr_ae (ae_restrict_of_ae
        (flatSource_ae_eq_jet_of_profile h r).symm)
    simpa only [he] using construction_stationary_indicator_norm_le D hD f hf
  · intro t
    filter_upwards [construction_extended_positive_source_le_shell_ae t,
      construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
        hscale hmargin t, flatSource_ae_eq_jet_of_profile h r] with q hb he hjet
    rw [constructionIndicatorSource_apply, ← he]
    by_cases hq : q ∈ D
    · rw [indicator_of_mem hq]
      have hb' := hb
      rw [indicator_of_mem hq, hjet] at hb'
      exact hb'
    · rw [indicator_of_notMem hq]
      change q ∉ {y | profileFunction h y < 1} at hq
      simpa only [indicator_of_notMem hq] using hb

/-- Positive selected sources tend to zero on the fixed cylinder as the flattening
scales tend to zero in the full subcritical range. -/
theorem construction_indicatorSource_norm_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (mu R m T S p : ℝ)
    (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (r : ℕ → ℝ) (hr : ∀ j, 0 < r j) (hs : ∀ j, 2 * Real.rpow (r j) alpha ≤ 1)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (fun P : KineticPoint d =>
      max (constructionIndicatorSource h (r j) mu R (KineticPoint.equivProd d P)) 0)
      (ENNReal.ofReal p)
      (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0)  := by
  let hexponent := he
  have construction_flat_source_decay_of_profile :
      Tendsto (fun j => eLpNorm
      (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j))
      (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}))
      atTop (nhds 0) := by
    obtain ⟨C, r0, hC, hr0, hb⟩ := flat_source_eLpNorm_le_of_profile d alpha p ha ha1 hp h
    have he : ∀ᶠ j in atTop, r j < r0 := hlim.eventually (gt_mem_nhds hr0)
    have hpow0 : Tendsto (fun j => Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))
        atTop (nhds 0) := by
      simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow hexponent.ne'] using ((Real.continuous_rpow_const hexponent.le).tendsto 0 |>.comp hlim)
    have hup : Tendsto (fun j => ENNReal.ofReal
        (C * Real.rpow (r j) (alpha - 2 + 4 * (d : ℝ) / p))) atTop (nhds 0) := by
      simpa [Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (hpow0.const_mul C)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    · exact Eventually.of_forall (fun _ => bot_le)
    · filter_upwards [he] with j hj
      exact hb (r j) (hr j) hj
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  let C := (volume (Ioo (T - S ^ 2) T)) ^ (1 / (ENNReal.ofReal p).toReal)
  have hC : C ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg
    (by positivity) (measure_Ioo_lt_top.ne)
  have hu0 : Tendsto (fun j => C * eLpNorm
      (flatSource (profileMatrix h) (profileFunction h) flatteningPsi alpha (r j))
      (ENNReal.ofReal p) (volume.restrict {q | profileFunction h q < 1}))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using! (ENNReal.continuous_const_mul hC).tendsto 0 |>.comp (construction_flat_source_decay_of_profile)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu0
    (fun _ => bot_le) (fun j => construction_indicatorSource_norm_le hd ha ha1 h
      (r j) mu R m T S (hr j) hmu hR hm hS hrate (hs j) hmargin _ hp0 hpTop)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

section



namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Filter MeasureTheory Set HypoellipticAleksandrov.Parabolic
open scoped Topology Convolution ENNReal MatrixOrder Matrix.Norms.Elementwise

/-- The same strictly interior point retains the required height for every late kernel. -/
theorem construction_smoothed_interior_height_eventually {d : ℕ} {alpha : ℝ}
    (h : CounterProfileStatement d alpha) (r mu R S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hS : 0 < S)
    (hTS : barrierTime mu < S ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hsmall : flatteningOffset * Real.rpow r alpha ≤ 1 / 4)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2) :
    ∃ P ∈ backwardCylinder (⟨barrierTime mu, 0, 0⟩ : KineticPoint d) S,
      ∀ᶠ n in atTop, (1 / 4 : ℝ) ≤
        smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) P := by
  obtain ⟨_, _, _, _, _, _, _, h0, _⟩ := selectedProfile_spec h
  obtain ⟨t, ht, hT, hh⟩ := timeCutoff_interior_height (profileFunction h)
    alpha r mu R h0 hr hmu hsmall
  have hq : profileFunction h (0, 0) < 1 := by
    change profileFunction h 0 < 1
    rw [h0]
    norm_num
  have hh' : 5 / 16 < zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, 0, 0⟩ := by
    rw [(zeroExtendedProfile_eq_raw_on_profile (profileFunction h) alpha r mu R hr hmu hR hvel (⟨t, 0, 0⟩ : KineticPoint d) hq)]
    exact hh
  refine ⟨⟨t, 0, 0⟩, construction_origin_mem_cylinder _ S t hS hTS ht hT, ?_⟩
  filter_upwards [(mollify_preserves_height_eventually (fun q : XV d => zeroExtendedProfile (profileFunction h) alpha r mu R ⟨t, q.1, q.2⟩) (continuous_zeroExtendedProfile_spatial_of_profile h r mu R hr hmu hR hscale hvel t) 0 hh')] with n hn
  exact hn.le


/-- The normalized mollifier respects an essential bound, without changing the selected
representative on its exceptional null set. -/
theorem construction_spatialMollify_norm_le_ae {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
    [FiniteDimensional ℝ G] [Measure.IsAddHaarMeasure (volume : Measure G)]
    (phi : ContDiffBump (0 : G)) (g : G → ℝ) (hg : AEStronglyMeasurable g volume)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂volume, |g x| ≤ C) (q : G) :
    ‖spatialMollify phi g q‖ ≤ C := by
  let f := fun x => max (-C) (min (g x) C)
  have hf : AEStronglyMeasurable f volume :=
    (aemeasurable_const.max (hg.aemeasurable.min aemeasurable_const)).aestronglyMeasurable
  have he : f =ᵐ[volume] g := by
    filter_upwards [hb] with x hx
    have hh := abs_le.mp hx
    simp only [f, min_eq_left hh.2, max_eq_right hh.1]
  have hfB : ∀ x, ‖f x‖ ≤ C := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (neg_le_self hC) (min_le_right _ _)
  have hc : spatialMollify phi f = spatialMollify phi g := by
    exact convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      (Filter.Eventually.of_forall (fun _ => rfl)) he
  rw [← hc]
  exact spatialMollify_norm_le phi f hf C hC hfB q


/-- Each extended first component has a global essential spatial bound uniform on a
compact time interval, using the same selected weak representative as the convolution. -/
theorem construction_extendedGradient_uniform_ae_bound {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m a b : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (i : Fin (d + d)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ᵐ q ∂volume, |constructionExtendedNativeGradient h r mu R m t q i| ≤ C := by
  let K := (spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}
  have hK : IsCompact K := (isCompact_profile_unit_sublevel ha h).image
    (spatialCoordinateCLE d).symm.continuous
  obtain ⟨C, hC, hb⟩ := construction_rawGradient_uniform_bound h r hr mu R a b K hK i
  refine ⟨C, hC, fun t ht => ?_⟩
  filter_upwards [(construction_ae_native _ (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm hscale (fun q hq => (hmargin q hq).le) t))] with q hq
  let x := (spatialCoordinateCLE d).symm q
  by_cases hp : profileFunction h q < 1
  · have hp' : profileFunction h (spatialCoordinateCLE d x) < 1 := by
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
    rw [constructionExtendedNativeGradient,
      (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x hp').1 i]
    exact hb t ht x ⟨q, hp.le, rfl⟩
  · have hp' : 1 ≤ profileFunction h (spatialCoordinateCLE d x) := by
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp
    change |constructionExtendedPackedGradient h r mu R m t x i| ≤ C
    rw [(hq hp').1 i, abs_zero]
    exact hC

/-- Each extended second component has a global essential spatial bound uniform on a
compact time interval; the profile boundary contributes no extra representative. -/
theorem construction_extendedHessian_uniform_ae_bound {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m a b : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (i k : Fin d) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b,
      ∀ᵐ q ∂volume, |constructionExtendedNativeHessian h r mu R m t q i k| ≤ C := by
  let K := (spatialCoordinateCLE d).symm '' {q | profileFunction h q ≤ 1}
  have hK : IsCompact K := (isCompact_profile_unit_sublevel ha h).image
    (spatialCoordinateCLE d).symm.continuous
  obtain ⟨C, hC, hb⟩ := construction_rawHessian_uniform_bound h r hr mu R a b K hK i k
  refine ⟨C, hC, fun t ht => ?_⟩
  filter_upwards [(construction_ae_native _ (construction_extended_jets_zero_outside_profile hd ha ha1 h r mu R m hr hmu hR hm hscale (fun q hq => (hmargin q hq).le) t))] with q hq
  let x := (spatialCoordinateCLE d).symm q
  by_cases hp : profileFunction h q < 1
  · have hp' : profileFunction h (spatialCoordinateCLE d x) < 1 := by
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using hp
    rw [constructionExtendedNativeHessian,
      (construction_extended_jets_eq_raw_on_profile h r mu R m t hm hmargin x hp').2 i k]
    exact hb t ht x ⟨q, hp.le, rfl⟩
  · have hp' : 1 ≤ profileFunction h (spatialCoordinateCLE d x) := by
      simpa only [x, ContinuousLinearEquiv.apply_symm_apply] using not_lt.mp hp
    change |constructionExtendedPackedHessian h r mu R m t x i k| ≤ C
    rw [(hq hp').2 i k, abs_zero]
    exact hC


/-- The actual operator is bounded uniformly over all smoothing radii on a bounded
velocity region and compact time interval. All convolution bounds are essential bounds
of the selected representatives, rather than assumptions on the classical derivatives. -/
theorem construction_smoothedOperator_uniform_bound {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m a b S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 ≤ S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (A : XV d → PDE.Mat d) (AC : ℝ) (hAC : 0 ≤ AC)
    (hAb : ∀ q i k, |A q i k| ≤ AC) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ phi : ContDiffBump (0 : XV d), ∀ P : KineticPoint d,
      P.time ∈ Icc a b → (∀ i, |P.velocity i| ≤ S) →
      |backwardOperator (fun _t x v => A (x, v))
        (smoothedZeroExtendedProfile h r mu R phi) P| ≤ C  := by
  have construction_extendedTimeJet_uniform_bound :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ q,
      |constructionExtendedTimeJet h r mu R t q| ≤ C := by
    let K := Icc a b ×ˢ {q | profileFunction h q ≤ 1}
    have hK : IsCompact K := isCompact_Icc.prod (isCompact_profile_unit_sublevel ha h)
    obtain ⟨C, hC, hb⟩ := construction_compact_scalar_bound K hK _
      (construction_rawTimeJet_joint_continuous h r mu R)
    refine ⟨C, hC, fun t ht q => ?_⟩
    by_cases hp : profileFunction h q < 1
    · have hq : q ∈ {y | profileFunction h y < 1} := hp
      rw [constructionExtendedTimeJet, indicator_of_mem hq]
      exact hb (t, q) ⟨ht, hp.le⟩
    · have hq : q ∉ {y | profileFunction h y < 1} := hp
      rw [constructionExtendedTimeJet, indicator_of_notMem hq, abs_zero]
      exact hC
  have hg (i : Fin d) := construction_extendedGradient_uniform_ae_bound hd ha ha1 h
    r mu R m a b hr hmu hR hm hscale hmargin (Fin.castAdd d i)
  have hh (i k : Fin d) := construction_extendedHessian_uniform_ae_bound hd ha ha1 h
    r mu R m a b hr hmu hR hm hscale hmargin i k
  choose G hG hbG using hg
  choose H hH hbH using hh
  obtain ⟨CT, hCT, hbCT⟩ := construction_extendedTimeJet_uniform_bound
  let C := CT + (∑ i : Fin d, S * G i) + ∑ i : Fin d, ∑ k : Fin d, AC * H i k
  have hC : 0 ≤ C := add_nonneg
    (add_nonneg hCT (Finset.sum_nonneg (fun i _ => mul_nonneg hS (hG i))))
    (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun k _ => mul_nonneg hAC (hH i k))))
  refine ⟨C, hC, fun phi P ht hv => ?_⟩
  have hgg (i : Fin d) := construction_spatialMollify_norm_le_ae phi
    (fun q => constructionExtendedNativeGradient h r mu R m P.time q (Fin.castAdd d i))
    (construction_locallyIntegrable_native _
      (construction_extendedGradient_locallyIntegrable h r hr mu R m P.time
        (Fin.castAdd d i))).aestronglyMeasurable
    (G i) (hG i) (hbG i P.time ht) (P.position, P.velocity)
  have hhh (i k : Fin d) := construction_spatialMollify_norm_le_ae phi
    (fun q => constructionExtendedNativeHessian h r mu R m P.time q i k)
    (construction_locallyIntegrable_native _

        (construction_extendedHessian_locallyIntegrable h r hr mu R
          m P.time i k)).aestronglyMeasurable
    (H i k) (hH i k) (hbH i k P.time ht) (P.position, P.velocity)
  rw [construction_smoothed_operator_eq hd ha ha1 h r mu R m hr hmu hR hm hscale
    (fun q hq => (hmargin q hq).le)]
  apply (abs_sub _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    apply add_le_add
    · simpa using (construction_spatialMollify_norm_le_ae phi (constructionExtendedTimeJet h r mu R P.time) (construction_extendedTimeJet_locallyIntegrable h r mu R P.time).aestronglyMeasurable CT hCT (Filter.Eventually.of_forall (hbCT P.time ht)) (P.position, P.velocity))
    · unfold PDE.vecDot
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hv i) (by simpa using hgg i)
        (abs_nonneg _) hS
  · unfold matrixContraction
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    rw [abs_mul]
    exact mul_le_mul (hAb _ i k) (by simpa using hhh i k)
      (abs_nonneg _) hAC


/-- Spatial smoothing of each fixed flattened cutoff recovers the positive source in
finite-exponent norm on the fixed cylinder, without an analytic premise. -/
theorem construction_positiveSource_error_tendsto {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (r mu R m T S : ℝ)
    (hr : 0 < r) (hmu : 0 < mu) (hR : 0 < R) (hm : m < R ^ 2) (hS : 0 < S)
    (hscale : 2 * Real.rpow r alpha ≤ 1)
    (hmargin : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < m)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (fun P =>
      max (backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P) 0 -
      max (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)) 0)
      p (volume.restrict (backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S)))
      atTop (𝓝 0)  := by
  have construction_smoothedOperator_tendsto_ae_spacetime :
      ∀ᵐ P : KineticPoint d ∂volume, Tendsto (fun n =>
      backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P)
      atTop (𝓝 (constructionIndicatorSource h r mu R (KineticPoint.equivProd d P))) := by
    have hA := (selectedProfile_spec h).2.2.2.2.1
    have hF (n : ℕ) := measurable_backwardOperator_of_joint_smooth (profileMatrix h) hA
      (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
    have he := construction_fixed_time_tendsto_ae_spacetime
      (fun n z => backwardOperator (fun _t x v => profileMatrix h (x, v))
        (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n))
        ((KineticPoint.equivProd d).symm z)) (constructionIndicatorSource h r mu R)
      (fun n => (hF n).comp (KineticPoint.measurable_equivProd_symm d))
      (construction_indicatorSource_measurable h r mu R) ?_
    · simpa only [Equiv.symm_apply_apply] using! he
    · intro t
      filter_upwards [construction_smoothed_operator_tendsto_ae hd ha ha1 h r mu R m
        hr hmu hR hm hscale (fun q hq => (hmargin q hq).le) (profileMatrix h) t,
        construction_extendedSource_eq_indicator_ae hd ha ha1 h r mu R m hr hmu hR hm
          hscale hmargin t] with q hq heq
      simpa only [constructionIndicatorSource_apply,
        ← heq] using! hq
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  have hQm : MeasurableSet Q := (isOpen_backwardCylinder _ _ hS).measurableSet
  have : IsFiniteMeasure nu := ⟨by
    simpa only [nu, Measure.restrict_apply_univ] using
      (backwardCylinder_volume_lt_top (⟨T, 0, 0⟩ : KineticPoint d) S hS)⟩
  let F := fun n P => backwardOperator (fun _t x v => profileMatrix h (x, v))
    (smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n)) P
  let g := fun P => constructionIndicatorSource h r mu R (KineticPoint.equivProd d P)
  have hA := (selectedProfile_spec h).2.2.2.2.1
  have hF (n : ℕ) : Measurable (F n) :=
    measurable_backwardOperator_of_joint_smooth (profileMatrix h) hA _
      (smoothedZeroExtendedProfile_contDiff ha h r mu R hr hmu hR
        (fun q hq => (hmargin q hq).trans hm) (standardMollifierSequence n))
  have hg : Measurable g := (construction_indicatorSource_measurable h r mu R).comp
    (KineticPoint.measurable_equivProd d)
  let AC := 3 * (|profileLowerEllipticity h| + |profileUpperEllipticity h|)
  have hAC : 0 ≤ AC := mul_nonneg (by norm_num) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hAb q i k : |profileMatrix h q i k| ≤ AC :=
    coefficient_entry_abs_le_of_ellipticity
      ((selectedProfile_spec h).2.2.2.2.2.1 q).1
      ((selectedProfile_spec h).2.2.2.2.2.1 q).2 i k
  obtain ⟨C, hC, hb⟩ := construction_smoothedOperator_uniform_bound hd ha ha1 h
    r mu R m (T - S ^ 2) T S hr hmu hR hm hS.le hscale hmargin
    (profileMatrix h) AC hAC hAb
  have hFb (n : ℕ) : ∀ᵐ P ∂nu, |F n P| ≤ C := by
    filter_upwards [ae_restrict_mem hQm] with P hP
    have hh := (construction_mem_cylinder_iff T S hS P).mp hP
    exact hb (standardMollifierSequence n) P ⟨hh.1.le, hh.2.1.le⟩
      (fun i => (PDE.abs_apply_le_vecEuclideanNorm P.velocity i).trans hh.2.2.1.le)
  have hl : ∀ᵐ P ∂nu, Tendsto (fun n => F n P) atTop (𝓝 (g P)) :=
    ae_restrict_of_ae (construction_smoothedOperator_tendsto_ae_spacetime)
  have hgb : ∀ᵐ P ∂nu, |g P| ≤ C := by
    filter_upwards [hl, ae_all_iff.mpr hFb] with P hP hbP
    exact le_of_tendsto' hP.abs hbP
  exact construction_positive_part_error_tendsto nu p hp0 hpTop F g
    (fun n => (hF n).aestronglyMeasurable) hg.aestronglyMeasurable C hC hFb hgb hl


/-- For any fixed internally justified geometry, the literal measurable family is
constructed by a separate spatial smoothing scale for each flattening scale. -/
theorem construction_measurableFamily_of_geometry {d : ℕ} (hd : 1 ≤ d)
    {alpha : ℝ} (ha : 0 < alpha) (ha1 : alpha < 1)
    (h : CounterProfileStatement d alpha) (p R mu S : ℝ)
    (hp : 1 ≤ p) (he : 0 < alpha - 2 + 4 * (d : ℝ) / p)
    (hR : 0 < R) (hmu : 0 < mu) (hS : 0 < S)
    (hrate : mu = (d : ℝ) * profileLowerEllipticity h / R ^ 2)
    (hTS : barrierTime mu < S ^ 2)
    (hvel : ∀ q, profileFunction h q ≤ 1 → PDE.vecNormSq q.2 < R ^ 2)
    (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) :
    MeasurableFamilyStatement d p (profileLowerEllipticity h) (profileUpperEllipticity h)
      ⟨barrierTime mu, 0, 0⟩ S    := by
  have construction_small_scale_threshold :
      ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      flatteningOffset * Real.rpow r alpha ≤ 1 / 4 ∧
      2 * Real.rpow r alpha ≤ 7 / 8 := by
    have hc : 0 < flatteningOffset := zero_lt_one.trans flatteningOffset_bounds.1
    let a : ℝ := 1 / (4 * flatteningOffset)
    have hap : 0 < a := div_pos zero_lt_one (mul_pos (by norm_num) hc)
    let r0 : ℝ := Real.rpow a alpha⁻¹
    have hr0 : 0 < r0 := Real.rpow_pos_of_pos hap _
    have hpower : Real.rpow r0 alpha = a := Real.rpow_inv_rpow hap.le ha.ne'
    refine ⟨r0, hr0, ?_⟩
    intro r hr hrr
    have hp := Real.rpow_le_rpow hr.le hrr.le ha.le
    change Real.rpow r alpha ≤ Real.rpow r0 alpha at hp
    rw [hpower] at hp
    have hca : flatteningOffset * a = 1 / 4 := by dsimp [a]; field_simp
    have hb : flatteningOffset * Real.rpow r alpha ≤ 1 / 4 := by
      calc
        _ ≤ flatteningOffset * a := mul_le_mul_of_nonneg_left hp hc.le
        _ = _ := hca
    have hpow := (Real.rpow_pos_of_pos hr alpha).le
    have hco := mul_le_mul_of_nonneg_right flatteningOffset_bounds.1.le hpow
    constructor
    · exact hb
    · simp only [Real.rpow_eq_pow] at hb hpow hco ⊢
      nlinarith
  have construction_smoothed_boundary_eventually (T : ℝ) (S : ℝ) (hS : 0 < S) (hTS : T < S ^ 2) (hgeom : ∀ q, profileFunction h q ≤ 1 →
      PDE.vecEuclideanNorm q.1 < S ^ 3 ∧ PDE.vecEuclideanNorm q.2 < S) (r : ℝ) (mu : ℝ) (R : ℝ) :
      ∀ᶠ n in atTop, ∀ P : KineticPoint d,
      P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
      smoothedZeroExtendedProfile h r mu R (standardMollifierSequence n) P = 0 := by
    have construction_exists_smoothing_collar :
        ∃ delta : ℝ, 0 < delta ∧ ∀ (r mu R : ℝ) (phi : ContDiffBump 0),
        phi.rOut < delta → ∀ P : KineticPoint d,
        P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S →
        smoothedZeroExtendedProfile h r mu R phi P = 0 := by
      let box : Set (XV d) := {q | PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧
        PDE.vecNormSq q.2 < S ^ 2}
      have ho : IsOpen box :=
        (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_fst) continuous_const).inter
          (isOpen_lt (PDE.contDiff_vecNormSq.continuous.comp continuous_snd) continuous_const)
      have hsub : {q | profileFunction h q ≤ 1} ⊆ box := by
        intro q hq
        have hh := hgeom q hq
        have hx := PDE.vecEuclideanNorm_nonneg q.1
        have hv := PDE.vecEuclideanNorm_nonneg q.2
        have hs3 := pow_pos hS 3
        change PDE.vecNormSq q.1 < (S ^ 3) ^ 2 ∧ PDE.vecNormSq q.2 < S ^ 2
        rw [← PDE.vecEuclideanNorm_sq, ← PDE.vecEuclideanNorm_sq]
        constructor <;> nlinarith
      have hK := isCompact_profile_unit_sublevel ha h
      obtain ⟨delta, hd, hb⟩ := hK.exists_thickening_subset_open ho hsub
      refine ⟨delta, hd, ?_⟩
      intro r mu R phi hphi P hP
      have hfaces : P.time = T - S ^ 2 ∨
          P.velocity ∈ PDE.euclideanSphere 0 S ∨
          P.position ∈ PDE.euclideanSphere 0 (S ^ 3) := by
        simpa [relativePosition, or_assoc] using hP.2
      rcases hfaces with ht | hv | hx
      · apply smoothedZeroExtendedProfile_eq_zero_of_time
        change P.time = T - S ^ 2 at ht
        linarith
      · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
        intro hq
        have hh := hb (Metric.thickening_mono hphi.le _ hq)
        have he : PDE.vecNormSq P.velocity = S ^ 2 := by
          simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hv
        exact (ne_of_lt hh.2) he
      · apply smoothedZeroExtendedProfile_eq_zero_outside_thickening
        intro hq
        have hh := hb (Metric.thickening_mono hphi.le _ hq)
        have he : PDE.vecNormSq P.position = (S ^ 3) ^ 2 := by
          simpa [PDE.euclideanSphere, PDE.euclideanSqDist] using hx
        exact (ne_of_lt hh.1) he
    obtain ⟨delta, hd, hb⟩ := construction_exists_smoothing_collar
    have hr := standardMollifierSequence_rOut_tendsto (G := XV d)
    filter_upwards [hr.eventually (Iio_mem_nhds hd)] with n hn
    exact hb r mu R (standardMollifierSequence n) hn
  have construction_diagonal_choice (error : ℕ → ℕ → ℝ≥0∞) (herr : ∀ j, Tendsto (error j) atTop (nhds 0)) (good : ℕ → ℕ → Prop) (hgood : ∀ j, ∀ᶠ k in atTop, good j k) :
      ∃ scale : ℕ → ℕ,
      (∀ j, good j (scale j) ∧
        error j (scale j) < ENNReal.ofReal (1 / ((j : ℝ) + 1))) ∧
      Tendsto (fun j => error j (scale j)) atTop (nhds 0) := by
    classical
    have hchoose : ∀ j, ∃ k, good j k ∧
        error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
      intro j
      have hp : 0 < (1 / ((j : ℝ) + 1)) := by positivity
      have he : ∀ᶠ k in atTop,
          error j k < ENNReal.ofReal (1 / ((j : ℝ) + 1)) :=
        (herr j).eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hp))
      exact ((hgood j).and he).exists
    choose scale hs using hchoose
    refine ⟨scale, hs, ?_⟩
    have hu : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1)))
        atTop (nhds 0) := by
      simpa [Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => bot_le) (fun j => (hs j).2.le)
  obtain ⟨m, hm, hmargin⟩ := construction_exists_strict_velocity_margin ha h R hvel
  obtain ⟨r0, hr0, hsmall⟩ := construction_small_scale_threshold
  obtain ⟨r, hr, hlim⟩ := construction_exists_scales r0 hr0
  have hscale (j : ℕ) : 2 * Real.rpow (r j) alpha ≤ 1 :=
    ((hsmall (r j) (hr j).1 (hr j).2).2).trans (by norm_num)
  have hheight (j : ℕ) : flatteningOffset * Real.rpow (r j) alpha ≤ 1 / 4 :=
    (hsmall (r j) (hr j).1 (hr j).2).1
  let T := barrierTime mu
  let Q := backwardCylinder (⟨T, 0, 0⟩ : KineticPoint d) S
  let nu := volume.restrict Q
  let pE := ENNReal.ofReal p
  have hpE : 1 ≤ pE := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hp0 : pE ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hp)).ne'
  have hpTop : pE ≠ ∞ := ENNReal.ofReal_ne_top
  let U := fun j n => smoothedZeroExtendedProfile h (r j) mu R (standardMollifierSequence n)
  let g := fun j P => max (constructionIndicatorSource h (r j) mu R
    (KineticPoint.equivProd d P)) 0
  let f := fun j n P => max (backwardOperator (fun _t x v => profileMatrix h (x, v))
    (U j n) P) 0
  let error := fun j n => eLpNorm (fun P => f j n P - g j P) pE nu
  have herr (j : ℕ) : Tendsto (error j) atTop (𝓝 0) :=
    construction_positiveSource_error_tendsto hd ha ha1 h (r j) mu R m T S
      (hr j).1 hmu hR hm hS (hscale j) hmargin pE hp0 hpTop
  let good := fun j n =>
    (∀ P, P ∈ initialFullLateralBoundary (⟨T, 0, 0⟩ : KineticPoint d) S → U j n P = 0) ∧
    (∃ P ∈ Q, (1 / 4 : ℝ) ≤ U j n P)
  have hgood (j : ℕ) : ∀ᶠ n in atTop, good j n := by
    obtain ⟨P, hP, hh⟩ := construction_smoothed_interior_height_eventually h (r j) mu R S
      (hr j).1 hmu hR hS hTS (hscale j) (hheight j) hvel
    filter_upwards [construction_smoothed_boundary_eventually T S hS hTS hgeom
      (r j) mu R, hh] with n hn hhP
    exact ⟨hn, P, hP, hhP⟩
  obtain ⟨scale, hs, heLim⟩ := construction_diagonal_choice error herr good hgood
  refine ⟨profileMatrix h, fun j => U j (scale j),
    (selectedProfile_spec h).2.2.2.2.1, (selectedProfile_spec h).2.2.2.2.2.1,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact smoothedZeroExtendedProfile_contDiff ha h (r j) mu R (hr j).1 hmu hR hvel _
  · intro j P
    exact smoothedZeroExtendedProfile_nonneg h (r j) mu R _ P
  · intro j P hP
    exact (hs j).1.1 P hP
  · intro j
    exact (hs j).1.2
  · have hgLim : Tendsto (fun j => eLpNorm (g j) pE nu) atTop (𝓝 0) :=
      construction_indicatorSource_norm_tendsto hd ha ha1 h mu R m T S p hmu hR hm hS
        hrate hmargin hp he r (fun j => (hr j).1) hscale hlim
    have hu : Tendsto (fun j => error j (scale j) + eLpNorm (g j) pE nu)
        atTop (𝓝 0) := by
      simpa using heLim.add hgLim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ => bot_le)
    intro j
    have hn := eLpNorm_add_le (p := pE) (μ := nu)
      (f := fun P => f j (scale j) P - g j P) (g := g j) hpE
    have heq : (fun P => f j (scale j) P - g j P) + g j = f j (scale j) := by
      funext P
      simp only [Pi.add_apply, sub_add_cancel]
    rw [heq] at hn
    exact hn

/-- The measurable family holds at the exact parameters already published to the
smooth-coefficient lane; all choices are those made in `counterParameters`. -/
theorem measurableFamily_holds (d : ℕ) (hd : 1 ≤ d) (p : ℝ)
    (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    MeasurableFamilyStatement d p (counterParameters d p).1 (counterParameters d p).2.1
      (counterParameters d p).2.2.1 (counterParameters d p).2.2.2 := by
  classical
  let h := counterProfileFor d hd p hp hpd
  have ha := counterAlpha_spec d hd p hp hpd
  let geom := construction_fixed_geometry_of_profile hd ha.1 h
  let R := geom.choose
  let mu := geom.choose_spec.choose
  let S := geom.choose_spec.choose_spec.choose
  have hg := geom.choose_spec.choose_spec.choose_spec
  have hh := construction_measurableFamily_of_geometry hd ha.1 ha.2.1 h p R mu S hp ha.2.2
    hg.1 hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1
  simpa only [counterParameters, dite_eq_left (And.intro hd (And.intro hp hpd))] using! hh


/-- Coefficient mollification after fixing each smooth function proves the literal smooth
family conjunct, with the same ellipticity bounds, cylinder and function sequence. -/
theorem smoothFamily_of_measurable {d : ℕ} {p lam Lam : ℝ}
    {P₀ : KineticPoint d} {R : ℝ} (hp : 1 ≤ p) (hR : 0 < R)
    (h : MeasurableFamilyStatement d p lam Lam P₀ R) :
    SmoothFamilyStatement d p lam Lam P₀ R := by
  classical
  obtain ⟨A, U, hA, hb, hU, hnonneg, hboundary, hheight, hsource⟩ := h
  have hpn : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hchoose : ∀ j : ℕ, ∃ k : ℕ,
      eLpNorm (fun P => matrixContraction
        (mollifiedMatrix (standardMollifierSequence k) A (P.position, P.velocity) -
          A (P.position, P.velocity)) (kineticVelocityHessian (U j) P))
        (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) <
        ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    have he := smooth_coefficient_error_tendsto A lam Lam hA hb (U j) (hU j)
      P₀ R hR (ENNReal.ofReal p) hpn ENNReal.ofReal_ne_top
    exact (he.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))).exists
  choose k hk using hchoose
  let B : ℕ → XV d → PDE.Mat d := fun j => mollifiedMatrix (standardMollifierSequence (k j)) A
  have hB j := smooth_coefficients_same_bounds (standardMollifierSequence (k j)) A lam Lam hA hb
  have hBm : ∀ j i l, Measurable (fun q => B j q i l) := by
    intro j i l
    exact ((continuous_apply l).comp ((continuous_apply i).comp (hB j).1.continuous)).measurable
  refine ⟨B, U, ?_, ?_, hU, hnonneg, hboundary, hheight, ?_⟩
  · intro j i l
    exact (ContinuousLinearMap.proj l).contDiff.comp
      ((ContinuousLinearMap.proj i).contDiff.comp (hB j).1)
  · intro j q
    exact (hB j).2 q
  · let E := fun j P => matrixContraction
      (B j (P.position, P.velocity) - A (P.position, P.velocity))
      (kineticVelocityHessian (U j) P)
    have heps : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          tendsto_one_div_add_atTop_nhds_zero_nat
    have he : Tendsto (fun j => eLpNorm (E j) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R))) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds heps
        (fun j => bot_le) (fun j => (hk j).le)
    have hlim := hsource.add he
    have hlim0 : Tendsto (fun j =>
        eLpNorm (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
          (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)) +
        eLpNorm (E j) (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
        atTop (𝓝 0) := by
      simpa only [add_zero] using! hlim
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim0
      (fun j => bot_le)
    intro j
    exact positive_source_norm_le_coefficient_error A (B j) hA (hBm j) (U j) (hU j)
      (volume.restrict (backwardCylinder P₀ R)) (ENNReal.ofReal p) hp1

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample

namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter MeasureTheory Counterexample
open scoped MatrixOrder

/-- Autonomous counterexamples for every finite exponent below `4d`, with fixed shared
ellipticity bounds and cylinder, constructed internally in both coefficient classes. -/
theorem kinetic_aleksandrov_autonomous_counterexample_aux
    (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 1 ≤ p) (hpd : p < 4 * (d : ℝ)) :
    ∃ lam Lam : ℝ, ∃ P₀ : KineticPoint d, ∃ R : ℝ,
      0 < lam ∧ lam ≤ Lam ∧ 0 < R ∧
      ((∃ A : (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ i k, Measurable (fun z => A z i k)) ∧
          (∀ z, lam • (1 : PDE.Mat d) ≤ A z ∧ A z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0)) ∧
       (∃ A : ℕ → (PDE.Vec d × PDE.Vec d) → PDE.Mat d,
        ∃ U : ℕ → KineticPoint d → ℝ,
          (∀ j i k, ContDiff ℝ (⊤ : ℕ∞) (fun z => A j z i k)) ∧
          (∀ j z, lam • (1 : PDE.Mat d) ≤ A j z ∧
            A j z ≤ Lam • (1 : PDE.Mat d)) ∧
          (∀ j, ContDiff ℝ (⊤ : ℕ∞)
            (fun q : ℝ × (PDE.Vec d × PDE.Vec d) =>
              U j ((KineticPoint.equivProd d).symm q))) ∧
          (∀ j P, 0 ≤ U j P) ∧
          (∀ j P, P ∈ initialFullLateralBoundary P₀ R → U j P = 0) ∧
          (∀ j, ∃ P ∈ backwardCylinder P₀ R, (1 / 4 : ℝ) ≤ U j P) ∧
          Tendsto (fun j => eLpNorm
            (fun P => max (backwardOperator (fun _t x v => A j (x, v)) (U j) P) 0)
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R)))
            atTop (nhds 0))) := by
  apply construction_of_families ?_ d hd p hp hpd
  intro d hd p hp hpd
  have hm := measurableFamily_holds d hd p hp hpd
  exact ⟨hm, smoothFamily_of_measurable hp
    (counterParameters_pos d hd p hp hpd).2.2 hm⟩

end HypoellipticAleksandrov.KineticAleksandrov

end

