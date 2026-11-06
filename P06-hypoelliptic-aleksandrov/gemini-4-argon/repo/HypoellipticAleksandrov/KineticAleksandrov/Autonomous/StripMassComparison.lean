module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.StripMassQuadraticCalculus
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelTheorem
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EvolutionInstance
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

/-! # Quadratic comparison for compact interior source potentials -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo Evolution Occupation
open scoped Topology
open HypoellipticAleksandrov.Parabolic

/- Closing the native interval gives precisely the scalar endpoint inequalities. -/
theorem intervalDomain_closure_bounds (H : Interval) {v }
    (hv : v ∈ closure (intervalDomain H)) : H.lo ≤ v 0 ∧ v 0 ≤ H.hi := by
  constructor
  · exact closure_minimal (fun y hy =>
      (PDE.mem_oneDimensionalAxisBox_iff.mp hy).1.le)
      (isClosed_le continuous_const (continuous_apply 0)) hv
  · exact closure_minimal (fun y hy =>
      (PDE.mem_oneDimensionalAxisBox_iff.mp hy).2.le)
      (isClosed_le (continuous_apply 0) continuous_const) hv

/- The literal interval barrier is continuous on spacetime. -/
private theorem sliceRegular_of_smooth {u D}
    (hD : IsOpen D)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' D)) (p : Point) (hp : p ∈ D) :
    IsSliceRegularAt u p := by
  have hx : (evolutionHomeomorph 1).symm p ∈ evolutionHomeomorph 1 ⁻¹' D := by
    simpa using hp
  have hj := hu.contDiffAt
    ((hD.preimage (evolutionHomeomorph 1).continuous).mem_nhds hx)
  have h := (hj.of_le (by simp : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).comp
      (p.time, p.position, p.velocity) (evolutionProdCLE 1).symm.contDiff.contDiffAt
  apply IsSliceRegularAt.of_contDiffAt
  have heq : (fun q => (u ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm q)) =
      rawLift u := by
    funext q
    simp [evolutionHomeomorph, rawLift, KineticPoint.homeomorphProd,
      KineticPoint.isometryEquivProd, KineticPoint.equivProd]
    rfl
  change ContDiffAt ℝ 2
    (fun q => (u ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm q))
    (p.time, p.position, p.velocity) at h
  rwa [heq] at h

/- The exact `1/(2 lambda)` barrier bounds each nonnegative compact interior unit source. -/
theorem strip_duhamel_le_quadratic
    (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (E : StripEvolution H)
    (hE : IsStripEvolution A H E) (T : ℝ) (g : Point → ℝ)
    (hgn : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (rawLift g)) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T)
    (p₀ : Point) (hp₀ : p₀ ∈ evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T) :
    duhamelPotential E.2 T g p₀ ≤ stripQuadraticBarrier H lam p₀ := by
  obtain ⟨⟨-, C, -, hCb⟩, -, hsm, -, heq, hc, ht, hl, -⟩ :=
    kinetic_duhamel hH (by omega) (intervalDomain_admissible H) (zeroCurve_piecewiseC1 1)
      hlam hLam one_pos (evolutionCoefficient A.a) (evolutionCoefficient_smooth A)
      (evolutionCoefficient_symmetric A.a) (evolutionCoefficient_bounds A)
      (identityDrift 1) (identityDrift_smooth 1) (identityDrift_bounds 1)
      E.1 E.2 hE T g hgn hgs hgc hgU
  have hΩ := isOpen_of_isAdmissibleEvolutionDomain (intervalDomain_admissible H)
  have hD := isOpen_duhamelCylinder (γ := fun _ => 0) hΩ continuous_const T
  have hs : ∀ a, movingClosedSlab (intervalDomain H) (fun _ => 0) a T ⊆
      evolutionPastClosedCylinder (intervalDomain H) (fun _ => 0) T :=
    fun _ _ hp => ⟨hp.2.1, hp.2.2⟩
  have ha : ∀ a, movingActiveSlab (intervalDomain H) (fun _ => 0) a T ⊆
      evolutionPastOpenCylinder (intervalDomain H) (fun _ => 0) T :=
    fun _ _ hp => ⟨hp.2.1, hp.2.2⟩
  have hq : ∀ a, ∀ p ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) a T,
      0 ≤ stripQuadraticBarrier H lam p := by
    intro a p hp
    apply stripQuadraticBarrier_nonneg H hlam p
    apply intervalDomain_closure_bounds H
    simpa only [mem_closure_movingDomain_iff, sub_zero] using hp.2.2
  have hreg := fun p hp => sliceRegular_of_smooth hD hsm p (ha p₀.time hp)
  have _h_inl_10 : Continuous (stripQuadraticBarrier H lam) := by
    have heq : stripQuadraticBarrier H lam = fun p =>
        (p.position 0 - H.lo) * (H.hi - p.position 0) / (2 * lam) :=
      funext (stripQuadraticBarrier_eq H lam)
    rw [heq]
    have hv : Continuous (fun p : Point => p.position 0) :=
      (continuous_apply 0).comp continuous_position
    exact ((hv.sub continuous_const).mul (continuous_const.sub hv)).div_const _
  have hmax := growth_comparison hΩ continuous_const hlam (evolutionCoefficient_bounds A)
    (identityDrift_bounds 1).1 (le_refl 0) zero_le_one
    (a := p₀.time) (T := T) (u := fun p => duhamelPotential E.2 T g p -
      stripQuadraticBarrier H lam p)
    ⟨C, fun p hp => by
      have h1 := le_abs_self (duhamelPotential E.2 T g p)
      have h2 := hCb p
      have h3 := hq p₀.time p hp
      linarith⟩
    ((hc.mono (hs p₀.time)).sub _h_inl_10.continuousOn)
    (fun p hp => (hreg p hp).sub (stripQuadraticBarrier_regular H lam p))
    (fun p hp => by
      have _h_xinl_0 (a : ℝ → ℝ → ℝ) (H : Interval) (lam p) : transportedForwardOperator (evolutionCoefficient a) (SectionTwo.identityDrift 1) (stripQuadraticBarrier H lam) p = -a (p.velocity 0) (p.position 0) / lam := by
        have hslice : (fun y : PDE.Vec 1 => stripQuadraticBarrier H lam
            ⟨p.time, y, p.velocity⟩) = fun y =>
            (fun s : ℝ => (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 + s))
              (PDE.vecNormSq (y - intervalMidpoint H)) := rfl
        have hd := matrixContraction_sliceHessian_comp_vecNormSq_sub
          (m := intervalMidpoint H) (x := p.position)
          (contDiffAt_affine_weight (-1 / (2 * lam)) (-(H.hi - H.lo) ^ 2 / 4) _)
          (evolutionCoefficient a p.time p.position p.velocity)
        rw [transportedForwardOperator_apply]
        unfold fullKineticCoefficientAt
        rw [diffusedHessian_eq_sliceHessian, hslice, hd]
        have hgrad : kineticVelocityGradient (stripQuadraticBarrier H lam) p = 0 := by
          ext i
          change fderiv ℝ (fun _ : PDE.Vec 1 =>
            (-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
              PDE.vecNormSq (p.position - intervalMidpoint H))) p.velocity (PDE.basisVec i) = 0
          rw [(hasFDerivAt_const
            ((-1 / (2 * lam)) * (-(H.hi - H.lo) ^ 2 / 4 +
              PDE.vecNormSq (p.position - intervalMidpoint H))) p.velocity).fderiv]
          rfl
        rw [hgrad]
        simp only [kineticTimeDerivative, stripQuadraticBarrier, deriv_const,
          deriv_affine_weight, zero_mul, zero_add, PDE.vecDot, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, Matrix.trace, Matrix.diag, Fin.sum_univ_one,
          evolutionCoefficient, add_zero]
        by_cases hl : lam = 0
        · simp [hl]
        · field_simp
      rw [viscousTransportedOperator_sub (hreg p hp) (stripQuadraticBarrier_regular H lam p),
        viscousTransportedOperator_zero, viscousTransportedOperator_zero,
        heq p (ha p₀.time hp), _h_xinl_0]
      have hb := (A.bounds (p.velocity 0) (p.position 0)).1
      have hv : 1 ≤ A.a (p.velocity 0) (p.position 0) / lam :=
        (le_div_iff₀ hlam).2 (by simpa using hb)
      rw [neg_div]
      linarith [hg1 p])
    (fun p hp hpt => by rw [ht p hpt]; linarith [hq p₀.time p hp])
    (fun p hp hpf => by rw [hl p hpf]; linarith [hq p₀.time p hp])
  have hp : p₀ ∈ movingClosedSlab (intervalDomain H) (fun _ => 0) p₀.time T :=
    ⟨le_rfl, hp₀.1.le, subset_closure hp₀.2⟩
  exact sub_nonpos.mp (hmax p₀ hp)

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
