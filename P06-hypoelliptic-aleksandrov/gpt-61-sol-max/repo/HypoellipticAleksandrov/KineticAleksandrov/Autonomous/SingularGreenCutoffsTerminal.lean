module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsDynkin
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.AutonomyBoundedData
public import PDEFoundation.Calculus.RegularityOrder


/-! # Derived terminal Green identity for bounded smooth tests -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open SectionTwo Evolution Set

/-- The actual signed Green potential of a smooth test is its value minus its
actual terminal-kernel value. The forcing is its literal kinetic operator. -/
theorem fullspace_green_terminal_error_smooth_datum
    (hH : HormanderHypoellipticityStatement) {lam Lam : ℝ}
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam)
    (E : FullSpaceEvolution) (hE : IsFullSpaceEvolution A E) (T : ℝ)
    (f : Point → ℝ) (hf : ContDiff ℝ 2 (f ∘ evolutionHomeomorph 1))
    (Cf M : ℝ) (hM : 0 ≤ M) (hfb : ∀ p, |f p| ≤ Cf)
    (hLf : ∀ p, |transportedForwardOperator (evolutionCoefficient A.a)
      (identityDrift 1) f p| ≤ M)
    (F : BoundedBorel (EvolutionAmbientState 1)) (hF : ContDiff ℝ PDE.smoothOrder F)
    (δ : ℝ) (hFt : ∀ p, p.time = T → |f p - F (p.position, p.velocity)| ≤ δ)
    (p : Point) (hp : p.time < T) :
    |duhamelPotential E.2 T
      ((evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T).indicator
        (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
          (identityDrift 1) f q)) p -
      (f p - ∫ x, F x ∂E.2.master
        (wholeSpaceQuery p.time T hp.le p.position p.velocity))| ≤ δ := by
  obtain ⟨u, hu, hr⟩ := fullspace_bounded_smooth_solution hH hlam hLam A E hE T F hF
  let D := evolutionPastOpenCylinder autonomousWholeDomain (fun _ => 0) T
  let g := D.indicator (fun q => -transportedForwardOperator (evolutionCoefficient A.a)
    (identityDrift 1) f q)
  have hD : IsOpen D := isOpen_duhamelCylinder
    (isOpen_of_isAdmissibleEvolutionDomain autonomousWholeDomain_admissible)
    continuous_const T

  have hus : ContDiffOn ℝ PDE.smoothOrder (u ∘ evolutionHomeomorph 1)
      (evolutionHomeomorph 1 ⁻¹' D) := by
    apply contDiffOn_comp_evolutionHomeomorph_iff.mpr
    rw [← evolutionPastInteriorRaw_eq_image]
    exact hu.2.2.1



  have hgb (q : Point) : |g q| ≤ M := by
    by_cases hq : q ∈ D
    · simpa only [g, indicator_of_mem hq, abs_neg] using hLf q
    · simp only [g, indicator_of_notMem hq, abs_zero]; exact hM
  obtain ⟨Cu, -, hCu⟩ := hu.1
  have hwhole (q : Point) :
      q.position ∈ closure (movingDomain autonomousWholeDomain (fun _ => 0) q.time) := by
    change q.position ∈ closure (movingDomain (wholeSpace 1) (fun _ => 0) q.time)
    rw [movingDomain_wholeSpace, closure_univ]; trivial
  have hreg (q : Point) (hq : q ∈ D) : IsSliceRegularAt f q :=
    IsSliceRegularAt.of_contDiffAt (by
      have hh := hf.contDiffAt.comp (q.time, q.position, q.velocity)
        (evolutionProdCLE 1).symm.contDiff.contDiffAt
      have he : (fun x => (f ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm x)) =
          rawLift f := by
        funext x
        simp [evolutionHomeomorph, rawLift, KineticPoint.homeomorphProd,
          KineticPoint.isometryEquivProd, KineticPoint.equivProd]
        rfl
      change ContDiffAt ℝ 2
        (fun x => (f ∘ evolutionHomeomorph 1) ((evolutionProdCLE 1).symm x))
        (q.time, q.position, q.velocity) at hh
      rwa [he] at hh)
  have hureg (q : Point) (hq : q ∈ D)  :=
    reconstruction_slice_regular_of_contDiffOn hD hus q hq
  have hgreen := fullspace_green_terminal_error hH hlam A E hE T (fun q => f q - u q) g
    (hf.contDiffOn.sub (hus.of_le (by simp))) ((show Continuous f by
        have he : f = (f ∘ evolutionHomeomorph 1) ∘ (evolutionHomeomorph 1).symm := by
          funext q; simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
        rw [he]
        exact hf.continuous.comp (evolutionHomeomorph 1).symm.continuous).continuousOn.sub hu.2.1) ((show Continuous ((transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f)) by
            have hc := (continuous_transportedOperator_c2 A hf).comp
              (evolutionHomeomorph 1).symm.continuous
            convert hc using 1
            funext q
            rw [Function.comp_apply,
              transportedOperator_comp hf.contDiffAt, Homeomorph.apply_symm_apply]).neg.measurable.indicator hD.measurableSet) (Cf + Cu) M hM
    (fun q hq => (abs_sub _ _).trans
      (add_le_add (hfb q) (hCu q ⟨hq, hwhole q⟩))) hgb
    (fun q hq => indicator_of_notMem ((fun hh => not_lt_of_ge hq hh.left)) _)
    δ (fun q hq => by
      rw [hu.2.2.2.2.1 q ⟨hq, hwhole q⟩]
      exact hFt q hq)
    (fun q hq => by
      have hqd : q ∈ D := ⟨hq, by
        change q.position ∈ movingDomain (wholeSpace 1) (fun _ => 0) q.time
        rw [movingDomain_wholeSpace]; trivial⟩
      rw [← viscousTransportedOperator_zero,
        viscousTransportedOperator_sub (hreg q hqd) (hureg q hqd),
        viscousTransportedOperator_zero, viscousTransportedOperator_zero,
        hu.2.2.2.1 q hqd, sub_zero]
      dsimp only [g]
      rw [indicator_of_mem hqd, neg_neg]) p hp
  have hrepr := hr (wholeSpaceQuery p.time T hp.le p.position p.velocity) rfl
  change u p = _ at hrepr
  rw [hrepr] at hgreen
  exact hgreen

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
