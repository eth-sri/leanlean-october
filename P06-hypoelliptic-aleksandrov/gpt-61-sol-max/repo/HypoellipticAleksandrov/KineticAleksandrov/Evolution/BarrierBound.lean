module

import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierCollar
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import Aesop



/-!
# The global bound `|u| ≤ ‖F‖` for viscous classical terminal solutions

A viscous classical terminal solution with terminal datum bounded by a constant `c ≥ 0` is
bounded by `c` on the whole past closed cylinder.  This is the first of the two barriers of
(A.1) (the barrier `‖F‖`, i.e. the case `w(d) ≥ w(d_*)` of the `min`).
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov.Parabolic Set
open scoped MatrixOrder

variable {n : ℕ}

/-- The viscous operator annihilates constants. -/
theorem viscousTransportedOperator_const  (B : FullKineticCoefficient n)
    (b : PDE.VectorField n) (ε c : ℝ) (p : KineticPoint n) :
    viscousTransportedOperator B b ε (fun _ => c) p = 0 := by
  have h1 : kineticTimeDerivative (fun _ : KineticPoint n => c) p = 0 := by
    unfold kineticTimeDerivative
    simp
  have h2 : diffusedHessian (fun _ : KineticPoint n => c) p = 0 :=
    sliceHessian_const c p.position
  have h3 : kineticVelocityHessian (fun _ : KineticPoint n => c) p = 0 :=
    sliceHessian_const c p.velocity
  have h4 : kineticVelocityGradient (fun _ : KineticPoint n => c) p = 0 :=
    classicalGradient_const c p.velocity
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply, h1, h2, h3, h4]
  simp [PDE.vecDot]

variable {Ω : PDE.VelocityRegion n} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ)

include hΩ hγ in
/-- The negative of a viscous classical solution solves the problem with negated datum. -/
theorem IsClassicalViscousTerminalSolution.neg   {B : FullKineticCoefficient n}
    {b : PDE.VectorField n} {ε τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)}
    {u : HypoellipticAleksandrov.KineticScalarField n} (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) :
    IsClassicalViscousTerminalSolution Ω γ B b ε τ (-F) (fun q => -u q) := by
  obtain ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ := hu
  refine ⟨⟨C, hC0, fun p hp => by simpa using hC p hp⟩, hcont.neg, hsmooth.neg, ?_, ?_, ?_⟩
  · intro p hp
    have hreg := IsClassicalViscousTerminalSolution.isSliceRegularAt hΩ hγ
      ⟨⟨C, hC0, hC⟩, hcont, hsmooth, hop, hterm, hlat⟩ hp

    have e : (fun q => -u q) = fun q => (-1 : ℝ) * u q := by
      funext q
      ring
    rw [e, (viscousTransportedOperator_const_mul (B := B) (b := b) (ε := ε) (-1) hreg), hop p hp]
    simp
  · aesop
  · intro p hp
    show -u p = 0
    rw [hlat p hp]
    simp

variable {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.VectorField n} (hb : HasEuclideanLipschitzDrift Lb b) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {τ : ℝ} {F : BoundedBorel (EvolutionAmbientState n)} {u : HypoellipticAleksandrov.KineticScalarField n} (hu : IsClassicalViscousTerminalSolution Ω γ B b ε τ F u) {c : ℝ}

include hΩ hγ hlam hB hb hε0 hε1 hu
/-- A viscous classical solution with terminal datum at most `c ≥ 0` is at most `c`. -/
theorem classical_le_const    (hc : 0 ≤ c)
    (hFc : ∀ y z, y ∈ closure (movingDomain Ω γ τ) → F (y, z) ≤ c) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, u p ≤ c := by
  intro p₀ hp₀
  have hslab : ∀ a, movingClosedSlab Ω γ a τ ⊆ evolutionPastClosedCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  have hact : ∀ a, movingActiveSlab Ω γ a τ ⊆ evolutionPastOpenCylinder Ω γ τ :=
    fun a p hp => ⟨hp.2.1, hp.2.2⟩
  obtain ⟨C₁, -, hC₁⟩ := hu.1

  have hres := growth_comparison (a := p₀.time) (T := τ) (u := fun q => u q - c) hΩ hγ hlam
    hB hb hε0 hε1 ?_ ?_ ?_ ?_ ?_ ?_ p₀ (⟨le_rfl, hp₀.1, hp₀.2⟩)
  ·
    linarith
  · refine ⟨C₁, fun p hp => ?_⟩
    have := hC₁ p (hslab _ hp)
    have := le_abs_self (u p)
    show u p - c ≤ C₁
    linarith
  · exact (hu.2.1.mono (hslab _)).sub continuousOn_const
  · intro p hp
    exact (hu.isSliceRegularAt hΩ hγ (hact _ hp)).sub (IsSliceRegularAt.const c p)
  · intro p hp

    rw [viscousTransportedOperator_sub (hu.isSliceRegularAt hΩ hγ (hact _ hp)) (IsSliceRegularAt.const c p),
      hu.2.2.2.1 p (hact _ hp), viscousTransportedOperator_const]
    simp
  · intro p hp hpT
    have hterm : p ∈ evolutionTerminalClosure Ω γ τ := ⟨hpT, hpT ▸ hp.2.2⟩
    have e1 := hu.2.2.2.2.1 p hterm
    have := hFc p.position p.velocity hterm.2
    show u p - c ≤ 0
    linarith
  · intro p hp hfr

    show u p - c ≤ 0
    rw [hu.2.2.2.2.2 p (⟨hp.2.1, hfr⟩)]
    linarith

/-- A viscous classical solution with terminal datum bounded by `c ≥ 0` is bounded by `c`. -/
theorem classical_abs_le_const
    (hFc : ∀ q, |F q| ≤ c) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ τ, |u p| ≤ c := by
  have hc : 0 ≤ c := le_trans (abs_nonneg _) (hFc 0)
  intro p hp
  have h1 := classical_le_const hΩ hγ hlam hB hb hε0 hε1 hu hc
    (fun y z _ => (le_abs_self _).trans (hFc (y, z))) p hp
  have h2 := classical_le_const hΩ hγ hlam hB hb hε0 hε1 (hu.neg hΩ hγ) hc
    (fun y z _ => by
      have := hFc (y, z)
      have := neg_abs_le (F (y, z))
      simp only [BoundedBorel.neg_apply]
      linarith) p hp

  exact abs_le.mpr ⟨by linarith, h1⟩

end HypoellipticAleksandrov.KineticAleksandrov
