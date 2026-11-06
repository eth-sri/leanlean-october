module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TerminalPointValue
import Mathlib.Tactic.Linarith

/-!
# Weighted comparison of an intermediate trace with compact terminal data

The first solution may have a later terminal time. Only its restriction to the slab
ending at the intermediate time is used. The terminal error is propagated by the
explicit Euclidean growth barrier, without applying existence to noncompact data.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set

variable {n : ℕ} {Ω : PDE.VelocityRegion n} (hΩ : IsOpen Ω) {γ : ℝ → PDE.Vec n} (hγ : Continuous γ) {lam Lam : ℝ} (hlam : 0 < lam) {B : FullKineticCoefficient n} (hB : HasEverywhereLoewnerBounds lam Lam B) {Lb : ℝ} {b : PDE.VectorField n} (hb : HasEuclideanLipschitzDrift Lb b) {r τ δ : ℝ} (hrτ : r ≤ τ) (hδ : 0 ≤ δ) {F G : BoundedBorel (EvolutionAmbientState n)} {u v : HypoellipticAleksandrov.KineticScalarField n} (hu : IsClassicalTerminalSolution Ω γ B b τ F u) (hv : IsClassicalTerminalSolution Ω γ B b r G v)

include hΩ hγ hlam hB hb hrτ hδ hu hv
/-- A weighted terminal error between two classical solutions propagates to every
point of the earlier closed cylinder. The first solution may end at a later time. -/
theorem classical_intermediate_sub_le_growth

    (hterm : ∀ p ∈ evolutionTerminalClosure Ω γ r,
      u p - v p ≤ δ * (1 + radialSq p)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ r,
      u p - v p ≤ δ *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) r p := by
  have hu' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b τ F u).2 hu
  have hv' := (isClassicalViscousTerminalSolution_zero_iff Ω γ B b r G v).2 hv
  let cg := growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb


  have hΦpos (p : KineticPoint n)  := (growthBarrier_pos cg r p).le
  have hΦop (p : KineticPoint n)  :=
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
    (a := p₀.time) (T := r) (u := fun p => u p - v p - δ * (growthBarrier (n := n) cg r) p)
    ?_ ?_ ?_ ?_ ?_ ?_ p₀ ⟨le_rfl, hp₀.1, hp₀.2⟩
  · linarith only [hmax]
  · refine ⟨C₁ + C₂, fun p hp => ?_⟩


    have hnon := mul_nonneg hδ (hΦpos p)
    linarith only [((abs_le.mp (hC₁ p (hlater p hp))).2), ((abs_le.mp (hC₂ p (hclosed p hp))).1), hnon]
  · exact ((hu'.2.1.mono (hlater)).sub
      (hv'.2.1.mono (hclosed))).sub
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


    have hbound := (hterm p ⟨ht, ht ▸ hp.2.2⟩).trans (mul_le_mul_of_nonneg_left (one_add_radialSq_le_growthBarrier (show 0 ≤ cg by
        dsimp [cg, growthConstant]
        have := PDE.vecEuclideanNorm_nonneg (b 0)
        positivity) hp.2.1) hδ)
    linarith only [hbound]
  · intro p hp hfr
    rw [hu'.2.2.2.2.2 p ⟨hp.2.1.trans hrτ, hfr⟩,
      hv'.2.2.2.2.2 p ⟨hp.2.1, hfr⟩, sub_self]
    exact sub_nonpos.mpr (mul_nonneg hδ (hΦpos p))

/-- Absolute weighted terminal errors propagate under the same Euclidean growth barrier. -/
theorem classical_intermediate_abs_sub_le_growth

    (hterm : ∀ p ∈ evolutionTerminalClosure Ω γ r,
      |u p - v p| ≤ δ * (1 + radialSq p)) :
    ∀ p ∈ evolutionPastClosedCylinder Ω γ r,
      |u p - v p| ≤ δ *
        growthBarrier (growthConstant n Lam (PDE.vecEuclideanNorm (b 0)) Lb) r p := by
  have hupper := classical_intermediate_sub_le_growth hΩ hγ hlam hB hb hrτ hδ hu hv
    (fun p hp => (le_abs_self _).trans (hterm p hp))
  have hlower := classical_intermediate_sub_le_growth hΩ hγ hlam hB hb hrτ hδ
    (hu.smul hΩ hγ (-1)) (hv.smul hΩ hγ (-1)) (fun p hp => by

      linarith only [((abs_le.mp (hterm p hp)).1)])
  intro p hp

  exact abs_le.mpr ⟨by linarith only [(hlower p hp)], hupper p hp⟩

end HypoellipticAleksandrov.KineticAleksandrov
