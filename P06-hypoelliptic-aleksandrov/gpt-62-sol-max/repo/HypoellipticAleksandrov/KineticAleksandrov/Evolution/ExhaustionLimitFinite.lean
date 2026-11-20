module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitEquation
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitTrace
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingFinite
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitClassical
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitBoundary
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.PastGluingLocality
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitAdjoint
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionLimitMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual finite-slab classical ball solutions

All finite-slab steps are supplied by the actual exhaustion construction:
bounds, continuity, interior smoothness, the pointwise equation, and both traces.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set Filter MeasureTheory
open Evolution
open scoped Topology MatrixOrder

/-- Actual finite ball approximants yield a classical finite-slab solution relative
to the explicit Hörmander input. No boundary estimate or weak equation is assumed. -/
theorem isClassicalViscousFiniteSolution_innerBallDirichletLimit
    {n : ℕ} (E : InnerBallExhaustion n) (hεpos : 0 < E.ε) :
    IsClassicalViscousFiniteSolution E.domain E.Γ E.B E.b E.ε E.α E.τ E.F
      (E.limit) := by
  have hr0 := E.radius_pos
  have htrace := innerBallDirichletLimit_bound_terminal_lateral E
  have hcont := continuousOn_innerBallDirichletLimit E
  have hlocal (δ S : ℝ) (hδ : 0 < δ) (hδr : δ < E.r0) :=
    classical_innerBallDirichletLimit_on_innerCylinder (S0 := S) E hδ hδr hεpos
  refine ⟨⟨E.C, E.hC, htrace.1⟩, hcont, ?_, ?_, ?_, ?_⟩
  · intro q hq
    let p : KineticPoint n := ⟨q.1, q.2.1, q.2.2⟩
    obtain ⟨δ, S, hδ, hδr, hp⟩ := exists_boundedInnerOpenCylinder_mem hr0
      (p := p) ⟨hq.1, hq.2.1⟩ hq.2.2
    let x := (evolutionProdCLE n).symm q
    have hxp : evolutionHomeomorph n x = p := by
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    have hx : x ∈ evolutionHomeomorph n ⁻¹'
        (E.innerOpen δ S) := by
      change evolutionHomeomorph n x ∈ (E.innerOpen δ S)
      rw [hxp]
      exact hp
    have hV := (isOpen_boundedInnerOpenCylinder (E.r0 - δ) E.hΓ E.α E.τ S).preimage
      (evolutionHomeomorph n).continuous
    have hc := ((hlocal δ S hδ hδr).1.contDiffAt (hV.mem_nhds hx)).comp q
      (evolutionProdCLE n).symm.contDiff.contDiffAt
    have hfun : (E.limit ∘ evolutionHomeomorph n) ∘
        (evolutionProdCLE n).symm = fun q =>
          E.limit ⟨q.1, q.2.1, q.2.2⟩ := by
      funext q
      change E.limit
        (evolutionHomeomorph n ((evolutionProdCLE n).symm q)) =
        E.limit ⟨q.1, q.2.1, q.2.2⟩
      apply congrArg (E.limit)
      apply (KineticPoint.equivProd n).injective
      change (evolutionProdCLE n) ((evolutionProdCLE n).symm q) = q
      exact (evolutionProdCLE n).apply_symm_apply q
    simpa only [hfun] using hc.contDiffWithinAt
  · intro p hp ha
    obtain ⟨δ, S, hδ, hδr, hpU⟩ := exists_boundedInnerOpenCylinder_mem hr0
      ⟨ha, hp.2.1⟩ hp.2.2
    exact (hlocal δ S hδ hδr).2 p hpU
  · intro p hp
    have hpc : p ∈ E.closedSlab :=
      ⟨by rw [hp.1]; exact E.hατ.le, hp.1.le, by simpa only [hp.1] using hp.2⟩
    exact htrace.2.1 p hpc hp.1
  · intro p _ hp
    exact htrace.2.2 p hp

end HypoellipticAleksandrov.KineticAleksandrov
