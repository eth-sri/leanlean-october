module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRescaling
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Dge2CutoffRadial
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Uniform Hessian signs on the fixed cutoff annulus

Compactness is applied to the actual differentiated interpolation, with the two
perturbation parameters tending to zero independently.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/- The velocity Hessian quadratic form of the rescaled interpolation. -/
def rescaledHessian {d } (alpha sigma s t : ℝ) (e z w : PDE.Vec d) : ℝ :=
  fderiv ℝ (fun a => fderiv ℝ (rescaledCutoff alpha sigma s t e) a w) z w

/- The fixed compact annulus and Euclidean unit direction parameter. -/
def cutoffAnnulus (d : ℕ) : Set (PDE.Vec d × PDE.Vec d) :=
  {q | PDE.vecNormSq q.1 = 1 ∧ 1 ≤ PDE.vecEuclideanNorm q.2 ∧
    PDE.vecEuclideanNorm q.2 ≤ 2}

/- The fixed annulus is compact in the native product topology. -/
def rescaledSignRegion (d : ℕ) (alpha sigma : ℝ) :
    Set ((PDE.Vec d × PDE.Vec d) × (ℝ × ℝ)) :=
  {q | q.1.2 ≠ 0 ∧ seedBase (q.2.2 * sigma) q.1.2 (q.2.2 • q.1.1) ≠ 0 ∧
    (∃ w, 0 < rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w) ∧
    (∃ w, rescaledHessian alpha sigma q.2.1 q.2.2 q.1.1 q.1.2 w < 0)}

/- Both strict Hessian signs persist locally in the regular parameter region. -/
theorem cutoffAnnulus_zero_signs (d : ℕ) (hd : 2 ≤ d) (alpha sigma : ℝ)
    (ha : 0 < alpha) (ha1 : alpha < 1) :
    cutoffAnnulus d ×ˢ ({(0, 0)} : Set (ℝ × ℝ)) ⊆ rescaledSignRegion d alpha sigma := by
  rintro ⟨⟨e, z⟩, p⟩ ⟨hz, hp⟩
  have hp0 : p = (0, 0) := Set.mem_singleton_iff.mp hp
  subst p
  have hz0 : z ≠ 0 := by
    intro hzero
    have hh := hz.2.1
    simp [hzero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot] at hh
    norm_num at hh
  have hbase : seedBase (0 * sigma) z ((0 : ℝ) • e) ≠ 0 := by
    simpa [seedBase] using PDE.vecNormSq_eq_zero_iff.not.mpr hz0
  have heq : rescaledCutoff alpha sigma 0 0 e = radialProfile alpha := by
    funext a
    simp [rescaledCutoff, seedBase, radialProfile]
  have hh (w : PDE.Vec d) : rescaledHessian alpha sigma 0 0 e z w =
      radialHessianForm alpha z w w := by
    unfold rescaledHessian
    rw [heq, radialProfile_hessian alpha z w w hz0]
  obtain ⟨w, hw⟩ := radialHessian_positive_direction d hd alpha ha z hz0
  change z ≠ 0 ∧ seedBase (0 * sigma) z ((0 : ℝ) • e) ≠ 0 ∧ _
  refine ⟨hz0, hbase, ⟨w, ?_⟩, ⟨z, ?_⟩⟩
  · rw [hh]
    exact hw
  · rw [hh]
    exact radialHessian_radial_neg alpha ha ha1 z hz0

/- One open parameter neighborhood preserves both signs uniformly on the fixed annulus. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
