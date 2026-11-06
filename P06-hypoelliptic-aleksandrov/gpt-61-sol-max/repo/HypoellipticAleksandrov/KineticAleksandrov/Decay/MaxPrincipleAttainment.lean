module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.MaxPrincipleGeometry
public import Mathlib.Topology.Order.Compact

/-!
# Positive maximum attainment on a moving tube

The source's two alternatives at spatial infinity provide actual compact
maximum attainment; this is a result, not a premise of comparison.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open HypoellipticAleksandrov Set

variable {d : ℕ}

variable (u : HypoellipticAleksandrov.KineticScalarField d) (K : Set (KineticPoint d))

/-- Independence of the transported coordinate on a given tube. -/
def IsTransportIndependentOn   : Prop :=
  ∀ p ∈ K, ∀ z : PDE.Vec d, u ⟨p.time, p.position, z⟩ = u p

/-- Uniform decay to negative infinity in the explicit Euclidean transported norm. -/
def IsUniformlyNegAtInfinityOn   : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 0 ≤ R ∧
    ∀ p ∈ K, R ≤ PDE.vecEuclideanNorm p.velocity → u p ≤ M

/-- Under either spatial-infinity alternative, a positive value yields a positive
maximum on the entire moving tube. -/
theorem exists_positive_isMaxOn_maximumClosedTube
    {Ω : PDE.VelocityRegion d} {γ : ℝ → PDE.Vec d} {a b : ℝ}
    {u : HypoellipticAleksandrov.KineticScalarField d}
    (hΩ : IsCompact (closure Ω)) (hγ : ContinuousOn γ (Icc a b))
    (hu : ContinuousOn u (maximumClosedTube Ω γ a b))
    (hcontrol : IsTransportIndependentOn u (maximumClosedTube Ω γ a b) ∨
      IsUniformlyNegAtInfinityOn u (maximumClosedTube Ω γ a b))
    {q : KineticPoint d} (hq : q ∈ maximumClosedTube Ω γ a b) (hpos : 0 < u q) :
    ∃ p ∈ maximumClosedTube Ω γ a b,
      0 < u p ∧ IsMaxOn u (maximumClosedTube Ω γ a b) p := by
  rcases hcontrol with hind | hinfty
  · let K  := {p ∈ maximumClosedTube Ω γ a b |
      p.velocity ∈ PDE.euclideanClosedBall 0 0}
    let q0 : KineticPoint d := ⟨q.time, q.position, 0⟩
    have hq0 : q0 ∈ K := by
      refine ⟨hq, ?_⟩
      simp [q0, PDE.euclideanClosedBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot]

    obtain ⟨p, hp, hmax⟩ := (isCompact_maximumClosedTube_truncated hΩ hγ le_rfl).exists_isMaxOn ⟨q0, hq0⟩ (hu.mono (fun _ h => h.1))
    have hpPos : 0 < u p := by

      exact lt_of_lt_of_le ((hind q hq 0).symm ▸ hpos) (hmax hq0)
    refine ⟨p, hp.1, hpPos, ?_⟩
    intro x hx

    change u x ≤ u p
    rw [← hind x hx 0]
    exact hmax (by
        refine ⟨hx, ?_⟩
        simp [PDE.euclideanClosedBall, PDE.euclideanSqDist, PDE.vecNormSq, PDE.vecDot])
  · obtain ⟨R, hR, hbound⟩ := hinfty 0
    let K  := {p ∈ maximumClosedTube Ω γ a b |
      p.velocity ∈ PDE.euclideanClosedBall 0 R}
    have hqR : PDE.vecEuclideanNorm q.velocity < R := by
      by_contra hnot
      exact (not_le_of_gt hpos) (hbound q hq (le_of_not_gt hnot))
    have hqK : q ∈ K := by
      refine ⟨hq, ?_⟩
      rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR]
      simpa only [sub_zero] using hqR.le

    obtain ⟨p, hp, hmax⟩ := (isCompact_maximumClosedTube_truncated hΩ hγ hR).exists_isMaxOn ⟨q, hqK⟩ (hu.mono (fun _ h => h.1))
    have hpPos  := lt_of_lt_of_le hpos (hmax hqK)
    refine ⟨p, hp.1, hpPos, ?_⟩
    intro x hx
    by_cases hxR : x.velocity ∈ PDE.euclideanClosedBall 0 R
    · exact hmax ⟨hx, hxR⟩
    ·
      exact (hbound x hx (by
          rw [PDE.mem_euclideanClosedBall_iff_vecEuclideanNorm_le hR] at hxR
          simp only [sub_zero] at hxR
          exact (lt_of_not_ge hxR).le)).trans hpPos.le

end HypoellipticAleksandrov.KineticAleksandrov.Decay
