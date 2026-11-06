/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic

/-!
# Identity from real boxes

Scalar identity on each coordinate enlarges a real box to a complex
polydisc. Scalar identity on complex lines then propagates neighborhood
equality across an open preconnected domain. This argument does not assume
a several-variable power series theorem.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- Equal values on a real interval accumulate at its real center. -/
theorem frequently_eq_of_real_interval (a R : ℝ) (hR : 0 < R) (f g : ℂ → ℂ)
    (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (a : ℂ), f z = g z := by
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
  let δ := min ε R / 2
  have hδ : 0 < δ := half_pos (lt_min hε hR)
  have hδε  := (half_lt_self (lt_min hε hR)).trans_le (min_le_left _ _)
  have hδR  := (half_lt_self (lt_min hε hR)).trans_le (min_le_right _ _)
  refine ⟨((a + δ : ℝ) : ℂ), hball ⟨?_, ?_⟩, heq (a + δ) ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
      add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hδε
  · simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj, add_eq_left]
    exact hδ.ne'
  grind

/-- Scalar holomorphic identity from the real diameter of a disk. -/
theorem eqOn_ball_of_real_interval (a R : ℝ) (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (a : ℂ) R))
    (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) R))
    (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g (Metric.ball (a : ℂ) R) :=
  (hf.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd Metric.isOpen_ball) (convex_ball _ _).isPreconnected
    (Metric.mem_ball_self hR) (frequently_eq_of_real_interval a R hR f g heq)

/-- A complex line parameterization is a real affine map as well. -/
noncomputable def complexLineAffine {N : ℕ} (a b : Fin N → ℂ) : ℂ →ᵃ[ℝ] (Fin N → ℂ) :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (b - a)).restrictScalars ℝ).toLinearMap.toAffineMap +
    AffineMap.const ℝ ℂ a

/-- The affine map has the expected complex-line formula. -/
@[simp] theorem complexLineAffine_apply {N : ℕ} (a b : Fin N → ℂ) (t : ℂ) :
    complexLineAffine a b t = a + t • (b - a) := by
  simp [complexLineAffine, add_comm]







/-- Coordinates in `S` are complex; the other coordinates stay real. -/
def mixedCoordinates {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ) (x : Fin N → ℝ) :
    Fin N → ℂ := fun i => if i ∈ S then z i else (x i : ℂ)

/-- Before an index has been complexified, a real update commutes with mixing. -/
theorem mixedCoordinates_update {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → ℝ) (i : Fin N) (hi : i ∉ S) (w : ℝ) :
    mixedCoordinates S z (Function.update x i w) =
      Function.update (mixedCoordinates S z x) i (w : ℂ) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates, hi]
  · simp [mixedCoordinates, hj]

/-- Complexifying an additional index is a complex update. -/
theorem mixedCoordinates_insert {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ)
    (x : Fin N → ℝ) (i : Fin N) :
    mixedCoordinates (insert i S) z x = Function.update (mixedCoordinates S z x) i (z i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates]
  · simp [mixedCoordinates, hj]

/-- A mixture of points in a centered real box and its complex polydisc stays inside. -/
theorem mixedCoordinates_mem_polydisc {N : ℕ} (S : Finset (Fin N))
    (a : Fin N → ℝ) (R : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : z ∈ complexPolydisc (fun i => (a i : ℂ)) R) (x : Fin N → ℝ)
    (hx : ∀ i, |x i - a i| < R i) :
    mixedCoordinates S z x ∈ complexPolydisc (fun i => (a i : ℂ)) R := by
  intro i
  by_cases hi : i ∈ S
  · simpa [mixedCoordinates, hi] using hz i
  · simpa [mixedCoordinates, hi, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hx i

variable {N : ℕ} (a : Fin N → ℂ) (R : Fin N → ℝ)

include N a R in
/-- A coordinate update stays in the polydisc when its value stays in the coordinate disk. -/
theorem update_mem_polydisc 
    (z : Fin N → ℂ) (hz : z ∈ complexPolydisc a R) (i : Fin N) (w : ℂ)
    (hw : w ∈ Metric.ball (a i) (R i)) : Function.update z i w ∈ complexPolydisc a R := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self, Metric.mem_ball, dist_eq_norm] using hw
  continuity

/-- Scalar identity, one coordinate at a time, fills a real-centered polydisc.

The induction is over a finite set of already complexified coordinates. At
its empty stage the hypothesis supplies equality. At an insertion stage,
the old equality gives equality on the real diameter of the new coordinate
disk; scalar identity gives equality on the whole disk. The final stage is
all coordinates, including the empty family in dimension zero.
-/
theorem eqOn_polydisc_of_real_box {N : ℕ} (a : Fin N → ℝ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (complexPolydisc (fun i => (a i : ℂ)) R))
    (hg : DifferentiableOn ℂ g (complexPolydisc (fun i => (a i : ℂ)) R))
    (heq : ∀ x : Fin N → ℝ, (∀ i, |x i - a i| < R i) →
      f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) :
    EqOn f g (complexPolydisc (fun i => (a i : ℂ)) R) := by
  classical
  intro z hz
  have hmix : ∀ S : Finset (Fin N), ∀ x : Fin N → ℝ,
      (∀ i, |x i - a i| < R i) →
      f (mixedCoordinates S z x) = g (mixedCoordinates S z x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        continuity
    | @insert i S hi hS =>
        intro x hx
        let y := mixedCoordinates S z x
        have hy := mixedCoordinates_mem_polydisc S a R z hz x hx
        have hmap  :=
          fun w hw => update_mem_polydisc _ R y hy i w hw
        have hupdate : DifferentiableOn ℂ (Function.update y i)
            (Metric.ball (a i : ℂ) (R i)) :=
          fun w _ => (hasFDerivAt_update y w).differentiableAt.differentiableWithinAt
        have hfl := hf.comp hupdate hmap
        have hgl := hg.comp hupdate hmap
        have hreal : ∀ w : ℝ, |w - a i| < R i →
            f (Function.update y i (w : ℂ)) = g (Function.update y i (w : ℂ)) := by
          intro w hw
          have hx' : ∀ j, |Function.update x i w j - a j| < R j := by
            grind
          have hid := hS (Function.update x i w) hx'
          rw [mixedCoordinates_update S z x i hi w] at hid
          exact hid
        have hid := eqOn_ball_of_real_interval (a i) (R i) (hR i)
          (f ∘ Function.update y i) (g ∘ Function.update y i) hfl hgl hreal
          (show z i ∈ Metric.ball (a i : ℂ) (R i) by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz i)
        rw [mixedCoordinates_insert]
        exact hid
  have hcenter : ∀ i, |a i - a i| < R i := by simpa using hR
  have hall : mixedCoordinates Finset.univ z a = z := by
    funext i
    simp only [mixedCoordinates, Finset.mem_univ, ite_true]
  grind

include N a R in
/-- The open polydisc is contained in the product of its closed coordinate disks. -/
theorem complexPolydisc_subset_closed_pi  :
    complexPolydisc a R ⊆ Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) := by
  intro z hz i _
  simpa only [Metric.mem_closedBall, dist_eq_norm] using (hz i).le

include N a R in
/-- Closed coordinate disks with strictly smaller radii fit in a norm ball. -/
theorem closed_pi_subset_ball 
    (ε : ℝ) (hε : 0 < ε) (hR : ∀ i, R i < ε) :
    Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ Metric.ball a ε := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro i
  have hi := hz i (mem_univ i)
  have hnorm : ‖z i - a i‖ ≤ R i := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hi
  exact hnorm.trans_lt (hR i)

include N a R in
/-- The product of closed coordinate disks is compact in the finite product topology. -/
theorem isCompact_closed_pi  :
    IsCompact (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))) :=
  isCompact_univ_pi fun i => isCompact_closedBall (a i) (R i)

/-- An open neighborhood contains a compact closed polydisc and its open interior.

The closed contour must lie in the domain before applying Cauchy integration.
The half-radius choice retains a strict margin at every coordinate. It also
avoids choosing a minimum over coordinates, so it applies in dimension zero.
-/
theorem exists_closed_polydisc_subset_open {N : ℕ} (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (a : Fin N → ℂ) (ha : a ∈ U) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U ∧
      complexPolydisc a R ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let R : Fin N → ℝ := fun _ => ε / 2
  have hR : ∀ i, 0 < R i := fun _ => half_pos hε
  have hclosed  :=
    (closed_pi_subset_ball a R ε hε (fun _ => half_lt_self hε)).trans hball
  exact ⟨R, hR, hclosed, (complexPolydisc_subset_closed_pi a R).trans hclosed⟩

end DOZZ.Proofs
