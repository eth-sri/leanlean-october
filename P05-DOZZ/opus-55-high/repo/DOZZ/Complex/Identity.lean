/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.FDeriv.Pi

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
section
variable (a R : ℝ)
section
variable (hR : 0 < R) (f g : ℂ → ℂ)
include hR

/-- Equal values on a real interval accumulate at its real center. -/
theorem frequently_eq_of_real_interval (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (a : ℂ), f z = g z := by
  rw [Filter.frequently_iff]
  intro V hV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hV
  let δ := min ε R / 2
  have hδ : 0 < δ := by positivity
  have hδε : δ < ε := by grind
  have hδR : δ < R := by grind
  refine ⟨((a + δ : ℝ) : ℂ), hball ⟨?_, ?_⟩, heq _ ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub,
      add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hδε
  · simp
    exact hδ.ne'
  grind

/-- Scalar holomorphic identity from the real diameter of a disk. -/
theorem eqOn_ball_of_real_interval (hf : DifferentiableOn ℂ f (Metric.ball (a : ℂ) R))
    (hg : DifferentiableOn ℂ g (Metric.ball (a : ℂ) R))
    (heq : ∀ x : ℝ, |x - a| < R → f (x : ℂ) = g (x : ℂ)) :
    EqOn f g (Metric.ball (a : ℂ) R) :=
  (hf.analyticOnNhd Metric.isOpen_ball).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd Metric.isOpen_ball) (convex_ball ..).isPreconnected
    (Metric.mem_ball_self hR) (frequently_eq_of_real_interval a R hR f g heq)

end

end

/-- A complex line parameterization is a real affine map as well. -/
noncomputable def complexLineAffine {N : ℕ} (a b : Fin N → ℂ) : ℂ →ᵃ[ℝ] (Fin N → ℂ) :=
  ((ContinuousLinearMap.toSpanSingleton ℂ (b - a)).restrictScalars ℝ).toLinearMap.toAffineMap +
    AffineMap.const ℝ ℂ a
section
variable {N : ℕ}
section
variable (a b : Fin N → ℂ)

/-- The affine map has the expected complex-line formula. -/
@[simp] theorem complexLineAffine_apply (t : ℂ) :
    complexLineAffine a b t = a + t • (b - a) := by
  simp [complexLineAffine, add_comm]

/-- Complex-line restriction is differentiable in its scalar complex parameter.

Although the affine structure used for convexity is real, the same formula
is complex differentiable. The two scalar roles are kept explicit here.
-/
theorem differentiable_complexLineAffine :
    Differentiable ℂ (complexLineAffine a b) := by
  have heq : (complexLineAffine a b : ℂ → (Fin N → ℂ)) =
      fun t => a + t • (b - a) := by
    aesop
  simp_all

end

/-- Neighborhood equality propagates throughout a complex ball by scalar lines. -/
theorem eqOn_ball_of_eventuallyEq (a : Fin N → ℂ) (R : ℝ)
    (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball a R))
    (hg : DifferentiableOn ℂ g (Metric.ball a R))
    (b : Fin N → ℂ) (hb : b ∈ Metric.ball a R) (heq : f =ᶠ[𝓝 b] g) :
    EqOn f g (Metric.ball a R) := by
  intro z hz
  let L : ℂ → (Fin N → ℂ) := fun t => b + t • (z - b)
  let V := L ⁻¹' Metric.ball a R
  have hL : Differentiable ℂ L := by
    fun_prop
  have hV : IsOpen V := Metric.isOpen_ball.preimage hL.continuous
  have hconv : Convex ℝ V := by
    have hVeq : V = complexLineAffine b z ⁻¹' Metric.ball a R := by
      aesop
    rw [hVeq]
    exact (convex_ball a R).affine_preimage _
  have hzero : 0 ∈ V := by aesop
  have hone : 1 ∈ V := by aesop
  have hfl :=
    hf.comp hL.differentiableOn (fun _ ht => ht)
  have hgl :=
    hg.comp hL.differentiableOn (fun _ ht => ht)
  have hfg : f ∘ L =ᶠ[𝓝 0] g ∘ L := by
    apply heq.comp_tendsto
    simpa [L] using hL.continuous.continuousAt.tendsto (x := 0)
  have hid := (hfl.analyticOnNhd hV).eqOn_of_preconnected_of_eventuallyEq
    (hgl.analyticOnNhd hV) hconv.isPreconnected hzero hfg hone
  aesop

/-- Scalar-line propagation gives identity on any open preconnected domain. -/
theorem eqOn_of_preconnected_of_eventuallyEq (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (hconn : IsPreconnected U) (f g : (Fin N → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (a : Fin N → ℂ) (ha : a ∈ U) (heq : f =ᶠ[𝓝 a] g) : EqOn f g U := by
  let Z := {z | f =ᶠ[𝓝 z] g}
  have hZ : IsOpen Z := isOpen_setOfPred_eventually_nhds
  have hseed : (U ∩ Z).Nonempty := by tauto
  have hclosed : closure Z ∩ U ⊆ Z := by
    intro z hz
    obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz.2)
    obtain ⟨b, hbZ, hbdist⟩ := Metric.mem_closure_iff.mp hz.1 R hR
    have hb : b ∈ Metric.ball z R := by
      simpa only [Metric.mem_ball, dist_comm] using hbdist
    have hid := eqOn_ball_of_eventuallyEq z R f g (hf.mono hRU) (hg.mono hRU) b hb hbZ
    exact Filter.eventually_of_mem (Metric.ball_mem_nhds z hR) fun w hw => hid hw
  intro z hz
  exact ((hconn.subset_of_closure_inter_subset hZ hseed hclosed) hz).eq_of_nhds

end

/-- Coordinates in `S` are complex; the other coordinates stay real. -/
def mixedCoordinates {N : ℕ} (S : Finset (Fin N)) (z : Fin N → ℂ) (x : Fin N → ℝ) :
    Fin N → ℂ := fun i => if i ∈ S then z i else (x i : ℂ)
section
variable {N : ℕ}
section
variable (S : Finset (Fin N))
section
variable (z : Fin N → ℂ) (x : Fin N → ℝ) (i : Fin N)

/-- Before an index has been complexified, a real update commutes with mixing. -/
theorem mixedCoordinates_update (hi : i ∉ S) (w : ℝ) :
    mixedCoordinates S z (Function.update x i w) =
      Function.update (mixedCoordinates S z x) i (w : ℂ) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates, hi]
  · simp [mixedCoordinates, hj]

/-- Complexifying an additional index is a complex update. -/
theorem mixedCoordinates_insert :
    mixedCoordinates (insert i S) z x = Function.update (mixedCoordinates S z x) i (z i) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp [mixedCoordinates]
  · simp [mixedCoordinates, hj]

end

/-- A mixture of points in a centered real box and its complex polydisc stays inside. -/
theorem mixedCoordinates_mem_polydisc (a R : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : z ∈ complexPolydisc (fun i => (a i : ℂ)) R) (x : Fin N → ℝ)
    (hx : ∀ i, |x i - a i| < R i) :
    mixedCoordinates S z x ∈ complexPolydisc (fun i => (a i : ℂ)) R := by
  intro i
  by_cases hi : i ∈ S
  · simpa [mixedCoordinates, hi] using hz i
  · simpa [mixedCoordinates, hi, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hx i

end

/-- A coordinate update stays in the polydisc when its value stays in the coordinate disk. -/
theorem update_mem_polydisc (a : Fin N → ℂ) (R : Fin N → ℝ)
    (z : Fin N → ℂ) (hz : z ∈ complexPolydisc a R) (i : Fin N) (w : ℂ)
    (hw : w ∈ Metric.ball (a i) (R i)) : Function.update z i w ∈ complexPolydisc a R := by
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [Function.update_self, Metric.mem_ball, dist_eq_norm] using hw
  aesop

/-- Scalar identity, one coordinate at a time, fills a real-centered polydisc.

The induction is over a finite set of already complexified coordinates. At
its empty stage the hypothesis supplies equality. At an insertion stage,
the old equality gives equality on the real diameter of the new coordinate
disk; scalar identity gives equality on the whole disk. The final stage is
all coordinates, including the empty family in dimension zero.
-/
theorem eqOn_polydisc_of_real_box (a R : Fin N → ℝ)
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
        intro x hx
        have hempty : mixedCoordinates ∅ z x = fun i => (x i : ℂ) := by
          rfl
        rw [hempty]
        exact heq x hx
    | @insert i S hi hS =>
        intro x hx
        let y := mixedCoordinates S z x
        have hy := mixedCoordinates_mem_polydisc S a R z hz x hx
        have hmap : MapsTo (Function.update y i) (Metric.ball (a i : ℂ) (R i))
            (complexPolydisc (fun j => (a j : ℂ)) R) :=
          fun w hw => update_mem_polydisc _ R y hy i w hw
        have hupdate : DifferentiableOn ℂ (Function.update y i)
            (Metric.ball (a i : ℂ) (R i)) :=
          fun w _ => (hasFDerivAt_update y w).differentiableAt.differentiableWithinAt
        have hreal : ∀ w : ℝ, |w - a i| < R i →
            f (Function.update y i (w : ℂ)) = g (Function.update y i (w : ℂ)) := by
          intro w hw
          have hx' : ∀ j, |Function.update x i w j - a j| < R j := by
            grind
          have hid := hS _ hx'
          rw [mixedCoordinates_update S z x i hi w] at hid
          exact hid
        have hid := eqOn_ball_of_real_interval (a i) (R i) (hR i)
          (f ∘ Function.update y i) _ (hf.comp hupdate hmap) (hg.comp hupdate hmap) hreal
          (show z i ∈ Metric.ball (a i : ℂ) (R i) by
            simpa only [Metric.mem_ball, dist_eq_norm] using hz i)
        rw [mixedCoordinates_insert]
        exact hid
  have hcenter : ∀ i, |a i - a i| < R i := by simp_all
  have hall : mixedCoordinates Finset.univ z a = z := by
    funext i
    simp only [mixedCoordinates, Finset.mem_univ, ite_true]
  grind
section
variable (a : Fin N → ℂ) (R : Fin N → ℝ)

/-- The open polydisc is contained in the product of its closed coordinate disks. -/
theorem complexPolydisc_subset_closed_pi :
    complexPolydisc a R ⊆ Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) := by
  intro z hz i _
  simpa only [Metric.mem_closedBall, dist_eq_norm] using (hz i).le

/-- Closed coordinate disks with strictly smaller radii fit in a norm ball. -/
theorem closed_pi_subset_ball (ε : ℝ) (hε : 0 < ε) (hR : ∀ i, R i < ε) :
    Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ Metric.ball a ε := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hε]
  intro i
  have hnorm : ‖z i - a i‖ ≤ R i := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using (hz i (mem_univ i))
  exact hnorm.trans_lt (hR i)

/-- The product of closed coordinate disks is compact in the finite product topology. -/
theorem isCompact_closed_pi :
    IsCompact (Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i))) :=
  isCompact_univ_pi fun i => isCompact_closedBall (a i) (R i)

end

/-- An open neighborhood contains a compact closed polydisc and its open interior.

The closed contour must lie in the domain before applying Cauchy integration.
The half-radius choice retains a strict margin at every coordinate. It also
avoids choosing a minimum over coordinates, so it applies in dimension zero.
-/
theorem exists_closed_polydisc_subset_open (U : Set (Fin N → ℂ))
    (hU : IsOpen U) (a : Fin N → ℂ) (ha : a ∈ U) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      Set.pi Set.univ (fun i => Metric.closedBall (a i) (R i)) ⊆ U ∧
      complexPolydisc a R ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  let R : Fin N → ℝ := fun _ => ε / 2
  have hR : ∀ i, 0 < R i := fun _ => half_pos hε
  have hclosed :=
    (closed_pi_subset_ball a R ε hε (fun _ => half_lt_self hε)).trans hball
  exact ⟨R, hR, hclosed, (complexPolydisc_subset_closed_pi a R).trans hclosed⟩

end

end DOZZ.Proofs
