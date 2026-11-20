module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationWeakIntegration
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeCoord
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.HormanderBridgeWeak

/-! # Local calculus of weak transported equations -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Evolution
open MeasureTheory Set Filter
open scoped Topology

variable {d : ℕ}

/-- The transported adjoint vanishes off the topological support of the test. -/
theorem transportedAdjoint_eq_zero_of_notMem_tsupport {B : FullKineticCoefficient d}
    {b : PDE.Vec d → PDE.Vec d} (ψ : EvolutionVec d → ℝ) {x : EvolutionVec d}
    (hx : x ∉ tsupport ψ) : transportedAdjoint B b ψ x = 0 := by
  have hz : ∀ (φ : EvolutionVec d → ℝ) (v : EvolutionVec d), tsupport φ ⊆ tsupport ψ →
      fderiv ℝ φ x v = 0 := fun φ v hφ =>
    image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v)
      (fun h => hx (hφ (tsupport_evolution_fderiv_apply φ v h)))
  have h1 : fderiv ℝ ψ x basisT = 0 := hz ψ _ subset_rfl
  have h3 : ∀ l, fderiv ℝ ψ x (basisZ l) = 0 := fun l => hz ψ _ subset_rfl
  have h2 : ∀ i j, fderiv ℝ (fun y => fderiv ℝ (fun w : EvolutionVec d =>
      B (Evolution.timeCoord d w) (diffusedCoord d w) (transportedCoord d w) i j * ψ w) y
        (basisV j)) x (basisV i) = 0 := by
    intro i j
    refine hz _ _ ?_
    intro y hy
    have hy1 := tsupport_evolution_fderiv_apply _ (basisV j) hy
    exact tsupport_mul_subset_right hy1
  unfold transportedAdjoint
  simp only [h1, h2, h3, mul_zero, Finset.sum_const_zero, neg_zero, add_zero, sub_zero]

section
variable {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}

/-- The transported adjoint's support is contained in the support of its test. -/
theorem tsupport_transportedAdjoint_subset (ψ : EvolutionVec d → ℝ) :
    tsupport (transportedAdjoint B b ψ) ⊆ tsupport ψ := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (transportedAdjoint_eq_zero_of_notMem_tsupport ψ hnot)
  · exact isClosed_tsupport ψ

/-- The transported adjoint of a smooth test is smooth. -/
theorem contDiff_transportedAdjoint
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    {ψ : EvolutionVec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (transportedAdjoint B b ψ) := by
  unfold transportedAdjoint
  refine (((contDiff_fderiv_apply hψ _).neg).add ?_).sub ?_
  · exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      contDiff_fderiv_apply (contDiff_fderiv_apply ((contDiff_coeffAt_entry hB i j).mul hψ) _) _
  · exact ContDiff.sum fun l _ => ((contDiff_pi.1 hb l).comp (diffusedCoord d).contDiff).mul
      (contDiff_fderiv_apply hψ _)

/-- The transported adjoint of a compactly supported test is compactly supported. -/
theorem hasCompactSupport_transportedAdjoint {ψ : EvolutionVec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (transportedAdjoint B b ψ) :=
  HasCompactSupport.intro hc fun _ hx => transportedAdjoint_eq_zero_of_notMem_tsupport ψ hx

end


section
variable {U V : Set (EvolutionVec d)} {B : FullKineticCoefficient d} {b : PDE.Vec d → PDE.Vec d}
variable {u v f g : EvolutionVec d → ℝ}

section
variable (hu : IsWeakTransportedSolution B b U u f)
include hu

/-- Changing a source off the test domain does not change the equation. -/
theorem IsWeakTransportedSolution.congr_source
    (hU : MeasurableSet U) (hfg : EqOn f g U) : IsWeakTransportedSolution B b U u g :=
  ⟨hu.1, fun ψ hψ hc hs => (hu.2 ψ hψ hc hs).trans
    (setIntegral_congr_fun hU fun x hx => congrArg (· * ψ x) (hfg hx))⟩

/-- A weak solution is a weak solution on every subdomain. -/
theorem IsWeakTransportedSolution.mono (hVU : V ⊆ U) :
    IsWeakTransportedSolution B b V u f := by
  refine ⟨hu.1.mono_set hVU, fun ψ hψ hc hs => ?_⟩
  have hl : ∀ x ∉ V, u x * transportedAdjoint B b ψ x = 0 := fun x hx => by
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun h => hx (hs h)), mul_zero]
  have hr : ∀ x ∉ V, f x * ψ x = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hl, setIntegral_eq_integral_of_forall_compl_eq_zero hr,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hl x (fun h => hx (hVU h))),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hr x (fun h => hx (hVU h)))]
  exact hu.2 ψ hψ hc (hs.trans hVU)

theorem IsWeakTransportedSolution.neg :
    IsWeakTransportedSolution B b U (fun x => -u x) (fun x => -f x) := by
  refine ⟨hu.1.neg, fun ψ hψ hc hs => ?_⟩
  simp only [neg_mul, integral_neg, hu.2 ψ hψ hc hs]

/-- Subtracting solutions with the same forcing leaves a homogeneous equation. -/
theorem IsWeakTransportedSolution.sub_same_source
    (hv : IsWeakTransportedSolution B b U v f)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b) :
    IsWeakTransportedSolution B b U (fun x => u x - v x) (fun _ => 0) := by
  refine ⟨hu.1.sub hv.1, fun ψ hψ hc hs => ?_⟩
  have ha := (contDiff_transportedAdjoint hB hb hψ).continuous
  have hac : HasCompactSupport (transportedAdjoint B b ψ) := hasCompactSupport_transportedAdjoint hc
  have has : tsupport (transportedAdjoint B b ψ) ⊆ U := (tsupport_transportedAdjoint_subset ψ).trans hs
  have hiu := (integrable_weak_mul_test hu.1 ha hac has).integrableOn (s := U)
  have hiv := (integrable_weak_mul_test hv.1 ha hac has).integrableOn (s := U)
  simp only [sub_mul, integral_sub hiu hiv, hu.2 ψ hψ hc hs, hv.2 ψ hψ hc hs,
    sub_self, zero_mul, integral_zero]

end

/-- Adding solutions with opposite sources leaves a homogeneous equation. -/
theorem IsWeakTransportedSolution.add_neg_source (hu : IsWeakTransportedSolution B b U u f)
    (hv : IsWeakTransportedSolution B b U v (fun x => -f x))
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b) :
    IsWeakTransportedSolution B b U (fun x => u x + v x) (fun _ => 0) := by
  have h : IsWeakTransportedSolution B b U (fun x => -v x) f := by
    simpa only [neg_neg] using hv.neg
  simpa only [sub_neg_eq_add] using hu.sub_same_source h hB hb

end
end HypoellipticAleksandrov.KineticAleksandrov.Evolution
