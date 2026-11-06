module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsSpatialC2

/-! # Compact support and continuity of actual spatial generators -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open HypoellipticAleksandrov Parabolic SectionTwo Evolution Occupation Set MeasureTheory

/-- An actual compact C² native spatial test has a continuous compactly supported generator. -/
theorem compact_spatial_generator {lam Lam : ℝ} (A : SmoothAutonomous lam Lam)
    (F : EvolutionAmbientState 1 → ℝ) (hF : ContDiff ℝ 2 F) (hc : HasCompactSupport F) :
    Continuous (fun x : EvolutionAmbientState 1 =>
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩) ∧
    HasCompactSupport (fun x : EvolutionAmbientState 1 =>
      transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1)
        (fun q => F (q.position, q.velocity)) ⟨0, x.1, x.2⟩) := by
  let f := fun q : Point => F (q.position, q.velocity)
  let π := fun x : EvolutionVec 1 => (diffusedCoord 1 x, transportedCoord 1 x)
  let fraw := fun x : EvolutionVec 1 => F (π x)
  have hπ : Continuous π :=
    (diffusedCoord 1).continuous.prodMk (transportedCoord 1).continuous
  have hfraw : ContDiff ℝ 2 fraw := hF.comp
    ((diffusedCoord 1).contDiff.prodMk (transportedCoord 1).contDiff)
  have hfeq : f ∘ evolutionHomeomorph 1 = fraw := by
    aesop
  let H := fun x : EvolutionAmbientState 1 =>
    transportedForwardOperator (evolutionCoefficient A.a) (identityDrift 1) f ⟨0, x.1, x.2⟩
  let x0 := fun x : EvolutionAmbientState 1 => (evolutionProdCLE 1).symm (0, x)
  have hx0 : Continuous x0 :=
    (evolutionProdCLE 1).symm.continuous.comp (continuous_const.prodMk continuous_id)
  have hHeq : H = (transportedOperator (evolutionCoefficient A.a) (identityDrift 1) fraw)
      ∘ x0 := by
    funext x
    have hh := transportedOperator_comp (B := evolutionCoefficient A.a)
      (b := identityDrift 1) (u := f) (x := x0 x) (by rw [hfeq]; fun_prop)
    have hx : evolutionHomeomorph 1 (x0 x) = ⟨0, x.1, x.2⟩ := by
      simp [x0, evolutionHomeomorph]
      rfl
    grind
  have hHc : Continuous H := by
    rw [hHeq]
    exact (continuous_transportedOperator_c2 A hfraw).comp hx0
  have hHk : HasCompactSupport H := by
    apply hc.of_isClosed_subset (isClosed_tsupport H)
    apply closure_minimal ?_ (isClosed_tsupport F)
    intro x hx
    by_contra hn
    have hnx : x0 x ∉ tsupport fraw := by
      intro hh
      have hhit := tsupport_comp_subset_preimage F hπ hh
      aesop
    have hz := transportedOperator_eq_zero_of_notMem_tsupport hnx
      (evolutionCoefficient A.a) (identityDrift 1)
    simp_all
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
