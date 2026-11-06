module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Comparison
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstractDefect

/-! # Comparison with a nonnegative source potential on compact inner cylinders -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov.Parabolic Set

/-- Potential comparison with the operator inequality derived from its source premises. -/
theorem abp_potential_comparison {d : ℕ}
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (A : FullKineticCoefficient d) (u W g : KineticPoint d → ℝ)
    (hu : IsKineticC112On u (forwardCylinder Z₀ R hR))
    (hW : IsKineticC112On W (forwardCylinder Z₀ R hR))
    (hW0 : ∀ P ∈ forwardCylinder Z₀ R hR, 0 ≤ W P)
    (hWop : ∀ P ∈ forwardCylinder Z₀ R hR, forwardKineticOperator A W P = -g P)
    (hA : ∀ P ∈ forwardCylinder Z₀ R hR, (A P.time P.position P.velocity).PosSemidef)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlt : δ < R ^ 2 / 2)
    (ε : ℝ) (hε : 0 < ε)
    (hmajor : ∀ P ∈ closure (innerCylinder Z₀ R hR δ hδ0 hδlt),
      abpPositiveCutoff ε (u P) * max (-forwardKineticOperator A u P) 0 ≤ g P)
    (M : ℝ) (hboundary : ∀ P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt,
      max (u P) 0 ≤ M) :
    ∀ P ∈ innerCylinder Z₀ R hR δ hδ0 hδlt, u P ≤ M + W P + ε := by
  let w := fun P : KineticPoint d => u P + (-1) * W P + (-ε)
  have hw := comparison_regular_add
    (comparison_regular_add hu (comparison_regular_const_mul hW (-1)))
    (comparison_regular_const (-ε) _)
  have hc := closure_innerCylinder_subset Z₀ R hR δ hδ0 hδlt
  obtain ⟨hr,heq⟩ := innerCylinder_eq_forwardCylinder Z₀ R hR δ hδ0 hδlt
  obtain ⟨hr',heqB⟩ := innerExitBoundary_eq_exitBoundary Z₀ R hR δ hδ0 hδlt
  let Q := forwardCylinder (innerCentre Z₀ δ) _ hr
  have hcl : closure Q ⊆ forwardCylinder Z₀ R hR := by
    grind
  have hQi : Q ⊆ forwardCylinder Z₀ R hR := subset_closure.trans hcl
  have hsub : ∀ P ∈ Q, 0 < w P → 0 ≤ forwardKineticOperator A w P := by
    intro P hP hpos
    have hPQ := hQi hP
    have hup : ε ≤ u P := by
      grind
    have hθ := (abpPositiveCutoff_spec hε).2.2.2 _ hup
    have hPc : P ∈ closure (innerCylinder Z₀ R hR δ hδ0 hδlt) := by
      rw [heq]
      exact subset_closure hP
    have hm := hmajor P hPc
    rw [hθ] at hm
    have hd := le_max_left (-forwardKineticOperator A u P) 0
    rw [comparison_forwardOperator_add
      (comparison_regular_add hu (comparison_regular_const_mul hW _))
      (comparison_regular_const _ _) A hPQ,
      comparison_forwardOperator_add hu (comparison_regular_const_mul hW _) A hPQ,
      comparison_forwardOperator_const_mul hW _ A hPQ,
      comparison_forwardOperator_const, hWop P hPQ]
    linarith
  have hcompare := kinetic_comparison _ _ hr A w
    (fun P hP => hA P (hQi hP)) (hw.continuousOn.mono hcl)
    (comparison_regular_mono hw hQi) hsub
  have hb : sSup ((fun P => max (w P) 0) '' exitBoundary (innerCentre Z₀ δ)
      _ hr) ≤ M := by
    apply csSup_le ((comparison_exitBoundary_nonempty _ _ hr).image _)
    rintro _ ⟨P,hP,rfl⟩
    have hPb : P ∈ innerExitBoundary Z₀ R hR δ hδ0 hδlt := by
      simp_all
    have hPQ := hcl hP.1
    grind
  intro P hP
  rw [heq] at hP
  have h := (hcompare P (subset_closure hP)).trans hb
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
