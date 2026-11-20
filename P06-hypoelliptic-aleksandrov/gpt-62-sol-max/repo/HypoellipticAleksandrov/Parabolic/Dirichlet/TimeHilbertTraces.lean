module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative

/-!
# Canonical reverse-time Hilbert traces

This module selects the continuous spatial-`L²` representative of a
reverse-time Gelfand curve and evaluates that representative at the two closed
time endpoints. These are not evaluations of the raw Bochner representative.
-/

@[expose] public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The canonical continuous spatial-`L²` representative supplied by the
reverse-time Hilbert-representative theorem. -/
noncomputable def reverseTimeHilbertRepresentative
    {d : ℕ} {Ω : Set (PDE.Vec d)}
    (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
    (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
    (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g) :
    C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 : ℝ≥0∞)) :=
  Classical.choose (ExistsUnique.exists
    (existsUnique_reverseTimeHilbertRepresentative hΩ T hT u g hderiv))

section
variable {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T)
  (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T)
  (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)
include hΩ T hT u g hderiv

/-- The canonical representative agrees with the reverse-time Bochner curve
almost everywhere and satisfies the positive-sign energy increment. -/
theorem reverseTimeHilbertRepresentative_spec :
    ReverseTimeHilbertRepresentativeAgrees hΩ T u
      (reverseTimeHilbertRepresentative hΩ T hT u g hderiv) ∧
    ∀ s t : ℝ, ∀ hs : s ∈ Set.Icc 0 T, ∀ ht : t ∈ Set.Icc 0 T,
      s ≤ t →
        ‖reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨t, ht⟩‖ ^ 2 -
            ‖reverseTimeHilbertRepresentative hΩ T hT u g hderiv ⟨s, hs⟩‖ ^ 2 =
          2 * (∫ r in Set.Ioc s t,
            (g r) (u r) ∂reverseTimeVolume T) :=
  Classical.choose_spec (ExistsUnique.exists
    (existsUnique_reverseTimeHilbertRepresentative hΩ T hT u g hderiv))

/-- The reverse-time initial spatial-`L²` trace, defined at `tau = 0` from
the canonical continuous representative and not from the raw Bochner curve. -/
noncomputable def reverseTimeInitialTrace :
    PDE.ScalarLp Ω (2 : ℝ≥0∞) :=
  reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    ⟨(0 : ℝ), ⟨le_rfl, hT.le⟩⟩

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
