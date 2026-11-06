module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Lean.Elab.Tactic.SolveByElim
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative

section
open private HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeHilbertRepresentative_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertRepresentative
private alias _semanticProof_f333991d5c17 := HypoellipticAleksandrov.Parabolic.Dirichlet.reverseTimeHilbertRepresentative_eq
end


/-!
# Canonical reverse-time Hilbert traces

This module selects the continuous spatial-`L²` representative of a
reverse-time Gelfand curve and evaluates that representative at the two closed
time endpoints. These are not evaluations of the raw Bochner representative.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Two continuous spatial-`L²` curves which agree with the same reverse-time
Bochner curve almost everywhere have the same closed-time representative. -/
theorem ReverseTimeHilbertRepresentativeAgrees.unique
    {d : ℕ} {Ω : PDE.VelocityRegion d} {hΩ : IsOpen Ω} {T : ℝ}
    {u : ReverseTimeL2V hΩ T}
    {Ubar Vbar : C(↥(Set.Icc 0 T), PDE.ScalarLp Ω (2 ))}
    (hUbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Ubar)
    (hT : 0 < T)
    (hVbar : ReverseTimeHilbertRepresentativeAgrees hΩ T u Vbar) :
    Ubar = Vbar := (_semanticProof_f333991d5c17 hΩ T hT u Ubar Vbar hUbar hVbar)

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (hT : 0 < T) (u : ReverseTimeL2V hΩ T) (g : ReverseTimeL2VStar hΩ T) (hderiv : HasGelfandWeakTimeDerivative hΩ T hT u g)

/-- The canonical continuous spatial-`L²` representative supplied by the
reverse-time Hilbert-representative theorem. -/
def reverseTimeHilbertRepresentative
      :=
  Classical.choose (ExistsUnique.exists
    (existsUnique_reverseTimeHilbertRepresentative hΩ T hT u g hderiv))

/-- The canonical representative agrees with the reverse-time Bochner curve
almost everywhere and satisfies the positive-sign energy increment. -/
theorem reverseTimeHilbertRepresentative_spec
     :
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
def reverseTimeInitialTrace
     :
    PDE.ScalarLp Ω (2 ) :=
  reverseTimeHilbertRepresentative hΩ T hT u g hderiv
    ⟨(0 ), ⟨le_rfl, hT.le⟩⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
