module

public import OAI.NumberTheory.DirichletL.Descent.RootWindows

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def rootSchwartz {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) : 𝓢(ℝ, ℂ) := (hS i).toSchwartzMap (hU i)

@[simp] theorem rootSchwartz_apply {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) (y : ℝ) : rootSchwartz U hU hS i y = U i y := rfl

def secondRootSchwartz (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 6 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (secondRootWindows V)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2)

end
end SevenEighths.InverseMoment

end OAI
