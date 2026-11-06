module
import Mathlib
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open Asymptotics Filter Topology

namespace GuthMaynard.NativeMoment

/-
`EpsilonPowerBound f g` represents the Guth-Maynard asymptotic convention $f(T) \lessapprox g(T)$.
It means that for any $\varepsilon > 0$, we have $|f(T)| \ll_{\varepsilon} T^{\varepsilon} |g(T)|$ as $T \to \infty$.
The implicit constant may depend on $\varepsilon$.
-/
def EpsilonPowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → (fun T => |f T|) =O[atTop] (fun T => T ^ ε * |g T|)




