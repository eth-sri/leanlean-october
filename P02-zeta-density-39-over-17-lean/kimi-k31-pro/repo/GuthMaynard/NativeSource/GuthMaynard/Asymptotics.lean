module
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

open Asymptotics Filter Topology

namespace GuthMaynard.NativeMoment

/--
`EpsilonPowerBound f g` represents the Guth-Maynard asymptotic convention $f(T) \lessapprox g(T)$.
It means that for any $\varepsilon > 0$, we have $|f(T)| \ll_{\varepsilon} T^{\varepsilon} |g(T)|$ as $T \to \infty$.
The implicit constant may depend on $\varepsilon$.
-/
def EpsilonPowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ (ε : ℝ), ε > 0 → (fun T => |f T|) =O[atTop] (fun T => T ^ ε * |g T|)

theorem EpsilonPowerBound.trans {f g h : ℝ → ℝ}
    (h1 : EpsilonPowerBound f g) (h2 : EpsilonPowerBound g h) :
    EpsilonPowerBound f h := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have H1 : (fun T => |f T|) =O[atTop] (fun T => T ^ (ε / 2) * |g T|) := h1 (ε / 2) hε2
  have H2 : (fun T => |g T|) =O[atTop] (fun T => T ^ (ε / 2) * |h T|) := h2 (ε / 2) hε2
  have H3 : (fun T => T ^ (ε / 2) * |g T|) =O[atTop] (fun T => T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)) :=
    IsBigO.mul (isBigO_refl (fun T => T ^ (ε / 2)) atTop) H2
  have H4 := H1.trans H3
  have Heq : (fun T => T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)) =ᶠ[atTop] (fun T => T ^ ε * |h T|) := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hT_pos : 0 < T := by linarith
    have h_pow_add : T ^ (ε / 2) * T ^ (ε / 2) = T ^ (ε / 2 + ε / 2) := by
      exact (Real.rpow_add hT_pos _ _).symm
    calc T ^ (ε / 2) * (T ^ (ε / 2) * |h T|)
      _ = (T ^ (ε / 2) * T ^ (ε / 2)) * |h T| := mul_assoc .. |>.symm
      _ = T ^ (ε / 2 + ε / 2) * |h T| := by rw [h_pow_add]
      _ = T ^ ε * |h T| := by ring_nf
  exact H4.trans_eventuallyEq Heq

end GuthMaynard.NativeMoment
