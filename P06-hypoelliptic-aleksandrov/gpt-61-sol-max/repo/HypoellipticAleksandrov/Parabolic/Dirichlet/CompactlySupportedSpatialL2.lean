module

public import PDEFoundation.Measure.LpSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Compactly supported continuous functions in restricted scalar `L²`

This module packages a continuous compactly supported scalar function into the
canonical restricted scalar `L²` carrier on an arbitrary raw spatial set.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

variable {Ω : PDE.VelocityRegion d} (q : PDE.ScalarField d) (hq : Continuous q) (hqcompact : HasCompactSupport q)

/-- Package a continuous compactly supported scalar function in restricted
scalar `L²` on an arbitrary raw spatial carrier. -/
def compactlySupportedContinuousToScalarLp
      :
    PDE.ScalarLp Ω (2 ) :=
  ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).toLp q

/-- The canonical restricted scalar `L²` package agrees almost everywhere with
its supplied continuous compactly supported function. -/
theorem coeFn_compactlySupportedContinuousToScalarLp
      :
    ⇑(compactlySupportedContinuousToScalarLp (Ω := Ω) q hq hqcompact) =ᵐ[PDE.volumeOn Ω] q := ((hq.memLp_of_hasCompactSupport hqcompact).restrict Ω).coeFn_toLp

/-- A uniformly bounded continuous field supported in a compact carrier has
the corresponding restricted-volume squared-energy bound. -/
theorem integral_sq_le_mul_volumeOn_of_tsupport_subset
     {Ω K : PDE.VelocityRegion d}
    (q : PDE.ScalarField d) (hq : Continuous q)
    (hK : IsCompact K) (hqK : tsupport q ⊆ K)
    (C : ℝ) (hqC : ∀ y : PDE.Vec d, ‖q y‖ ≤ C) :
    (∫ y, q y ^ 2 ∂PDE.volumeOn Ω) ≤
      C ^ 2 * (PDE.volumeOn Ω).real K := by






  calc
    (∫ y, q y ^ 2 ∂PDE.volumeOn Ω) ≤
        ∫ y, K.indicator (fun _ => C ^ 2) y ∂PDE.volumeOn Ω :=
      integral_mono (by
          exact (hq.pow 2).integrable_of_hasCompactSupport ((show HasCompactSupport q from hK.of_isClosed_subset (isClosed_tsupport q) hqK).mul_left)) ((integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet) (show ∀ y : PDE.Vec d, q y ^ 2 ≤ K.indicator (fun _ => C ^ 2) y by
                intro y
                by_cases hyK : y ∈ K
                · rw [Set.indicator_of_mem hyK, ← sq_abs]
                  exact (sq_le_sq₀ (abs_nonneg (q y)) ((norm_nonneg (q 0)).trans (hqC 0))).2 (hqC y)
                · rw [Set.indicator_of_notMem hyK]
                  have hyq : q y = 0 := by
                    apply image_eq_zero_of_notMem_tsupport
                    exact fun hyqSupport => hyK (hqK hyqSupport)
                  simp [hyq])
    _ = (PDE.volumeOn Ω).real K * C ^ 2 := (integral_indicator_const (C ^ 2) (IsCompact.measurableSet hK))
    _ = C ^ 2 * (PDE.volumeOn Ω).real K := mul_comm _ _

end HypoellipticAleksandrov.Parabolic.Dirichlet
