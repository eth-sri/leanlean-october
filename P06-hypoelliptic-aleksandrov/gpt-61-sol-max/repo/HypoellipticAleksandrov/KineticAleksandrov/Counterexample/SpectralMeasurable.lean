module

public import PDEFoundation.Ambient.Basic
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

/-!
# Canonical spectral projections without measurable eigenvector choices

The positive projection is the pointwise limit of continuous spectral ramps. The
finite spectrum makes the sequence eventually equal to the projection at each matrix.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped Matrix.Norms.L2Operator

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

/-- Indicator of the strictly positive spectral half-line. -/
def positiveSpectralIndicator (t : ℝ) : ℝ := if 0 < t then 1 else 0

/-- Continuous approximants to the positive spectral indicator. -/
def positiveSpectralRamp (n : ℕ) (t : ℝ) : ℝ := max 0 (min 1 ((n : ℝ) * t))

variable {d : ℕ} (M : PDE.Mat d)

/-- The canonical strictly positive spectral projection. -/
def positiveSpectralProjection  : PDE.Mat d :=
  cfc positiveSpectralIndicator M

/-- The canonical strictly negative spectral projection. -/
def negativeSpectralProjection  : PDE.Mat d :=
  positiveSpectralProjection (-M)

/-- The canonical zero spectral projection. -/
def zeroSpectralProjection  : PDE.Mat d :=
  1 - positiveSpectralProjection M - negativeSpectralProjection M

/-- Each spectral ramp is continuous on the whole real line. -/
theorem continuous_positiveSpectralRamp (n : ℕ) : Continuous (positiveSpectralRamp n) := by
  unfold positiveSpectralRamp
  fun_prop

/-- At each scalar the ramps eventually equal the spectral indicator. -/
theorem positiveSpectralRamp_eventually (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, positiveSpectralRamp n t = positiveSpectralIndicator t := by
  by_cases ht : 0 < t
  · obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
    filter_upwards [eventually_ge_atTop N] with n hn


    have hnt  := ((div_le_iff₀ ht).mp hN).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hn) ht.le)
    simp [positiveSpectralRamp, positiveSpectralIndicator, ht, min_eq_left hnt]
  · apply Eventually.of_forall
    intro n
    have hnt  := mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg n) (le_of_not_gt ht)

    simp [positiveSpectralRamp, positiveSpectralIndicator, ht, max_eq_left ((min_le_right _ _).trans hnt)]

/-- At a Hermitian matrix the ramp calculus eventually equals the positive projection. -/
theorem spectralRamp_eventually {d : ℕ} (M : PDE.Mat d) (hM : M.IsHermitian) :
    ∀ᶠ n : ℕ in atTop, cfc (positiveSpectralRamp n) M = positiveSpectralProjection M := by

  filter_upwards [(eventually_all.mpr fun i => positiveSpectralRamp_eventually (hM.eigenvalues i))] with n hn
  apply cfc_congr
  intro t ht
  rw [hM.spectrum_real_eq_range_eigenvalues] at ht
  obtain ⟨i, rfl⟩ := ht
  exact hn i

/-- Continuous matrix fields have continuous ramp functional calculi. -/
theorem continuous_spectralRamp {X : Type*} [TopologicalSpace X] {d : ℕ}
    (M : X → PDE.Mat d) (hM : Continuous M) (hherm : ∀ x, (M x).IsHermitian)
    (n : ℕ) : Continuous (fun x => cfc (positiveSpectralRamp n) (M x)) := by
  apply Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (positiveSpectralRamp n)
    (by simp) hM hherm (continuous_positiveSpectralRamp n).continuousOn

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
