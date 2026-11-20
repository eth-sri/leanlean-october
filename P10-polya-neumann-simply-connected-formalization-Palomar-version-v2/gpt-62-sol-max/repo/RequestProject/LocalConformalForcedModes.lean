module

public import RequestProject.ConformalDiskCoordinates

public import RequestProject.LocalConformalWeakModes

/-!
# Actual conformal harmonic coefficients with an independent mass forcing

The weak equation may contain a physical H¹ vector `q` distinct from its
solution `u`. Physical inverse-coordinate tests identify the mass term with
the actual Jacobian-weighted forcing of `q`, including for projected regular
solutions and resonant vectors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric Real
open scoped ComplexConjugate InnerProductSpace

/-- The genuine normalized weak equation with an independent physical mass
forcing vector. -/
def IsNormalizedNeumannForcedSolution {Ω : Set ℂ}
    (Q : NeumannH1 Ω →L[ℂ] L2Z) (b : L2Z) (u q : NeumannH1 Ω) : Prop :=
  ∀ v : NeumannH1 Ω,
    (∑ i, ⟪h1Gradient Ω i v, h1Gradient Ω i u⟫_ℂ) -
      ⟪h1Value Ω v, h1Value Ω q⟫_ℂ = ⟪Q v, b⟫_ℂ

private theorem normalize_forced_weak_mode {s t k a I b : ℂ}
    (hs : s ≠ 0) (hk : k ≠ 0)
    (h : s ^ 2 * k * a - I = t * s * b) :
    t * s * a - (t ^ 2 / k) * b = (t / (s * k)) * I := by grind


section

variable {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
include coords

local notation "PB" => coords.pullback
local notation "QT" => coords.halfTrace
local notation "BT" => coords.trace
local notation "MF" => localConformalMassForcing coords

private theorem forced_weak_test
    {b : L2Z} {u q : NeumannH1 (F '' ball (0 : ℂ) 1)}
    (hu : IsNormalizedNeumannForcedSolution QT b u q)
    {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    let d := smoothTraceH1 (ball (0 : ℂ) 1) ⟨diskHarmonicCutoff φ, diskHarmonicCutoff_testFunction hφ⟩
    (∑ i, inner ℂ (h1Gradient _ i d) (h1Gradient _ i (PB u))) -
      inner ℂ (h1Value _ d) (MF q) = inner ℂ (diskHalfTrace d) b := by
  obtain ⟨f, _, hf⟩ := exists_localConformal_physical_test coords hφ
  let v := smoothTraceH1 (F '' ball (0 : ℂ) 1) f
  have hg := localConformalH1Pullback_gradient_inner coords v u
  have hm := localConformal_mass_pairing coords v q
  have h := hu v
  change _ - _ = inner ℂ (diskHalfTrace (PB v)) b at h
  rw [← hg, hm, hf] at h
  exact h

/-- The signed harmonic tests give the same normalized equation at each nonzero frequency. -/
theorem localConformal_forced_principal_mode_ne_zero
    (b : L2Z) (u q : NeumannH1 (F '' ball (0 : ℂ) 1))
    (hu : IsNormalizedNeumannForcedSolution QT b u q) (n : ℤ) (hn : n ≠ 0) :
    QT u n - (((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)) * b n = diskMassForcingCoeff (MF q) n := by
  have hw : (2 * π : ℂ) * (n.natAbs : ℂ) * fourierCoeffOn two_pi_pos (BT u : ℝ → ℂ) n -
      inner ℂ (diskAreaMode n) (MF q) =
      ((Real.sqrt (sobWeight n) : ℂ) * (Real.sqrt (2 * π) : ℂ)) * b n := by
    cases n with
    | ofNat m =>
        have h := forced_weak_test coords hu (contDiff_diskHolomorphicMode m)
        change (∑ i, inner ℂ (h1Gradient _ i (diskHolomorphicH1Test m)) (h1Gradient _ i (PB u))) -
          inner ℂ (h1Value _ (diskHolomorphicH1Test m)) (MF q) =
            inner ℂ (diskHalfTrace (diskHolomorphicH1Test m)) b at h
        rw [disk_gradient_form_holomorphicTest, h1Value_diskHolomorphicH1Test, diskHalfTrace_holomorphicTest] at h
        simpa [diskAreaMode, localConformalDiskH1Trace, stdBasisZ_apply, lp.inner_single_left, inner_smul_left,
          RCLike.inner_apply'] using h
    | negSucc m =>
        have h := forced_weak_test coords hu (contDiff_diskAntiholomorphicMode (m + 1))
        change (∑ i, inner ℂ (h1Gradient _ i (diskAntiholomorphicH1Test (m + 1))) (h1Gradient _ i (PB u))) -
          inner ℂ (h1Value _ (diskAntiholomorphicH1Test (m + 1))) (MF q) =
            inner ℂ (diskHalfTrace (diskAntiholomorphicH1Test (m + 1))) b at h
        rw [disk_gradient_form_antiholomorphicTest, h1Value_diskAntiholomorphicH1Test,
          diskHalfTrace_antiholomorphicTest] at h
        have hneg : -((m + 1 : ℕ) : ℤ) = Int.negSucc m := by omega
        rw [hneg] at h
        simpa [diskAreaMode, localConformalDiskH1Trace, Int.natAbs_negSucc, stdBasisZ_apply,
          lp.inner_single_left, inner_smul_left, RCLike.inner_apply'] using h
  have hcast : (n.natAbs : ℂ) = ((|(n : ℝ)| : ℝ) : ℂ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, Complex.ofReal_natCast]
  rw [hcast] at hw
  have hs := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr two_pi_pos).ne'
  have hk : ((|(n : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hn))
  have hs2 : (Real.sqrt (2 * π) : ℂ) ^ 2 = (2 * π : ℂ) := by
    exact_mod_cast Real.sq_sqrt two_pi_pos.le
  have ht2 : (Real.sqrt (sobWeight n) : ℂ) ^ 2 = (sobWeight n : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sobWeight_pos n).le
  have hh := normalize_forced_weak_mode hs hk (by rwa [hs2])
  rw [ht2] at hh
  rw [localConformalDiskHalfTrace_apply]
  change (Real.sqrt (sobWeight n) : ℂ) * boundaryFourier (BT u) n - _ = _
  rw [boundaryFourier_apply]
  simpa [Complex.ofReal_div, Complex.ofReal_mul, diskMassForcingCoeff, mul_assoc] using hh

end

end PolyaNeumann

end
