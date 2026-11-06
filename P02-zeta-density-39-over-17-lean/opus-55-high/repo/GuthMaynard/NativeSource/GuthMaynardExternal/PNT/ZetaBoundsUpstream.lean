module
/- Adapted from PrimeNumberTheoremAnd/ZetaBounds.lean at upstream revision
4ecb950126c4290293c5662dfe0e884123171df5 (Apache-2.0). -/

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Auxiliary
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Fourier
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic
public import GuthMaynard.NativeSource.GuthMaynardExternal.PNT.ResidueCalcOnRectangles
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.EulerMaclaurin
public import WeylPort.Analytic.ZetaContinuation
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Topology Filter Interval Set Asymptotics

alias nativeMoment_div_cpow_eq_cpow_neg := div_cpow_eq_cpow_neg

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- The `nativeMoment_riemannZeta0` definition used by the source-facing construction in
`ZetaBoundsUpstream`. -/

noncomputable def nativeMoment_riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => nativeMoment_riemannZeta0

theorem nativeMoment_riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [nativeMoment_riemannZeta0, nativeMoment_div_cpow_eq_cpow_neg]; ring

alias Real.nativeMoment_differentiableAt_cpow_const_of_ne := Real.differentiableAt_cpow_const_of_ne

alias Complex.nativeMoment_one_div_cpow_eq := Complex.one_div_cpow_eq

alias nativeMoment_sum_eq_int_deriv := sum_eq_int_deriv

alias nativeMoment_xpos_of_uIcc := xpos_of_uIcc

alias nativeMoment_ZetaSum_aux1₁ := ZetaSum_aux1₁

alias nativeMoment_ZetaSum_aux1φDiff := ZetaSum_aux1φDiff

alias nativeMoment_ZetaSum_aux1φderiv := ZetaSum_aux1φderiv

alias nativeMoment_ZetaSum_aux1derivφCont := ZetaSum_aux1derivφCont

set_option backward.isDefEq.respectTransparency false in

alias nativeMoment_ZetaSum_aux1 := ZetaSum_aux1

alias nativeMoment_ZetaSum_aux1_3 := ZetaSum_aux1_3

alias Finset.nativeMoment_Ioc_eq_Ico := Finset.Ioc_eq_Ico

alias nativeMoment_finsetSum_tendsto_tsum := finsetSum_tendsto_tsum

alias Complex.nativeMoment_cpow_tendsto := Complex.cpow_tendsto

alias Complex.nativeMoment_cpow_inv_tendsto := Complex.cpow_inv_tendsto

alias nativeMoment_ZetaSum_aux2a := ZetaSum_aux2a

alias nativeMoment_ZetaSum_aux3 := ZetaSum_aux3

alias nativeMoment_integrableOn_of_Zeta0_fun := integrableOn_of_Zeta0_fun

alias nativeMoment_ZetaSum_aux2 := ZetaSum_aux2

alias nativeMoment_isOpen_aux := isOpen_aux

open MeasureTheory in
alias nativeMoment_integrable_log_over_pow := integrable_log_over_pow

open MeasureTheory in
alias nativeMoment_integrableOn_of_Zeta0_fun_log := integrableOn_of_Zeta0_fun_log

open MeasureTheory in
theorem nativeMoment_hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [Set.mem_ofPred_eq] at hs
  pm_37
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    pm_40
    convert nativeMoment_integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    pm_42
  have hF_int : Integrable (F s) μ := by
    convert nativeMoment_integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    pm_42
  pm_1234 nativeMoment_integrableOn_of_Zeta0_fun_log
  pm_38
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    pm_36
    · rw [mul_comm, ← mul_assoc]
      pm_41
      pm_7100 nativeMoment_ZetaSum_aux1_3
      pm_39
  pm_43
  have bound_integrable : Integrable bound μ := by
    simpa only [bound, μ, IntegrableOn, Real.norm_eq_abs] using
      nativeMoment_integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos
  pm_35

/-- The `nativeMoment_ζ₀'` definition used by the source-facing construction in `ZetaBoundsUpstream`. -/
noncomputable def nativeMoment_ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))

alias nativeMoment_HasDerivAt_neg_cpow_over2 := HasDerivAt_neg_cpow_over2

alias nativeMoment_HasDerivAt_cpow_over_var := HasDerivAt_cpow_over_var

theorem nativeMoment_HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (nativeMoment_ζ₀' N s) s := by
  unfold nativeMoment_riemannZeta0 nativeMoment_ζ₀'
  pm_44
  · have hh := (nativeMoment_HasDerivAt_cpow_over_var N (by change 1-s ≠ 0; exact sub_ne_zero.mpr s_ne_one.symm)).comp s
      ((hasDerivAt_const s (1:ℂ)).sub (hasDerivAt_id s))
    convert hh using 1 <;> simp [Function.comp_def, Pi.sub_def]
    ring
  pm_7384 nativeMoment_HasDerivAt_neg_cpow_over2
  · simp_rw [nativeMoment_div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    simpa [Pi.mul_def] using (hasDerivAt_id s).mul (nativeMoment_hasDerivAt_Zeta0Integral Npos reS_pos)

theorem nativeMoment_HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (nativeMoment_HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`
theorem nativeMoment_HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  pm_7670 Set.mem_ofPred_eq

alias nativeMoment_isPathConnected_aux := isPathConnected_aux

theorem nativeMoment_Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  pm_49 nativeMoment_HolomorphicOn_riemannZeta.analyticOnNhd Set.ofPred_subset_ofPred nativeMoment_HolomorphicOn_riemannZeta0 nativeMoment_isOpen_aux nativeMoment_isPathConnected_aux
  pm_47
  pm_48 Set.ofPred_subset_ofPred Set.mem_ofPred_eq nativeMoment_riemannZeta0_apply nativeMoment_ZetaSum_aux2

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{theorem}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{theorem}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients
