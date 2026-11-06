module
import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.Prod
public import Mathlib.Analysis.Normed.Group.Bounded
public import GuthMaynard.NativeSource.PrimeNumberTheoremAnd.SmoothExistence
public import GuthMaynard.NativeSource.GuthMaynard.DirichletPolynomial

@[expose] public section

open Complex Finset
open scoped BigOperators ContDiff

namespace GuthMaynard.NativeMoment

/-!
# Source-facing objects for Guth--Maynard large values

These are the finite objects used by Sections 3--12 of Guth--Maynard.  They
replace the unrelated and false parabola-decoupling model formerly present in
the project.  No analytic estimate is postulated in this file.
-/

/-- A fixed smooth cutoff supported on the source dyadic interval.  Derivative
bounds are recorded separately by the lemmas that consume a cutoff, so that
their constant dependencies remain visible. -/
structure GMSmoothCutoff where
  /-- The `toFun` component of `GMSmoothCutoff`. -/
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  nonneg : ∀ x, 0 ≤ toFun x
  bounded : ∀ x, toFun x ≤ 1
  support : Function.support toFun ⊆ Set.Icc 1 2
  equals_one : ∀ x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5 : ℝ), toFun x = 1

instance : CoeFun GMSmoothCutoff (fun _ => ℝ → ℝ) := ⟨GMSmoothCutoff.toFun⟩

/-- A source-admissible cutoff exists.  This is the PNT+ smooth Urysohn lemma
specialized to `[6/5,9/5] ⊂ (1,2)`. -/
theorem exists_gmSmoothCutoff : Nonempty GMSmoothCutoff := by
  obtain ⟨w, hwSmooth, _hwCompact, hwLower, hwUpper, hwSupport⟩ :=
    smooth_urysohn_support_Ioo (a := (1 : ℝ)) (b := 6 / 5)
      (c := 9 / 5) (d := 2) (by norm_num) (by norm_num)
  refine ⟨{
    toFun := w
    smooth := hwSmooth
    nonneg := ?_
    bounded := ?_
    support := ?_
    equals_one := ?_ }⟩
  · intro x
    have hzero : 0 ≤ Set.indicator (Set.Icc (6 / 5 : ℝ) (9 / 5))
        (1 : ℝ → ℝ) x := by
      by_cases hx : x ∈ Set.Icc (6 / 5 : ℝ) (9 / 5)
      · simp [Set.indicator, hx]
      · simp [Set.indicator, hx]
    exact hzero.trans (hwLower x)
  · intro x
    exact (hwUpper x).trans (by
      by_cases hx : x ∈ Set.Ioo (1 : ℝ) 2
      all_goals (simp_all <;> nlinarith))
  · rw [hwSupport]
    exact Set.Ioo_subset_Icc_self
  · intro x hx
    have hxOpen : x ∈ Set.Ioo (1 : ℝ) 2 := by
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ioo]
      constructor <;> linarith
    have hLower := hwLower x
    have hUpper := hwUpper x
    rw [Set.indicator_of_mem hx] at hLower
    rw [Set.indicator_of_mem hxOpen] at hUpper
    simpa using le_antisymm hUpper hLower

/-- Rows of the Guth--Maynard sampling matrix are the selected ordinates. -/
abbrev GMRow (W : Finset ℝ) := {t : ℝ // t ∈ W}

/-- Columns of the sampling matrix are the integers in `(N,2N]`. -/
abbrev GMColumn (N : ℕ) := {n : ℕ // n ∈ dyadicInterval N}

section
variable (cutoff : GMSmoothCutoff) (N : ℕ)
include cutoff N

/-- The smoothed sampling-matrix entry from Section 4. -/
noncomputable def gmMatrixEntry 
    {W : Finset ℝ} (t : GMRow W) (n : GMColumn N) : ℂ :=
  cutoff ((n : ℝ) / N) * (n : ℂ) ^ ((t : ℂ) * I)

/-- The smoothed positive-phase Dirichlet polynomial sampled by the matrix. -/
noncomputable def gmSmoothDirichletPoly 
    (b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicInterval N,
    cutoff ((n : ℝ) / N) * b n * (n : ℂ) ^ ((t : ℂ) * I)
end


/-- Guth--Maynard's exponential sum `R(v) = ∑_{t∈W} |v|^{it}`. -/
noncomputable def gmR (W : Finset ℝ) (v : ℝ) : ℂ :=
  ∑ t ∈ W, ((|v| : ℝ) : ℂ) ^ ((t : ℂ) * I)

section
variable (η : ℝ) (W : Finset ℝ)
include η W

/-- Ordered additive quadruples whose additive defect is at most `η`. -/
noncomputable def approximateAdditiveQuadruples  :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((W ×ˢ W) ×ˢ (W ×ˢ W)).filter fun q =>
    |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ η

/-- Tolerance-`η` additive energy of a finite real set.  The source energy is
`ApproxAddEnergy 1 W`; unlike `Finset.addEnergy`, this counts approximate real
equalities. -/
noncomputable def ApproxAddEnergy  : ℕ :=
  (approximateAdditiveQuadruples η W).card

theorem approxAddEnergy_le_card_pow_four  :
    ApproxAddEnergy η W ≤ W.card ^ 4 := by
  unfold ApproxAddEnergy approximateAdditiveQuadruples
  calc
    (((W ×ˢ W) ×ˢ (W ×ˢ W)).filter fun q =>
        |q.1.1 + q.1.2 - q.2.1 - q.2.2| ≤ η).card
        ≤ ((W ×ˢ W) ×ˢ (W ×ˢ W)).card := Finset.card_filter_le _ _
    _ = W.card ^ 4 := by simp only [Finset.card_product]; ring
end


theorem card_sq_le_approxAddEnergy {η : ℝ} (hη : 0 ≤ η) (W : Finset ℝ) :
    W.card ^ 2 ≤ ApproxAddEnergy η W := by
  classical
  let diagonal : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (W ×ˢ W).image fun p => (p, p)
  have hDiagonalCard : diagonal.card = (W ×ˢ W).card := by
    apply Finset.card_image_of_injective
    intro p q hpq
    exact congrArg Prod.fst hpq
  have hSubset : diagonal ⊆ approximateAdditiveQuadruples η W := by
    intro q hq
    change q ∈ (W ×ˢ W).image (fun p => (p, p)) at hq
    rw [Finset.mem_image] at hq
    rcases hq with ⟨p, hp, rfl⟩
    simp only [approximateAdditiveQuadruples, Finset.mem_filter,
      Finset.mem_product] at hp ⊢
    exact ⟨⟨hp, hp⟩, by simpa using hη⟩
  calc
    W.card ^ 2 = (W ×ˢ W).card := by simp [pow_two]
    _ = diagonal.card := hDiagonalCard.symm
    _ ≤ (approximateAdditiveQuadruples η W).card := Finset.card_le_card hSubset
    _ = ApproxAddEnergy η W := rfl

section
variable (W : Finset ℝ)
include W

theorem gmR_one  : gmR W 1 = W.card := by
  simp [gmR]

section
variable (v : ℝ) (hv : v ≠ 0)
include v hv

/-- The trivial pointwise estimate for the source exponential sum. -/
theorem norm_gmR_le_card  :
    ‖gmR W v‖ ≤ W.card := by
  calc
    ‖∑ t ∈ W, ((|v| : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ ≤
        ∑ t ∈ W, ‖((|v| : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ :=
      norm_sum_le _ _
    _ = ∑ _t ∈ W, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr hv)]
      simp
    _ = W.card := by simp

/-- Reciprocal arguments conjugate the source exponential sum. -/
theorem gmR_reciprocal  :
    gmR W (1 / v) = star (gmR W v) := by
  rw [gmR, gmR, star_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hvabs : 0 < |v| := abs_pos.mpr hv
  have harg : (((|v| : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hvabs.le]
    exact Real.pi_ne_zero.symm
  have hConj :=
    Complex.cpow_conj (((|v| : ℝ) : ℂ)) ((t : ℂ) * I) harg
  have hInv :=
    Complex.inv_cpow (((|v| : ℝ) : ℂ)) ((t : ℂ) * I) harg
  have hcast : (((|v|)⁻¹ : ℝ) : ℂ) = (((|v| : ℝ) : ℂ))⁻¹ := by
    norm_num
  rw [abs_div, abs_one, one_div, hcast, hInv]
  rw [← Complex.cpow_neg]
  simp_all

theorem norm_gmR_reciprocal  :
    ‖gmR W (1 / v)‖ = ‖gmR W v‖ := by
  rw [gmR_reciprocal W v hv, norm_star]
end
end



