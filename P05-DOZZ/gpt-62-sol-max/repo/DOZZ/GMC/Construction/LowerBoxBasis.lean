/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Rational lower boxes determine finite measures on the plane, and each box is
approximated pointwise by uniformly bounded continuous ramps. -/

@[expose] public section

open MeasureTheory Filter Topology Set MeasurableSpace
open scoped ENNReal BoundedContinuousFunction

namespace DOZZ.Proofs

noncomputable section

/-- The rational lower rectangle used to determine finite measures on the plane. -/
def gmcLowerBox (i : ℚ × ℚ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ))

/-- Rational lower boxes are measurable in the standard Borel structure on the plane. -/
theorem gmcLowerBox_measurableSet (i : ℚ × ℚ) : MeasurableSet (gmcLowerBox i) := by
  change MeasurableSet
    (Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ)))
  simp

/-- One-dimensional continuous ramps for rational lower intervals. -/
def gmcLowerApprox (q : ℚ) (n : ℕ) (x : ℝ) : ℝ :=
  max 0 (min 1 (1 - (n : ℝ) * (x - q)))

section
variable (q : ℚ) (n : ℕ)

/-- The rational lower-interval ramps are continuous. -/
theorem gmcLowerApprox_continuous :
    Continuous (gmcLowerApprox q n) := by
  change Continuous (fun x : ℝ => max 0 (min 1 (1 - (n : ℝ) * (x - q))))
  fun_prop

/-- The rational lower-interval ramps take values in `[0,1]`. -/
theorem gmcLowerApprox_bounds (x : ℝ) :
    0 ≤ gmcLowerApprox q n x ∧ gmcLowerApprox q n x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

end

/-- Pointwise convergence of the rational lower-interval ramps. -/
theorem gmcLowerApprox_tendsto (q : ℚ) (x : ℝ) :
    Tendsto (fun n : ℕ => gmcLowerApprox q n x) atTop
      (𝓝 (if x ≤ (q : ℝ) then 1 else 0)) := by
  by_cases hx : x ≤ (q : ℝ)
  · have heq : ∀ n, gmcLowerApprox q n x = 1 := by
      intro n
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hxq  := sub_nonpos.mpr hx
      have harg : 1 ≤ 1 - (n : ℝ) * (x - q) := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hn hxq]
      simp [gmcLowerApprox, min_eq_left harg]
    simp [hx, heq]
  · have hpos  := sub_pos.mpr (lt_of_not_ge hx)
    have hqx  := lt_of_not_ge hx
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (x - (q : ℝ)))
    have heventually : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop] fun n => gmcLowerApprox q n x := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : 1 / (x - (q : ℝ)) < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
      have hprod : 1 ≤ (n : ℝ) * (x - (q : ℝ)) := by
        have := (div_lt_iff₀ hpos).mp hNn
        nlinarith
      have harg : 1 - (n : ℝ) * (x - (q : ℝ)) ≤ 0 := by linarith
      have hmin : min 1 (1 - (n : ℝ) * (x - (q : ℝ))) ≤ 0 :=
        le_trans (min_le_right _ _) harg
      simp [gmcLowerApprox, max_eq_left hmin]
    have hT  :=
      Tendsto.congr' heventually tendsto_const_nhds
    convert hT using 1
    simp [not_le_of_gt hqx]

/-- The pointwise product form of the lower-box approximant. -/
def gmcLowerBoxApproxFun (i : ℚ × ℚ) (n : ℕ) (z : ℂ) : ℝ :=
  gmcLowerApprox i.1 n z.re * gmcLowerApprox i.2 n z.im

section
variable (i : ℚ × ℚ) (n : ℕ)

/-- Continuity of the pointwise lower-box approximant. -/
theorem gmcLowerBoxApproxFun_continuous :
    Continuous (gmcLowerBoxApproxFun i n) := ((gmcLowerApprox_continuous i.1 n).comp Complex.continuous_re).mul
    ((gmcLowerApprox_continuous i.2 n).comp Complex.continuous_im)

/-- Bounds for the continuous lower-box approximants. -/
theorem gmcLowerBoxApprox_bounds (z : ℂ) :
    0 ≤ gmcLowerBoxApproxFun i n z ∧ gmcLowerBoxApproxFun i n z ≤ 1 := by
  have h₁ := gmcLowerApprox_bounds i.1 n z.re
  have h₂ := gmcLowerApprox_bounds i.2 n z.im
  constructor
  · exact mul_nonneg h₁.1 h₂.1
  · calc
      gmcLowerApprox i.1 n z.re * gmcLowerApprox i.2 n z.im ≤
          1 * gmcLowerApprox i.2 n z.im := mul_le_mul_of_nonneg_right h₁.2 h₂.1
      _ ≤ 1 := by simpa using h₂.2

end

/-- Continuous bounded approximants to a rational lower box. They converge pointwise to its
indicator and stay between zero and one. -/
def gmcLowerBoxApprox (i : ℚ × ℚ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨gmcLowerBoxApproxFun i n, gmcLowerBoxApproxFun_continuous i n⟩
    1 (by
      intro z w
      have hz := gmcLowerBoxApprox_bounds i n z
      have hw := gmcLowerBoxApprox_bounds i n w
      change dist (gmcLowerBoxApproxFun i n z) (gmcLowerBoxApproxFun i n w) ≤ 1
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

/-- Pointwise convergence of the continuous lower-box approximants. -/
theorem gmcLowerBoxApprox_tendsto (i : ℚ × ℚ) (z : ℂ) :
    Tendsto (fun n : ℕ => gmcLowerBoxApprox i n z) atTop
      (𝓝 ((gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z)) := by
  have hreal := gmcLowerApprox_tendsto i.1 z.re
  have himag := gmcLowerApprox_tendsto i.2 z.im
  have hmul := hreal.mul himag
  convert hmul using 1
  · rfl
  · by_cases hr : z.re ≤ (i.1 : ℝ) <;> by_cases hi : z.im ≤ (i.2 : ℝ) <;>
      simp [gmcLowerBox, Complex.measurableEquivRealProd_apply, Set.indicator, hr, hi]

/-- Under any finite measure, the integrals of the lower-box approximants converge to its box
mass. -/
theorem gmcLowerBoxApprox_integral_tendsto (i : ℚ × ℚ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ z, gmcLowerBoxApprox i n z ∂μ) atTop
      (𝓝 (μ.real (gmcLowerBox i))) := by
  have hbound : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const 1
  have hdom : ∀ n, ∀ᵐ z ∂μ, ‖gmcLowerBoxApprox i n z‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [] with z
    have hz := gmcLowerBoxApprox_bounds i n z
    change |gmcLowerBoxApproxFun i n z| ≤ 1
    rw [abs_le]
    exact ⟨by linarith, hz.2⟩
  have hlim : ∀ᵐ z ∂μ,
      Tendsto (fun n : ℕ => gmcLowerBoxApprox i n z) atTop
        (𝓝 ((gmcLowerBox i).indicator (fun _ => (1 : ℝ)) z)) :=
    ae_of_all _ (gmcLowerBoxApprox_tendsto i)
  have hs : MeasurableSet (gmcLowerBox i) := by
    change MeasurableSet
      (Complex.measurableEquivRealProd ⁻¹' (Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ)))
    simp
  have hdomconv := tendsto_integral_of_dominated_convergence
    (fun _ : ℂ => (1 : ℝ))
    (fun n => (gmcLowerBoxApprox i n).continuous.measurable.aestronglyMeasurable)
    hbound hdom hlim
  rwa [← integral_indicator_one hs]

private def gmcRatLowerIntervals : Set (Set ℝ) :=
  ⋃ q : ℚ, {Set.Iic (q : ℝ)}

private theorem gmcRatLowerIntervals_spanning : IsCountablySpanning gmcRatLowerIntervals := by
  refine ⟨fun n => Set.Iic (n : ℝ), ?_, ?_⟩
  · intro n
    exact Set.mem_iUnion.mpr ⟨(n : ℚ), Set.mem_singleton _⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, le_of_lt hn⟩

private def gmcRatLowerRectangles : Set (Set (ℝ × ℝ)) :=
  Set.image2 (fun s t : Set ℝ => s ×ˢ t) gmcRatLowerIntervals gmcRatLowerIntervals

private theorem gmcRatLowerRectangles_generate :
    generateFrom gmcRatLowerRectangles = borel (ℝ × ℝ) := by
  have hreal : generateFrom gmcRatLowerIntervals = borel ℝ :=
    Real.borel_eq_generateFrom_Iic_rat.symm
  have hprod := generateFrom_eq_prod hreal hreal
    gmcRatLowerIntervals_spanning gmcRatLowerIntervals_spanning
  simpa only [gmcRatLowerRectangles, BorelSpace.measurable_eq] using hprod

private theorem gmcRatLowerRectangles_pi : IsPiSystem gmcRatLowerRectangles :=
  (Real.isPiSystem_Iic_rat).prod Real.isPiSystem_Iic_rat

private def gmcLowerBoxFamily : Set (Set ℂ) :=
  {s | ∃ t ∈ gmcRatLowerRectangles, Complex.measurableEquivRealProd ⁻¹' t = s}

private theorem gmcLowerBoxFamily_representation {s : Set ℂ} (hs : s ∈ gmcLowerBoxFamily) :
    ∃ i : ℚ × ℚ, gmcLowerBox i = s := by
  rcases hs with ⟨t, ht, rfl⟩
  change t ∈ Set.image2 (fun a b : Set ℝ => a ×ˢ b) gmcRatLowerIntervals gmcRatLowerIntervals at ht
  rcases Set.mem_image2.mp ht with ⟨a, ha, b, hb, rfl⟩
  rcases Set.mem_iUnion.mp ha with ⟨p, hp⟩
  rcases Set.mem_iUnion.mp hb with ⟨q, hq⟩
  simp only [Set.mem_singleton_iff] at hp hq
  subst a
  subst b
  exact ⟨(p, q), rfl⟩

private theorem gmcLowerBoxFamily_generate : generateFrom gmcLowerBoxFamily = borel ℂ := by
  calc
    generateFrom gmcLowerBoxFamily =
        MeasurableSpace.comap Complex.measurableEquivRealProd
          (generateFrom gmcRatLowerRectangles) := by
            rw [MeasurableSpace.comap_generateFrom]
            rfl
    _ = MeasurableSpace.comap Complex.measurableEquivRealProd (borel (ℝ × ℝ)) := by
          rw [gmcRatLowerRectangles_generate]
    _ = borel ℂ := by
          simpa only [BorelSpace.measurable_eq] using
            Complex.measurableEquivRealProd.measurableEmbedding.comap_eq

private theorem gmcLowerBoxFamily_pi : IsPiSystem gmcLowerBoxFamily :=
  gmcRatLowerRectangles_pi.comap Complex.measurableEquivRealProd

def gmcBasisSet : Option (ℚ × ℚ) → Set ℂ
  | none => Set.univ
  | some i => gmcLowerBox i

def gmcBasisFamily : Set (Set ℂ) := Set.range gmcBasisSet

private theorem gmcBasisFamily_eq :
    gmcBasisFamily = insert Set.univ gmcLowerBoxFamily := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => simp [gmcBasisSet]
    | some i =>
      right
      exact ⟨Set.Iic (i.1 : ℝ) ×ˢ Set.Iic (i.2 : ℝ), Set.mem_image2_of_mem
          (Set.mem_iUnion.mpr ⟨i.1, Set.mem_singleton _⟩)
          (Set.mem_iUnion.mpr ⟨i.2, Set.mem_singleton _⟩), rfl⟩
  · intro hs
    rcases hs with hs | hs
    · subst s
      exact ⟨none, rfl⟩
    · obtain ⟨i, hi⟩ := gmcLowerBoxFamily_representation hs
      exact ⟨some i, hi⟩

theorem gmcBasisFamily_pi : IsPiSystem gmcBasisFamily := by
  rw [gmcBasisFamily_eq]
  exact IsPiSystem.insert_univ gmcLowerBoxFamily_pi

theorem gmcBasisFamily_generate : generateFrom gmcBasisFamily = borel ℂ := by
  rw [gmcBasisFamily_eq]
  apply le_antisymm
  · apply generateFrom_le
    intro s hs
    rcases hs with hs | hs
    · subst s
      exact MeasurableSet.univ
    · have hgen := gmcLowerBoxFamily_generate
      exact hgen ▸ GenerateMeasurable.basic s hs
  · rw [← gmcLowerBoxFamily_generate]
    simp

theorem gmcBasisSet_measurableSet (i : Option (ℚ × ℚ)) : MeasurableSet (gmcBasisSet i) := by
  cases i with
  | none => exact MeasurableSet.univ
  | some i => exact gmcLowerBox_measurableSet i

end

end DOZZ.Proofs
