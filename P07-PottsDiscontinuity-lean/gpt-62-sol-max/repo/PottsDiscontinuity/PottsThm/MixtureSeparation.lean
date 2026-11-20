module

public import PottsDiscontinuity.PottsThm.ColoringErgodicity

/-! The mean and the second moment of each event in a finite mixture agree
with those of its pure phase if the mixture is also mixing. -/

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Filter Topology Finset
open scoped ENNReal

/-- A mixing finite average of mixing measures has no variation among its
components' probabilities of any measurable event. -/
theorem mixing_average_real_eq {C : Type*} [MeasurableSpace C] {q : ℕ} (hq : 0 < q)
    (μ : Measure (Vertex → C)) (ν : Fin q → Measure (Vertex → C))
    [∀ i, IsProbabilityMeasure (ν i)] (hμ : IsTranslationMixing μ)
    (hν : ∀ i, IsTranslationMixing (ν i))
    (h : μ = (q : ℝ≥0∞)⁻¹ • ∑ i, ν i)
    {A : Set (Vertex → C)} (hA : MeasurableSet A) (i : Fin q) : (ν i).real A = μ.real A := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hm (D : Set (Vertex → C)) :
      μ.real D = (q : ℝ)⁻¹ * ∑ j, (ν j).real D := by
    rw [h, Measure.real_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, Measure.finsetSum_apply,
      ENNReal.toReal_sum (fun j _ => measure_ne_top (ν j) _)]
    rfl
  have hlim := (tendsto_finsetSum univ fun j _ => hν j |>.2 A A hA hA).const_mul (q : ℝ)⁻¹
  have he (a : Vertex) := hm (A ∩ (spinShift a) ⁻¹' A)
  simp_rw [← he] at hlim
  have hsq := tendsto_nhds_unique (hμ.2 A A hA hA) hlim
  have hfirst := hm A
  field_simp [hq0] at hsq hfirst
  have hz : ∑ j, ((ν j).real A - μ.real A)^2 = 0 := by
    calc
      _ = ∑ j : Fin q, ((ν j).real A ^ 2 - (2 * μ.real A) * (ν j).real A + μ.real A ^ 2) :=
        sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const,
          card_univ, Fintype.card_fin, nsmul_eq_mul, ← hfirst, ← hsq]
        ring
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).mp hz i (mem_univ _)))

end PottsDiscontinuity.PottsThm
