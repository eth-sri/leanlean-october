/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedRealPolynomial
public import DOZZ.Complex.Identity

/-! Real charge margins persist on positive complex polydiscs. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs
section
variable {N : ℕ}
section
variable (γ : ℝ)

/-- The complex zero-mode power is a continuous affine function of all charges. -/
theorem complexMomentPower_continuous :
    Continuous (complexMomentPower (N := N) γ) := by
  unfold complexMomentPower
  fun_prop

/-- Strict real scalar margins give a complex polydisc on which all uniform-envelope bounds
hold simultaneously. -/
theorem complex_charge_budget_neighborhood (α : Fin N → ℝ)
    (A a lo hi b : ℝ) (hA : ∀ i, |α i| < A) (ha : ∀ i, α i < a)
    (hlo : lo < (2 * Q γ - ∑ i, α i) / γ - 1)
    (hhi : (2 * Q γ - ∑ i, α i) / γ < hi)
    (hb : |(2 * Q γ - ∑ i, α i) / γ| < b) :
    ∃ R : Fin N → ℝ, (∀ i, 0 < R i) ∧
      ∀ β ∈ complexPolydisc (fun i => (α i : ℂ)) R,
        (∀ i, |(β i).re| ≤ A) ∧ (∀ i, (β i).re ≤ a) ∧
          lo ≤ (complexMomentPower γ β).re - 1 ∧
          (complexMomentPower γ β).re ≤ hi ∧ ‖complexMomentPower γ β‖ ≤ b := by
  let U : Set (Fin N → ℂ) := {β |
    (∀ i, |(β i).re| < A) ∧ (∀ i, (β i).re < a) ∧
      lo < (complexMomentPower γ β).re - 1 ∧
      (complexMomentPower γ β).re < hi ∧ ‖complexMomentPower γ β‖ < b}
  have hre (i : Fin N) : Continuous (fun β : Fin N → ℂ => (β i).re) :=
    by fun_prop
  have hp := complexMomentPower_continuous (N := N) γ
  have hpr : Continuous (fun β => (complexMomentPower γ β).re) :=
    Complex.continuous_re.comp hp
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro β hβ
    have h1 : ∀ᶠ v in 𝓝 β, ∀ i, |(v i).re| < A :=
      eventually_all.mpr (fun i => (hre i).abs.continuousAt.eventually_lt_const (hβ.1 i))
    have h2 : ∀ᶠ v in 𝓝 β, ∀ i, (v i).re < a :=
      eventually_all.mpr (fun i => (hre i).continuousAt.eventually_lt_const (hβ.2.1 i))
    have h3 : ∀ᶠ v in 𝓝 β, lo < (complexMomentPower γ v).re - 1 :=
      continuousAt_const.eventually_lt
        (show ContinuousAt (fun v => (complexMomentPower γ v).re - 1) β from
          by fun_prop) hβ.2.2.1
    exact h1.and (h2.and (h3.and ((hpr.continuousAt.eventually_lt_const hβ.2.2.2.1).and (hp.norm.continuousAt.eventually_lt_const hβ.2.2.2.2))))
  have hc : (fun i => (α i : ℂ)) ∈ U := by
    change (∀ i, |(α i : ℂ).re| < A) ∧ (∀ i, (α i : ℂ).re < a) ∧ _
    simp only [Complex.ofReal_re, complexMomentPower_ofReal, Complex.norm_real,
      Real.norm_eq_abs]
    exact ⟨hA, ha, hlo, hhi, hb⟩
  obtain ⟨R, hR, _, hsub⟩ := exists_closed_polydisc_subset_open U hU _ hc
  refine ⟨R, hR, fun β hβ => ?_⟩
  have hv := hsub hβ
  exact ⟨fun i => (hv.1 i).le, fun i => (hv.2.1 i).le,
    hv.2.2.1.le, hv.2.2.2.1.le, hv.2.2.2.2.le⟩

end

/-- A real-centered polydisc contains a smaller positive polydisc with arbitrarily small
squared imaginary-charge size. -/
theorem polydisc_thin_imaginary (α R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (d : ℝ) (hd : 0 < d) :
    ∃ S : Fin N → ℝ, (∀ i, 0 < S i) ∧
      complexPolydisc (fun i => (α i : ℂ)) S ⊆ complexPolydisc (fun i => (α i : ℂ)) R ∧
        ∀ β ∈ complexPolydisc (fun i => (α i : ℂ)) S, (∑ i, (β i).im ^ 2) ≤ d := by
  have him : Continuous (fun β : Fin N → ℂ => ∑ i, (β i).im ^ 2) :=
    by fun_prop
  let U := complexPolydisc (fun i => (α i : ℂ)) R ∩ {β | (∑ i, (β i).im ^ 2) < d}
  have hU : IsOpen U := (isOpen_complexPolydisc _ R).inter
    (isOpen_lt him continuous_const)
  have hc : (fun i => (α i : ℂ)) ∈ U :=
    ⟨mem_complexPolydisc_center _ R hR, by simp_all⟩
  obtain ⟨S, hS, _, hsub⟩ := exists_closed_polydisc_subset_open U hU _ hc
  grind

end

end DOZZ.Proofs
