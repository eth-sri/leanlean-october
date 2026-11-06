/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ParameterDomain
public import Mathlib.Topology.Order.LeftRightNhds

/-! Strict real charge inequalities supply every margin used by the analytic estimates. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Around each strictly admissible real charge vector one can choose a common upper charge,
a small positive annular moment, and a higher positive endpoint moment with strict slack.
The lower endpoint leaves room for the derivative power. -/
theorem real_charge_moment_budget {I : Type*} [Fintype I]
    (γ : ℝ) (hγ : 0 < γ) (α : I → ℝ) (p : ℝ)
    (ha : ∀ i, α i < Q γ) (hp : p < 4 / γ ^ 2)
    (hpi : ∀ i, p < 2 / γ * (Q γ - α i)) :
    ∃ A a gap m g lo hi q b : ℝ,
      (∀ i, |α i| < A) ∧ (∀ i, α i < a) ∧ 0 < gap ∧ a + gap < Q γ ∧
      0 < m ∧ m ≤ 1 ∧ m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap))) ∧
      0 < g ∧ lo ≤ 0 ∧ lo < p - 1 ∧ 0 ≤ hi ∧ p < hi ∧ 1 < q ∧ |p| < b ∧
      hi * q + g ≤ 4 / γ ^ 2 ∧ hi * q + g ≤ 2 / γ * (Q γ - a) := by
  have hb0 : 0 < 4 / γ ^ 2 := by positivity
  have hi0 (i : I) : 0 < 2 / γ * (Q γ - α i) :=
    by simp_all
  have eb : ∀ᶠ t in 𝓝[>] (max p 0), t ∈ Ioo (max p 0) (4 / γ ^ 2) :=
    Ioo_mem_nhdsGT (max_lt hp hb0)
  have ei : ∀ᶠ t in 𝓝[>] (max p 0), ∀ i, t ∈ Ioo (max p 0) (2 / γ * (Q γ - α i)) :=
    eventually_all.mpr (fun i => Ioo_mem_nhdsGT (max_lt (hpi i) (hi0 i)))
  obtain ⟨t, ht, hti⟩ := (eb.and ei).exists
  have ht0 : 0 < t := by grind
  have hpt : p < t := by grind
  let u := Q γ - γ * t / 2
  have hau (i : I) : α i < u := by
    have hi := mul_lt_mul_of_pos_right (hti i).2 hγ
    have he : (2 / γ * (Q γ - α i)) * γ = 2 * (Q γ - α i) := by field_simp
    dsimp only [u]
    nlinarith
  have ea : ∀ᶠ a in 𝓝[<] u, ∀ i, α i < a :=
    eventually_all.mpr (fun i => by
      filter_upwards [Ioo_mem_nhdsLT (hau i)] with a ha
      exact ha.1)
  obtain ⟨a, hαa, ha0⟩ := (ea.and (Ioo_mem_nhdsLT (by linarith : u - 1 < u))).exists
  have hau' : a < u := ha0.2
  have haQ : a < Q γ := by dsimp only [u] at hau'; nlinarith
  have htroot : t < 2 / γ * (Q γ - a) := by
    apply (mul_lt_mul_iff_of_pos_right hγ).mp
    have he : (2 / γ * (Q γ - a)) * γ = 2 * (Q γ - a) := by field_simp
    dsimp only [u] at hau'
    nlinarith
  let gap := (Q γ - a) / 2
  have hgap : 0 < gap := by positivity
  have hgapQ : a + gap < Q γ := by grind
  let T := min (4 / γ ^ 2) (2 / γ * (Q γ - (a + gap)))
  have hT : 0 < T := by positivity
  let m := min 1 T / 2
  have hm : 0 < m := by positivity
  have hmT : m < T := by
    have := min_le_right (1 : ℝ) T
    dsimp only [m]
    linarith
  have hm1 : m ≤ 1 := by
    have := min_le_left (1 : ℝ) T
    dsimp only [m]
    linarith
  let hi := (max p 0 + t) / 2
  have hhi : 0 < hi := by positivity
  have hphi : p < hi := by grind
  have hhit : hi < t := by grind
  let q := 1 + (t - hi) / (2 * hi)
  have hq : 1 < q := by dsimp only [q]; linarith [div_pos (sub_pos.mpr hhit) (by positivity : 0 < 2 * hi)]
  have hhiq : hi * q = (hi + t) / 2 := by grind
  let g := (t - hi * q) / 2
  have hg : 0 < g := by grind
  have hgt : hi * q + g < t := by grind
  let A := 1 + ∑ i, |α i|
  have hA (i : I) : |α i| < A := by
    have he := Finset.single_le_sum
      (fun j _ => abs_nonneg (α j)) (Finset.mem_univ i)
    linarith
  let lo := min (-1) (p - 2)
  have hlo : lo ≤ 0 := by grind
  have hlop : lo < p - 1 := by grind
  exact ⟨A, a, gap, m, g, lo, hi, q, |p| + 1, hA, hαa, hgap, hgapQ, hm, hm1,
    hmT, hg, hlo, hlop, hhi.le, hphi, hq, by linarith, hgt.le.trans ht.2.le, hgt.le.trans htroot.le⟩

end DOZZ.Proofs
