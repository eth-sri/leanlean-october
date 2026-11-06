module

public import AnalyticESC.Dual.Attractor

@[expose] public section

/-!
# Lemma 2.6

The strong separation of the dual IFS from disjointness of cylinder intervals.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- On `I`, `F_w` applied to a constant `c` is affine in `c`. -/
private theorem re_dualComp_const (w : List (Fin N)) (c : ℝ) {x : ℝ} (hx : x ∈ I) :
    (Φ.dualComp w (fun _ => (c : ℂ)) x).re =
      (deriv (Φ.comp w.reverse) x).re * c + (Φ.dualProj (.fin w) x).re := by
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos hx)]; simp [Complex.mul_re]

/-- Points of one cylinder interval of `Φ` at `x ∈ I` are `c_max^{|w|} (K - k)` close. -/
theorem abs_sub_le_cmax_pow_of_mem_dualCylAt {k K : ℝ} (hkK : k ≤ K) (w : List (Fin N))
    {x : ℝ} (hx : x ∈ I) {p q : ℝ} (hp : p ∈ Φ.dualCylAt k K w x)
    (hq : q ∈ Φ.dualCylAt k K w x) : |p - q| ≤ Φ.cmax ^ w.length * (K - k) := by
  refine (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hq hp)).trans ?_
  have h := Φ.norm_deriv_comp_le w.reverse (subset_closure (ofReal_mem_nbhd Φ.ε_pos hx))
  rw [List.length_reverse] at h
  rw [Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx,
    show |(deriv (Φ.comp w.reverse) x).re * K + (Φ.dualProj (.fin w) x).re -
      ((deriv (Φ.comp w.reverse) x).re * k + (Φ.dualProj (.fin w) x).re)| =
      |(deriv (Φ.comp w.reverse) x).re| * (K - k) by
        rw [← abs_of_nonneg (sub_nonneg.2 hkK), ← abs_mul]; congr 1; ring]
  exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans h) (sub_nonneg.2 hkK)

/-- Lemma 2.6, (b) ⇒ (a): if `H_u(y) ∈ [k,K]` for all `u` and `y ∈ I`, and `F_i(k,K) ∩ F_j(k,K) = ∅`
in the sense of (2.2) for all `i, j ∈ Σ_{n+1}` with `i₁ ≠ j₁`, then the dual IFS satisfies the SSC. -/
theorem lemma_2_6 {k K : ℝ} (n : ℕ)
    (hH : ∀ u : ℕ → Fin N, ∀ y ∈ I, (Φ.dualProj (.inf u) y).re ∈ Icc k K)
    (hdisj : ∀ i j : Fin (n + 1) → Fin N, i 0 ≠ j 0 →
      Φ.DualCylDisjoint k K (List.ofFn i) (List.ofFn j)) : Φ.DualSSC := by
  intro i j hij
  obtain ⟨x, hx, hd⟩ := hdisj (fun m => i m) (fun m => j m) (by simpa using hij)
  have hxn := ofReal_mem_nbhd Φ.ε_pos hx
  have mem (u : ℕ → Fin N) :
      (Φ.dualProj (.inf u) x).re ∈ Φ.dualCylAt k K (List.ofFn fun m : Fin (n + 1) => u m) x := by
    set w := List.ofFn fun m : Fin (n + 1) => u m
    rw [Word.inf_eq_prepend u (n + 1), dualCylAt, Φ.re_dualComp_const _ _ hx,
      Φ.re_dualComp_const _ _ hx, Φ.dualProj_prepend w _ (subset_closure hxn),
      Φ.comp_ofReal w.reverse hx]
    simp only [Complex.add_re, Complex.mul_re, Φ.im_deriv_comp_ofReal _ hxn, zero_mul, sub_zero,
      mem_uIcc]
    obtain ⟨h1, h2⟩ := hH (fun m => u (n + 1 + m)) _ (Φ.re_comp_mem_I w.reverse hx)
    rcases le_total 0 (deriv (Φ.comp w.reverse) x).re with ha | ha
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  exact ⟨x, hx, fun heq => Set.disjoint_left.1 hd (heq ▸ mem i) (mem j)⟩

end IFS

end AnalyticESC
