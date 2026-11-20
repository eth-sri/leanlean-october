module

public import PottsDiscontinuity.Bethe.AsymptoticEndpoint
public import PottsDiscontinuity.BetheAnsatz.Defs

/-! # Endpoint factors in the eigenvalue ratio

Fixed-rank roots converge to `-π`. The spectral factor there is `Δ`,
so each missing boundary root contributes `|Δ|` to the denominator.
-/

@[expose] public section

open Set Filter Finset Complex
open scoped Topology BigOperators

namespace PottsDiscontinuity.Bethe

open BetheAnsatz

theorem ratio_z_neg_pi : z (-Real.pi) = -1 := by
  simp [z, Complex.ofReal_neg, mul_neg, Complex.exp_neg, mul_comm I, Complex.exp_pi_mul_I]

theorem ratio_M_neg_pi (c : ℝ) : M c (z (-Real.pi)) = (anisotropy c : ℂ) := by
  rw [ratio_z_neg_pi]
  simp only [M, sub_neg_eq_add, one_add_one_eq_two]
  unfold anisotropy
  push_cast
  ring

theorem ratio_continuousAt_M {x : ℝ} (hx : z x ≠ 1) (c : ℝ) :
    ContinuousAt (fun y => M c (z y)) x := by
  have hz : Continuous (z : ℝ → ℂ) := by
    unfold z
    fun_prop
  exact continuousAt_const.sub (continuousAt_const.div
    (continuousAt_const.sub hz.continuousAt) (sub_ne_zero.mpr (Ne.symm hx)))

variable {ι : Type*} {f : Filter ι} {c : ℝ} (hc : 2 < c) (s : ℕ) (x : ι → Fin s → ℝ) (y : ι → ℝ)
    (hx : ∀ j, Tendsto (fun i => x i j) f (𝓝 (-Real.pi)))

/-- An eventual mesh estimate suffices for endpoint convergence. -/
theorem ratio_tendsto_root_left_of_eventual_mesh
    {n : ι → ℕ} {hn : ∀ i, 0 < n i} (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (d : ι → ℝ) (hd : Tendsto d f (𝓝 0))
    (hdnonneg : ∀ i, 0 ≤ d i)
    (hmesh : ∀ᶠ i in f, ∀ j : Fin (n i + 1),
      rootPartitionPoint (p i) (hn i) j.succ -
        rootPartitionPoint (p i) (hn i) j.castSucc ≤ d i)
    {j : ∀ i, Fin (n i)} (J : ℕ) (hrank : ∀ i, (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) f (𝓝 (-Real.pi)) := by
  have hb : Tendsto (fun i => ((J : ℝ) + 1) * d i) f (𝓝 0) := by
    simpa only [mul_zero] using hd.const_mul ((J : ℝ) + 1)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hmesh, hb.eventually (gt_mem_nhds hε)] with i hi hbi
  rw [Real.dist_eq, sub_neg_eq_add,
    abs_of_nonneg (by have := ((hp i).1 (j i)).1; linarith)]
  have he := (root_distance_from_boundary (hp i) hi (j i)).1
  have hr : ((j i).val : ℝ) + 1 ≤ (J : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right (hrank i) 1
  exact he.trans_lt ((mul_le_mul_of_nonneg_right hr (hdnonneg i)).trans_lt hbi)

/-- Fixed-rank roots under the source density-convergence hypotheses. -/
theorem ratio_tendsto_root_left {Δ : ℝ} (hΔ : Δ < -1)
    (r : ℕ) (N n : ι → ℕ) (p : ∀ i, Fin (n i) → ℝ)
    (hp : ∀ i, p i ∈ S_n (n i)) (hn : ∀ i, 0 < n i) {hs : ∀ i, 2 * n i ≤ N i}
    (hcount : ∀ i, N i = 2 * (n i + r))
    (hNlim : Tendsto (fun i => (N i : ℝ)) f atTop)
    (hb : ∀ i, BddAbove (range fun α : Icc (-Real.pi) Real.pi =>
      |Xi (lamOf Δ) α * (rootStepDensity (N i) (p i) (hn i)
        (kMap (lamOf Δ) α) - rho Δ (kMap (lamOf Δ) α))|))
    (hlim : Tendsto (fun i => densityNorm Δ
      (fun x => rootStepDensity (N i) (p i) (hn i) x - rho Δ x)) f (𝓝 0))
    {j : ∀ i, Fin (n i)} (J : ℕ) (hrank : ∀ i, (j i).val ≤ J) :
    Tendsto (fun i => p i (j i)) f (𝓝 (-Real.pi)) := by
  obtain ⟨m, hm, hmesh⟩ := eventually_rootPartition_gap_le (hΔ := hΔ) (r := r) (N := N) (n := n) (p := p) (hp := hp) (hn := hn) (hs := hs) hcount (hb := hb) hlim
  let d := fun i => 2 * (2 * r + 1 : ℝ) / (m * (N i : ℝ))
  have hd : Tendsto d f (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp hNlim).const_mul (2 * (2 * r + 1 : ℝ) / m)
    grind
  exact ratio_tendsto_root_left_of_eventual_mesh p hp d hd (fun i => by positivity)
    hmesh J hrank

/-- Continuity of the spectral modulus at the endpoint. -/
theorem ratio_modulus_tendsto_endpoint {x : ι → ℝ}
    (hx : Tendsto x f (𝓝 (-Real.pi))) (c : ℝ) :
    Tendsto (fun i => ‖M c (z (x i))‖) f (𝓝 |anisotropy c|) := by
  have hz : z (-Real.pi) ≠ 1 := by grind [ratio_z_neg_pi]
  have ht := ((ratio_continuousAt_M hz c).norm.tendsto).comp hx
  simpa only [ratio_M_neg_pi, Complex.norm_real, Real.norm_eq_abs, Function.comp_def] using ht

include hc hx in
/-- The even source term (2), once the fixed-rank endpoint limits are known. -/
theorem ratio_even_boundary_tendsto :
    Tendsto (fun i => ((∏ j, ‖M c (z (x i j))‖) ^ 2)⁻¹) f
      (𝓝 ((|anisotropy c| ^ s) ^ 2)⁻¹) := by
  have ht := tendsto_finsetProd univ (fun j _ => ratio_modulus_tendsto_endpoint (hx j) c)
  simp only [prod_const, card_univ, Fintype.card_fin] at ht
  have hΔ := anisotropy_lt_neg_one hc
  have hn : ((|anisotropy c| ^ s) ^ 2) ≠ 0 := by
    apply pow_ne_zero
    apply pow_ne_zero
    grind
  simpa only [prod_const, card_univ, Fintype.card_fin] using (ht.pow 2).inv₀ hn

include hc hx in
/-- The odd source term (2), with one unpaired endpoint factor. -/
theorem ratio_odd_boundary_tendsto
    (hy : Tendsto y f (𝓝 (-Real.pi))) :
    Tendsto (fun i => (‖M c (z (y i))‖ * (∏ j, ‖M c (z (x i j))‖) ^ 2)⁻¹) f
      (𝓝 (|anisotropy c| ^ (2 * s + 1))⁻¹) := by
  have ht := tendsto_finsetProd univ (fun j _ => ratio_modulus_tendsto_endpoint (hx j) c)
  simp only [prod_const, card_univ, Fintype.card_fin] at ht
  have he : |anisotropy c| * (|anisotropy c| ^ s) ^ 2 =
      |anisotropy c| ^ (2 * s + 1) := by
    ring
  have hlim := (ratio_modulus_tendsto_endpoint hy c).mul (ht.pow 2)
  rw [he] at hlim
  apply hlim.inv₀
  apply pow_ne_zero
  exact abs_ne_zero.mpr (by have := anisotropy_lt_neg_one hc; linarith)

end PottsDiscontinuity.Bethe
