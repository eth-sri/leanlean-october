module

public import AnalyticESC.Dual.Attractor

public section

/-!
# Lemma 2.6

The strong separation of the dual IFS in terms of cylinder sets, (a) ⇔ (b), and in terms of the
dual natural projection, (a) ⇔ (c).
-/

namespace AnalyticESC

variable {K k x : ℝ}

open Set Filter

/-- The cylinder set `(k,K)` of Section 2.1: maps in `C^ω_ε([0,1])` with values in `(k,K)` on
`[0,1]`. -/
def dualCyl (ε k K : ℝ) : Set (ℂ → ℂ) :=
  {g | DifferentiableOn ℂ g (nbhd ε) ∧ ContinuousOn g (𝔹 ε) ∧
    (Ɐ (g x).im = 0) ∧
    Ɐ k < (g x).re ∧ (g x).re < K}

/-- The closed cylinder set `cl (k,K)`: maps in `C^ω_ε([0,1])` with values in `[k,K]` on
`[0,1]`. -/
def dualCylClosed (ε k K : ℝ) : Set (ℂ → ℂ) :=
  {g | DifferentiableOn ℂ g (nbhd ε) ∧ ContinuousOn g (𝔹 ε) ∧
    (Ɐ (g x).im = 0) ∧
    Ɐ k ≤ (g x).re ∧ (g x).re ≤ K}

namespace IFS

variable (Φ : IFS N ε)

/-! ## Iterates of the dual operators on `I` -/

/-- On `I`, `F_w` applied to a constant `c` is affine in `c`. -/
theorem re_dualComp_const w (c : ℝ) (hx : x ∈ I) :
    (Φ.dualComp w (fun _ => c) x).re =
      (𝔡ᶜ Φ w.reverse x).re * c + (Φ.dualProj (.fin w) x).re := by
  rw [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos hx)]
  simp

section
variable (hkK : k ≤ K) (hmaps : ∀ i, MapsTo (Φ.dualOp i) (dualCylClosed ε k K) (dualCyl ε k K))
include hmaps

/-- `F_w` maps the closed cylinder into itself if every `F_i` does. -/
theorem dualComp_mem_dualCylClosed w (hh : h ∈ dualCylClosed ε k K) :
    Φ.dualComp w h ∈ dualCylClosed ε k K := by
  induction w with
  | nil => exact hh
  | cons i w ih =>
    obtain ⟨h1, hcl, h2, h3⟩ := hmaps i ih
    exact ⟨h1, hcl, h2, fun x hx => ⟨(h3 x hx).1.le, (h3 x hx).2.le⟩⟩

include hkK

/-- If every `F_i` maps `cl (k,K)` into `(k,K)`, then `H_u` takes values in `[k,K]` on `I`, as
the limit of `F_{u|m} k`. -/
theorem re_dualProj_mem_Icc u (hy : y ∈ I) :
    (Φ.dualProj (.inf u) y).re ∈ Icc k K := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  have hyn := ofReal_mem_nbhd Φ.ε_pos hy
  refine isClosed_Icc.mem_of_tendsto ((Complex.continuous_re.tendsto _).comp
    (tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_)
      (tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one (K := ‖k‖ + M)))))
    (Eventually.of_forall fun m => (Φ.dualComp_mem_dualCylClosed hmaps
      (List.ofFn fun i : Fin m => u i) ⟨differentiableOn_const _, continuousOn_const,
        fun _ _ => Complex.ofReal_im k, fun _ _ => ⟨le_rfl, hkK⟩⟩).2.2.2 y hy)
  have hcl := subset_closure hyn
  rw [Φ.dualComp_apply _ _ hyn, Word.inf_eq_prepend_ofFn u m, Φ.dualProj_prepend _ _ hcl,
    show ∀ a b c d, a * b + c - (c + a * d) = a * (b - d) from fun _ _ _ _ => by ring,
    norm_mul]
  exact (mul_le_mul (Φ.norm_deriv_comp_le _ hcl) (norm_sub_le_of_le le_rfl (hM _ _
    (Φ.mapsTo_comp_closure _ hcl))) (norm_nonneg _) (pow_nonneg Φ.cmax_nonneg _)).trans_eq
      (by simp)

/-- If every `F_i` maps `cl (k,K)` into `(k,K)`, then `H_u(x)` lies in the cylinder interval
`conv((F_w k)(x), (F_w K)(x))` of every prefix `w` of `u`. -/
theorem re_dualProj_mem_dualCylAt u (n : ℕ) (hx : x ∈ I) :
    (Φ.dualProj (.inf u) x).re ∈ Φ.dualCylAt k K (List.ofFn fun m : Fin n => u m) x := by
  have hxn := ofReal_mem_nbhd Φ.ε_pos hx
  rw [Word.inf_eq_prepend_ofFn u n, dualCylAt, Φ.re_dualComp_const _ _ hx,
    Φ.re_dualComp_const _ _ hx, Φ.dualProj_prepend _ _ (subset_closure hxn), Φ.comp_ofReal _ hx,
    Complex.add_re, Complex.mul_re, Φ.im_deriv_comp_ofReal _ hxn, mem_uIcc]
  obtain ⟨h1, h2⟩ := Φ.re_dualProj_mem_Icc hkK hmaps (fun m => u (m + n)) (Φ.re_comp_mem_I _ hx)
  rcases le_total 0 (𝔡ᶜ Φ (List.ofFn fun m => u m).reverse x).re with ha | ha
  · exact .inl ⟨by nlinarith, by nlinarith⟩
  · exact .inr ⟨by nlinarith, by nlinarith⟩

end

/-- Points of one cylinder interval of `Φ` at `x ∈ I` are `c_max^{|w|} (K - k)` close. -/
theorem abs_sub_le_cmax_pow_of_mem_dualCylAt (hkK : k ≤ K) w
    (hx : x ∈ I) (hp : p ∈ Φ.dualCylAt k K w x)
    (hq : q ∈ Φ.dualCylAt k K w x) : |p - q| ≤ Φ.cmax ^ w.length * (K - k) := by
  refine (abs_sub_le_of_uIcc_subset_uIcc (uIcc_subset_uIcc hq hp)).trans ?_
  rw [Φ.re_dualComp_const _ _ hx, Φ.re_dualComp_const _ _ hx, add_sub_add_right_eq_sub, ← mul_sub,
    abs_mul, abs_of_nonneg (sub_nonneg.2 hkK)]
  have := Φ.norm_deriv_comp_le w.reverse (Φ.ofReal_mem_cl hx)
  rw [List.length_reverse] at this
  exact mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm _).trans this) (sub_nonneg.2 hkK)

/-- `G_i` maps `cl (-K,K)` into `(-K,K)` when `|g_i'| ≤ c` and `|g_i''/g_i'| ≤ M` on `[0,1]` and
`c K + M < K`. -/
theorem mapsTo_dualOp_dualCylClosed
    (hc : ∀ i, Ɐ ‖𝔡 Φ i x‖ ≤ c) (hM : ∀ i, Ɐ ‖Φ.nonlin i x‖ ≤ M)
    (hK : c * K + M < K) i :
    MapsTo (Φ.dualOp i) (dualCylClosed ε (-K) K) (dualCyl ε (-K) K) := by
  rintro h ⟨hd, _, hre, hb⟩
  obtain ⟨U, -, hU, hnl⟩ := Φ.exists_differentiableOn_nonlin i
  refine ⟨((((Φ.differentiableOn_f i).deriv isOpen_nbhd).mono nbhd_subset_two).mul
    (hd.comp ((Φ.differentiableOn_f i).mono nbhd_subset_two) (Φ.mapsTo_f i))).add
      (hnl.mono (subset_closure.trans hU)), ((((Φ.differentiableOn_f i).deriv
          isOpen_nbhd).continuousOn.mono closure_nbhd_subset_two).mul (hd.continuousOn.comp
            ((Φ.differentiableOn_f i).continuousOn.mono closure_nbhd_subset_two)
              (Φ.inClass i).mapsTo)).add (hnl.continuousOn.mono hU), fun x hx => ?_,
        fun x hx => abs_lt.1 ((Complex.abs_re_le_norm _).trans_lt (lt_of_le_of_lt ?_ hK))⟩ <;>
    have hy : Φ.f i x = ((Φ.f i x).re : ℂ) := Φ.comp_ofReal [i] hx <;>
    have hI : (Φ.f i x).re ∈ I := Φ.re_comp_mem_I [i] hx <;>
    rw [dualOp, hy]
  · simp [Φ.im_deriv_f_ofReal i (Φ.ofReal_mem_nbhd2 hx), hre _ hI, Φ.im_nonlin_ofReal i (ofReal_mem_nbhd Φ.ε_pos hx)]
  · refine (norm_add_le _ _).trans (add_le_add ?_ (hM i x hx))
    rw [norm_mul, ← Complex.abs_re_eq_norm.2 (hre _ hI)]
    exact mul_le_mul (hc i x hx) (abs_le.2 (hb _ hI)) (abs_nonneg _)
      ((norm_nonneg _).trans (hc i x hx))

/-- Lemma 2.6: (a) the dual IFS satisfies the SSC if and only if (b) there are `k < K` and
`n ≥ 1` with `F_i cl (k,K) ⊆ (k,K)` for every `i` and `F_i(k,K) ∩ F_j(k,K) = ∅`, in the sense of
(2.2), for all `i, j ∈ Σ_n` with `i₁ ≠ j₁`; and if and only if (c) there is `δ > 0` with
`sup_{x ∈ [0,1]} |H_i(x) - H_j(x)| > δ` for all `i, j ∈ Σ` with `i₁ ≠ j₁`. -/
theorem lemma_2_6 :
    (Φ.DualSSC ↔ ∃ k K, k < K ∧ ∃ n,
      (∀ i, MapsTo (Φ.dualOp i) (dualCylClosed ε k K) (dualCyl ε k K)) ∧
      ∀ i j : Fin (n + 1) → Fin N, i 0 ≠ j 0 →
        Φ.DualCylDisjoint k K (List.ofFn i) (List.ofFn j)) ∧
    (Φ.DualSSC ↔ ∃ δ > 0, ∀ i j, i 0 ≠ j 0 →
      δ < ⨆ x : I, ‖Φ.dualProj (.inf i) x - Φ.dualProj (.inf j) x‖) := by
  refine ⟨⟨fun hssc => ?_, ?_⟩, Φ.dualSSC_iff_exists_delta⟩
  · -- (a) ⇒ (b): compactness of pairs of infinite words, as in the manuscript.
    obtain ⟨M, hM0, hM⟩ := Φ.exists_nonlin_bound
    have hc := Φ.cmax_lt_one
    obtain ⟨K, hK0, hK⟩ : ∃ K > 0, Φ.cmax * K + M < K := ⟨M / (1 - Φ.cmax) + 1,
      by positivity,
      by linarith [mul_div_cancel₀ M (sub_pos.2 hc).ne']⟩
    have hmaps := Φ.mapsTo_dualOp_dualCylClosed
      (fun i x hx => Φ.norm_deriv_le_cmax i (Φ.ofReal_mem_cl hx))
      (fun i x hx => hM i _ (Φ.ofReal_mem_cl hx)) hK
    refine ⟨-K, K, by linarith, ?_⟩
    by_contra hnone
    -- pairs of infinite words whose prefixes of length `n + 1` give intersecting cylinders
    have hbad : ∀ n, ∃ u v : 𝔖 N, u 0 ≠ v 0 ∧ ¬ Φ.DualCylDisjoint (-K) K
        (List.ofFn fun m : Fin (n + 1) => u m) (List.ofFn fun m : Fin (n + 1) => v m) := by
      intro n
      by_contra h
      push Not at h
      refine hnone ⟨n, hmaps, fun i j hij => ?_⟩
      simpa using h (fun m => if hm : m < n + 1 then i ⟨m, hm⟩ else i 0)
        (fun m => if hm : m < n + 1 then j ⟨m, hm⟩ else j 0) (by simp_all)
    choose u v huv hbad using hbad
    obtain ⟨w, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun n => (u n, v n)
    obtain ⟨x, hx, hne⟩ := hssc w.1 w.2
      (((isClosed_discrete {q : Fin N × Fin N | q.1 ≠ q.2}).preimage (by fun_prop :
        Continuous fun p : 𝔖 N × 𝔖 N => (p.1 0, p.2 0))).mem_of_tendsto hlim
          (Eventually.of_forall fun n => huv (φ n)))
    have hxn := ofReal_mem_nbhd Φ.ε_pos hx
    have hev : Continuous fun u => Φ.dualProj (.inf u) x :=
      Φ.continuous_dualProj_inf (subset_closure hxn)
    refine hne (sub_eq_zero.1 (norm_le_zero_iff.1 (le_of_tendsto_of_tendsto'
      ((((hev.comp continuous_fst).sub (hev.comp continuous_snd)).norm.tendsto w).comp hlim)
      (by simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg hc).comp
        ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)).mul_const (2 * (K - -K)))
      fun n => ?_)))
    obtain ⟨p, hpi, hpj⟩ := Set.not_disjoint_iff.1 fun hd => hbad (φ n) ⟨x, hx, hd⟩
    have e1 := Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ hx
      (Φ.re_dualProj_mem_dualCylAt (by linarith) hmaps (u (φ n)) _ hx) hpi
    have e2 := Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt (by linarith) _ hx hpj
      (Φ.re_dualProj_mem_dualCylAt (by linarith) hmaps (v (φ n)) _ hx)
    simp
    rw [← Complex.abs_re_eq_norm.2 (by simp [Φ.im_dualProj_ofReal _ hxn]), Complex.sub_re]
    grind
  · -- (b) ⇒ (a): `H_i` and `H_j` lie in disjoint cylinder intervals at some `x`
    rintro ⟨k, K, hkK, n, hmaps, hdisj⟩
    intro i j hij
    obtain ⟨x, hx, hd⟩ := hdisj (fun m => i m) (fun m => j m) (by simp_all)
    refine ⟨x, hx, fun heq => Set.disjoint_left.1 hd
      (Φ.re_dualProj_mem_dualCylAt hkK.le hmaps i _ hx) ?_⟩
    exact heq ▸ Φ.re_dualProj_mem_dualCylAt hkK.le hmaps j _ hx

end IFS

end AnalyticESC
