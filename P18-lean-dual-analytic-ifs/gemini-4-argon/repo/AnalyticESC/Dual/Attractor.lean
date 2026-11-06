module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis

@[expose] public section

/-!
# The dual IFS and strong separation

Iterates of the dual operators, the strong separation of the dual in terms of the dual natural
projection (Lemma 2.6, (a) ⇔ (c)), and the incompatibility of dual strong separation with an
exact coincidence `f_a = f_b`.
-/

namespace AnalyticESC

open Set Metric Filter Topology

/-- Words agreeing with `w` on the first `m` letters form a neighbourhood of `w`. -/
private theorem eventually_forall_lt_eq {N : ℕ} (w : ℕ → Fin N) (m : ℕ) :
    ∀ᶠ v in 𝓝 w, ∀ k < m, v k = w k := by
  have (k : ℕ) : ∀ᶠ v in 𝓝 w, v k = w k := by
    have h := (continuous_apply k).continuousAt (x := w)
    rw [ContinuousAt, nhds_discrete (Fin N)] at h
    exact tendsto_pure.1 h
  simpa only [← Finset.mem_range, Filter.eventually_all_finset] using fun k _ => this k

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-- `F_w h = f_{w^←}' · (h ∘ f_{w^←}) + H_w` on `B_ε` (Section 2.1). -/
theorem dualComp_apply (w : List (Fin N)) (h : ℂ → ℂ) {z : ℂ} (hz : z ∈ nbhd ε) :
    Φ.dualComp w h z =
      deriv (Φ.comp w.reverse) z * h (Φ.comp w.reverse z) + Φ.dualProj (.fin w) z := by
  induction w generalizing z with
  | nil => simp [dualComp, dualProj, dualTerm]
  | cons i w ih =>
    have hcl : z ∈ closure (nbhd ε) := subset_closure hz
    show Φ.dualOp i (Φ.dualComp w h) z =
      deriv (Φ.comp (i :: w).reverse) z * h (Φ.comp (i :: w).reverse z) +
        Φ.dualProj ((Word.fin w).prepend [i]) z
    rw [dualOp, ih (Φ.mapsTo_f i hz), List.reverse_cons, Φ.deriv_comp_append _ _ hcl,
      Φ.comp_append, Φ.dualProj_prepend [i] _ hcl, List.reverse_singleton,
      show Φ.comp [i] = Φ.f i by simp, Φ.dualProj_singleton i z, Function.comp_apply]
    ring

/-- Compactness turns pointwise separation of first-letter branches into a uniform gap. -/
theorem exists_delta_of_dualSSC (h : Φ.DualSSC) :
    ∃ δ > 0, ∀ i j : ℕ → Fin N, i 0 ≠ j 0 →
      ∃ x ∈ I, δ < ‖Φ.dualProj (.inf i) x - Φ.dualProj (.inf j) x‖ := by
  by_contra! hcon
  choose i j hij hle using fun n : ℕ => hcon (n + 1 : ℝ)⁻¹ (by positivity)
  obtain ⟨⟨i₀, j₀⟩, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq fun n => (i n, j n)
  have hi : Tendsto (i ∘ φ) atTop (𝓝 i₀) := (continuous_fst.tendsto _).comp hlim
  have hj : Tendsto (j ∘ φ) atTop (𝓝 j₀) := (continuous_snd.tendsto _).comp hlim
  obtain ⟨n₀, hi0, hj0⟩ := ((hi.eventually (eventually_forall_lt_eq i₀ 1)).and
    (hj.eventually (eventually_forall_lt_eq j₀ 1))).exists
  obtain ⟨x, hx, hne⟩ := h i₀ j₀ (hi0 0 one_pos ▸ hj0 0 one_pos ▸ hij (φ n₀))
  obtain ⟨M, -, -, hMd⟩ := Φ.exists_dualProj_bounds
  have hcl : (x : ℂ) ∈ closure (nbhd ε) := subset_closure (ofReal_mem_nbhd Φ.ε_pos hx)
  have htend {u : ℕ → ℕ → Fin N} {u₀ : ℕ → Fin N} (hu : Tendsto u atTop (𝓝 u₀)) :
      Tendsto (fun n => Φ.dualProj (.inf (u n)) x) atTop (𝓝 (Φ.dualProj (.inf u₀) x)) :=
    Metric.tendsto_nhds.2 fun η hη => by
      obtain ⟨m, hm⟩ := (((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
        Φ.cmax_lt_one).const_mul (2 * M)).eventually (gt_mem_nhds (by simpa using hη))).exists
      filter_upwards [hu.eventually (eventually_forall_lt_eq u₀ m)] with n hn
      exact (dist_eq_norm _ _).trans_lt ((hMd _ _ m
        (Word.le_commonPrefixLength_iff.2 fun k hk => by simp [hn k hk]) _ hcl).trans_lt hm)
  exact sub_ne_zero.2 hne (norm_le_zero_iff.1 (le_of_tendsto_of_tendsto
    ((htend hi).sub (htend hj)).norm
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)))
    (Eventually.of_forall fun n => hle (φ n) x hx)))

/-- An exact coincidence `f_a = f_b` on `I`, for words of equal length with different last
letters, contradicts the strong separation of the dual. -/
theorem not_dualSSC_of_comp_eq {a b : List (Fin N)} (hlen : a.length = b.length)
    (hlast : a.getLast? ≠ b.getLast?) (h : ∀ x ∈ I, Φ.comp a x = Φ.comp b x) : ¬ Φ.DualSSC := by
  intro hssc
  have hEq : EqOn (Φ.comp a) (Φ.comp b) (nbhd ε) :=
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b)
      zero_lt_one subset_rfl h
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', i₀, rfl⟩
  · exact hlast (by rw [List.length_eq_zero_iff.1 hlen.symm])
  rcases List.eq_nil_or_concat' b with rfl | ⟨b', j₀, rfl⟩
  · simp at hlen
  let ext (v : List (Fin N)) (n : ℕ) : Fin N :=
    if hn : n < v.length then v[n] else i₀
  obtain ⟨x, hx, hne⟩ := hssc (ext (a' ++ [i₀]).reverse) (ext (b' ++ [j₀]).reverse)
    fun hxy => hlast (by simpa [ext] using hxy)
  have hxn := ofReal_mem_nbhd Φ.ε_pos hx
  have hcl := subset_closure hxn
  have hEv : Φ.comp (a' ++ [i₀]) =ᶠ[𝓝 (x : ℂ)] Φ.comp (b' ++ [j₀]) :=
    Filter.eventuallyEq_of_mem ((isOpen_nbhd ε).mem_nhds hxn) hEq
  refine hne ?_
  change Φ.dualProj ((Word.inf fun _ => i₀).prepend (a' ++ [i₀]).reverse) x =
    Φ.dualProj ((Word.inf fun _ => i₀).prepend (b' ++ [j₀]).reverse) x
  rw [Φ.dualProj_prepend _ _ hcl, Φ.dualProj_prepend _ _ hcl, List.reverse_reverse,
    List.reverse_reverse, Φ.dualProj_fin_reverse _ hxn, Φ.dualProj_fin_reverse _ hxn,
    hEv.deriv_eq, hEv.deriv.deriv_eq, hEq hxn]

end IFS

end AnalyticESC
