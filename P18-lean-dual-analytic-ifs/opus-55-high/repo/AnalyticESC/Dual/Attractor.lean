module

public import AnalyticESC.Dual.Projection
public import AnalyticESC.Analysis

public section

/-!
# The dual IFS and the strong separation of the dual

Iterates of the dual operators, continuity of the coding map, the strong separation of the dual
in terms of a uniform gap (Lemma 2.6, (a) ⇔ (c)), and the incompatibility of dual strong
separation with an exact coincidence `f_a = f_b`.
-/

namespace AnalyticESC

variable {z : ℂ}

open Set Filter Topology

/-- Words agreeing with `w` on the first `m` letters form a neighbourhood of `w`. -/
theorem eventually_forall_lt_eq (w : 𝔖 N) m :
    ∀ᶠ v in 𝓝 w, ∀ k < m, v k = w k := by
  have : ∀ k, ∀ᶠ v in 𝓝 w, v k = w k := by
    intro k
    have h := (continuous_apply k).continuousAt (x := w)
    rw [ContinuousAt, nhds_discrete (Fin N)] at h
    simp_all
  simpa only [← Finset.mem_range, Filter.eventually_all_finset] using fun k _ => this k

/-- `c_max^n K → 0`. -/
theorem tendsto_pow_mul_nhds_zero {c K : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun n => c ^ n * K) atTop (𝓝 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const K

namespace Word


theorem prepend_inf a (w : 𝔖 N) :
    (inf w).prepend a = inf fun n => if h : n < a.length then a[n] else w (n - a.length) := rfl

/-- An infinite word is its prefix of length `n` followed by its `n`-fold shift. -/
theorem inf_eq_prepend_ofFn (w : 𝔖 N) n :
    inf w = (inf fun k => w (k + n)).prepend (List.ofFn fun k : Fin n => w k) := by
  rw [prepend_inf]
  aesop

end Word

namespace IFS

variable (Φ : IFS N ε)

/-- `F_w h = f_{w^←}' · (h ∘ f_{w^←}) + H_w` on `B_ε` (Section 2.1). -/
theorem dualComp_apply w (h : ℂ → ℂ) (hz : z ∈ nbhd ε) :
    Φ.dualComp w h z =
      𝔡ᶜ Φ w.reverse z * h (Φ.comp w.reverse z) + Φ.dualProj (.fin w) z := by
  induction w generalizing z with
  | nil => simp [dualComp]
  | cons i w ih =>
    have hcl := subset_closure hz
    rw [show Word.fin (i :: w) = (Word.fin w).prepend [i] from rfl, Φ.dualProj_prepend _ _ hcl]
    simp only [dualComp, List.foldr_cons, Function.comp_apply, dualOp] at ih ⊢
    rw [ih (Φ.mapsTo_f i hz), List.reverse_cons, Φ.deriv_comp_append _ _ hcl, Φ.comp_append,
      dualProj_singleton]
    simp
    ring

/-- The coding map `w ↦ H_w(z)` is continuous on `Σ`. -/
theorem continuous_dualProj_inf (hz : z ∈ 𝔹 ε) :
    Continuous fun w => Φ.dualProj (.inf w) z := by
  obtain ⟨M, hMd⟩ := Φ.exists_dualProj_bounds
  refine continuous_iff_continuousAt.2 fun w => Metric.tendsto_nhds.2 fun δ hδ => ?_
  obtain ⟨m, hm⟩ := ((tendsto_pow_mul_nhds_zero Φ.cmax_nonneg Φ.cmax_lt_one
    (K := 2 * M)).eventually (gt_mem_nhds hδ)).exists
  filter_upwards [eventually_forall_lt_eq w m] with v hv
  rw [dist_eq_norm]
  linarith [hMd (.inf v) (.inf w) m (Word.le_commonPrefixLength_iff.2 fun k hk => by simp_all) z hz]

/-- Lemma 2.6, (a) ⇔ (c): compactness turns pointwise separation of first-letter branches into
a uniform gap. -/
theorem dualSSC_iff_exists_delta :
    Φ.DualSSC ↔ ∃ δ > 0, ∀ i j, i 0 ≠ j 0 →
      δ < ⨆ x : I, ‖Φ.dualProj (.inf i) x - Φ.dualProj (.inf j) x‖ := by
  obtain ⟨M, -, hM⟩ := Φ.exists_norm_dualProj_le
  have hx : ∀ x : I, (x : ℂ) ∈ 𝔹 ε := fun x =>
    Φ.ofReal_mem_cl x.2
  have hbdd : ∀ p : 𝔖 N × 𝔖 N, BddAbove (range fun x : I =>
      ‖Φ.dualProj (.inf p.1) x - Φ.dualProj (.inf p.2) x‖) := fun p =>
    ⟨M + M, by rintro _ ⟨x, rfl⟩; exact norm_sub_le_of_le (hM _ _ (hx x)) (hM _ _ (hx x))⟩
  constructor
  · intro h
    let S : Set (𝔖 N × 𝔖 N) := {p | p.1 0 ≠ p.2 0}
    rcases S.eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, fun i j hij => (hE.subset (show (i, j) ∈ S from hij)).elim⟩
    obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne
      ((isClosed_discrete {q : Fin N × Fin N | q.1 ≠ q.2}).preimage (by fun_prop :
        Continuous fun p : 𝔖 N × 𝔖 N => (p.1 0, p.2 0))).isCompact
      ((lowerSemicontinuous_ciSup hbdd fun x => (((Φ.continuous_dualProj_inf (hx x)).comp
        continuous_fst).sub ((Φ.continuous_dualProj_inf (hx x)).comp
          continuous_snd)).norm.lowerSemicontinuous).lowerSemicontinuousOn _)
    obtain ⟨x, hxI, hne⟩ := h p.1 p.2 hp
    have := (norm_pos_iff.2 (sub_ne_zero.2 hne)).trans_le (le_ciSup (hbdd p) ⟨x, hxI⟩)
    exact ⟨_, half_pos this, fun i j hij =>
      (half_lt_self this).trans_le (isMinOn_iff.1 hmin (i, j) hij)⟩
  · rintro ⟨δ, hδ, h⟩ i j hij
    by_contra! hcon
    have := h i j hij
    simp [fun x : I => hcon x x.2] at this
    linarith

/-- An exact coincidence `f_a = f_b` on `I`, for words of equal length with different last
letters, contradicts the strong separation of the dual. -/
theorem not_dualSSC_of_comp_eq (hlen : a.length = b.length)
    (hlast : a.getLast? ≠ b.getLast?) (h : Ɐ Φ.comp a x = Φ.comp b x) : ¬ Φ.DualSSC := by
  intro hs
  have hEq : EqOn (Φ.comp a) (Φ.comp b) (nbhd ε) :=
    eqOn_nbhd_of_eqOn_Icc Φ.ε_pos (Φ.differentiableOn_comp a) (Φ.differentiableOn_comp b)
      zero_lt_one subset_rfl h
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', x, rfl⟩
  · grind
  rcases List.eq_nil_or_concat' b with rfl | ⟨b', y, rfl⟩
  · grind
  have hxy : x ≠ y := fun hxy => hlast (by simp_all)
  obtain ⟨t, ht, hne⟩ := hs (fun n => if h : n < (a' ++ [x]).reverse.length then
    (a' ++ [x]).reverse[n] else x) (fun n => if h : n < (b' ++ [y]).reverse.length then
      (b' ++ [y]).reverse[n] else x) (by simp_all)
  have htz := ofReal_mem_nbhd Φ.ε_pos ht
  have hEv : Φ.comp (a' ++ [x]) =ᶠ[𝓝 (t : ℂ)] Φ.comp (b' ++ [y]) :=
    Filter.eventuallyEq_of_mem (isOpen_nbhd.mem_nhds htz) hEq
  apply hne
  rw [← Word.prepend_inf _ fun _ => x, ← Word.prepend_inf _ fun _ => x,
    Φ.dualProj_prepend _ _ (subset_closure htz), Φ.dualProj_prepend _ _ (subset_closure htz)]
  simp only [List.reverse_reverse]
  rw [Φ.dualProj_fin_reverse _ (subset_closure htz), Φ.dualProj_fin_reverse _ (subset_closure htz),
    hEv.deriv_eq, hEv.deriv.deriv_eq, hEq htz]

end IFS

end AnalyticESC
