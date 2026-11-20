module

public import AnalyticESC.Basic
public import AnalyticESC.Words

@[expose] public section

/-!
# Separation conditions

The natural projection, its modulus of continuity, and the relation between
constant projections and common fixed points. Basic estimates for separation of compositions.
-/

namespace AnalyticESC

open Set Metric Filter Topology
open Word (pref shift)

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

private theorem zero_mem_I : (0 : ℝ) ∈ I := ⟨le_rfl, zero_le_one⟩

theorem abs_re_comp_sub_le_mul (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |Φ.reComp w x - Φ.reComp w y| ≤ Φ.cmax ^ w.length * |x - y| := by
  simpa [Φ.comp_ofReal w hx, Φ.comp_ofReal w hy, ← Complex.ofReal_sub, Real.norm_eq_abs] using
    Φ.norm_comp_sub_le w (Φ.real_mem_closed hx) (Φ.real_mem_closed hy)

theorem abs_re_comp_sub_le (w : List (Fin N)) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    |Φ.reComp w x - Φ.reComp w y| ≤ Φ.cmax ^ w.length :=
  (Φ.abs_re_comp_sub_le_mul w hx hy).trans (mul_le_of_le_one_right (pow_nonneg Φ.cmax_nonneg _) (by grind))

theorem tendsto_natProj (w : ℕ → Fin N) :
    Tendsto (fun n => Φ.reComp (pref w n) 0) atTop (𝓝 (Φ.natProj w)) := by
  unfold natProj Challenge.natProj
  apply tendsto_nhds_limUnder
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric Φ.cmax 1 Φ.cmax_lt_one ?_)
  intro n
  rw [Nat.add_comm, Word.pref_add, Φ.reComp_append _ _ zero_mem_I, Real.dist_eq, one_mul]
  simpa [pref, shift] using
    Φ.abs_re_comp_sub_le (pref w n) zero_mem_I (Φ.re_comp_mem_I [w n] zero_mem_I)

theorem attractor_subset_I : Φ.attractor ⊆ I := by
  rintro _ ⟨w, rfl⟩
  exact isClosed_Icc.mem_of_tendsto (Φ.tendsto_natProj w)
    (Eventually.of_forall fun n => by simpa using Φ.re_comp_mem_I _ zero_mem_I)

theorem natProj_mem_I (ω : ℕ → Fin N) : Φ.natProj ω ∈ I :=
  Φ.attractor_subset_I ⟨ω, rfl⟩

/-- `π(ω) = f_{ω₁ ⋯ ω_k}(π(σ^k ω))`, where `σ` is the left shift. -/
theorem natProj_eq_comp_prefix (ω : ℕ → Fin N) (k : ℕ) :
    Φ.natProj ω = Φ.reComp (pref ω k) (Φ.natProj (shift ω k)) := by
  refine tendsto_nhds_unique ((tendsto_add_atTop_iff_nat k).2 (Φ.tendsto_natProj ω)) ?_
  refine (((Φ.hasDerivAt_re_comp (pref ω k) (Φ.natProj_mem_I (shift ω k))).continuousAt).tendsto.comp (Φ.tendsto_natProj (shift ω k))).congr fun n => ?_
  rw [Function.comp_apply, Word.pref_add, Φ.reComp_append _ _ zero_mem_I]

/-- The projection intertwines the first letter and the left shift. -/
theorem natProj_eq_realMap (ω : ℕ → Fin N) :
    Φ.natProj ω = Φ.realMaps (ω 0) (Φ.natProj (shift ω 1)) :=
  Φ.natProj_eq_comp_prefix ω 1

theorem abs_natProj_sub_le_of_prefix {n : ℕ} {x y : ℕ → Fin N} (h : ∀ k < n, x k = y k) :
    |Φ.natProj x - Φ.natProj y| ≤ Φ.cmax ^ n := by
  have he : (pref x n) = pref y n := by simp_all
  rw [Φ.natProj_eq_comp_prefix x n, Φ.natProj_eq_comp_prefix y n, he]
  simpa using Φ.abs_re_comp_sub_le (List.ofFn fun j => y j) (Φ.natProj_mem_I _) (Φ.natProj_mem_I _)

/-- The natural projection is continuous by its modulus on cylinders. -/
theorem continuous_natProj : Continuous Φ.natProj := continuous_iff_continuousAt.2 fun w => by
  refine Metric.tendsto_nhds.2 fun r hr => ?_
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg
    Φ.cmax_lt_one).eventually (gt_mem_nhds hr)).exists
  filter_upwards [eventually_all.2 fun k : Fin n => Word.eventually_eq_letter tendsto_id k] with v hv
  exact ((Φ.abs_natProj_sub_le_of_prefix (fun k hk => hv ⟨k, hk⟩)).trans_lt hn : |Φ.natProj v - Φ.natProj w| < r)

/-- The attractor is compact. -/
theorem isCompact_attractor : IsCompact Φ.attractor := isCompact_range Φ.continuous_natProj

/-- The attractor is nonempty. -/
theorem attractor_nonempty (hN : 0 < N) : Φ.attractor.Nonempty :=
  ⟨_, mem_range_self (fun _ => (⟨0, hN⟩ : Fin N))⟩

theorem natProj_const_fixed (i : Fin N) :
    Φ.realMaps i (Φ.natProj fun _ => i) = Φ.natProj fun _ => i :=
  (Φ.natProj_eq_realMap fun _ => i).symm

/-- A singleton attractor is equivalent to a common fixed point of the interval maps. -/
theorem attractor_eq_singleton_iff (hN : 0 < N) {x : ℝ} :
    Φ.attractor = {x} ↔ x ∈ I ∧ ∀ i, Φ.realMaps i x = x := by
  constructor
  · intro h
    refine ⟨Φ.attractor_subset_I (h ▸ mem_singleton x), fun i => ?_⟩
    simpa only [Function.apply_eq_of_range_eq_singleton h (fun _ => i)] using Φ.natProj_const_fixed i
  · rintro ⟨hx, hf⟩
    have : Nonempty (ℕ → Fin N) := ⟨fun _ => ⟨0, hN⟩⟩
    apply range_eq_singleton
    have hc (w : List (Fin N)) : Φ.reComp w x = x := by
      induction w with
      | nil => rfl
      | cons i w ih => rw [show i :: w = [i] ++ w from rfl, Φ.reComp_append _ _ hx, ih, reComp_singleton, hf]
    intro w
    exact dist_eq_zero.1 ((ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one Φ.cmax_nonneg Φ.cmax_lt_one)
      (fun n => by
        simpa only [← Φ.natProj_eq_comp_prefix, hc, List.length_ofFn, Real.dist_eq] using
          Φ.abs_re_comp_sub_le (pref w n) (Φ.natProj_mem_I (shift w n)) hx)).antisymm dist_nonneg)

theorem exists_attractor_eq_singleton_iff (hN : 0 < N) :
    (∃ x, Φ.attractor = {x}) ↔ ∃ x ∈ I, ∀ i, Φ.realMaps i x = x :=
  exists_congr fun _ => Φ.attractor_eq_singleton_iff hN

theorem norm_le_supDist (i j : List (Fin N)) {x : ℝ} (hx : x ∈ I) :
    ‖Φ.comp i x - Φ.comp j x‖ ≤ Φ.supDist i j := by
  obtain ⟨M, -, hM⟩ := Φ.exists_comp_bound
  refine le_ciSup (f := fun t : I => ‖Φ.comp i (t : ℝ) - Φ.comp j (t : ℝ)‖)
    ⟨2 * M, forall_mem_range.2 fun t => ?_⟩ ⟨x, hx⟩
  have ht := Φ.real_mem_closed t.2
  simp_all [sub_le_twice]

theorem esc_of_sesc (h : Φ.SESC) : Φ.ESC := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, Frequently.of_forall h⟩

end IFS

end AnalyticESC
