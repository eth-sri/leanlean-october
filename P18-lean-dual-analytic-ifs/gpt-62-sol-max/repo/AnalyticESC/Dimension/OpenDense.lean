module

public import AnalyticESC.Dimension.Rapaport
public import AnalyticESC.Generic.OpenDense
public import AnalyticESC.Conjugation.Linearisation

@[expose] public section

/-!
# Corollary 1.7

The systems of `𝔖_N` with equality in (1.6) contain a `d₂`-open and `d₂`-dense subset of `𝔖_N`, for
`N ≥ 2`. The open set is the open set of Theorem 1.4 intersected with the systems whose attractor
is not a singleton, which is open and dense for `N ≥ 2`; Theorem 1.6 applies to its systems.
-/

namespace AnalyticESC

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal

namespace System

variable {N : ℕ}

def nondegenerate (N : ℕ) : Set (System N) :=
  {F | ¬ ∃ x ∈ I, ∀ i, (F.val i x).re = x}

private theorem isOpen_nondegenerate : IsOpen (nondegenerate N) := by
  have h (i : Fin N) : IsOpen {p : System N × I | (p.1.val i p.2).re ≠ p.2.val} :=
    (isClosed_eq (Complex.continuous_re.comp (continuous_jet_eval i 0)) (by fun_prop)).isOpen_compl
  convert isOpen_forall_compact (isOpen_iUnion h) using 1
  ext F
  simp [nondegenerate]

/-- If the maps have a common fixed point, move one map toward a different interior point. -/
private theorem dense_nondegenerate (hN : 2 ≤ N) : Dense (nondegenerate N) := Metric.dense_iff.2 fun F r hr => by
  let Φ := F.ifs
  let f := Φ.f
  by_cases hfix : ∃ x ∈ I, ∀ i, (f i x).re = x
  swap
  · exact ⟨F, mem_ball_self hr, hfix⟩
  obtain ⟨p, hp, hfp⟩ := hfix
  obtain ⟨q, hq, hqp⟩ := (Ioo_infinite (zero_lt_one (α := ℝ))).exists_notMem_finite (finite_singleton p)
  let j : Fin N := ⟨0, by omega⟩
  let k : Fin N := ⟨1, by omega⟩
  have hk : k ≠ j := by grind
  let _ : Nonempty (Fin N) := ⟨j⟩
  obtain ⟨t, ht, hd⟩ := Φ.exists_small_inward q hr
  let g := Function.update f j (inward (f j) q t)
  let G : System N := ⟨g, _, Φ.ε_pos,
    (Function.forall_update_iff _ _).2 ⟨(Φ.inClass j).inward Φ.ε_pos hq ht, fun i _ => Φ.inClass i⟩⟩
  refine ⟨G, ?_, ?_⟩
  · rw [mem_ball, dist_eq_d2, d2Sys_eq]
    exact Finite.ciSup_lt_iff.2 ((Function.forall_update_iff f (fun i u => d2Map (f i) u < r)).2
      ⟨hd j, fun i _ => by simpa [d2Map, jetDist] using hr⟩)
  · change ¬ ∃ x ∈ I, ∀ i, (g i x).re = x
    rintro ⟨x, hx, hgx⟩
    have hxk : (f k x).re = x := by simpa [g, Function.update_of_ne hk] using hgx k
    obtain rfl : x = p := by
      by_contra! hne
      have h := Φ.abs_re_comp_sub_le_mul [k] hx hp
      simp only [List.length_singleton, pow_one] at h
      change |(f k x).re - (f k p).re| ≤ _ at h
      rw [hxk, hfp k] at h
      exact h.not_gt (mul_lt_of_lt_one_left (abs_pos.2 (sub_ne_zero.2 hne)) Φ.cmax_lt_one)
    have h := hgx j
    simp only [g, Function.update_self, re_inward, hfp] at h
    grind

end System

/-- Corollary 1.7. The dimension equality is generic when there are at least two maps. -/
theorem _root_.Challenge.audit_dim_open_dense {N : ℕ} (hM : RapaportMeasureStatement) (hS : RapaportSetStatement)
    (hN : 2 ≤ N) : Generic[N, Challenge.DimEquality] := by
  apply generic_of_open_dense ((System.isOpen_separated N).inter System.isOpen_nondegenerate)
    ((System.dense_separated N).inter_of_isOpen_right (System.dense_nondegenerate hN) System.isOpen_nondegenerate)
  rintro F ⟨hsep, hnd⟩
  exact F.ifs.theorem_1_6 hM hS (by omega)
    (fun h => hnd ((F.ifs.exists_attractor_eq_singleton_iff (by omega)).1 h))
    (F.ifs.esc_of_sesc (F.ifs.theorem_2_2 hsep))

end AnalyticESC
