module

public import AnalyticESC.Dual.Attractor
public import AnalyticESC.Separation

public section

set_option hygiene false
local notation "𝖄" => x p
local notation "𝖍" => Fin n → Fin N

/-!
# Lemma 4.1

For a system whose compositions along distinct finite words differ on `[0,1]`, a choice of
points `x_{i,j}`, `(i, j) ∈ ℬ_n`, at which the cylinders of pairs that are not bad are disjoint,
with orbits that are injective, meet only at the base point, and are disjoint for different
pairs. Systems without exact overlaps satisfy the hypothesis.

The points are chosen one pair at a time, by induction over finite sets of pairs. At each step
the admissible points form an infinite subset of `I` (all of `I` for a bad pair, a relative
neighbourhood of a point of disjointness otherwise), and the excluded points are finite: by the
identity theorem two distinct compositions agree at finitely many points of `I`, and each
composition is injective on `I`.
-/

namespace AnalyticESC

open Set Filter Topology

namespace IFS

variable (Φ : IFS N ε)

/-! ## Compositions on `I` -/

/-- Two compositions along distinct words agree at finitely many points of `I`. -/
theorem finite_eq_comp (h : Φ.NoCoincidence) (hvw : v ≠ w) :
    {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = (Φ.comp w t).re}.Finite := by
  obtain ⟨x, hx, hne⟩ := h v w hvw
  exact (finite_zeros Φ.ε_pos ((Φ.differentiableOn_comp v).sub (Φ.differentiableOn_comp w))
    ⟨x, hx, sub_ne_zero.2 hne⟩).subset fun t ⟨ht, heq⟩ => ⟨ht, sub_eq_zero.2 (by
      rw [Φ.comp_ofReal v ht, Φ.comp_ofReal w ht, heq])⟩

/-- The exceptional points of `I`: two distinct compositions of length at most `n` agree there,
or one of them takes a value in the finite set `F`. -/
theorem finite_exceptional (h : Φ.NoCoincidence) n {F : Set ℝ}
    (hF : F.Finite) :
    {t : ℝ | t ∈ I ∧ ((∃ v w, v.length ≤ n ∧ w.length ≤ n ∧ v ≠ w ∧
      (Φ.comp v t).re = (Φ.comp w t).re) ∨
      ∃ v, v.length ≤ n ∧ (Φ.comp v t).re ∈ F)}.Finite := by
  have hW := List.finite_length_le (Fin N) n
  refine ((hW.biUnion fun v _ => hW.biUnion fun w _ =>
      Set.finite_iUnion fun hvw : v ≠ w => Φ.finite_eq_comp h hvw).union
    (hW.biUnion fun v _ => hF.biUnion fun y _ => Set.Subsingleton.finite (s := {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = y}) fun _ ha _ hb =>
      Φ.injOn_re_comp v ha.1 hb.1 (ha.2.trans hb.2.symm))).subset ?_
  rintro t ⟨ht, ⟨v, w, hv, hw, hvw, heq⟩ | ⟨v, hv, hvF⟩⟩
  · aesop
  · aesop

/-! ## Disjointness of the cylinders near a point -/

/-- The points of `I` at which the cylinders are disjoint, if they are disjoint at some point,
form an infinite set. -/
theorem infinite_good k K a b :
    {t : ℝ | t ∈ I ∧ (Φ.DualCylDisjoint k K a b →
      Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t))}.Infinite := by
  by_cases hd : Φ.DualCylDisjoint k K a b
  · obtain ⟨x, hx, hdx⟩ := hd
    -- the endpoints `(F_w c)(t)` of the cylinders depend continuously on `t ∈ I`
    have hc : ∀ (w : 𝔚 N) c,
        Tendsto (fun t : ℝ => (Φ.dualComp w (fun _ => c) t).re) (𝓝[I] x)
          (𝓝 (Φ.dualComp w (fun _ => c) x).re) := fun w c =>
      (Complex.continuous_re.comp_continuousOn ((((((Φ.differentiableOn_comp w.reverse).deriv
        isOpen_nbhd).continuousOn).mul (continuousOn_const (c := c))).add
          (Φ.differentiableOn_dualProj (.fin w)).continuousOn).comp
            Complex.continuous_ofReal.continuousOn fun t ht => ofReal_mem_nbhd Φ.ε_pos ht)).congr
        (fun t ht => by simp [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos ht)]) x hx
    simp only [dualCylAt, uIcc, disjoint_iff_inter_eq_empty, Icc_inter_Icc, Icc_eq_empty_iff,
      not_le] at hdx ⊢
    exact (((infinite_of_mem_nhds (⟨x, hx⟩ : I) (preimage_coe_mem_nhds_subtype.2
      ((((hc a k).max (hc a K)).min ((hc b k).max (hc b K))).eventually_lt
        (((hc a k).min (hc a K)).max ((hc b k).min (hc b K))) hdx))).image
          Subtype.val_injective.injOn)).mono (by simp_all)
  · exact (Set.Icc_infinite zero_lt_one).mono fun t ht => ⟨ht, fun h' => absurd h' hd⟩

/-! ## Lemma 4.1 -/

/-- Lemma 4.1, by induction over finite sets `S` of pairs: points `x_p ∈ I` at which the
cylinders of pairs that are not bad are disjoint, such that the points `f_v(x_p)`, `|v| ≤ n`,
are distinct for distinct `(p, v)`. -/
theorem lemma_4_1 (h : Φ.NoCoincidence) k K n
    (S : Finset (𝖍 × 𝖍)) :
    ∃ x : 𝖍 × 𝖍 → ℝ, ∀ p ∈ S, x p ∈ I ∧
      (Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
        Disjoint (Φ.dualCylAt k K (List.ofFn p.1) 𝖄) (Φ.dualCylAt k K (List.ofFn p.2) 𝖄)) ∧
      ∀ q ∈ S, ∀ v w, v.length ≤ n → w.length ≤ n → (p, v) ≠ (q, w) →
        (Φ.comp v 𝖄).re ≠ (Φ.comp w (x q)).re := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨t, ⟨ht, hdisj⟩, hex⟩ := ((Φ.infinite_good k K (List.ofFn a.1) (List.ofFn a.2)).sdiff
      (Φ.finite_exceptional h n ((S.finite_toSet.prod (List.finite_length_le _ n)).image
        fun qw => (Φ.comp qw.2 (x qw.1)).re))).nonempty
    have hu : ∀ q ∈ S, Function.update x a t q = x q := fun q hq =>
      Function.update_of_ne (ne_of_mem_of_not_mem hq ha) _ _
    have key : ∀ q ∈ S, ∀ v w, v.length ≤ n → w.length ≤ n →
        (Φ.comp v t).re ≠ (Φ.comp w (x q)).re := fun q hq v w hv hw he =>
      hex ⟨ht, Or.inr ⟨v, hv, (q, w), ⟨hq, hw⟩, he.symm⟩⟩
    refine ⟨Function.update x a t, fun p hp => ?_⟩
    rcases Finset.mem_insert.1 hp with rfl | hpS
    · grind
    · grind

end IFS

end AnalyticESC
