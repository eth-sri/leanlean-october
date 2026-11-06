module

public import AnalyticESC.Dual.Attractor
public import AnalyticESC.Separation

@[expose] public section

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

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε : ℝ} (Φ : IFS N ε)

/-! ## Compositions on `I` -/

/-- Two compositions along distinct words agree at finitely many points of `I`. -/
private theorem finite_eq_comp (h : Φ.NoCoincidence) {v w : List (Fin N)} (hvw : v ≠ w) :
    {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = (Φ.comp w t).re}.Finite := by
  obtain ⟨x, hx, hne⟩ := h v w hvw
  refine (finite_zeros Φ.ε_pos ((Φ.differentiableOn_comp v).sub (Φ.differentiableOn_comp w))
    ⟨x, hx, sub_ne_zero.2 hne⟩).subset fun t ⟨ht, heq⟩ => ⟨ht, ?_⟩
  show Φ.comp v t - Φ.comp w t = 0
  rw [Φ.comp_ofReal v ht, Φ.comp_ofReal w ht, heq, sub_self]

/-- The exceptional points of `I`: a nonempty composition of length at most `n` fixes `t` or
takes a value in the finite set `F`. -/
private theorem finite_exceptional (h : Φ.NoCoincidence) (n : ℕ) {F : Set ℝ}
    (hF : F.Finite) :
    {t : ℝ | t ∈ I ∧ ∃ v : List (Fin N), v.length ≤ n ∧
      ((v ≠ [] ∧ (Φ.comp v t).re = t) ∨ (Φ.comp v t).re ∈ F)}.Finite := by
  refine ((List.finite_length_le (Fin N) n).biUnion fun v _ =>
    (Set.finite_iUnion fun hv : v ≠ [] => Φ.finite_eq_comp h hv).union
      (hF.biUnion fun y _ => Set.Subsingleton.finite (s := {t : ℝ | t ∈ I ∧ (Φ.comp v t).re = y})
        fun _ ha _ hb => Φ.injOn_re_comp v ha.1 hb.1 (ha.2.trans hb.2.symm))).subset ?_
  rintro t ⟨ht, v, hv, ⟨hne, hfix⟩ | hvF⟩
  · exact mem_biUnion hv (Or.inl (mem_iUnion_of_mem hne ⟨ht, by simpa using hfix⟩))
  · exact mem_biUnion hv (Or.inr (mem_biUnion hvF ⟨ht, rfl⟩))

/-! ## Disjointness of the cylinders near a point -/

private theorem disjoint_uIcc_iff {a b c d : ℝ} :
    Disjoint (uIcc a b) (uIcc c d) ↔ max a b < min c d ∨ max c d < min a b := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hcon
    exact Set.disjoint_left.1 h ⟨le_max_left _ _, max_le min_le_max hcon.1⟩
      ⟨le_max_right _ _, max_le hcon.2 min_le_max⟩
  · rintro (h | h) <;> exact Set.disjoint_left.2 fun x hx hx' =>
      by linarith [hx.1, hx.2, hx'.1, hx'.2]

/-- The endpoints `(F_w c)(t)` of the cylinders depend continuously on `t ∈ I`. -/
private theorem continuousOn_dualComp_const (w : List (Fin N)) (c : ℝ) :
    ContinuousOn (fun t : ℝ => (Φ.dualComp w (fun _ => (c : ℂ)) t).re) I := by
  have hg : ContinuousOn (fun z => deriv (Φ.comp w.reverse) z * c + Φ.dualProj (.fin w) z) (nbhd ε) :=
    ((((Φ.differentiableOn_comp w.reverse).deriv (isOpen_nbhd ε)).continuousOn).mul
      continuousOn_const).add (Φ.differentiableOn_dualProj (.fin w)).continuousOn
  refine (Complex.continuous_re.comp_continuousOn
    (hg.comp Complex.continuous_ofReal.continuousOn fun _ ht => ofReal_mem_nbhd Φ.ε_pos ht)).congr
    fun t ht => by simp [Φ.dualComp_apply w _ (ofReal_mem_nbhd Φ.ε_pos ht)]

/-- A relative neighbourhood in `I` of a point of `I` is infinite. -/
private theorem infinite_of_mem_nhdsWithin_I {S : Set ℝ} {x : ℝ} (hx : x ∈ I)
    (hS : S ∈ 𝓝[I] x) : (S ∩ I).Infinite := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hS
  have hlt : max (x - r / 2) 0 < min (x + r / 2) 1 := by
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨by linarith, by linarith [hx.2]⟩, by linarith [hx.1], zero_lt_one⟩
  refine (Set.Icc_infinite hlt).mono fun t ht => ?_
  have h1 : t ∈ I := ⟨(le_max_right _ _).trans ht.1, ht.2.trans (min_le_right _ _)⟩
  exact ⟨hsub ⟨by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;>
    linarith [(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)], h1⟩, h1⟩

/-- The points of `I` at which the cylinders are disjoint, if they are disjoint at some point,
form an infinite set. -/
private theorem infinite_good (k K : ℝ) (a b : List (Fin N)) :
    {t : ℝ | t ∈ I ∧ (Φ.DualCylDisjoint k K a b →
      Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t))}.Infinite := by
  by_cases hd : Φ.DualCylDisjoint k K a b
  · obtain ⟨x, hx, hdx⟩ := hd
    have hc (w : List (Fin N)) (c : ℝ) :
        Tendsto (fun t : ℝ => (Φ.dualComp w (fun _ => (c : ℂ)) t).re) (𝓝[I] x)
          (𝓝 (Φ.dualComp w (fun _ => (c : ℂ)) x).re) :=
      Φ.continuousOn_dualComp_const w c x hx
    have hev : ∀ᶠ t in 𝓝[I] x, Disjoint (Φ.dualCylAt k K a t) (Φ.dualCylAt k K b t) := by
      unfold dualCylAt at hdx ⊢
      simp_rw [disjoint_uIcc_iff] at hdx ⊢
      rcases hdx with h1 | h1
      · exact (((hc a k).max (hc a K)).eventually_lt ((hc b k).min (hc b K)) h1).mono
          fun _ => Or.inl
      · exact (((hc b k).max (hc b K)).eventually_lt ((hc a k).min (hc a K)) h1).mono
          fun _ => Or.inr
    exact (infinite_of_mem_nhdsWithin_I hx hev).mono fun _ ht => ⟨ht.2, fun _ => ht.1⟩
  · exact (Set.Icc_infinite zero_lt_one).mono fun _ ht => ⟨ht, (absurd · hd)⟩

/-! ## Orbits -/

/-- The combined orbit of a pair of words at `t`. -/
noncomputable abbrev pairOrbit {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) (t : ℝ) : List ℝ :=
  Φ.orbit (List.ofFn p.1) t ++ Φ.orbit (List.ofFn p.2) t

/-- The properties of Lemma 4.1 (a) and (b) for one pair `p` and the point `t`. -/
def Good (k K : ℝ) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) (t : ℝ) : Prop :=
  t ∈ I ∧ (Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2) →
      Disjoint (Φ.dualCylAt k K (List.ofFn p.1) t) (Φ.dualCylAt k K (List.ofFn p.2) t)) ∧
    ∀ v : List (Fin N), v ≠ [] → v.length ≤ n → (Φ.comp v t).re ≠ t

/-- One step of the induction in Lemma 4.1: a point for the pair `p` whose orbits avoid the
finite set `F`. -/
private theorem exists_point (h : Φ.NoCoincidence) (k K : ℝ) {n : ℕ}
    (p : (Fin n → Fin N) × (Fin n → Fin N)) {F : Set ℝ} (hF : F.Finite) :
    ∃ t, Φ.Good k K p t ∧ ∀ y ∈ Φ.pairOrbit p t, y ∉ F := by
  obtain ⟨t, ⟨ht, hdisj⟩, hex⟩ := ((Φ.infinite_good k K (List.ofFn p.1)
    (List.ofFn p.2)).sdiff (Φ.finite_exceptional h n hF)).nonempty
  refine ⟨t, ⟨ht, hdisj, fun v hv hlen hvt => hex ⟨ht, v, hlen, Or.inl ⟨hv, hvt⟩⟩⟩, fun y hy => ?_⟩
  rcases List.mem_append.1 hy with hy | hy <;>
    { obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
      exact fun hvF => hex ⟨ht, _, by simp, Or.inr hvF⟩ }

/-- The induction of Lemma 4.1 over finite sets of pairs. -/
private theorem exists_points_finset (h : Φ.NoCoincidence) (k K : ℝ) (n : ℕ)
    (S : Finset ((Fin n → Fin N) × (Fin n → Fin N))) :
    ∃ x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ,
      (∀ p ∈ S, Φ.Good k K p (x p)) ∧
      ∀ p ∈ S, ∀ q ∈ S, p ≠ q → ∀ y ∈ Φ.pairOrbit p (x p), y ∉ Φ.pairOrbit q (x q) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨x, hgood, hsep⟩ := ih
    let F : Set ℝ := ⋃ q ∈ S, {y | y ∈ Φ.pairOrbit q (x q)}
    have hF : F.Finite := S.finite_toSet.biUnion fun q _ => List.finite_toSet _
    obtain ⟨t, hgt, havoid⟩ := Φ.exists_point h k K a hF
    have hxS : ∀ q ∈ S, Function.update x a t q = x q :=
      fun q hq => Function.update_of_ne (ne_of_mem_of_not_mem hq ha) _ _
    refine ⟨Function.update x a t, fun p hp => ?_, fun p hp q hq hpq y hy => ?_⟩
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · rwa [Function.update_self]
      · rw [hxS p hp]; exact hgood p hp
    · rcases Finset.mem_insert.1 hp with rfl | hpS <;>
        rcases Finset.mem_insert.1 hq with rfl | hqS
      · exact absurd rfl hpq
      · rw [Function.update_self] at hy; rw [hxS q hqS]
        exact fun hyq => havoid y hy (mem_biUnion hqS hyq)
      · rw [hxS p hpS] at hy; rw [Function.update_self]
        exact fun hyq => havoid y hyq (mem_biUnion hpS hy)
      · rw [hxS p hpS] at hy; rw [hxS q hqS]
        exact hsep p hpS q hqS hpq y hy

/-- The conclusions of Lemma 4.1 for the points `x` and words of length `n`. -/
structure IsPointChoice (k K : ℝ) (n : ℕ)
    (x : (Fin n → Fin N) × (Fin n → Fin N) → ℝ) : Prop where
  good : ∀ p, Φ.Good k K p (x p)
  sep : ∀ p q, p ≠ q → ∀ y ∈ Φ.pairOrbit p (x p), y ∉ Φ.pairOrbit q (x q)

/-- Lemma 4.1. A pair `(i, j)` is not bad when `F_i(k, K) ∩ F_j(k, K) = ∅` in the sense of (2.2). -/
theorem lemma_4_1 (n : ℕ) (k K : ℝ) (h : Φ.NoCoincidence) :
    ∃ x, Φ.IsPointChoice k K n x := by
  classical
  obtain ⟨x, hgood, hsep⟩ := Φ.exists_points_finset h k K n Finset.univ
  exact ⟨x, fun p => hgood p (Finset.mem_univ _),
    fun p q => hsep p (Finset.mem_univ _) q (Finset.mem_univ _)⟩

end IFS

end AnalyticESC
