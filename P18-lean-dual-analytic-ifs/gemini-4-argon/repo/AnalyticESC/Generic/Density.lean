module

public import AnalyticESC.Generic.Continuity
public import AnalyticESC.Generic.Agreement
public import AnalyticESC.Generic.MultiplicativeBump
public import AnalyticESC.Generic.Points

@[expose] public section

/-!
# The density step of Theorem 1.4

The proof of Theorem 1.4 in Section 4.2, after the interpolation `IFS.exists_noCoincidence_near`: an IFS whose maps
send `[0,1]` into `(0,1)` and whose compositions along distinct finite words differ on `[0,1]` has
arbitrarily `d₂`-close perturbations whose dual IFS satisfies the SSC.

The proof follows the paper with words of length `n + 1`, to match Lemma 2.6. The points of
Lemma 4.1 and their orbits are split, for each letter `ℓ`, into the set `𝒴_ℓ` of the points
`x_{i,j}` of the bad pairs with `i₁ = ℓ` and the set `𝒵_ℓ` of the remaining orbit points, and
Proposition 4.2 perturbs each map accordingly. A strictly invariant cylinder is fixed first;
uniform continuity estimates in the `d₂` metric give a neighbourhood where its strict
inclusions persist. Only then are `δ` and the word length chosen.
-/

namespace AnalyticESC

open Set Metric Filter Topology

namespace IFS

variable {N : ℕ} {ε ε' : ℝ}

/-! ## Orbits -/

/-- The point of index `m ≤ |w|` lies on the orbit `𝒪_w(t)`. -/
private theorem re_comp_take_mem_orbit (Φ : IFS N ε) {w : List (Fin N)} {m : ℕ}
    (hm : m ≤ w.length) (t : ℝ) : (Φ.comp (w.take m).reverse t).re ∈ Φ.orbit w t :=
  List.mem_map.2 ⟨m, List.mem_range.2 (Nat.lt_succ_of_le hm), rfl⟩

/-- The base point `t` is the first point of the orbit `𝒪_p(t)`. -/
private theorem self_mem_pairOrbit (Φ : IFS N ε) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N))
    (t : ℝ) : t ∈ Φ.pairOrbit p t :=
  List.mem_append_left _ (by simpa using Φ.re_comp_take_mem_orbit (Nat.zero_le _) t)

/-- The points of an orbit from a point of `I` lie in `I`. -/
private theorem mem_I_of_mem_orbit (Φ : IFS N ε) {w : List (Fin N)} {t y : ℝ} (ht : t ∈ I)
    (hy : y ∈ Φ.orbit w t) : y ∈ I := by
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
  exact Φ.re_comp_mem_I _ ht

/-! ## The point sets `𝒴_ℓ` and `𝒵_ℓ` -/

/-- A pair `(i, j)` is bad when `F_i(k,K)` and `F_j(k,K)` are not disjoint in the sense
of (2.2). -/
private def Bad (Φ : IFS N ε) (k K : ℝ) {n : ℕ} (p : (Fin n → Fin N) × (Fin n → Fin N)) :
    Prop :=
  ¬ Φ.DualCylDisjoint k K (List.ofFn p.1) (List.ofFn p.2)

/-- The union of the orbits `𝒪_i(x_{i,j}) ∪ 𝒪_j(x_{i,j})`. -/
private noncomputable def orbitPoints (Φ : IFS N ε) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) : Finset ℝ := by
  classical exact Finset.univ.biUnion fun p => (Φ.pairOrbit p (x p)).toFinset

/-- The set `𝒴_ℓ`: the points `x_{i,j}` of the bad pairs `(i, j)` with `i₁ = ℓ`. -/
private noncomputable def badPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact (Finset.univ.filter fun p => Φ.Bad k K p ∧ p.1 0 = ℓ).image x

/-- The set `𝒵_ℓ`: the orbit points outside `𝒴_ℓ`. -/
private noncomputable abbrev goodPoints (Φ : IFS N ε) (k K : ℝ) (n : ℕ)
    (x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ) (ℓ : Fin N) : Finset ℝ := by
  classical exact Φ.orbitPoints n x \ Φ.badPoints k K n x ℓ

private theorem mem_orbitPoints {Φ : IFS N ε} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {y : ℝ} :
    y ∈ Φ.orbitPoints n x ↔ ∃ p, y ∈ Φ.pairOrbit p (x p) := by
  simp [orbitPoints]

private theorem mem_badPoints {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
    {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ} {ℓ : Fin N} {y : ℝ} :
    y ∈ Φ.badPoints k K n x ℓ ↔
      ∃ p, (Φ.Bad k K p ∧ p.1 0 = ℓ) ∧ x p = y := by
  simp [badPoints]

namespace IsPointChoice

variable {Φ : IFS N ε} {k K : ℝ} {n : ℕ}
  {x : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N) → ℝ}

/-- `x_{i,j} ∈ 𝒴_ℓ` exactly when `(i, j)` is bad and `i₁ = ℓ`. -/
private theorem mem_badPoints_iff (hx : Φ.IsPointChoice k K (n + 1) x)
    (p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)) (ℓ : Fin N) :
    x p ∈ Φ.badPoints k K n x ℓ ↔ Φ.Bad k K p ∧ p.1 0 = ℓ := by
  rw [mem_badPoints]
  refine ⟨fun ⟨q, hqb, hqx⟩ => ?_, fun h => ⟨p, h, rfl⟩⟩
  by_contra h
  exact hx.sep q p (by rintro rfl; exact h hqb) (x q)
    (Φ.self_mem_pairOrbit _ _) (hqx.symm ▸ Φ.self_mem_pairOrbit _ _)

/-- The orbit points of a pair other than its base point lie in every `𝒵_ℓ`. -/
private theorem mem_goodPoints_of_ne (hx : Φ.IsPointChoice k K (n + 1) x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} {y : ℝ}
    (hy : y ∈ Φ.pairOrbit p (x p)) (hne : y ≠ x p)
    (ℓ : Fin N) : y ∈ Φ.goodPoints k K n x ℓ := by
  refine Finset.mem_sdiff.2 ⟨mem_orbitPoints.2 ⟨p, hy⟩, fun hY => ?_⟩
  obtain ⟨q, -, rfl⟩ := mem_badPoints.1 hY
  exact hx.sep p q (by rintro rfl; exact hne rfl) (x q) hy (Φ.self_mem_pairOrbit _ _)

/-- The base point `x_{i,j}` lies in `𝒵_ℓ` unless `(i, j)` is bad and `i₁ = ℓ`. -/
private theorem self_mem_goodPoints (hx : Φ.IsPointChoice k K (n + 1) x)
    {p : (Fin (n + 1) → Fin N) × (Fin (n + 1) → Fin N)} {ℓ : Fin N}
    (h : ¬ (Φ.Bad k K p ∧ p.1 0 = ℓ)) : x p ∈ Φ.goodPoints k K n x ℓ :=
  Finset.mem_sdiff.2 ⟨mem_orbitPoints.2 ⟨p, Φ.self_mem_pairOrbit _ _⟩,
    fun hY => h ((hx.mem_badPoints_iff p ℓ).1 hY)⟩

end IsPointChoice

/-! ## Bounds for the perturbation -/

/-- Uniform bound on `H_u` in a `d₂` neighbourhood of `Φ`. -/
theorem exists_invariant_cylinder_near (Φ : IFS N ε) (hN : 0 < N) :
    ∃ K > 0, ∃ η > 0, ∀ {ε' : ℝ} (Ψ : IFS N ε'), d2 Φ Ψ < η →
      ∀ u : ℕ → Fin N, ∀ y ∈ I, (Ψ.dualProj (.inf u) y).re ∈ Icc (-K) K := by
  obtain ⟨M, hM0, hM⟩ := Φ.exists_norm_dualProj_le
  obtain ⟨A, η₀, hη₀, hcont⟩ := Φ.exists_dualProj_sub_le_d2 hN
  let K := M + 1
  let η := min η₀ (1 / (|A| + 1))
  refine ⟨K, by dsimp [K]; positivity, η, lt_min hη₀ (by positivity), fun {ε'} Ψ hΨ u y hy => ?_⟩
  have hηA : d2 Φ Ψ < 1 / (|A| + 1) := hΨ.trans_le (min_le_right _ _)
  have hA : A * d2 Φ Ψ < 1 := by
    have hd := Continuity.d2_nonneg Φ Ψ
    have h := (lt_div_iff₀ (by positivity : 0 < |A| + 1)).1 hηA
    nlinarith [le_abs_self A, mul_le_mul_of_nonneg_right (le_abs_self A) hd]
  have he := hcont Ψ (hΨ.trans_le (min_le_left _ _)) (.inf u) y hy
  have hb := hM (.inf u) y (subset_closure (ofReal_mem_nbhd Φ.ε_pos hy))
  have ht := norm_sub_norm_le (Ψ.dualProj (.inf u) y) (Φ.dualProj (.inf u) y)
  rw [norm_sub_rev] at ht
  exact abs_le.1 ((Complex.abs_re_le_norm _).trans (by dsimp [K]; linarith))

/-- The `d₂` distance from bounds on the three differences on `I`. -/
private theorem d2_le (hN : 0 < N) (Φ : IFS N ε) (Ψ : IFS N ε') {a b e : ℝ}
    (h0 : ∀ i, ∀ x ∈ I, ‖Ψ.f i x - Φ.f i x‖ ≤ a)
    (h1 : ∀ i, ∀ x ∈ I, ‖deriv (Ψ.f i) x - deriv (Φ.f i) x‖ ≤ b)
    (h2 : ∀ i, ∀ x ∈ I, ‖deriv (deriv (Ψ.f i)) x - deriv (deriv (Φ.f i)) x‖ ≤ e) :
    d2 Φ Ψ ≤ a + b + e := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have : Nonempty I := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  exact ciSup_le fun i => add_le_add (add_le_add
    (ciSup_le fun x => by rw [norm_sub_rev]; exact h0 i x x.2)
    (ciSup_le fun x => by rw [norm_sub_rev]; exact h1 i x x.2))
    (ciSup_le fun x => by rw [norm_sub_rev]; exact h2 i x x.2)

/-! ## The density step -/

/-- The density step in the proof of Theorem 1.4. -/
theorem exists_dualSSC_near (hN : 0 < N) (Φ : IFS N ε)
    (hI : ∀ i, ∀ x ∈ I, (Φ.f i x).re ∈ Ioo 0 1) (hnc : Φ.NoCoincidence) {r : ℝ} (hr : 0 < r) :
    ∃ ε' : ℝ, ∃ Ψ : IFS N ε', d2 Φ Ψ < r ∧ Ψ.DualSSC := by
  -- Fix an invariant cylinder, then choose `δ` within its continuity neighbourhood.
  obtain ⟨K, hK0, η, hη, hstable⟩ := Φ.exists_invariant_cylinder_near hN
  set δ := min r η / 24
  have hδ : 0 < δ := div_pos (lt_min hr hη) (by norm_num)
  have hδr : 23 * δ < min r η := by dsimp [δ]; linarith [lt_min hr hη]
  have hkK : -K ≤ K := by linarith
  have hc1 := Φ.cmax_lt_one
  have hc0 := Φ.cmax_nonneg
  -- the length `n + 1` of the words
  obtain ⟨n, hn0⟩ := exists_pow_lt_of_lt_one
    (show 0 < δ / 3 / (K - -K) from div_pos (by linarith) (by linarith)) hc1
  have hn : Φ.cmax ^ (n + 1) * (K - -K) < δ / 3 :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc0 hc1.le (Nat.le_succ n))
      (by linarith)).trans_lt ((lt_div_iff₀ (by linarith)).1 hn0)
  -- the points of Lemma 4.1
  obtain ⟨x, hx⟩ := Φ.lemma_4_1 (n + 1) (-K) K hnc
  -- the perturbation of Proposition 4.2
  choose g hg using fun i => proposition_4_2 (Y := Φ.badPoints (-K) K n x i)
    (Z := Φ.goodPoints (-K) K n x i) Φ.ε_pos (Φ.inClass i) (hI i)
    (fun _ hy => by obtain ⟨p, -, rfl⟩ := mem_badPoints.1 hy; exact (hx.good p).1)
    (fun y hy => by
      obtain ⟨p, hy⟩ := mem_orbitPoints.1 (Finset.mem_sdiff.1 hy).1
      exact (List.mem_append.1 hy).elim (Φ.mem_I_of_mem_orbit (hx.good p).1)
        (Φ.mem_I_of_mem_orbit (hx.good p).1))
    (by unfold goodPoints; exact disjoint_sdiff_self_right) hδ
  obtain ⟨ε', hε', hgε'⟩ := exists_inClass_forall hN fun i => (hg i).1
  obtain ⟨Ψ, rfl⟩ : ∃ Ψ : IFS N ε', Ψ.f = g := ⟨⟨g, hε', hgε'⟩, rfl⟩
  have hd : d2 Φ Ψ < min r η :=
    (d2_le hN Φ Ψ (fun i y hy => ((hg i).2.2.2.2.1 y hy).le)
      (fun i y hy => ((hg i).2.2.2.2.2.1 y hy).le)
      (fun i y hy => ((hg i).2.2.2.2.2.2 y hy).le)).trans_lt (by linarith)
  refine ⟨ε', Ψ, hd.trans_le (min_le_left _ _), ?_⟩
  have hZ : ∀ ℓ, ∀ z ∈ Φ.goodPoints (-K) K n x ℓ, AgreeAt (Φ.f ℓ) (Ψ.f ℓ) z :=
    fun ℓ z hz => ⟨((hg ℓ).2.1 z (Finset.mem_union_right _ hz)).1,
      ((hg ℓ).2.1 z (Finset.mem_union_right _ hz)).2, (hg ℓ).2.2.1 z hz⟩
  refine Ψ.lemma_2_6 n (hstable Ψ (hd.trans_le (min_le_right _ _))) fun i j hij => ?_
  set p := (i, j)
  have ht := (hx.good p).1
  refine ⟨x p, ht, ?_⟩
  have hpos {u : Fin (n + 1) → Fin N}
      (horb : ∀ y ∈ Φ.orbit (List.ofFn u) (x p), y ∈ Φ.pairOrbit p (x p))
      {m : ℕ} (h0 : 0 < m) (hm : m ≤ (List.ofFn u).length) (ℓ : Fin N) :
      AgreeAt (Φ.f ℓ) (Ψ.f ℓ) (Φ.comp ((List.ofFn u).take m).reverse (x p)).re :=
    hZ _ _ (hx.mem_goodPoints_of_ne (horb _ (Φ.re_comp_take_mem_orbit hm _))
      ((hx.good p).2.2 _ (by simp [h0.ne']) (by simp)) ℓ)
  have hcyl {u : Fin (n + 1) → Fin N}
      (horb : ∀ y ∈ Φ.orbit (List.ofFn u) (x p), y ∈ Φ.pairOrbit p (x p))
      (h0 : ¬ (Φ.Bad (-K) K p ∧ p.1 0 = u 0)) :
      Ψ.dualCylAt (-K) K (List.ofFn u) (x p) = Φ.dualCylAt (-K) K (List.ofFn u) (x p) :=
    dualCylAt_eq_of_agreeAt Φ Ψ (-K) K ht fun m hm => by
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · simpa using hZ _ _ (hx.self_mem_goodPoints h0)
      · exact hpos horb hm0 hm.le _
  by_cases hb : Φ.Bad (-K) K p
  · have hmemY := (hx.mem_badPoints_iff p _).2 ⟨hb, rfl⟩
    obtain ⟨h0, h1⟩ := (hg (p.1 0)).2.1 _ (Finset.mem_union_left _ hmemY)
    rw [List.ofFn_succ (f := p.1), dualCylAt_cons_eq_of_agreeAt Φ Ψ (-K) K ht h0 h1 fun m hm => by
        rw [← List.ofFn_succ (f := p.1)]
        exact hpos (fun _ => List.mem_append_left _) (Nat.succ_pos m) (by simp at hm ⊢; omega) _,
      ← List.ofFn_succ (f := p.1), hcyl (fun _ => List.mem_append_right _) (fun h => hij h.2)]
    refine disjoint_image_add_of_abs_sub_lt
      (fun a ha a' ha' => (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht ha ha').trans_lt
        (by simpa using hn))
      (fun b hb b' hb' => (Φ.abs_sub_le_cmax_pow_of_mem_dualCylAt hkK _ ht hb hb').trans_lt
        (by simpa using hn))
      (not_disjoint_iff_nonempty_inter.1 fun hd => hb ⟨x p, ht, hd⟩) ?_
    rw [Complex.abs_re_eq_norm.2 (by
      rw [Complex.sub_im, Ψ.im_nonlin_ofReal _ (ofReal_mem_nbhd Ψ.ε_pos ht),
        Φ.im_nonlin_ofReal _ (ofReal_mem_nbhd Φ.ε_pos ht), sub_zero])]
    exact (hg (p.1 0)).2.2.2.1 _ hmemY
  · rw [hcyl (fun _ => List.mem_append_left _) (fun h => hb h.1),
      hcyl (fun _ => List.mem_append_right _) (fun h => hb h.1)]
    exact (hx.good p).2.1 (not_not.1 hb)

end IFS

end AnalyticESC
