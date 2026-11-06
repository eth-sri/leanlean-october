/-
Copyright (c) 2026 Ben Keene. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Keene
-/
module

public import SemigroupBetti.Fiber

/-!
# The algebraic bridge: `μ(I) ≤ β₁`

Write-up `PROOF_B_lean_writeup.md`, §2, Definition 4 and Lemma 0 (parts B–F, in the
"explicit generating set" form).

Let `I = ker (K[X₀,…,X₃] → K[t], Xᵢ ↦ t^{nᵢ})`.  For every degree `d ≤ H` with nonempty
fiber we fix a base component `C₀` of `∇_d` and a representative `rep C` of every component,
and take the binomials `X^{rep C} - X^{rep C₀}`, `C ≠ C₀`.  There are at most
`∑_{d ≤ H} (c_d - 1) = β₁` of them, and they generate `I`:

* every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in their span, by strong induction on
  the degree (an edge of `∇_d` factors as `Xᵢ · (binomial of smaller degree)`; a path is a sum of
  edges; different components are linked through the chosen representatives; above `H` the
  graph is connected by Lemma 0A);
* every element of `I` is a `K`-combination of such binomials (coefficient sums vanish on
  each fiber).

Main results: `GenData.toricKer_eq_span`, `GenData.spanRank_le_beta1_of_n_eq`.
Also `GenData.ofChallenge`: the conversion from the arithmetic hypotheses of `Challenge.lean`.
-/

@[expose] public section

namespace SemigroupBetti

open Finset MvPolynomial

section Mono

variable (K : Type*) [Field K]

/-- The monomial `X^z` for `z : Fin 4 → ℕ`. -/
noncomputable def mono (z : Fin 4 → ℕ) : MvPolynomial (Fin 4) K :=
  monomial (Finsupp.equivFunOnFinite.symm z) 1

/-- The toric map `K[X₀,…,X₃] → K[t]`, `Xᵢ ↦ t^{nᵢ}`. -/
noncomputable def toricMap (n : Fin 4 → ℕ) : MvPolynomial (Fin 4) K →ₐ[K] Polynomial K :=
  aeval (fun i => (Polynomial.X : Polynomial K) ^ n i)

variable {K}

lemma mono_coe (s : Fin 4 →₀ ℕ) : mono K ⇑s = monomial s 1 := by
  simp [mono]

lemma toricMap_monomial (n : Fin 4 → ℕ) (s : Fin 4 →₀ ℕ) (c : K) :
    toricMap K n (monomial s c) = Polynomial.C c * Polynomial.X ^ (∑ i, s i * n i) := by
  rw [toricMap, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma X_mul_mono (i : Fin 4) (u : Fin 4 → ℕ) :
    (X i : MvPolynomial (Fin 4) K) * mono K u = mono K (u + Pi.single i 1) := by
  rw [mono, mono, X, monomial_mul_monomial, one_mul]
  rw [show Finsupp.single i 1 + Finsupp.equivFunOnFinite.symm u =
    Finsupp.equivFunOnFinite.symm (u + Pi.single i 1) by
      ext j
      by_cases h : j = i <;> simp [h, add_comm]]

end Mono

namespace GenData

variable (G : GenData) (K : Type*) [Field K]

lemma toricMap_mono (z : Fin 4 → ℕ) : toricMap K G.n (mono K z) = Polynomial.X ^ G.nu z := by
  rw [mono, toricMap_monomial]; simp [nu]

/-- The toric ideal, written exactly as in `Challenge.lean` (`SemigroupBetti.toricIdeal K G.n`
unfolds to this). -/
noncomputable abbrev toricKer : Ideal (MvPolynomial (Fin 4) K) :=
  RingHom.ker (MvPolynomial.aeval (fun i => (Polynomial.X : Polynomial K) ^ G.n i)).toRingHom

lemma mem_toricKer {f : MvPolynomial (Fin 4) K} : f ∈ G.toricKer K ↔ toricMap K G.n f = 0 :=
  RingHom.mem_ker

/-! ### Representatives, base components, and the generating binomials -/

/-- A chosen representative factorization of a component of `∇_d`. -/
noncomputable def rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : Fin 4 → ℕ :=
  (Quot.out C : G.fiber d).1

lemma nu_rep {d : ℕ} (C : (G.nabla d).ConnectedComponent) : G.nu (G.rep C) = d :=
  G.mem_fiber.1 (Quot.out C).2

lemma rep_mk {d : ℕ} (C : (G.nabla d).ConnectedComponent) :
    (G.nabla d).connectedComponentMk (⟨G.rep C, (Quot.out C).2⟩ : G.fiber d) = C :=
  Quot.out_eq C

open Classical in
/-- The chosen binomials of degree `d`: `X^{rep C} - X^{rep C₀}` for `C ≠ C₀`, where `C₀` is
a fixed base component (none if the fiber is empty). -/
noncomputable def genSet (d : ℕ) : Finset (MvPolynomial (Fin 4) K) :=
  if h : Nonempty (G.nabla d).ConnectedComponent then
    (univ.erase (Classical.choice h)).image
      (fun C => mono K (G.rep C) - mono K (G.rep (Classical.choice h)))
  else ∅

open Classical in
/-- All chosen binomials, over the degrees `d ≤ H`. -/
noncomputable def binomGens : Finset (MvPolynomial (Fin 4) K) :=
  (range (G.H + 1)).biUnion (G.genSet K)

/-! ### Every equal-degree binomial lies in the span -/

/-- Path step (write-up Lemma 0D). -/
lemma sub_mem_of_reachable {J : Ideal (MvPolynomial (Fin 4) K)} {d : ℕ}
    (IH : ∀ e < d, ∀ z z' : Fin 4 → ℕ, G.nu z = e → G.nu z' = e → mono K z - mono K z' ∈ J)
    {x y : G.fiber d} (h : (G.nabla d).Reachable x y) : mono K x.1 - mono K y.1 ∈ J := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons u v w hadj _ ih =>
    rw [← sub_add_sub_cancel _ (mono K v.1) _]
    apply add_mem _ ih
    have hz := G.mem_fiber.1 u.2
    have hz' := G.mem_fiber.1 v.2
    obtain ⟨i, hi, hi'⟩ := hadj.2
    have key : ∀ y : Fin 4 → ℕ, 0 < y i → y = (y - Pi.single i 1) + Pi.single i 1 := by
      intro y hy; ext j; by_cases hj : j = i <;> simp [hj] <;> omega
    have hdeg : ∀ y : Fin 4 → ℕ, 0 < y i → G.nu y = G.nu (y - Pi.single i 1) + G.n i := by
      intro y hy
      conv_lhs => rw [key y hy]
      rw [G.nu_add, G.nu_single, one_mul]
    rw [key u.1 hi, key v.1 hi', ← X_mul_mono, ← X_mul_mono, ← mul_sub]
    refine J.mul_mem_left _ (IH (G.nu (u.1 - Pi.single i 1)) ?_ _ _ rfl ?_)
    · have := hdeg u.1 hi; have := G.n_pos i; omega
    · have := hdeg u.1 hi; have := hdeg v.1 hi'; omega

/-- Base-component step (write-up Lemma 0D/0F): the chosen binomials link any two
representatives at a degree `d ≤ H`. -/
lemma rep_sub_rep_mem {d : ℕ} (hd : d ≤ G.H) (C C' : (G.nabla d).ConnectedComponent) :
    mono K (G.rep C) - mono K (G.rep C') ∈ Ideal.span (G.binomGens K : Set _) := by
  classical
  have h : Nonempty (G.nabla d).ConnectedComponent := ⟨C⟩
  let C0 := Classical.choice h
  have base (D : (G.nabla d).ConnectedComponent) :
      mono K (G.rep D) - mono K (G.rep C0) ∈ Ideal.span (G.binomGens K : Set _) := by
    by_cases hD : D = C0
    · rw [hD, sub_self]; exact zero_mem _
    · apply Ideal.subset_span
      simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe, Set.mem_Iio]
      refine ⟨d, by omega, ?_⟩
      unfold genSet
      simp only [h, ↓reduceDIte]
      exact mem_image.2 ⟨D, mem_erase.2 ⟨hD, mem_univ _⟩, rfl⟩
  rw [← sub_sub_sub_cancel_right _ _ (mono K (G.rep C0))]
  exact sub_mem (base C) (base C')

/-- **Lemma 0 (B–F), binomial form.** Every binomial `X^z - X^{z'}` with `ν z = ν z'` lies in
the ideal spanned by the chosen binomials. -/
lemma mono_sub_mem_span (d : ℕ) : ∀ z z' : Fin 4 → ℕ, G.nu z = d → G.nu z' = d →
    mono K z - mono K z' ∈ Ideal.span (G.binomGens K : Set _) := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro z z' hz hz'
  let x : G.fiber d := ⟨z, G.mem_fiber.2 hz⟩
  let y : G.fiber d := ⟨z', G.mem_fiber.2 hz'⟩
  change mono K x.1 - mono K y.1 ∈ _
  by_cases hr : (G.nabla d).Reachable x y
  · exact G.sub_mem_of_reachable K IH hr
  · set Cx := (G.nabla d).connectedComponentMk x
    set Cy := (G.nabla d).connectedComponentMk y
    have hne : Cx ≠ Cy := fun h => hr (SimpleGraph.ConnectedComponent.exact h)
    have hd : d ≤ G.H := G.le_H_of_contributes (by
      unfold contributes ncomp
      exact Fintype.one_lt_card_iff.2 ⟨Cx, Cy, hne⟩)
    have h1 := G.sub_mem_of_reachable K IH (x := x) (y := ⟨G.rep Cx, (Quot.out Cx).2⟩)
      (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cx).symm)
    have h2 := G.sub_mem_of_reachable K IH (x := ⟨G.rep Cy, (Quot.out Cy).2⟩) (y := y)
      (SimpleGraph.ConnectedComponent.exact (G.rep_mk Cy))
    convert add_mem (add_mem h1 (G.rep_sub_rep_mem K hd Cx Cy)) h2 using 1 <;> ring

/-! ### The kernel is spanned by equal-degree binomials -/

open Classical in
/-- A chosen factorization of `d` (junk `0` when the fiber is empty). -/
noncomputable def root (d : ℕ) : Fin 4 → ℕ :=
  if h : (G.fiber d).Nonempty then h.choose else 0

/-- **Lemma 0B.** An element of the kernel has zero coefficient sum on every fiber. -/
lemma coeff_sum_eq_zero {f : MvPolynomial (Fin 4) K} (hf : f ∈ G.toricKer K) (d : ℕ) :
    ∑ s ∈ f.support.filter (fun s : Fin 4 →₀ ℕ => G.nu ⇑s = d), f.coeff s = 0 := by
  have hφ := (G.mem_toricKer K).1 hf
  rw [f.as_sum, map_sum] at hφ
  have := congrArg (fun p : Polynomial K => p.coeff d) hφ
  simp only [toricMap_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_filter]
  simpa [nu, eq_comm] using this

/-- **Lemma 0F.** The toric ideal is generated by the chosen binomials. -/
theorem toricKer_eq_span : G.toricKer K = Ideal.span (G.binomGens K : Set _) := by
  apply le_antisymm
  · intro f hf
    set J := Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))
    have hsplit : f = ∑ s ∈ f.support, C (f.coeff s) * (mono K s - mono K (G.root (G.nu s))) +
        ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) := by
      simpa only [← sum_add_distrib, ← mul_add, sub_add_cancel, mono_coe,
        C_mul_monomial, mul_one] using f.as_sum
    have hzero : ∑ s ∈ f.support, C (f.coeff s) * mono K (G.root (G.nu s)) = 0 := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun s : Fin 4 →₀ ℕ => G.nu s)
        (t := f.support.image (fun s : Fin 4 →₀ ℕ => G.nu s)) (fun s hs => mem_image_of_mem _ hs)]
      refine Finset.sum_eq_zero fun d _ => ?_
      rw [Finset.sum_congr rfl (fun s hs => by rw [(mem_filter.1 hs).2]), ← Finset.sum_mul,
        ← map_sum, G.coeff_sum_eq_zero K hf d, map_zero, zero_mul]
    rw [hsplit, hzero, add_zero]
    exact J.sum_mem fun s _ => J.mul_mem_left _ (G.mono_sub_mem_span K (G.nu s) s _ rfl (by
      have h : (G.fiber (G.nu s)).Nonempty := ⟨s, G.mem_fiber.2 rfl⟩
      rw [root]; simp only [h, ↓reduceDIte]
      exact G.mem_fiber.1 h.choose_spec))
  · classical
    apply Ideal.span_le.2
    intro p hp
    simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe] at hp
    obtain ⟨d, -, hp⟩ := hp
    unfold genSet at hp
    split_ifs at hp with h
    · obtain ⟨C, -, rfl⟩ := mem_image.1 hp
      apply (G.mem_toricKer K).2
      rw [map_sub, toricMap_mono, toricMap_mono, G.nu_rep, G.nu_rep, sub_self]
    · simp at hp

/-- **Bridge (inequality half of Lemma 0).** `μ(I) ≤ β₁`, with `μ` = `Submodule.spanRank`. -/
theorem spanRank_le_beta1_of_n_eq {n : Fin 4 → ℕ} (hn : G.n = n) :
    (RingHom.ker (MvPolynomial.aeval (R := K)
      (fun i => (Polynomial.X : Polynomial K) ^ n i)).toRingHom).spanRank ≤
      (G.beta1 : Cardinal) := by
  subst hn
  change (G.toricKer K).spanRank ≤ _
  rw [G.toricKer_eq_span K]
  calc (Ideal.span (G.binomGens K : Set (MvPolynomial (Fin 4) K))).spanRank
      ≤ Cardinal.mk (G.binomGens K : Set (MvPolynomial (Fin 4) K)) :=
        Submodule.spanRank_span_le_card _
    _ = (#(G.binomGens K) : Cardinal) := Cardinal.mk_coe_finset
    _ ≤ (G.beta1 : Cardinal) := Nat.cast_le.2 (by
      classical
      exact card_biUnion_le.trans (sum_le_sum fun d _ => by
        unfold genSet
        split_ifs with h
        · refine card_image_le.trans ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, ncomp]
        · simp))

end GenData

/-! ### From the hypotheses of `Challenge.lean` to `GenData` -/

namespace GenData

/-- Build `GenData` from the arithmetic hypotheses `0 < n 0`, `StrictMono n`, and
`Finset.univ.gcd n = 1`. The combinatorial development does not use minimality. -/
def ofChallenge (n : Fin 4 → ℕ) (hpos : 0 < n 0) (hmono : StrictMono n)
    (hgcd : Finset.univ.gcd n = 1) : GenData :=
  have h01 : n 0 < n 1 := hmono (by decide)
  have h12 : n 1 < n 2 := hmono (by decide)
  have h23 : n 2 < n 3 := hmono (by decide)
  { m := n 0
    a := n 1 - n 0
    b := n 2 - n 0
    w := n 3 - n 0
    m_pos := hpos
    a_pos := by omega
    a_lt_b := by omega
    b_lt_w := by omega
    gcd_eq_one := by
      set g := Nat.gcd (n 0) (Nat.gcd (n 1 - n 0) (Nat.gcd (n 2 - n 0) (n 3 - n 0)))
      have h0 : g ∣ n 0 := Nat.gcd_dvd_left _ _
      have ha : g ∣ n 1 - n 0 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      have hb : g ∣ n 2 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
      have hw : g ∣ n 3 - n 0 :=
        (Nat.gcd_dvd_right _ _).trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
      have hall : ∀ i ∈ (Finset.univ : Finset (Fin 4)), g ∣ n i := by
        intro i _
        fin_cases i
        · exact h0
        · convert Nat.dvd_add h0 ha using 1 <;> simp <;> omega
        · convert Nat.dvd_add h0 hb using 1 <;> simp <;> omega
        · convert Nat.dvd_add h0 hw using 1 <;> simp <;> omega
      exact Nat.dvd_one.1 (hgcd ▸ Finset.dvd_gcd hall) }

end GenData

end SemigroupBetti
