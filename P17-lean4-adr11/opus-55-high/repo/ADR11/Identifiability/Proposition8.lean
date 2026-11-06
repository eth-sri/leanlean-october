module

public import ADR11.Nonbinary.FourTaxa
public import ADR11.Identifiability.Lemma5
public import ADR11.Identifiability.Quartets
public import ADR11.Identifiability.FiveTaxa.Binary
public import ADR11.Identifiability.FiveTaxa.Common

/-!
# Propositions 7 and 8: five taxa

* `proposition7`: for `|X| = 5`, `ℙ_{σ⁺}` determines the rooted topology `ψ⁺`.
* `proposition8`: for `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺`.
* `equation7`, `equation8`, `equation9`: the remaining branch length of the balanced, caterpillar
  and pseudocaterpillar trees (proof of Proposition 8), with arguments of the logarithms greater
  than `1`.

The proofs follow the paper. Proposition 7: by Corollary 6 the unrooted tree `ψ⁻` is known, and
the taxa are named so that its splits are `ab|cde` and `abc|de`; the least probable class and the
class of the second smallest probability (inequalities (4)–(6)) tell the seven binary rootings of
`ψ⁻` apart. The classes of the seven rootings are computed in
`ADR11.Identifiability.FiveTaxa.Binary`.
Proposition 8: `ψ⁺` is known by Proposition 7 and `λ⁻` by Corollary 6; after relabelling, `ψ⁺` is
one of the three representatives, every edge not at the root has the length of its split in `λ⁻`,
and the edges at the root are given by (7), (8) or (9).

* `p78_length_eq_of_not_root`, `p78_length_eq_of_sibling`: the lengths given by `λ⁻`.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- For any taxon set, the unrooted gene tree distribution determines the unrooted metric species
tree. -/
theorem sameUnrootedMetricTree_of_unrootedDist_eq (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameUnrootedMetricTree σ' :=
  SpeciesTree.sameUnrootedMetricTree_of_restrict σ σ' fun Q hQ hQ4 =>
    (unrootedDist_eq_iff_four (by simpa using hQ4) _ _).1 (unrootedDist_restrict_eq h Q hQ)

/-- **Proposition 7** (`prop:cases`). For `|X| = 5` the rooted species tree topology `ψ⁺` is determined by
`ℙ_{σ⁺}`. -/
theorem proposition7 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.clusters = σ'.clusters := by
  -- By Corollary 6, `σ` and `σ'` have the same unrooted topology `ψ⁻`. We name the taxa so that
  -- its splits are `ab|cde` and `abc|de`; `ψ⁺` is then one of the binary rootings of `U5 2`.
  obtain ⟨e, he⟩ := exists_equiv_unroot_eq_U5_two_of_isBinary hX σ hσ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 2 := by
    rwa [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← ((sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h).1), ← unroot_relabelFamily]
  have hR := mem_binaryRootings5 _ ((σ.isBinary_relabel_iff e.symm).2 hσ) he
  have hR' := mem_binaryRootings5 _ ((σ'.isBinary_relabel_iff e.symm).2 hσ') he'
  have hd := (SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h
  refine relabelFamily_injective e.symm ?_
  change (σ.relabel e.symm).clusters = (σ'.relabel e.symm).clusters
  generalize σ.relabel e.symm = τ at hR hd ⊢
  generalize σ'.relabel e.symm = τ' at hR' hd ⊢
  -- The classes of gene trees are read off the distribution.
  have hL := cls_leastClass_congr hd
  have hS := cls_secondClass_congr hd
  -- The least probable class and the class of the second smallest probability (by the
  -- inequalities (4)–(6) and relabelling) differ for the seven binary rootings of `U5 2`.
  simp only [binaryRootings5, ← caterpillar5.eq_1, ← balanced5.eq_1, ← pseudocaterpillar5.eq_1,
    mem_insert, mem_singleton] at hR hR'
  rcases hR with h | h | h | h | h | h | h <;> rcases hR' with h' | h' | h' | h' | h' | h' | h' <;>
    simp only [h, h', caterpillar_extremeClasses, balanced_extremeClasses,
      pseudocaterpillar_minClass, p78_classes_cat1, p78_classes_cat2, p78_classes_cat3,
      p78_classes_bal1] at hL hS ⊢ <;>
    first | exact absurd hL (by decide) | exact absurd hS (by decide)

/-- The logarithm step of equations (7)-(9): if `d = n e^{-kℓ}` with `n > 0` and `e^{-ℓ} < 1`, then
`ℓ = (1/k) log(n/d)` and `n/d > 1`. -/
theorem p8_log {n d ℓ c : ℝ} {k : ℕ} (hn : 0 < n) (hd : d = n * exp (-ℓ) ^ k) (hℓ : exp (-ℓ) < 1)
    (hk : c * k = 1) : ℓ = c * log (n / d) ∧ 1 < n / d := by
  rw [hd, div_mul_cancel_left₀ hn.ne', log_inv, log_pow, log_exp, one_lt_inv₀ (by positivity)]
  exact ⟨by linear_combination -ℓ * hk, pow_lt_one₀ (exp_pos _).le hℓ (by rintro rfl; simp at hk)⟩

/-- **Equation (7)** (proof of Proposition 8, balanced case): for `(((a,b):x,c):y,(d,e):z)`,
`XYZ = 6u₅ + 9u₇`, `XY³Z = 15u₇`, hence `y = (1/2) log((2u₅ + 3u₇)/(5u₇))`, and the argument of
the logarithm is greater than `1`. -/
theorem equation7 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = balanced5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) * exp (-σ.length {3, 4}) =
        6 * u σ 5 + 9 * u σ 7 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 * exp (-σ.length {3, 4}) =
        15 * u σ 7 ∧
      σ.length {0, 1, 2} = 1 / 2 * log ((2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7)) ∧
      1 < (2 * u σ 5 + 3 * u σ 7) / (5 * u σ 7) := by
  obtain ⟨-, -, -, -, -, h5, -, -, -, h7, -⟩ := equation11 σ hσ
  exact ⟨by rw [h5, h7]; ring, by rw [h7]; ring, p8_log (k := 2) (by rw [h5, h7]; ring_nf; positivity)
    (by rw [h5, h7]; ring) (five_exp_bounds hσ {0, 1, 2}).2 (by norm_num)⟩

/-- **Equation (8)** (proof of Proposition 8, caterpillar case): for
`((((a,b):x,c):y,d):z,e)`, `XY³ = 3(-u₂ + u₃ + 5u₇)`, `XY³Z⁶ = 15(u₂ - u₃ + u₇)`, hence
`z = (1/6) log((-u₂ + u₃ + 5u₇)/(5u₂ - 5u₃ + 5u₇))`, and the argument of the logarithm is greater
than `1`. -/
theorem equation8 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = caterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 =
        3 * (-u σ 2 + u σ 3 + 5 * u σ 7) ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {0, 1, 2}) ^ 3 *
          exp (-σ.length {0, 1, 2, 3}) ^ 6 = 15 * (u σ 2 - u σ 3 + u σ 7) ∧
      σ.length {0, 1, 2, 3} =
        1 / 6 * log ((-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7)) ∧
      1 < (-u σ 2 + u σ 3 + 5 * u σ 7) / (5 * u σ 2 - 5 * u σ 3 + 5 * u σ 7) := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h7, -⟩ := equation12 σ hσ
  exact ⟨by rw [h2, h3, h7]; ring, by rw [h2, h3, h7]; ring,
    p8_log (k := 6) (by rw [h2, h3, h7]; ring_nf; positivity) (by rw [h2, h3, h7]; ring)
      (five_exp_bounds hσ {0, 1, 2, 3}).2 (by norm_num)⟩

/-- **Equation (9)** (proof of Proposition 8, pseudocaterpillar case): for
`(((a,b):x,(d,e):y):z,c)`, `XY = 12u₅ + 3u₈`, `XYZ⁶ = 30u₅ - 15u₈`, hence
`z = (1/6) log((4u₅ + u₈)/(10u₅ - 5u₈))`, and the argument of the logarithm is greater than `1`. -/
theorem equation9 (σ : SpeciesTree (Fin 5)) (hσ : σ.clusters = pseudocaterpillar5) :
    exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) = 12 * u σ 5 + 3 * u σ 8 ∧
      exp (-σ.length {0, 1}) * exp (-σ.length {3, 4}) * exp (-σ.length {0, 1, 3, 4}) ^ 6 =
        30 * u σ 5 - 15 * u σ 8 ∧
      σ.length {0, 1, 3, 4} = 1 / 6 * log ((4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8)) ∧
      1 < (4 * u σ 5 + u σ 8) / (10 * u σ 5 - 5 * u σ 8) := by
  obtain ⟨-, -, -, -, -, h5, -, -, -, -, -, -, -, h8, -⟩ := equation13 σ hσ
  exact ⟨by rw [h5, h8]; ring, by rw [h5, h8]; ring, p8_log (k := 6) (by rw [h5, h8]; ring_nf; positivity)
    (by rw [h5, h8]; ring) (five_exp_bounds hσ {0, 1, 3, 4}).2 (by norm_num)⟩

/-- Proof of Proposition 8: the edge above a cluster `A` whose complement is not a cluster (an
edge not at the root) has the length of the split `A | Aᶜ` of `λ⁻`. -/
theorem p78_length_eq_of_not_root {H : Finset (Finset (Fin 5))} {τ τ' : SpeciesTree (Fin 5)}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    {A : Finset (Fin 5)} (hA : A ∈ H ∧ A ≠ univ ∧ Aᶜ ∉ H ∧ 2 ≤ #A ∧ 2 ≤ #Aᶜ) :
    τ.length A = τ'.length A := by
  obtain ⟨hA, hAu, hB, h2, h2c⟩ := hA
  rw [← five_unrootedLength_mem τ rfl (hτ ▸ hA) hAu (hτ ▸ hB),
    ← five_unrootedLength_mem τ' rfl (hτ' ▸ hA) hAu (hτ' ▸ hB)]
  exact hU.2 A (mem_unroot.2 (Or.inl ⟨hτ ▸ hA, hAu⟩)) h2 h2c

/-- Proof of Proposition 8: the two edges at the root, above `A` and above `B = Aᶜ`, form the edge
`A | B` of `λ⁻`, so the length of one of them determines the other. -/
theorem p78_length_eq_of_sibling {H : Finset (Finset (Fin 5))} {τ τ' : SpeciesTree (Fin 5)}
    (hτ : τ.clusters = H) (hτ' : τ'.clusters = H) (hU : τ.SameUnrootedMetricTree τ')
    {A B : Finset (Fin 5)} (hAB : Aᶜ = B ∧ A ∈ H ∧ A ≠ univ ∧ B ∈ H ∧ B ≠ univ ∧ 2 ≤ #A ∧ 2 ≤ #B)
    (hl : τ.length B = τ'.length B) : τ.length A = τ'.length A := by
  obtain ⟨hAB, hA, hAu, hB, hBu, h2, h2c⟩ := hAB
  have e := five_unrootedLength_both τ hAB (hτ ▸ hA) hAu (hτ ▸ hB) hBu
  have e' := five_unrootedLength_both τ' hAB (hτ' ▸ hA) hAu (hτ' ▸ hB) hBu
  have := hU.2 A (mem_unroot.2 (Or.inl ⟨hτ ▸ hA, hAu⟩)) h2 (hAB ▸ h2c)
  linarith

/-- **Proposition 8** (`prop:5taxa`). For `|X| = 5`, `ℙ_{σ⁺}` determines `σ⁺ = (ψ⁺, λ⁺)`. -/
theorem proposition8 (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := by
  -- By Proposition 7, `ψ⁺` is determined; by Corollary 6, `λ⁻` is determined.
  have hψ := proposition7 hX σ σ' hσ hσ' h
  -- Relabelling the taxa, we may assume that `ψ⁺` is `(((a,b),c),(d,e))`, `((((a,b),c),d),e)` or
  -- `(((a,b),(d,e)),c)`.
  obtain ⟨e, he⟩ := p78_exists_relabel_rep hX σ hσ
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e]
  have hψ' : (σ'.relabel e).clusters = (σ.relabel e).clusters := by simp_all
  have hU' := (SpeciesTree.sameUnrootedMetricTree_relabel_iff σ σ' e).2 (sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h)
  have hu := cls_u_congr ((SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e).2 h)
  generalize σ.relabel e = τ at he hψ' hU' hu ⊢
  generalize σ'.relabel e = τ' at hψ' hU' hu ⊢
  -- Every edge not at the root has the length of its split in `λ⁻`; the edges at the root are
  -- given by (7) (with the edge `abc|de` of `λ⁻` for the balanced tree), (8) and (9).
  rcases he with h | h | h <;> have h' := hψ'.trans h <;>
    refine five_sameRootedMetricTree_of_lengths h h' ?_ <;> simp only [mem_insert, mem_singleton] <;>
    rintro A (rfl | rfl | rfl) <;>
    first
    | exact p78_length_eq_of_not_root h h' hU' (by decide)
    | rw [(equation8 τ h).2.2.1, (equation8 τ' h').2.2.1, hu 2, hu 3, hu 7]
    | rw [(equation9 τ h).2.2.1, (equation9 τ' h').2.2.1, hu 5, hu 8]
    | rw [(equation7 τ h).2.2.1, (equation7 τ' h').2.2.1, hu 5, hu 7]
    | exact p78_length_eq_of_sibling h h' hU' (B := {0, 1, 2}) (by decide)
        (by rw [(equation7 τ h).2.2.1, (equation7 τ' h').2.2.1, hu 5, hu 7])

end ADR11
