module

public import ADR11.Nonbinary.FiveTaxa.Ac1Classes
public import ADR11.Identifiability.Proposition8
public meta import ADR11.Rootings.Proofs

/-!
# Propositions 7 and 8 for nonbinary species trees (Appendix C)

On five taxa the unrooted gene tree distribution determines the rooted metric species tree, binary
or not (`appC_sameRootedMetricTree`). By the nonbinary Corollary 6
(`sameUnrootedMetricTree_of_unrootedDist_eq`) the unrooted species tree is determined; after
relabelling the taxa it is the star `U5 0`, the tree `U5 1` with the split `ab|cde`, or the binary
tree `U5 2` with the splits `ab|cde` and `abc|de`, and the species tree is one of its rootings.
Two different rootings are told apart by their classes of gene trees (Table 7 and
`ADR11.Nonbinary.FiveTaxa.Ac1Classes`), except `P₄` from `P₈` and the balanced trees from `P₆`,
which are told apart by whether the solved `Z` is `1` or less (`ac1_P8_Z`, `ac2_Z`). Two binary
trees are handled by Proposition 8; the branch lengths are solved from the equations of Table 7.
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {τ : SpeciesTree (Fin 5)}

/-- The classes of `(a,b,(c,(d,e)))`, by permuting the labels `a ↔ e, b ↔ d` in `P₆`. -/
theorem ac1_classes_P6' (h : τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}}) :
    cls_leastClass τ = {5, 6, 8, 9, 11, 12} ∧ cls_secondClass τ = {7, 10, 14, 15} :=
  cls_classes_of p78_flip (ac1_classes_P6 _ ·) h

/-! ### `P₄` versus `P₈` -/

/-- The transformed length `Z = e^{-z}` of the edge `z` of `P₈ = ((a,b):z,(c,d,e):y)`, solved from
its equations of Table 7 (`u₄ = YZ/6 - Y³Z/10` and `u₅ = Y³Z/15`): `Z² = (6u₄ + 9u₅)³/(15u₅)`. -/
noncomputable def ac1_solveZ (τ : SpeciesTree (Fin 5)) : ℝ :=
  √((6 * u τ 4 + 9 * u τ 5) ^ 3 / (15 * u τ 5))

/-- `Z = e^{-z} < 1` for `P₈`. -/
theorem ac1_P8_Z (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) :
    ac1_solveZ τ = exp (-τ.length {0, 1}) := by
  have := (exp_pos (-τ.length {2, 3, 4})).ne'
  rw [ac1_solveZ, ← Real.sqrt_sq (exp_pos _).le]
  congr 1
  msc_rw h
  field_simp
  ring

theorem ac1_P8_lt (h : τ.clusters = hierarchyOf {{0, 1}, {2, 3, 4}}) : ac1_solveZ τ < 1 :=
  ac1_P8_Z h ▸ (five_exp_bounds h {0, 1}).2

/-- `Z = 1` for `P₄ = ((c,d,e):y,a,b)`. -/
theorem ac1_P4_Z (h : τ.clusters = hierarchyOf {{2, 3, 4}}) : ac1_solveZ τ = 1 := by
  have := (exp_pos (-τ.length {2, 3, 4})).ne'
  rw [ac1_solveZ, ← Real.sqrt_one]
  congr 1
  msc_rw h
  field_simp
  ring

/-! ### The balanced trees versus `P₆` -/

/-- `Z = e^{-z}` solved from the equations (11) of the balanced tree `(((a,b):x,c):y,(d,e):z)`:
by equation (7), `XYZ = 6u₅ + 9u₇` and `XY³Z = 15u₇`, so `Y⁻² = (2u₅ + 3u₇)/(5u₇)`; and
`YZ = 3u₂ + 3u₅ + 9u₇`. -/
noncomputable def ac2_solveZ (u₂ u₅ u₇ : ℝ) : ℝ :=
  (3 * u₂ + 3 * u₅ + 9 * u₇) * √((2 * u₅ + 3 * u₇) / (5 * u₇))

theorem ac2_solveZ_eq {u₂ u₅ u₇ X Y Z : ℝ} (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (h₂ : u₂ = 1 / 3 * Y * Z - 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z)
    (h₅ : u₅ = 1 / 6 * X * Y * Z - 1 / 10 * X * Y ^ 3 * Z) (h₇ : u₇ = 1 / 15 * X * Y ^ 3 * Z) :
    ac2_solveZ u₂ u₅ u₇ = Z := by
  subst h₂ h₅ h₇
  rw [ac2_solveZ, show (2 * _ + 3 * _) / (5 * _) = Y⁻¹ ^ 2 by field_simp; ring, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- The balanced tree versus `P₆`: solving the equations of the balanced tree for `Z` gives
`Z < 1` for `(((a,b):x,c):y,(d,e):z)` and `Z = 1` for `P₆ = (((a,b):x,c):y,d,e)`; likewise for
`((a,b):z,(c,(d,e):x):y)` and `(a,b,(c,(d,e):x):y)`, with the labels permuted. -/
theorem ac2_Z : (τ.clusters = balanced5 → ac2_solveZ (u τ 2) (u τ 5) (u τ 7) < 1) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {0, 1, 2}} → ac2_solveZ (u τ 2) (u τ 5) (u τ 7) = 1) ∧
    (τ.clusters = hierarchyOf {{0, 1}, {3, 4}, {2, 3, 4}} →
      ac2_solveZ (u τ 13) (u τ 15) (u τ 9) < 1) ∧
    (τ.clusters = hierarchyOf {{3, 4}, {2, 3, 4}} → ac2_solveZ (u τ 13) (u τ 15) (u τ 9) = 1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [balanced5] at h
    obtain ⟨z0, z1⟩ := five_exp_bounds h {3, 4}
    rwa [ac2_solveZ_eq (exp_pos (-τ.length {0, 1})) (exp_pos (-τ.length {0, 1, 2})) z0
      (by msc h) (by msc h) (by msc h)]
  · exact ac2_solveZ_eq (exp_pos (-τ.length {0, 1})) (exp_pos (-τ.length {0, 1, 2})) one_pos
      (by msc h) (by msc h) (by msc h)
  · obtain ⟨z0, z1⟩ := five_exp_bounds h {0, 1}
    rwa [ac2_solveZ_eq (exp_pos (-τ.length {3, 4})) (exp_pos (-τ.length {2, 3, 4})) z0
      (by msc h) (by msc h) (by msc h)]
  · exact ac2_solveZ_eq (exp_pos (-τ.length {3, 4})) (exp_pos (-τ.length {2, 3, 4})) one_pos
      (by msc h) (by msc h) (by msc h)

/-! ### The rootings of `U5 0`, `U5 1` and `U5 2` -/

section Binary

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option synthInstance.maxSize 1000 in
/-- The seven binary rootings of `U5 2` are binary hierarchies. -/
theorem ac2_binaryRootings_isBinary : ∀ H ∈ binaryRootings5, ∀ A ∈ H, 2 ≤ #A →
    ∃ B ∈ H, ∃ C ∈ H, Disjoint B C ∧ B ∪ C = A := by
  decide +kernel

end Binary

theorem ac2_isBinary {H} (h : τ.clusters = H) (hH : H ∈ binaryRootings5 := by decide +kernel) :
    τ.IsBinary :=
  ac2_binaryRootings_isBinary _ (h ▸ hH)

set_option maxHeartbeats 4000000 in
/-- Appendix C: two rootings of `U5 k` with the same unrooted gene tree distribution have the same
rooted metric tree. Two different rootings have different classes of gene trees, or differ in the
solved `Z`; two binary rootings are handled by Proposition 8; the branch lengths of the nonbinary
rootings are solved from Table 7. -/
theorem appC_rootings {τ τ' : SpeciesTree (Fin 5)} {k : ℕ} (hk : k ∈ ({0, 1, 2} : Finset ℕ))
    (hR : τ.clusters ∈ rootings5 k) (hR' : τ'.clusters ∈ rootings5 k)
    (hd : τ.unrootedDist id = τ'.unrootedDist id) : τ.SameRootedMetricTree τ' := by
  have hL := cls_leastClass_congr hd
  have hS := cls_secondClass_congr hd
  have hu := cls_u_congr hd
  have hZ : (ac1_solveZ τ < 1 ↔ ac1_solveZ τ' < 1) ∧
      (ac2_solveZ (u τ 2) (u τ 5) (u τ 7) < 1 ↔ ac2_solveZ (u τ' 2) (u τ' 5) (u τ' 7) < 1) ∧
      (ac2_solveZ (u τ 13) (u τ 15) (u τ 9) < 1 ↔ ac2_solveZ (u τ' 13) (u τ' 15) (u τ' 9) < 1) := by
    simp only [ac1_solveZ, hu, iff_self, and_self]
  generalize h : τ.clusters = R at hR
  generalize h' : τ'.clusters = R' at hR'
  simp only [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl | rfl <;>
    simp only [rootings5, binaryRootings5, ← caterpillar5.eq_1, ← balanced5.eq_1, ← pseudocaterpillar5.eq_1,
      mem_insert, mem_singleton] at hR hR' <;>
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hR' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [h, h', ac1_classes_P1, ac1_classes_0_1, ac1_classes_0_2, ac1_classes_0_3,
      ac1_classes_0_4, ac1_classes_0_5, ac1_classes_P2, ac1_classes_P4, ac1_classes_P8,
      ac1_classes_1_3, ac1_classes_1_4, ac1_classes_1_5, ac1_classes_1_6, ac1_classes_1_7,
      caterpillar_extremeClasses, balanced_extremeClasses, pseudocaterpillar_minClass,
      p78_classes_cat1, p78_classes_cat2, p78_classes_cat3, p78_classes_bal1, ac1_classes_P5,
      ac1_classes_P6, ac1_classes_P6', ac1_P8_lt, ac1_P4_Z, ac2_Z, lt_self_iff_false, true_iff, iff_true, false_and, and_false] at hL hS hZ <;>
    first
    | exact absurd hL (by decide)
    | exact absurd hS (by decide)
    | exact proposition8 (Fintype.card_fin 5) τ τ' (ac2_isBinary h) (ac2_isBinary h') hd
    | refine five_sameRootedMetricTree_of_lengths h h' ?_
      simp only [mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
      msc_have h
      msc_have h'
      first
      | exact five_length_eq 6 (by norm_num) one_pos (by linarith [hu 1, hu 2])
      | exact five_length_eq 1 one_ne_zero one_pos (by linarith [hu 4])
      | exact five_length_eq 3 (by norm_num) one_pos (by linarith [hu 5])
      | exact ⟨five_length_eq 1 one_ne_zero one_pos
          (by linarith [hu 2, hu 3, hu 4, hu 5, hu 7, hu 9, hu 13, hu 15]),
        five_length_eq 1 one_ne_zero one_pos
          (by linarith [hu 2, hu 3, hu 4, hu 5, hu 7, hu 9, hu 13, hu 15])⟩
      | -- `P₈`: `Z` is solved by `ac1_solveZ`, then `u₅ = Y³Z/15` gives `Y`
        have hz : τ.length {0, 1} = τ'.length {0, 1} := by
          have e : ac1_solveZ τ = ac1_solveZ τ' := by rw [ac1_solveZ, ac1_solveZ, hu 4, hu 5]
          rw [ac1_P8_Z h, ac1_P8_Z h'] at e
          exact neg_inj.1 (Real.exp_injective e)
        refine ⟨hz, ?_⟩
        simp only [hz] at *
        exact five_length_eq 3 (by norm_num) (exp_pos (-τ'.length {0, 1})) (by linarith [hu 5])
      | -- `P₉`: `u₁ - u₅` gives `Y`, then `u₅` gives `Z`; `P₇`: `u₈ + 4u₄` (or `u₅`, `u₆`)
        -- gives `X`, then `u₄` gives `Z`
        refine (and_iff_left_of_imp fun hy => ?_).2
          (five_length_eq 1 one_ne_zero one_pos (by linarith [hu 1, hu 4, hu 5, hu 6, hu 8]))
        simp only [hy] at *
        first
        | exact five_length_eq 6 (by norm_num) (pow_pos (exp_pos (-τ'.length {2, 3, 4})) 3)
            (by linarith [hu 5])
        | exact five_length_eq 6 (by norm_num) (exp_pos (-τ'.length {0, 1})) (by linarith [hu 4])
    | exact five_sameRootedMetricTree_of_lengths h h' (by simp)

/-- Appendix C: on five taxa, two species trees, binary or not, with the same unrooted gene tree
distribution have the same rooted metric tree. -/
theorem appC_sameRootedMetricTree {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 5) (σ σ' : SpeciesTree X)
    (h : σ.unrootedDist id = σ'.unrootedDist id) : σ.SameRootedMetricTree σ' := by
  -- the unrooted species tree is determined (Corollary 6, extended to nonbinary trees); name the
  -- taxa so that it is `U5 0`, `U5 1` or `U5 2`
  have hU := sameUnrootedMetricTree_of_unrootedDist_eq σ σ' h
  obtain ⟨e, k, hk, he⟩ := exists_equiv_unroot_eq_U5 hX σ
  have he' : unroot (σ'.relabel e.symm).clusters = U5 k := by
    rwa [SpeciesTree.relabel_clusters, unroot_relabelFamily, ← hU.1, ← unroot_relabelFamily]
  rw [← SpeciesTree.sameRootedMetricTree_relabel_iff σ σ' e.symm]
  exact appC_rootings hk (classify_mem_rootings5 _ k hk he) (classify_mem_rootings5 _ k hk he')
    ((SpeciesTree.unrootedDist_relabel_eq_iff σ σ' e.symm).2 h)

end ADR11
