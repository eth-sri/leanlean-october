module
public import ADR11.Computation.Quartet
public import ADR11.Trees.Classify
public import ADR11.Trees.Metric

/-! Write `aᵢ = exp(-tᵢ)` for the three possible internal splits of a
quartet (length zero when absent). The probability of quartet `i` is
`1 - aᵢ + a₁a₂a₃/3`. At most one `aᵢ` differs from one. -/
@[expose] public section
namespace ADR11.Quartet
open Finset Real Skeleton _root_.ADR11.Computation
noncomputable section

def weight (σ : Tree) (i : Fin 3) := exp (-σ.unrootedLength (decC 4 (side i)))
def background (a : Fin 3 → ℝ) := a 0 * a 1 * a 2 / 3
def output (a : Fin 3 → ℝ) (i : Fin 3) := 1 - a i + background a

theorem sides (σ : Tree) (i : Fin 3) : weight σ i = Sparse.branch σ (side i) * Sparse.branch σ (15-side i) := by
  have e := (by decide : ∀ i : Fin 3, decC 4 (15-side i) = (decC 4 (side i))ᶜ) i
  simp [weight,Sparse.branch,e,← exp_add,← neg_add,σ.edge_add_compl]

theorem at_gene (σ : Tree) (i : Fin 3) : σ.unrootedDist id (gene i) = output (weight σ) i := by
  rw [Sparse.likelihood σ (checked _ (full_mem σ) i)]
  simp [Sparse.eval,Sparse.mon,polynomial,output,background,pairs,key,sides]; ring

attribute [-instance] Fintype.decidableForallFintype in
private theorem elsewhere (σ : Tree) (T : Family 4) (hT : ∀ i, T ≠ gene i) : σ.unrootedDist id T = 0 := by
  obtain ⟨k,hk⟩ := (by decide +kernel : ∀ s ∈ full 4, ∃ k : Fin 3, ∀ i, i ≠ k → decC 4 (side i) ∉ unroot s) _ (full_mem σ)
  have one (i) (h : i ≠ k) : weight σ i = 1 := by simp [weight,SpeciesTree.split_zero (hk i h)]
  have mass : ∑ T ∈ univ.image gene, σ.unrootedDist id T = 1 := by
    rw [sum_image (by decide : Function.Injective gene).injOn,Fin.sum_univ_three]
    fin_cases k <;> simp +decide [at_gene,output,background,one] <;> ring
  have le := sum_le_univ_sum_of_nonneg (s := insert T (univ.image gene)) (Challenge.unrootedDist_nonneg σ id)
  rw [sum_insert (by simpa [eq_comm] using hT),mass,Challenge.unrootedDist_sum] at le
  linarith [Challenge.unrootedDist_nonneg σ id T]

attribute [-instance] Fintype.decidableForallFintype in
theorem weight_eq_iff (σ τ : Tree) :
    σ.unrootedDist id = τ.unrootedDist id ↔ weight σ = weight τ := by
  constructor
  · intro h
    obtain ⟨i,hi,hj⟩ := (by decide +kernel : ∀ s ∈ full 4, ∀ r ∈ full 4, ∃ i : Fin 3,
      decC 4 (side i) ∉ unroot s ∧ decC 4 (side i) ∉ unroot r) _ (full_mem σ) _ (full_mem τ)
    have one (μ : Tree) (hm : decC 4 (side i) ∉ unroot μ.clusters) : weight μ i = 1 := by simp [weight,SpeciesTree.split_zero hm]
    have vals (j : Fin 3) := (at_gene σ j).symm.trans ((congrFun h _).trans (at_gene τ j))
    have bg := vals i; simp [output, one σ hi,one τ hj] at bg
    funext j; simpa [output,bg] using vals j
  · intro h; funext T; by_cases e : ∃ i, T = gene i
    · obtain ⟨i,rfl⟩ := e; rw [at_gene,at_gene,h]
    · push Not at e; rw [elsewhere σ T e,elsewhere τ T e]

attribute [-instance] Fintype.decidableForallFintype in
private theorem metric (σ τ : Tree) : weight σ = weight τ ↔ σ.SameUnrootedMetricTree τ := by
  constructor
  · intro h
    have lens (A : Finset (Fin 4)) (hA : #A = 2) : σ.unrootedLength A = τ.unrootedLength A := by
      obtain ⟨i,hi | hi⟩ := (by decide : ∀ A ∈ (univ : Family 4), #A = 2 → ∃ i : Fin 3,
        A = decC 4 (side i) ∨ Aᶜ = decC 4 (side i)) A (mem_univ _) hA
      all_goals simpa [weight,← hi, SpeciesTree.unrootedLength_compl] using congrFun h i
    refine ⟨?_,fun A _ ha hb => lens A (by rw [card_compl] at hb; simp at hb; omega)⟩
    ext A; by_cases h2 : #A = 2
    · rw [SpeciesTree.split_pos, SpeciesTree.split_pos, lens _ h2]
    · have trivial (μ : Tree) : A ∈ unroot μ.clusters ↔ #A = 1 ∨ #A = 3 := by
        exact (by decide +kernel : ∀ s ∈ full 4, ∀ A ∈ (univ : Family 4), #A ≠ 2 → (A ∈ unroot s ↔ #A = 1 ∨ #A = 3)) _ (full_mem μ) A (mem_univ _) h2
      rw [trivial,trivial]
  · intro h; funext i; unfold weight; rw [SpeciesTree.split_eq h] <;> fin_cases i <;> decide

end
end ADR11.Quartet
namespace ADR11

theorem Challenge.proposition11_theorem9_four {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 4) (σ τ : SpeciesTree X) :
    σ.unrootedDist id = τ.unrootedDist id ↔ σ.SameUnrootedMetricTree τ := by
  let e := Fintype.equivFinOfCardEq hX
  rw [← SpeciesTree.unrootedDist_relabel_eq_iff σ τ e, Quartet.weight_eq_iff, Quartet.metric,
    SpeciesTree.sameUnrootedMetricTree_relabel_iff]

end ADR11
