module

public import ADR11.MSC.Basic

@[expose] public section

namespace ADR11

open Finset MonoidAlgebra

@[simp] theorem pushD_comp {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : β → γ) (p : α → ℝ) (c : γ) :
    pushD g (pushD f p) c = pushD (g ∘ f) p c := by
  simpa only [mul_ite, mul_one, mul_zero, pushD, Function.comp_apply] using
    pushD_test f p (fun y => if g y = c then 1 else 0)

@[simp] theorem pushD_id {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) : pushD id p = p := by
  funext a
  simp [pushD]

@[simp] theorem pushD_equiv {α β : Type*} [Fintype α] [DecidableEq β]
    (e : α ≃ β) (p : α → ℝ) (b : β) : pushD e p b = p (e.symm b) := by
  classical
  simp [pushD, ← e.eq_symm_apply]

open scoped Matrix in
theorem pushD_bind {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : β → γ) (p : α → ℝ) (q : Matrix α β ℝ) (c : γ) :
    pushD f (p ᵥ* q) c = ∑ a, p a * pushD f (q a) c := by
  simp_rw [pushD, Matrix.vecMul, dotProduct, mul_sum, mul_ite, mul_zero, ite_sum_zero]
  exact sum_comm

section Lumping

open scoped Matrix
variable {L M : Type*} [Fintype L] [DecidableEq L] [Fintype M] [DecidableEq M]
variable (r : ClusterFamily L → ClusterFamily M)
variable (hQ : ∀ {F}, IsForest F → ∀ u : ClusterFamily M → ℝ,
  ∑ G, kingmanGenerator F G * u (r G) = ∑ G, kingmanGenerator (r F) G * u G)

include hQ

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

open Filter in
/-- The same intertwining applies to each branch and to the absorbing root. -/
theorem population_push {F : ClusterFamily L} (hF : IsForest F) (hR : IsForest (r F))
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} {A : Finset X} {B : Finset Y}
    (hroot : B = univ ↔ A = univ) (hlen : len' B = len A) :
    pushD r (populationKernel len A F) = populationKernel len' B (r F) := by
  simp only [populationKernel, hroot, hlen]
  funext G
  split_ifs
  · have h : Tendsto (fun t => pushD r (kingmanTransition t F) G) atTop
        (nhds (pushD r (kingmanAbsorption F) G)) := by
      apply tendsto_finsetSum _
      intro H _
      split_ifs
      · exact tendsto_kingmanTransition hF H
      · exact tendsto_const_nhds
    simp_rw [transition_push kingmanGenerator r hQ hF] at h
    exact tendsto_nhds_unique h (tendsto_kingmanTransition hR G)
  · exact transition_push kingmanGenerator r hQ hF _ G

end Lumping

namespace Independent

/-- Independent histories combine by union of their forests. -/
scoped instance unionMonoid {β : Type*} [DecidableEq β] : CommMonoid (Finset β) where
  one := ∅
  mul := (· ∪ ·)
  mul_assoc := union_assoc
  one_mul := empty_union
  mul_one := union_empty
  mul_comm := union_comm

@[simp] theorem mul_def {β : Type*} [DecidableEq β] (F G : Finset β) : F * G = F ∪ G := rfl
/-- Express a distribution as an element of the monoid algebra, so multiplication combines
independent outcomes. The coefficients are allowed to be signed. -/
noncomputable def law {α : Type*} [Finite α] (p : α → ℝ) : MonoidAlgebra ℝ α :=
  .ofCoeff (Finsupp.equivFunOnFinite.symm p)

theorem law_injective {α : Type*} [Finite α] : Function.Injective (law (α := α)) :=
  MonoidAlgebra.ofCoeff_injective.comp Finsupp.equivFunOnFinite.symm.injective

theorem law_sum {α : Type*} [Fintype α] (p : α → ℝ) : law p = ∑ a, single a (p a) := by
  classical
  ext a
  simp [law, coeff_sum, Finsupp.single_apply, sum_ite_eq']

theorem law_push {α β : Type*} [Fintype α] [Finite β] [DecidableEq β] (f : α → β) (p : α → ℝ) :
    law (pushD f p) = mapDomain f (law p) := by
  classical
  rw [law_sum p]
  ext b
  simp [law, pushD, Finsupp.mapDomain_finsetSum, coeff_sum, Finsupp.single_apply, eq_comm]

private theorem prod_eq_sup {ι β : Type*} [DecidableEq β] (s : Finset ι) (f : ι → Finset β) :
    ∏ i ∈ s, f i = s.sup f := by
  rfl

theorem law_entering {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]
    (H : ClusterFamily X) (len : Finset X → ℝ) (s : L → X) (A : Finset X) :
    law (enteringDist H len s A) = single (sampledForest s A) 1 *
      ∏ B ∈ childClusters H A, law (forestDist H len s B) := by
  classical
  rw [← prod_coe_sort]
  conv_rhs => arg 2; simp only [law_sum]
  rw [Fintype.prod_sum, mul_sum]
  simp_rw [prod_single, single_mul_single, prod_eq_sup, one_mul]
  ext G
  simp [law, coeff_sum, enteringDist, pushD, Finsupp.single_apply, union_comm]

section Transport

variable {X Y L M : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype L] [DecidableEq L] [Fintype M] [DecidableEq M]

set_option backward.isDefEq.respectTransparency false in
/-- A map on forest states that respects union and commutes with the population kernels
also commutes with the within-species-tree recursion. -/
theorem forestDist_push (f : ClusterFamily L →* ClusterFamily M) (g : Finset X ↪ Finset Y)
    {H : ClusterFamily X} {H' : ClusterFamily Y} (hH : IsHierarchy H)
    {len : Finset X → ℝ} {len' : Finset Y → ℝ} {s : L → X} {s' : M → Y}
    (hs : ∀ A, f (sampledForest s A) = sampledForest s' (g A))
    (hc : ∀ A ∈ H, childClusters H' (g A) = (childClusters H A).image g ∨
      law (pushD f (enteringDist H len s A)) = law (enteringDist H' len' s' (g A)))
    (hk : ∀ A ∈ H, ∀ F, IsForest F → pushD f (populationKernel len A F) = populationKernel len' (g A) (f F))
    {A : Finset X} (hA : A ∈ H) :
    pushD f (forestDist H len s A) = forestDist H' len' s' (g A) := by
  induction A using Finset.strongInduction with
  | H A ih =>
    have E : law (pushD f (enteringDist H len s A)) = law (enteringDist H' len' s' (g A)) := by
      rcases hc A hA with c | h
      · rw [law_push, law_entering, law_entering, c, prod_image g.injective.injOn]
        change mapDomainRingHom ℝ f _ = _
        rw [map_mul, map_prod]
        simp only [mapDomainRingHom_apply, mapDomain_single, hs]
        congr 1
        exact prod_congr rfl fun B hB => by rw [← law_push, ih B (child_lt hB) (child_mem hB)]
      · exact h
    funext G
    simp only [forestDist_eq, Matrix.vecMul, dotProduct, pushD_bind, ← law_injective E, pushD_test]
    exact sum_mul_congr fun F _ hF => congrFun (hk A hA F (enteringDist_support hH len s hF).1) G

end Transport

theorem sample_mul_law {β : Type*} [Fintype β] [DecidableEq β] (S : Finset β) (p : Finset β → ℝ)
    (h : ∀ F, p F ≠ 0 → S ⊆ F) : single S 1 * law p = law p := by
  simp_rw [law_sum, mul_sum, single_mul_single, mul_def, one_mul]
  exact sum_congr rfl fun F _ => by by_cases hF : p F = 0 <;> simp [hF, union_eq_right.2 ∘ h F]

variable {X L : Type*} [Fintype X] [DecidableEq X] [Fintype L] [DecidableEq L]

/-- With at most one lineage, the forest cannot change. -/
theorem law_forestDist_small {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (hk : #(samplesIn s A) ≤ 1) :
    law (forestDist H len s A) = single (sampledForest s A) 1 := by
  have hs (G : ClusterFamily L) (hn : G ≠ sampledForest s A) : forestDist H len s A G = 0 := by
    by_contra hp
    obtain ⟨hG, hsub, hlin⟩ := forestDist_support hH len s hp
    apply hn (Subset.antisymm (fun C hC => ?_) hsub)
    have hC' : C ⊆ samplesIn s A := hlin ▸ subset_lineages hC
    have := (card_le_card hC').trans hk
    have := (hG.1 C hC).card_pos
    obtain ⟨l, rfl⟩ := card_eq_one.1 (by omega : #C = 1)
    exact mem_sampledForest.2 ⟨l, mem_samplesIn.1 (hC' (by simp)), rfl⟩
  have hm := forestDist_sum hH len s A
  rw [sum_eq_single_of_mem _ (mem_univ _) (fun G _ => hs G)] at hm
  rw [law_sum, sum_eq_single_of_mem _ (mem_univ _) (fun G _ hn => by simp [hs G hn]), hm]

/-- If the child populations each have at most one lineage, only the population above `A`
can affect the sampled forest. Includes the case with no children. -/
theorem entering_of_small_children {H : ClusterFamily X} (hH : IsHierarchy H) (len : Finset X → ℝ)
    (s : L → X) {A : Finset X} (h : ∀ B ∈ childClusters H A, #(samplesIn s B) ≤ 1) :
    law (enteringDist H len s A) = single (sampledForest s A) 1 := by
  rw [law_entering, prod_congr rfl (fun B hB => law_forestDist_small hH len s (h B hB)),
    prod_single, prod_eq_sup, single_mul_single, prod_const_one, one_mul, mul_def,
    union_eq_left.2 (Finset.sup_le fun B hB => sampledForest_mono (child_lt hB).subset)]

end Independent
end ADR11
