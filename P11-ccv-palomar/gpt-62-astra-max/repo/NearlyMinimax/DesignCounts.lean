module

public import NearlyMinimax.LowSmoothnessVariance

@[expose] public section

/-! # IID design patch counts

Patch membership is measured under an actual product probability measure
on the design sample. The binomial law is derived by partitioning that
sample space into disjoint membership cells.
-/

namespace NearlyMinimax

open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

section
variable {α : Type*} {n : ℕ} (A : Set α) (s : Finset (Fin n)) (x : Fin n → α)

/-- Number of iid design observations falling in a patch. -/
def designPatchCount : ℕ :=
  (Finset.univ.filter fun i => x i ∈ A).card

/-- The cell with precisely the observation indices in `s` inside the patch. -/
def designMembershipCell : Set (Fin n → α) :=
  Set.pi Set.univ (fun i => if i ∈ s then A else Aᶜ)

theorem design_patch_count_le :
    designPatchCount A x ≤ n := by
  unfold designPatchCount
  simpa using Finset.card_le_card (Finset.filter_subset (fun i => x i ∈ A) Finset.univ)

theorem design_membership_cell_iff :
    x ∈ designMembershipCell A s ↔ ∀ i, x i ∈ A ↔ i ∈ s := by
  grind [designMembershipCell]

end

section
variable {α : Type*} (n : ℕ) (A : Set α)

theorem design_membership_cell_measurable [MeasurableSpace α]
    {n : ℕ} {A : Set α} (hA : MeasurableSet A) (s : Finset (Fin n)) :
    MeasurableSet (designMembershipCell A s) := by
  apply MeasurableSet.pi Set.countable_univ
  aesop

theorem design_membership_cells_disjoint :
    Pairwise (fun s t : Finset (Fin n) => Disjoint (designMembershipCell A s) (designMembershipCell A t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hs ht
  apply hst
  ext i
  exact ((design_membership_cell_iff A s x).mp hs i).symm.trans
    ((design_membership_cell_iff A t x).mp ht i)

/-- The count event is a disjoint union of cells indexed by subsets of its count. -/
theorem design_patch_count_fiber (k : ℕ) :
    {x | designPatchCount A x = k} =
      ⋃ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, designMembershipCell A s := by
  ext x
  constructor
  · intro hx
    let s  := Finset.univ.filter fun i => x i ∈ A
    apply Set.mem_iUnion.mpr
    refine ⟨s, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · aesop
    · rw [design_membership_cell_iff]
      simp [s]
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.mp hx
    have hfilter : (Finset.univ.filter fun i => x i ∈ A) = s := by
      ext i
      simpa using (design_membership_cell_iff A s x).mp hxs i
    change (Finset.univ.filter fun i => x i ∈ A).card = k
    grind

end

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Membership cells have the product Bernoulli probabilities dictated by
independence under the iid design product measure. -/
theorem iid_design_membership_cell_measure [IsProbabilityMeasure μ] (n : ℕ) (A : Set α)
    (s : Finset (Fin n)) :
    (Measure.pi (fun _ => μ)) (designMembershipCell A s) =
      (μ A) ^ s.card * (μ Aᶜ) ^ (n - s.card) := by
  rw [designMembershipCell, Measure.pi_pi]
  simp [apply_ite]
  rw [Finset.prod_ite]
  have hin : (Finset.univ.filter fun i => i ∈ s) = s := by simp
  have hout : (Finset.univ.filter fun i => i ∉ s) = Finset.univ \ s := by ext i; simp
  rw [hin, hout]
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ s)]

/-- Exact binomial count law, in real probabilities, for an arbitrary measurable
patch under an arbitrary iid design probability measure. -/
theorem iid_design_patch_count_probability [IsProbabilityMeasure μ] (n : ℕ) {A : Set α} (hA : MeasurableSet A) (k : ℕ) :
    (Measure.pi (fun _ => μ)).real {x : Fin n → α | designPatchCount A x = k} =
      binomialCountMass n (μ.real A) k := by
  rw [measureReal_def, design_patch_count_fiber, measure_biUnion_finset]
  · rw [ENNReal.toReal_sum (fun s _ => measure_ne_top _ _)]
    have hcell (s : Finset (Fin n)) (hs : s ∈ Finset.univ.powersetCard k) :
        ((Measure.pi (fun _ => μ)) (designMembershipCell A s)).toReal =
          (μ.real A) ^ k * (1 - μ.real A) ^ (n - k) := by
      rw [iid_design_membership_cell_measure, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, (Finset.mem_powersetCard.mp hs).2]
      have hcompl : μ.real Aᶜ = 1 - μ.real A := by
        simpa using measureReal_compl hA (μ := μ)
      solve_by_elim
    rw [Finset.sum_congr rfl hcell]
    simp [binomialCountMass] <;> ring
  · solve_by_elim [design_membership_cells_disjoint]
  · solve_by_elim [design_membership_cell_measurable]

/-- The patch count is a measurable random variable. -/
theorem design_patch_count_measurable
    (n : ℕ) {A : Set α} (hA : MeasurableSet A) : Measurable (designPatchCount (n := n) A) := by
  have heq : designPatchCount A =
      (fun x => ∑ i : Fin n, if x i ∈ A then 1 else 0) := by
    funext x
    exact Finset.card_filter _ _
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (hA.preimage (measurable_pi_apply i)) measurable_const measurable_const

/-- Every finite function of the actual patch count integrates against its
binomial law. This connects the counting estimate to the iid design measure. -/
theorem iid_design_count_integral [IsProbabilityMeasure μ] (n : ℕ) {A : Set α} (hA : MeasurableSet A)
    (e : ℕ → ℝ) :
    (∫ x, e (designPatchCount A x) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∑ k ∈ Finset.range (n + 1), binomialCountMass n (μ.real A) k * e k := by
  have hm k : MeasurableSet {x | designPatchCount A x = k} :=
    (measurableSet_singleton k).preimage (design_patch_count_measurable n hA)
  have hdecomp (x : Fin n → α) : e (designPatchCount A x) =
      ∑ k ∈ Finset.range (n + 1),
        ({x | designPatchCount A x = k}).indicator (fun _ => e k) x := by
    symm
    calc
      _ = _ := by
        apply Finset.sum_eq_single (designPatchCount A x)
        · aesop
        · intro hn
          grind [design_patch_count_le A x]
      _ = _ := by simp
  rw [(funext hdecomp), integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_indicator_const (e k) (hm k), iid_design_patch_count_probability μ n hA k]
    rfl
  · intro k _
    exact (integrable_const (e k)).indicator (hm k)

/-- Integration of a genuine iid patch count gives the quadratic collision
energy bound, without assuming a binomial count law as a hypothesis. -/
theorem iid_design_collision_energy_bound
    {μ : Measure α} [IsProbabilityMeasure μ] {n : ℕ} {A : Set α} (hA : MeasurableSet A)
    (C η : ℝ) (e : ℕ → ℝ) (hC : 0 ≤ C) (hmean : n * μ.real A ≤ 1)
    (he0 : e 0 = 0) (he1 : e 1 = 0) (he : ∀ k, 2 ≤ k → e k ≤ C ^ k * η ^ 4) :
    (∫ x, e (designPatchCount A x) ∂Measure.pi (fun _ : Fin n => μ)) ≤
      C ^ 2 * Real.exp C * η ^ 4 * (n * μ.real A) ^ 2 := by
  rw [iid_design_count_integral μ n hA e]
  exact binomial_collision_energy_bound measureReal_nonneg
    measureReal_le_one hC hmean he0 he1 he

end

end NearlyMinimax
