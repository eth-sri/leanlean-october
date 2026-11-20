module

public import QPBT.Upstream
public import MIPStarRE.LDT.Basic.DistributionAvg

/-! # Operations on finite distributions

Finite distributions support products, convex mixtures, dependent binds,
normalized restrictions, and push-forwards.  Uniform laws are preserved by
bijections and balanced maps, their product projections are uniform, and
dependent uniform sampling agrees with push-forward from a product.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Summing on the range of a finite embedding is summing over its domain. -/
theorem sum_filter_range_embedding {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] (e : A ↪ B) [DecidablePred (· ∈ Set.range e)] (f : B → R) :
    (∑ b ∈ Finset.univ.filter (fun b => b ∈ Set.range e), f b) = ∑ a, f (e a) := by
  rw [show Finset.univ.filter (fun b => b ∈ Set.range e) = Finset.univ.map e by ext; simp,
    Finset.sum_map]

/-- Restricting a sum of nonnegative terms along an embedding decreases it. -/
theorem sum_embedding_le {A B R : Type*} [Fintype A] [Fintype B]
    [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (e : A ↪ B) (f : B → R) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  rw [← Finset.sum_map Finset.univ e f]
  exact Finset.sum_le_univ_sum_of_nonneg hf

/-- The product of two finite distributions, a formalization-only auxiliary
used by the sandwich construction; blueprint `lem:ld-sandwich`,
paper `06_nonlocal_games_and_mipstar.tex:465-501`. -/
noncomputable def Distribution.prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) : Distribution (α × β) where
  support := μ.support.product ν.support
  weight p := μ.weight p.1 * ν.weight p.2
  nonnegative p := mul_nonneg (μ.nonnegative p.1) (ν.nonnegative p.2)
  outsideSupport p hp := by
    by_cases hμ : p.1 ∈ μ.support
    · have hν : p.2 ∉ ν.support := by
        intro h
        simp_all
      simp [ν.outsideSupport p.2 hν]
    · simp [μ.outsideSupport p.1 hμ]

/-- An average over a product is the iterated average. -/
theorem Distribution.avgOver_prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (f : α × β → ℝ) :
    avgOver (Distribution.prod μ ν) f = avgOver μ fun a => avgOver ν fun b => f (a, b) := by
  simp only [avgOver, Distribution.prod, Finset.mul_sum, mul_assoc]
  exact Finset.sum_product' _ _ fun a b => μ.weight a * (ν.weight b * f (a, b))

/-- The product of two probability distributions is a probability
distribution; blueprint `lem:ld-sandwich`, paper
`06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem Distribution.prod_isProbability {α β : Type*}
    [DecidableEq α] [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).IsProbability := by
  suffices avgOver (Distribution.prod μ ν) (fun _ => 1) = 1 by
    simpa only [avgOver_const, mul_one, Distribution.IsProbability, Distribution.totalWeight] using this
  simp only [Distribution.avgOver_prod, avgOver_const_of_isProbability, hμ, hν]

/-- The convex mixture with a coefficient in `[0,1]`, as used for
the equal mixture in blueprint
`def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
noncomputable def Distribution.mix {α : Type*} [DecidableEq α]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (μ ν : Distribution α) : Distribution α where
  support := μ.support ∪ ν.support
  weight a := t * μ.weight a + (1 - t) * ν.weight a
  nonnegative a := by
    exact add_nonneg
      (mul_nonneg ht0 (μ.nonnegative a))
      (mul_nonneg (sub_nonneg.mpr ht1) (ν.nonnegative a))
  outsideSupport a ha := by
    have hμ : a ∉ μ.support := fun h => ha (Finset.mem_union_left _ h)
    have hν : a ∉ ν.support := fun h => ha (Finset.mem_union_right _ h)
    simp [μ.outsideSupport a hμ, ν.outsideSupport a hν]

/-- A convex mixture of probability distributions is a probability distribution;
blueprint `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem Distribution.mix_isProbability {α : Type*} [DecidableEq α]
    (t : ℝ) (μ ν : Distribution α) (hμ : μ.IsProbability)
    (hν : ν.IsProbability) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Distribution.mix t ht0 ht1 μ ν).IsProbability := by
  have hμ_union :
      ∑ a ∈ μ.support ∪ ν.support, μ.weight a = 1 := by
    apply hμ.weight_sum_eq_one_of_subset
    intro a ha
    simp_all
  have hν_union :
      ∑ a ∈ μ.support ∪ ν.support, ν.weight a = 1 := by
    apply hν.weight_sum_eq_one_of_subset
    intro a ha
    simp_all
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.mix]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hμ_union, hν_union]
  ring

/-- The dependent bind of finite distributions used for typed question
distributions, blueprint `def:typed-cl-distributions`, paper
`07_types.tex:84-94`. -/
noncomputable def Distribution.bind {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) : Distribution β where
  support := μ.support.biUnion (fun a => (ν a).support)
  weight b := ∑ a ∈ μ.support, μ.weight a * (ν a).weight b
  nonnegative b := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonnegative a) ((ν a).nonnegative b)
  outsideSupport b hb := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : b ∉ (ν a).support := by
      intro h
      simp_all
    simp [ν a |>.outsideSupport b hnot]

/-- Formalization-only auxiliary: an average against a dependent bind is the
iterated average.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_bind {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) (f : β → ℝ) :
    avgOver (Distribution.bind μ ν) f =
      avgOver μ (fun a => avgOver (ν a) f) := by
  classical
  simp only [avgOver, Distribution.bind, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact (Finset.sum_subset (by grind) fun b _ hb => by simp [(ν a).outsideSupport b hb]).symm

/-- A dependent bind of probability distributions is a probability distribution;
blueprint
`def:typed-cl-distributions`, paper `07_types.tex:84-94`. -/
theorem Distribution.bind_isProbability {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν : α → Distribution β) (hμ : μ.IsProbability)
    (hν : ∀ a ∈ μ.support, (ν a).IsProbability) :
    (Distribution.bind μ ν).IsProbability := by
  suffices avgOver (Distribution.bind μ ν) (fun _ => 1) = 1 by
    simpa only [avgOver_const, mul_one, Distribution.IsProbability, Distribution.totalWeight] using this
  rw [avgOver_bind]
  refine (avgOver_congr_on_support μ _ (fun _ => 1) fun a ha => ?_).trans
    (avgOver_const_of_isProbability μ hμ 1)
  exact avgOver_const_of_isProbability _ (hν a ha) _

/-- Restrict a distribution to a decidable positive-mass event and normalize it,
as in blueprint
`def:ith-restricted-line`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
noncomputable def Distribution.restrict {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) : Distribution α where
  support := μ.support.filter p
  weight a := if p a then μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b else 0
  nonnegative a := by
    split
    · exact div_nonneg (μ.nonnegative a) (le_of_lt hpos)
    · rfl
  outsideSupport a ha := by
    by_cases hp : p a
    · have hμ : a ∉ μ.support := fun h => ha (Finset.mem_filter.mpr ⟨h, hp⟩)
      simp [μ.outsideSupport a hμ]
    · simp_all

/-- Restriction to a positive-mass event preserves total probability;
blueprint
`def:ith-restricted-line`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem Distribution.restrict_isProbability {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) :
    (Distribution.restrict μ p hpos).IsProbability := by
  simp only [Distribution.IsProbability, Distribution.totalWeight,
    Distribution.restrict]
  calc
    _ =
        ∑ a ∈ μ.support.filter p,
          μ.weight a / ∑ b ∈ μ.support.filter p, μ.weight b := by
      apply Finset.sum_congr rfl
      simp_all
    _ = (∑ a ∈ μ.support.filter p, μ.weight a) /
        ∑ b ∈ μ.support.filter p, μ.weight b := by
      rw [Finset.sum_div]
    _ = 1 := div_self hpos.ne'

/-! ### Push-forwards of finite and uniform distributions

The results of this section are not named in the paper.  They record the
elementary behaviour of push-forwards of finite distributions, and of uniform
distributions on finite types, that the line-point samplers of the low-degree
game and the identification of question distributions with typed conditionally
linear distributions rely on.
-/

/-- Formalization-only lemma: two finite distributions coincide as soon as
their supports and weight functions coincide.  This is the support statement
`lem:distribution-ext-support` in blueprint chapter 13. -/
theorem Distribution.ext_of_support_of_weight {α : Type*} {μ ν : Distribution α}
    (hsupport : μ.support = ν.support) (hweight : μ.weight = ν.weight) :
    μ = ν := by
  cases μ with
  | mk s w hn ho =>
    simp_all

/-- Equal supports and equal averages identify a finite distribution. The support
hypothesis is needed since support points need not have strictly positive weight. -/
theorem Distribution.ext_of_support_of_avgOver {α : Type*} {μ ν : Distribution α}
    (hs : μ.support = ν.support) (h : ∀ f : α → ℝ, avgOver μ f = avgOver ν f) : μ = ν := by
  classical
  apply Distribution.ext_of_support_of_weight hs
  funext a
  have e (D : Distribution α) : avgOver D (fun b => if b = a then 1 else 0) = D.weight a := by
    by_cases ha : a ∈ D.support
    · simp [avgOver, mul_ite, ha]
    · simp [avgOver, mul_ite, ha, D.outsideSupport a ha]
  rw [← e μ, ← e ν, h]

/-- Formalization-only lemma: successive push-forwards of a finite distribution
compose.  This is `lem:distribution-map-comp` in blueprint chapter 13. -/
theorem Distribution.map_map {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (e : α → β) (f : β → γ) :
    (μ.map e).map f = μ.map fun a => f (e a) := by
  refine Distribution.ext_of_support_of_avgOver (Finset.image_image ..) fun f' => ?_
  simp only [Distribution.avgOver_map]

/-- Formalization-only lemma: every point of a nonempty finite type carries the
reciprocal of the type's cardinality as its uniform weight.  This is
`lem:uniform-distribution-weight` in blueprint chapter 13. -/
theorem uniformDistribution_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

/-- Formalization-only lemma: a push-forward of a uniform law assigns to a point
the cardinality of its fibre divided by the cardinality of the source.  This is
`lem:uniform-map-fibre-weight` in blueprint chapter 13. -/
theorem uniformDistribution_map_weight {α γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [DecidableEq γ]
    (e : α → γ) (c : γ) :
    ((uniformDistribution α).map e).weight c =
      (((Finset.univ : Finset α).filter fun x => e x = c).card : Error) *
        (1 / (Fintype.card α : Error)) := by simp_all [Finset.sum_congr rfl fun x _ => uniformDistribution_weight_apply α x, Finset.sum_const, nsmul_eq_mul]

/-- Formalization-only lemma: a map whose fibers all have the same cardinality
pushes the uniform distribution forward to the uniform distribution.  This is
`lem:uniform-map-equal-fibers` in blueprint chapter 13. -/
theorem uniformDistribution_map_of_card_fiber {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α → β) (c : ℕ)
    (hc : ∀ b : β, ((Finset.univ : Finset α).filter fun a => e a = b).card = c) :
    (uniformDistribution α).map e = uniformDistribution β := by
  have hcpos : 0 < c := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    have hmem : a₀ ∈ (Finset.univ : Finset α).filter fun a => e a = e a₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨a₀, hmem⟩
    simp_all
  have hcard : Fintype.card α = Fintype.card β * c := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := e) (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β))
      (fun a _ => Finset.mem_univ _)
    rw [Finset.card_univ] at h
    rw [h, Finset.sum_congr rfl fun b _ => hc b]
    simp
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset α).image e = (Finset.univ : Finset β)
    ext b
    simp
    have hne : ((Finset.univ : Finset α).filter fun a => e a = b).Nonempty := by
      rw [← Finset.card_pos, hc]
      assumption
    grind
  · funext b
    have hbeta : (Fintype.card β : Error) ≠ 0 := by
      simp
    have hc' : (c : Error) ≠ 0 := by exact_mod_cast hcpos.ne'
    simp_all [uniformDistribution_weight_apply, Finset.sum_const, nsmul_eq_mul]

/-- Formalization-only lemma: relabelling along a bijection preserves
uniformity.  This is `lem:uniform-map-equivalence` in blueprint chapter 13. -/
theorem uniformDistribution_map_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] (E : α ≃ β) :
    (uniformDistribution α).map E = uniformDistribution β := by
  refine uniformDistribution_map_of_card_fiber _ 1 fun b => ?_
  have hfilter :
      ((Finset.univ : Finset α).filter fun a => E a = b) = {E.symm b} := by
    ext a
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [hfilter]
  simp

/-- Formalization-only lemma: the first marginal of the uniform distribution on
a product is uniform.  This is `lem:uniform-product-first-marginal` in blueprint
chapter 13. -/
theorem uniformDistribution_map_fst {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] :
    (uniformDistribution (α × β)).map Prod.fst = uniformDistribution α := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card β) fun a => ?_
  have hfilter : ((Finset.univ : Finset (α × β)).filter fun p => p.1 = a)
      = ({a} : Finset α) ×ˢ (Finset.univ : Finset β) := by
    ext p
    grind
  rw [hfilter, Finset.card_product]
  simp

/-- Formalization-only lemma: binding the uniform law on a finite subset to a
family of uniformly seeded push-forwards is the push-forward of the uniform law
on the product of an indexing type for that subset with the seed space.  This is
`lem:uniform-bind-on-finset-map` in blueprint chapter 13. -/
theorem bind_uniformOnFinset_map {α β γ σ : Type*} [DecidableEq α]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (s : Finset α) (e : σ ≃ {a : α // a ∈ s}) (g : α → β → γ) :
    Distribution.bind (Distribution.uniformOnFinset s)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (σ × β)).map fun q => g (e q.1).1 q.2 := by
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change s.biUnion (fun a => (Finset.univ : Finset β).image (g a)) =
      (Finset.univ : Finset (σ × β)).image _
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, rfl⟩
      exact ⟨e.symm ⟨a, ha⟩, b, by simp⟩
    · rintro ⟨x, b, rfl⟩
      exact ⟨e x, (e x).2, b, rfl⟩
  · simp only [avgOver_bind, Distribution.avgOver_map]
    rw [avgOver_uniform_prod (fun x b => F (g (e x).1 b))]
    exact avgOver_uniformOnFinset_equiv s e _

/-- Formalization-only lemma: binding a uniform distribution to a family of
uniformly seeded push-forwards is the push-forward of the uniform distribution
on the product.  This is `lem:uniform-bind-map` in blueprint chapter 13. -/
theorem bind_uniformDistribution_map {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    (g : α → β → γ) :
    Distribution.bind (uniformDistribution α)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (α × β)).map fun p => g p.1 p.2 :=
  bind_uniformOnFinset_map Finset.univ
    (Equiv.subtypeUnivEquiv fun a : α => Finset.mem_univ a).symm g

/-! ## Elementary rewriting of finite distributions -/

/-- Formalization-only auxiliary: the mass of a decidable event is the average
of its indicator.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.sum_filter_weight_eq_avgOver {α : Type*}
    (μ : Distribution α) (p : α → Prop) [DecidablePred p] :
    ∑ a ∈ μ.support.filter p, μ.weight a =
      avgOver μ (fun a => if p a then 1 else 0) := by
  unfold avgOver
  rw [Finset.sum_filter]
  simp

/-- A constant weighted by an event has average equal to its mass times the constant. -/
theorem avgOver_ite_const {X : Type*} (μ : Distribution X)
    (p : X → Prop) [DecidablePred p] (c : ℝ) :
    avgOver μ (fun x => if p x then c else 0) =
      avgOver μ (fun x => if p x then 1 else 0) * c := by
  rw [← avgOver_mul_const]
  exact avgOver_congr _ _ _ fun x => by split <;> simp_all

/-- Splitting a kernel into its diagonal and a uniform multiple of its off-diagonal. -/
theorem sum_diagWeighted {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → X → ℝ) (r : ℝ) :
    (∑ x, ∑ y, (if x = y then 1 else r) * w x y) =
      (1 - r) * (∑ x, w x x) + r * ∑ x, ∑ y, w x y := by
  calc
    _ = ∑ x, ∑ y, ((if x = y then (1 - r) * w x y else 0) + r * w x y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      split <;> simp_all <;> ring
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Formalization-only auxiliary: a push-forward commutes with a dependent
bind.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.bind_map {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (ν : α → Distribution β) (f : β → γ) :
    (Distribution.bind μ ν).map f =
      Distribution.bind μ (fun a => (ν a).map f) := by
  classical
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support.biUnion fun a => (ν a).support).image f =
      μ.support.biUnion fun a => (ν a).support.image f
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_image]
    grind
  · simp only [avgOver_bind, Distribution.avgOver_map, Distribution.avgOver_prod]

/-! ## Reindexing a dependent mixture -/

/-- Mixing along a push-forward index is mixing along the original index.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_map_left {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : Distribution α) (f : α → β) (ν : β → Distribution γ) :
    Distribution.bind (μ.map f) ν =
      Distribution.bind μ (fun a => ν (f a)) := by
  classical
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support.image f).biUnion (fun b => (ν b).support) =
      μ.support.biUnion (fun a => (ν (f a)).support)
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_image]
    grind
  · simp only [avgOver_bind, Distribution.avgOver_map, Distribution.avgOver_prod]

/-- A dependent mixture depends on the mixed family only on the index
support.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_congr_support {α β : Type*} [DecidableEq β]
    (μ : Distribution α) (ν ν' : α → Distribution β)
    (h : ∀ a ∈ μ.support, ν a = ν' a) :
    Distribution.bind μ ν = Distribution.bind μ ν' := by
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change μ.support.biUnion (fun a => (ν a).support) =
      μ.support.biUnion (fun a => (ν' a).support)
    grind
  · funext b
    exact Finset.sum_congr rfl fun a ha => by simp_all

/-- Iterated dependent mixtures associate.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_bind {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (ν : α → Distribution β) (ρ : β → Distribution γ) :
    Distribution.bind (Distribution.bind μ ν) ρ =
      Distribution.bind μ (fun a => Distribution.bind (ν a) ρ) := by
  classical
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support.biUnion fun a => (ν a).support).biUnion (fun b => (ρ b).support) =
      μ.support.biUnion (fun a => (ν a).support.biUnion (fun b => (ρ b).support))
    ext b
    simp only [Finset.mem_biUnion]
    grind
  · simp only [avgOver_bind, Distribution.avgOver_map, Distribution.avgOver_prod]

/-! ## Products with an independent factor -/

/-- A product with a fixed independent second factor distributes over a
dependent mixture of the first factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_bind_left {α β γ : Type*} [DecidableEq β]
    [DecidableEq γ] (μ : Distribution α) (ν : α → Distribution β)
    (ρ : Distribution γ) :
    Distribution.prod (Distribution.bind μ ν) ρ =
      Distribution.bind μ (fun a => Distribution.prod (ν a) ρ) := by
  classical
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support.biUnion fun a => (ν a).support) ×ˢ ρ.support =
      μ.support.biUnion (fun a => (ν a).support ×ˢ ρ.support)
    ext b
    simp only [Finset.mem_biUnion, Finset.mem_product]
    grind
  · simp only [avgOver_bind, Distribution.avgOver_map, Distribution.avgOver_prod]

/-! ## The equal two-term mixture as a uniform dependent mixture -/

/-- The equal mixture of two laws is the dependent mixture indexed by a
uniform pair of labels.  Blueprint `def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.bind_uniform_fin_two {α : Type*} [DecidableEq α]
    (μ ν : Distribution α) :
    Distribution.bind (uniformDistribution (Fin 2)) ![μ, ν] =
      Distribution.mix (1 / 2) (by norm_num) (by norm_num) μ ν := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · change (Finset.univ : Finset (Fin 2)).biUnion
        (fun i => (![μ, ν] i).support) = μ.support ∪ ν.support
    ext a <;> simp_all
  · funext a
    change (∑ i ∈ (Finset.univ : Finset (Fin 2)),
        (uniformDistribution (Fin 2)).weight i * (![μ, ν] i).weight a) =
      1 / 2 * μ.weight a + (1 - 1 / 2) * ν.weight a
    rw [Fin.sum_univ_two, uniformDistribution_weight_apply,
      uniformDistribution_weight_apply, Fintype.card_fin]
    norm_num

/-! ## Averages of the distribution operations -/

/-- Formalization-only auxiliary: an average against a convex mixture is the
convex combination of the two averages.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_mix {α : Type*} [DecidableEq α] (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (μ ν : Distribution α) (f : α → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  rw [avgOver_eq_sum_superset μ f (s := μ.support ∪ ν.support) Finset.subset_union_left,
    avgOver_eq_sum_superset ν f (s := μ.support ∪ ν.support) Finset.subset_union_right]
  simp only [avgOver, Distribution.mix, add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

/-- Formalization-only auxiliary: one component of a uniform mixture carries at
most the whole nonnegative average, scaled by its mixture weight.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_bind_uniform_component_le {ι β : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [DecidableEq β]
    (ν : ι → Distribution β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (i : ι) :
    1 / (Fintype.card ι : ℝ) * avgOver (ν i) f ≤
      avgOver (Distribution.bind (uniformDistribution ι) ν) f := by
  classical
  rw [avgOver_bind]
  have hterm : ∀ j ∈ (Finset.univ : Finset ι),
      0 ≤ (uniformDistribution ι).weight j * avgOver (ν j) f := fun j _ =>
    mul_nonneg ((uniformDistribution ι).nonnegative j) (avgOver_nonneg _ _ hf)
  have hsingle := Finset.single_le_sum
    (f := fun j => (uniformDistribution ι).weight j * avgOver (ν j) f)
    hterm (Finset.mem_univ i)
  rw [uniformDistribution_weight_apply] at hsingle
  exact hsingle

end MIPStarRE.QPBT
