module

public import QPBT.Upstream

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

/-! ## Nonemptiness of the support of a probability law -/

theorem avgOver_eq_sum_univ {X : Type*} [Fintype X] (μ : Distribution X) (f : X → ℝ) :
    avgOver μ f = ∑ x, μ.weight x * f x :=
  (Distribution.sum_univ_eq_sum_support μ _ (fun x hx => by simp [μ.outsideSupport x hx])).symm

theorem Distribution.weight_eq_avg_indicator {X : Type*} [DecidableEq X] (D : Distribution X) (x : X) :
    D.weight x = avgOver D (fun a => if a = x then 1 else 0) := by
  by_cases h : x ∈ D.support <;> simp [avgOver, mul_ite, h, D.outsideSupport]

theorem Distribution.map_fst_weight {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    (D : Distribution (X × Y)) (x : X) : (D.map Prod.fst).weight x = ∑ y, D.weight (x, y) := by
  rw [Distribution.weight_eq_avg_indicator, Distribution.avgOver_map, avgOver_eq_sum_univ,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp [mul_ite]

private theorem prob_iff_avg_one {α : Type*} (μ : Distribution α) :
    μ.IsProbability ↔ avgOver μ (fun _ => 1) = 1 := by simp [Distribution.IsProbability, Distribution.totalWeight, avgOver_const]

/-- A law of total mass one has a nonempty support.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.support_nonempty_of_isProbability {α : Type*}
    {μ : Distribution α} (hμ : μ.IsProbability) : μ.support.Nonempty := by
  by_contra! h
  simpa [h] using hμ.weight_sum_eq_one

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
        exact hp (Finset.mem_product.mpr ⟨hμ, h⟩)
      simp [ν.outsideSupport p.2 hν]
    · simp [μ.outsideSupport p.1 hμ]

/-- Expectation under independent sampling is iterated expectation. -/
theorem avgOver_prod {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (f : α × β → ℝ) :
    avgOver (Distribution.prod μ ν) f = avgOver μ (fun a => avgOver ν (fun b => f (a, b))) := by
  simp [avgOver, Distribution.prod, Finset.sum_product, Finset.mul_sum, mul_assoc]

/-- The product of two probability distributions is a probability
distribution; blueprint `lem:ld-sandwich`, paper
`06_nonlocal_games_and_mipstar.tex:465-501`. -/
theorem Distribution.prod_isProbability {α β : Type*}
    [DecidableEq α] [DecidableEq β] {μ : Distribution α} {ν : Distribution β}
    (hμ : μ.IsProbability) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).IsProbability := by
  rw [prob_iff_avg_one, avgOver_prod]
  simp only [avgOver_const_of_isProbability ν hν, avgOver_const_of_isProbability μ hμ]

section

variable {α : Type*} [DecidableEq α] (t : ℝ) (μ ν : Distribution α) (hμ : μ.IsProbability)
  (hν : ν.IsProbability) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

include ht1 ht0 in
/-- The convex mixture with a coefficient in `[0,1]`, as used for
the equal mixture in blueprint
`def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
noncomputable def Distribution.mix
    (μ ν : Distribution α) : Distribution α where
  support := μ.support ∪ ν.support
  weight a := t * μ.weight a + (1 - t) * ν.weight a
  nonnegative a := add_nonneg
      (mul_nonneg ht0 (μ.nonnegative a))
      (mul_nonneg (sub_nonneg.mpr ht1) (ν.nonnegative a))
  outsideSupport a ha := by
    simp [μ.outsideSupport a (fun h => ha (Finset.mem_union_left _ h)), ν.outsideSupport a (fun h => ha (Finset.mem_union_right _ h))]

include hν hμ in
/-- A convex mixture of probability distributions is a probability distribution;
blueprint `def:line-point-dist`, paper
`08_classical_and_quantum_low_degree_tests.tex:274-287`. -/
theorem Distribution.mix_isProbability :
    (Distribution.mix t ht0 ht1 μ ν).IsProbability := by
  have hμ_union :
      ∑ a ∈ μ.support ∪ ν.support, μ.weight a = 1 := by
    apply hμ.weight_sum_eq_one_of_subset
    simp
  have hν_union :
      ∑ a ∈ μ.support ∪ ν.support, ν.weight a = 1 := by
    apply hν.weight_sum_eq_one_of_subset
    simp
  simp [Distribution.IsProbability, Distribution.totalWeight, Distribution.mix, Finset.sum_add_distrib, ← Finset.mul_sum, hμ_union, hν_union]

end

section

variable {α β : Type*} [DecidableEq β] (μ : Distribution α) (ν : α → Distribution β)

/-- The dependent bind of finite distributions used for typed question
distributions, blueprint `def:typed-cl-distributions`, paper
`07_types.tex:84-94`. -/
noncomputable def Distribution.bind : Distribution β where
  support := μ.support.biUnion (fun a => (ν a).support)
  weight b := ∑ a ∈ μ.support, μ.weight a * (ν a).weight b
  nonnegative b := Finset.sum_nonneg fun a _ => mul_nonneg (μ.nonnegative a) ((ν a).nonnegative b)
  outsideSupport b hb := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : b ∉ (ν a).support := by
      intro h
      exact hb (Finset.mem_biUnion.mpr ⟨a, ha, h⟩)
    simp [ν a |>.outsideSupport b hnot]

/-- Formalization-only auxiliary: an average against a dependent bind is the
iterated average.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_bind (f : β → ℝ) :
    avgOver (Distribution.bind μ ν) f =
      avgOver μ (fun a => avgOver (ν a) f) := by
  classical
  unfold avgOver Distribution.bind
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [← Finset.mul_sum]
  congr 1
  apply (Finset.sum_subset (Finset.subset_biUnion_of_mem _ ha) _).symm
  intro b _ hb
  simp [(ν a).outsideSupport b hb]

/-- A dependent bind of probability distributions is a probability distribution;
blueprint
`def:typed-cl-distributions`, paper `07_types.tex:84-94`. -/
theorem Distribution.bind_isProbability (hμ : μ.IsProbability)
    (hν : ∀ a ∈ μ.support, (ν a).IsProbability) :
    (Distribution.bind μ ν).IsProbability := by
  rw [prob_iff_avg_one, avgOver_bind]
  apply Eq.trans _ ((prob_iff_avg_one μ).mp hμ)
  exact Finset.sum_congr rfl fun a ha => by simp only [avgOver_const_of_isProbability _ (hν a ha)]

end

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
    · exact le_rfl
  outsideSupport a ha := by
    by_cases hp : p a
    · simp [hp, μ.outsideSupport a (fun h => ha (Finset.mem_filter.mpr ⟨h, hp⟩))]
    · simp [hp]

theorem avgOver_restrict {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p] (hp) (f : α → ℝ) :
    avgOver (Distribution.restrict μ p hp) f =
      avgOver μ (fun a => if p a then f a else 0) / avgOver μ (fun a => if p a then 1 else 0) := by
  simp only [avgOver, Distribution.restrict, Finset.sum_filter, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  split <;> simp_all [div_mul_eq_mul_div]

/-- Restriction to a positive-mass event preserves total probability;
blueprint
`def:ith-restricted-line`, paper
`14_analysis_of_the_pauli_basis_test.tex:1038-1048`. -/
theorem Distribution.restrict_isProbability {α : Type*} [DecidableEq α]
    (μ : Distribution α) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a) :
    (Distribution.restrict μ p hpos).IsProbability := by
  rw [prob_iff_avg_one, avgOver_restrict, div_self]
  simpa [avgOver, Finset.sum_filter, mul_ite] using hpos.ne'

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
  solve_by_elim [Distribution.mk.congr_simp]

/-- A finite distribution with specified support is determined by the
expectations of all scalar test functions (take singleton indicators). -/
theorem Distribution.ext_avg {α : Type*} {μ ν : Distribution α}
    (hs : μ.support = ν.support) (hav : ∀ f : α → ℝ, avgOver μ f = avgOver ν f) : μ = ν := by
  apply Distribution.ext_of_support_of_weight hs
  funext a
  classical
  simpa only [← Distribution.weight_eq_avg_indicator] using hav (fun b => if b = a then 1 else 0)

/-- Formalization-only lemma: successive push-forwards of a finite distribution
compose.  This is `lem:distribution-map-comp` in blueprint chapter 13. -/
theorem Distribution.map_map {α β γ : Type*}
    [DecidableEq β] [DecidableEq γ]
    (μ : Distribution α) (e : α → β) (f : β → γ) :
    (μ.map e).map f = μ.map fun a => f (e a) := by
  apply Distribution.ext_avg
  · aesop
  · intro f
    simp only [MIPStarRE.LDT.Distribution.avgOver_map]

/-- Formalization-only lemma: every point of a nonempty finite type carries the
reciprocal of the type's cardinality as its uniform weight.  This is
`lem:uniform-distribution-weight` in blueprint chapter 13. -/
theorem uniformDistribution_weight_apply (α : Type*)
    [Fintype α] [DecidableEq α] [Nonempty α] (a : α) :
    (uniformDistribution α).weight a = 1 / (Fintype.card α : Error) := by
  simp [uniformDistribution]

section

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- Formalization-only lemma: a push-forward of a uniform law assigns to a point
the cardinality of its fibre divided by the cardinality of the source.  This is
`lem:uniform-map-fibre-weight` in blueprint chapter 13. -/
theorem uniformDistribution_map_weight [DecidableEq γ]
    (e : α → γ) (c : γ) :
    ((uniformDistribution α).map e).weight c =
      (((Finset.univ : Finset α).filter fun x => e x = c).card : Error) *
        (1 / (Fintype.card α : Error)) := by
  simp [Finset.sum_const, nsmul_eq_mul, Finset.sum_congr rfl fun x _ => uniformDistribution_weight_apply α x]

/-- Formalization-only lemma: a map whose fibers all have the same cardinality
pushes the uniform distribution forward to the uniform distribution.  This is
`lem:uniform-map-equal-fibers` in blueprint chapter 13. -/
theorem uniformDistribution_map_of_card_fiber
    (e : α → β) (c : ℕ)
    (hc : ∀ b : β, ((Finset.univ : Finset α).filter fun a => e a = b).card = c) :
    (uniformDistribution α).map e = uniformDistribution β := by
  have hcpos : 0 < c := by
    obtain ⟨a₀⟩ := (inferInstance : Nonempty α)
    have hmem : a₀ ∈ Finset.univ.filter fun a => e a = e a₀ :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hpos := Finset.card_pos.mpr ⟨a₀, hmem⟩
    simp_all
  have hcard : Fintype.card α = Fintype.card β * c := by
    have h := Finset.card_eq_sum_card_fiberwise
      (f := e) (s := (Finset.univ : Finset α))
      (fun a _ => Finset.mem_univ _)
    simp_all
  apply Distribution.ext_of_support_of_weight
  · ext b
    simp
    have hne : (Finset.univ.filter fun a => e a = b).Nonempty := by
      rw [← Finset.card_pos, hc]
      exact hcpos
    grind
  · funext b
    change (∑ a ∈ (Finset.univ : Finset α).filter fun a => e a = b,
        (uniformDistribution α).weight a) = (uniformDistribution β).weight b
    rw [Finset.sum_congr rfl fun a _ => uniformDistribution_weight_apply α a,
      uniformDistribution_weight_apply, Finset.sum_const, hc, nsmul_eq_mul, hcard]
    push_cast
    field_simp

/-- Formalization-only lemma: relabelling along a bijection preserves
uniformity.  This is `lem:uniform-map-equivalence` in blueprint chapter 13. -/
theorem uniformDistribution_map_equiv (E : α ≃ β) :
    (uniformDistribution α).map E = uniformDistribution β := by
  refine uniformDistribution_map_of_card_fiber _ 1 fun b => ?_
  have hfilter :
      (Finset.univ.filter fun a => E a = b) = {E.symm b} := by
    aesop
  simp_all

/-- Formalization-only lemma: the first marginal of the uniform distribution on
a product is uniform.  This is `lem:uniform-product-first-marginal` in blueprint
chapter 13. -/
theorem uniformDistribution_map_fst :
    (uniformDistribution (α × β)).map Prod.fst = uniformDistribution α := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card β) fun a => ?_
  have hfilter : (Finset.univ.filter fun p => p.1 = a)
      = ({a}) ×ˢ (Finset.univ : Finset β) := by
    grind
  simp_all

/-- Formalization-only lemma: the second marginal of the uniform distribution
on a product is uniform.  This is `lem:uniform-product-second-marginal` in
blueprint chapter 13. -/
theorem uniformDistribution_map_snd :
    (uniformDistribution (α × β)).map Prod.snd = uniformDistribution β := by
  refine uniformDistribution_map_of_card_fiber _ (Fintype.card α) fun b => ?_
  have hfilter : (Finset.univ.filter fun p => p.2 = b)
      = (Finset.univ : Finset α) ×ˢ ({b}) := by
    grind
  simp_all

end

/-- Formalization-only lemma: binding the uniform law on a finite subset to a
family of uniformly seeded push-forwards is the push-forward of the uniform law
on the product of an indexing type for that subset with the seed space.  This is
`lem:uniform-bind-on-finset-map` in blueprint chapter 13. -/
theorem bind_uniformOnFinset_map {α β γ σ : Type*} [DecidableEq α]
    [Fintype σ] [DecidableEq σ] [Nonempty σ]
    [Fintype β] [DecidableEq β] [Nonempty β] [DecidableEq γ]
    {s : Finset α} {f : σ → α} (hinj : Function.Injective f)
    (himage : (Finset.univ : Finset σ).image f = s) (g : α → β → γ) :
    Distribution.bind (Distribution.uniformOnFinset s)
        (fun a => (uniformDistribution β).map (g a)) =
      (uniformDistribution (σ × β)).map fun q => g (f q.1) q.2 := by
  have hmem : ∀ a, a ∈ s ↔ ∃ x : σ, f x = a := by
    grind
  have hsum : ∀ h : α → Error, ∑ a ∈ s, h a = ∑ x : σ, h (f x) := by
    aesop
  apply Distribution.ext_of_support_of_weight
  · change s.biUnion (fun a => (Finset.univ : Finset β).image (g a)) =
      _
    aesop
  · funext c
    have key : ∀ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c =
        ((Finset.univ.filter fun b => g a b = c).card : Error) *
          (1 / ((Fintype.card σ) * (Fintype.card β))) := by
      intro a ha
      rw [Distribution.uniformOnFinset_weight, if_pos ha,
        uniformDistribution_map_weight, ← himage, Finset.card_image_of_injective _ hinj, Finset.card_univ]
      ring
    have hcount :
        ((Finset.univ : Finset (σ × β)).filter fun q => g (f q.1) q.2 = c).card =
          ∑ x : σ, (Finset.univ.filter fun b => g (f x) b = c).card := by
      simp only [Finset.card_filter]
      rw [Fintype.sum_prod_type]
    change (∑ a ∈ s, (Distribution.uniformOnFinset s).weight a *
        ((uniformDistribution β).map (g a)).weight c) =
      ∑ q ∈ Finset.univ.filter fun q => g (f q.1) q.2 = c,
        (uniformDistribution (σ × β)).weight q
    rw [Finset.sum_congr rfl key,
      hsum,
      ← Finset.sum_mul,
      Finset.sum_congr rfl fun q _ => uniformDistribution_weight_apply _ q,
      Finset.sum_const, nsmul_eq_mul, hcount, Fintype.card_prod]
    push_cast
    ring

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
  bind_uniformOnFinset_map Function.injective_id
    Finset.image_id g

/-! ## Elementary rewriting of finite distributions -/

section

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (μ : Distribution α)

/-- Formalization-only auxiliary: the mass of a decidable event is the average
of its indicator.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.sum_filter_weight_eq_avgOver (p : α → Prop) [DecidablePred p] :
    ∑ a ∈ μ.support.filter p, μ.weight a =
      avgOver μ (fun a => if p a then 1 else 0) := by
  unfold avgOver
  rw [Finset.sum_filter]
  simp

/-- Formalization-only auxiliary: a push-forward commutes with a dependent
bind.  Blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.bind_map (ν : α → Distribution β) (f : β → γ) :
    (Distribution.bind μ ν).map f =
      Distribution.bind μ (fun a => (ν a).map f) := by
  classical
  apply Distribution.ext_avg
  · change (μ.support.biUnion fun a => (ν a).support).image f =
      μ.support.biUnion fun a => (ν a).support.image f
    grind
  · intro f
    simp only [avgOver_bind, MIPStarRE.LDT.Distribution.avgOver_map]

end

/-- Formalization-only auxiliary: a family of normalized restrictions along the
fibers of a classifying map recovers the original law when every fiber carries
the uniform mass `1 / |ι|`.  This is the mixture step of
blueprint `lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1049-1051`. -/
theorem Distribution.bind_uniform_restrict_eq {α ι : Type*} [DecidableEq α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μ : Distribution α) (p : ι → α → Prop) [∀ i, DecidablePred (p i)]
    (hpos : ∀ i, 0 < ∑ a ∈ μ.support.filter (p i), μ.weight a)
    (hmass : ∀ i, ∑ a ∈ μ.support.filter (p i), μ.weight a =
      1 / (Fintype.card ι : ℝ))
    (hunique : ∀ a, ∃! i, p i a) :
    Distribution.bind (uniformDistribution ι)
        (fun i => Distribution.restrict μ (p i) (hpos i)) = μ := by
  classical
  apply Distribution.ext_of_support_of_weight
  · ext a
    constructor
    · intro ha
      obtain ⟨i, -, hai⟩ := Finset.mem_biUnion.mp ha
      exact (Finset.mem_filter.mp hai).1
    · intro ha
      obtain ⟨i, hi, -⟩ := hunique a
      exact Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨ha, hi⟩⟩
  · funext a
    change (∑ i ∈ Finset.univ, (uniformDistribution ι).weight i *
      (Distribution.restrict μ (p i) (hpos i)).weight a) = μ.weight a
    have hterm : ∀ i : ι, (uniformDistribution ι).weight i *
        (Distribution.restrict μ (p i) (hpos i)).weight a =
        if p i a then μ.weight a else 0 := by
      intro i
      rw [uniformDistribution_weight_apply]
      by_cases h : p i a
      · have hw : (Distribution.restrict μ (p i) (hpos i)).weight a =
            μ.weight a / (1 / (Fintype.card ι)) := by
          simp [Distribution.restrict, if_pos h, hmass]
        rw [hw, if_pos h]
        field_simp
      · grind [Distribution.restrict]
    simp_all
    obtain ⟨i₀, hi₀, huniq⟩ := hunique a
    rw [Finset.sum_eq_single]
    · rw [if_pos hi₀]
    · grind
    · simp

/-! ## Reindexing a dependent mixture -/

section

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (μ : Distribution α)
  (ν ν' : α → Distribution β)

/-- Mixing along a push-forward index is mixing along the original index.
Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_map_left (f : α → β) (ν : β → Distribution γ) :
    Distribution.bind (μ.map f) ν =
      Distribution.bind μ (fun a => ν (f a)) := by
  classical
  apply Distribution.ext_avg
  · change (μ.support.image f).biUnion (fun b => (ν b).support) =
      μ.support.biUnion _
    grind
  · intro f
    simp only [avgOver_bind, MIPStarRE.LDT.Distribution.avgOver_map]

/-- A dependent mixture depends on the mixed family only on the index
support.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_congr_support
    (h : ∀ a ∈ μ.support, ν a = ν' a) :
    Distribution.bind μ ν = Distribution.bind μ ν' := by
  apply Distribution.ext_of_support_of_weight
  · exact Finset.biUnion_congr rfl fun a ha => by simp_all
  · funext b
    exact Finset.sum_congr rfl fun a ha => by simp_all

/-- A dependent mixture of a constant family is that constant law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_const (hμ : μ.IsProbability) (ν : Distribution β) :
    Distribution.bind μ (fun _ => ν) = ν := by
  have hne := Distribution.support_nonempty_of_isProbability hμ
  apply Distribution.ext_of_support_of_weight
  · change μ.support.biUnion _ = ν.support
    grind
  · funext b
    change (∑ a ∈ μ.support, μ.weight a * ν.weight b) = ν.weight b
    simp [← Finset.sum_mul, hμ.weight_sum_eq_one]

/-! ## Associativity of dependent mixtures -/

/-- Iterated dependent mixtures associate.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.bind_bind (ρ : β → Distribution γ) :
    Distribution.bind (Distribution.bind μ ν) ρ =
      Distribution.bind μ (fun a => Distribution.bind (ν a) ρ) := by
  classical
  apply Distribution.ext_avg
  · change (μ.support.biUnion (fun a => (ν a).support)).biUnion
        (fun b => (ρ b).support) =
      μ.support.biUnion (fun a => (ν a).support.biUnion (fun b => (ρ b).support))
    grind
  · intro f
    simp only [avgOver_bind]

end

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
  apply Distribution.ext_avg
  · change (μ.support.biUnion (fun a => (ν a).support)) ×ˢ ρ.support =
      μ.support.biUnion (fun a => (ν a).support ×ˢ ρ.support)
    grind
  · intro f
    simp only [avgOver_bind, avgOver_prod]

/-! ## The equal two-term mixture as a uniform dependent mixture -/

variable {α ι β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [DecidableEq β]
  (μ : Distribution α)

/-- The equal mixture of two laws is the dependent mixture indexed by a
uniform pair of labels.  Blueprint `def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.bind_uniform_fin_two [DecidableEq α]
    (μ ν : Distribution α) :
    Distribution.bind (uniformDistribution (Fin 2)) ![μ, ν] =
      Distribution.mix (1 / 2) (by norm_num) (by norm_num) μ ν := by
  classical
  apply Distribution.ext_of_support_of_weight
  · change Finset.univ.biUnion
        (fun i => (![μ, ν] i).support) = μ.support ∪ ν.support
    aesop
  · funext a
    change (∑ i ∈ Finset.univ,
        (uniformDistribution (Fin 2)).weight i * (![μ, ν] i).weight a) =
      1 / 2 * μ.weight a + (1 - 1 / 2) * ν.weight a
    simp [Fin.sum_univ_two, uniformDistribution_weight_apply, Fintype.card_fin]
    norm_num

/-! ## Averages of the distribution operations -/

/-- Formalization-only auxiliary: an average against a convex mixture is the
convex combination of the two averages.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1058`. -/
theorem avgOver_mix [DecidableEq α] (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (μ ν : Distribution α) (f : α → ℝ) :
    avgOver (Distribution.mix t ht0 ht1 μ ν) f =
      t * avgOver μ f + (1 - t) * avgOver ν f := by
  classical
  unfold avgOver
  have hsplit : (∑ a ∈ μ.support ∪ ν.support,
        (t * μ.weight a + (1 - t) * ν.weight a) * f a) =
      t * (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) +
        (1 - t) * (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) := by
    simp [Finset.mul_sum, ← Finset.sum_add_distrib]
    grind
  have hμ : (∑ a ∈ μ.support ∪ ν.support, μ.weight a * f a) =
      ∑ a ∈ μ.support, μ.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_left ?_).symm
    intro a _ ha
    simp [μ.outsideSupport a ha]
  have hν : (∑ a ∈ μ.support ∪ ν.support, ν.weight a * f a) =
      ∑ a ∈ ν.support, ν.weight a * f a := by
    refine (Finset.sum_subset Finset.subset_union_right ?_).symm
    intro a _ ha
    simp [ν.outsideSupport a ha]
  change (∑ a ∈ μ.support ∪ ν.support,
    (t * μ.weight a + _ * ν.weight a) * f a) = _
  simp_all

/-- Formalization-only auxiliary: one component of a uniform mixture carries at
most the whole nonnegative average, scaled by its mixture weight.  Blueprint
`lem:restricted-line-mixture-bounds`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1052-1056`. -/
theorem avgOver_bind_uniform_component_le
    (ν : ι → Distribution β) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) (i : ι) :
    1 / (Fintype.card ι : ℝ) * avgOver (ν i) f ≤
      avgOver (Distribution.bind (uniformDistribution ι) ν) f := by
  classical
  rw [avgOver_bind]
  have hsingle := Finset.single_le_sum
    (f := fun j => (uniformDistribution ι).weight j * avgOver (ν j) f)
    (fun j _ =>
      mul_nonneg ((uniformDistribution ι).nonnegative j) (avgOver_nonneg _ _ hf)) (Finset.mem_univ i)
  rw [uniformDistribution_weight_apply] at hsingle
  exact hsingle

end MIPStarRE.QPBT
