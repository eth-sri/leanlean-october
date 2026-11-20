module

public import MIPStarRE.LDT.Basic.PMFAverages
public import QPBT.Games.DistributionAux

/-!
# Products, marginals, and restrictions of finite distributions

The finite-distribution push-forward calculus gives corresponding identities
for probability mass functions and for projections transported across finite
equivalences.  These forms are used by the directly indexed low-degree
line-point laws and by the correspondence between the seed-indexed and directly
indexed question distributions. Products can be expressed as dependent mixtures, and
conditioning on an event of one factor preserves the independence of the other.

## References

- `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-272`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`
- `docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open MIPStarRE.LDT

/-- Formalization-only lemma for the low-degree sampling laws: if an
equivalence identifies a nonempty finite set with the product of two nonempty
finite sets and a map agrees with the first projection, then the map sends the
uniform law to the uniform law on the first factor.  This is
`lem:uniform-first-marginal-after-equivalence` in blueprint chapter 13. -/
theorem uniformDistribution_map_fst_of_equiv
    {alpha beta gamma : Type*}
    [Fintype alpha] [DecidableEq alpha] [Nonempty alpha]
    [Fintype beta] [DecidableEq beta] [Nonempty beta]
    [Finite gamma] [Nonempty gamma]
    (e : alpha ≃ beta × gamma) (f : alpha → beta)
    (hf : ∀ a, f a = (e a).1) :
    (uniformDistribution alpha).map f = uniformDistribution beta := by
  classical
  letI := Fintype.ofFinite gamma
  calc
    _ =
        (uniformDistribution alpha).map (fun a => (e a).1) := by
      congr 1
      funext a
      exact hf a
    _ = _ :=
      (Distribution.map_map _ _ _).symm
    _ = (uniformDistribution (beta × gamma)).map Prod.fst := by
      rw [uniformDistribution_map_equiv]
    _ = _ := uniformDistribution_map_fst

/-! ## Push-forward of one factor of a product -/

/-- Pushing the first factor of a product forward is pushing the product
forward along the map acting on that factor alone.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_left {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (f : α → γ) :
    Distribution.prod (μ.map f) ν =
      (Distribution.prod μ ν).map (fun w => (f w.1, w.2)) := by
  classical
  apply Distribution.ext_avg
  · ext w
    simp [Distribution.prod, Prod.exists]
    <;> grind
  · intro test
    simp only [avgOver_prod, MIPStarRE.LDT.Distribution.avgOver_map]

/-! ## The first marginal of a product -/

/-- The first marginal of a product whose second factor is a probability law
is the first factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) {ν : Distribution β} (hν : ν.IsProbability) :
    (Distribution.prod μ ν).map Prod.fst = μ := by
  classical
  apply Distribution.ext_avg
  · ext w
    simp [Distribution.prod, Prod.exists]
    have := Distribution.support_nonempty_of_isProbability hν
    <;> grind
  · intro test
    simp only [avgOver_prod, MIPStarRE.LDT.Distribution.avgOver_map, avgOver_const_of_isProbability _ hν]

section

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ] (μ : Distribution α)
  (ν : Distribution β)

/-! ## A product as a dependent mixture -/

/-- A push-forward of a product is the dependent mixture, over the first
factor, of the push-forwards of the second factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_eq_bind
    (g : α × β → γ) :
    (Distribution.prod μ ν).map g =
      Distribution.bind μ (fun a => ν.map (fun b => g (a, b))) := by
  classical
  apply Distribution.ext_avg
  · ext w
    simp [Distribution.prod, Distribution.bind, Prod.exists]
    <;> grind
  · intro test
    simp only [avgOver_prod, MIPStarRE.LDT.Distribution.avgOver_map, avgOver_bind]

end

/-! ## The support and the weight of a product -/

section

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (μ : Distribution α) (ν : Distribution β)

/-- The support of a product law is the product of the supports.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_support :
    (Distribution.prod μ ν).support = μ.support ×ˢ ν.support := rfl

/-- The weight of a product law is the product of the weights.  Blueprint
`def:line-point-dist`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:274-287`.
-/
theorem Distribution.prod_weight (w : α × β) :
    (Distribution.prod μ ν).weight w = μ.weight w.1 * ν.weight w.2 := rfl

/-! ## Push-forward along a bijection -/

/-- A push-forward along a bijection is identified by the supports and the
weights it compares: if the map matches the two supports and carries each
weight to the corresponding weight, and if it has a two-sided inverse, the
push-forward is the target law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.map_bijective_eq (f : α → β)
    (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b)
    (hs : ∀ a, a ∈ μ.support ↔ f a ∈ ν.support)
    (hw : ∀ a, μ.weight a = ν.weight (f a)) :
    μ.map f = ν := by
  classical
  apply Distribution.ext_of_support_of_weight
  · ext b
    simp
    constructor
    · grind
    · intro hb
      refine ⟨g b, (hs (g b)).mpr ?_, hfg b⟩
      simp_all
  · funext b
    simp
    have hfilter : μ.support.filter (fun a => f a = b) =
        μ.support.filter (fun a => a = g b) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, h⟩
        exact ⟨ha, by rw [← h, hgf]⟩
      · rintro ⟨ha, h⟩
        simp_all
    rw [hfilter, Finset.filter_eq']
    by_cases hmem : g b ∈ μ.support
    · simp_all
    · simp [if_neg hmem]
      refine (ν.outsideSupport b ?_).symm
      grind

end

/-! ## Push-forward of the second factor of a product -/

/-- Pushing the second factor of a product forward is pushing the product
forward along the map acting on that factor alone.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_right {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (g : β → γ) :
    Distribution.prod μ (ν.map g) =
      (Distribution.prod μ ν).map (fun w => (w.1, g w.2)) := by
  classical
  apply Distribution.ext_avg
  · ext w
    simp [Distribution.prod, Prod.exists]
    <;> grind
  · intro test
    simp only [avgOver_prod, MIPStarRE.LDT.Distribution.avgOver_map]

/-! ## Uniform laws on products -/

/-- Formalization-only auxiliary: the uniform law on a product of two finite
types is the product of the uniform laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_prod (α β : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] :
    uniformDistribution (α × β) =
      Distribution.prod (uniformDistribution α) (uniformDistribution β) := by
  classical
  apply Distribution.ext_of_support_of_weight
  · show _ =
      Finset.univ.product Finset.univ
    simp
  · funext p
    show _ =
      (uniformDistribution α).weight p.1 * (uniformDistribution β).weight p.2
    simp [uniformDistribution_weight_apply, Fintype.card_prod]
    push_cast
    field_simp

/-- Formalization-only auxiliary: the mass of an event depending only on the
second factor is the same under a uniform product law and under the uniform
law of that factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_snd_event_mass {α β : Type*} [Fintype α]
    [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β]
    (p : β → Prop) [DecidablePred p] :
    ∑ w ∈ (uniformDistribution (α × β)).support.filter (fun w => p w.2),
        (uniformDistribution (α × β)).weight w =
      ∑ b ∈ (uniformDistribution β).support.filter p,
        (uniformDistribution β).weight b := by
  classical
  rw [Distribution.sum_filter_weight_eq_avgOver,
    Distribution.sum_filter_weight_eq_avgOver,
    ← uniformDistribution_map_snd (α := α) (β := β), Distribution.avgOver_map]

/-! ## Conditioning one factor of a product -/

/-- Formalization-only auxiliary: normalized restriction depends on the
restricted law only through its support and weights.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_congr {α : Type*} [DecidableEq α]
    {μ ν : Distribution α} (h : μ = ν) {p : α → Prop} [DecidablePred p]
    (hμ : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hν : 0 < ∑ a ∈ ν.support.filter p, ν.weight a) :
    Distribution.restrict μ p hμ = Distribution.restrict ν p hν := by
  subst h
  rfl

variable {α β : Type*}

/-- Restricting a product law to an event depending on the second factor alone
leaves the first factor unchanged and independent of the conditioned second
factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_prod_snd [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hμ : μ.IsProbability) (p : β → Prop) [DecidablePred p]
    (hpos : 0 < ∑ b ∈ ν.support.filter p, ν.weight b)
    (hpos' : 0 < ∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.2), (Distribution.prod μ ν).weight w) :
    Distribution.restrict (Distribution.prod μ ν) (fun w => p w.2) hpos' =
      Distribution.prod μ (Distribution.restrict ν p hpos) := by
  classical
  have hprodsupp : (Distribution.prod μ ν).support =
      μ.support ×ˢ ν.support := rfl
  have hsupp : (Distribution.prod μ ν).support.filter (fun w => p w.2) =
      μ.support ×ˢ (ν.support.filter p) := by
    rw [hprodsupp]
    ext w
    simp
    tauto
  have hmass : (∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.2), (Distribution.prod μ ν).weight w) =
      ∑ b ∈ ν.support.filter p, ν.weight b := by
    rw [hsupp, Finset.sum_product]
    simp_rw [Distribution.prod_weight, ← Finset.mul_sum, ← Finset.sum_mul,
      hμ.weight_sum_eq_one, one_mul]
  apply Distribution.ext_of_support_of_weight hsupp
  funext w
  simp only [Distribution.prod_weight, Distribution.restrict, ite_mul, mul_ite, zero_mul, mul_zero]
  split
  · simp only [Distribution.prod_weight] at hmass
    rw [hmass]
    ring
  · rfl

/-- Conditioning a uniform product law on an event of its second factor leaves
the first factor uniform and independent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrict_uniform_prod_snd [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] (p : β → Prop)
    [DecidablePred p]
    (hpos : 0 < ∑ b ∈ (uniformDistribution β).support.filter p,
      (uniformDistribution β).weight b)
    (hpos' : 0 < ∑ w ∈ (uniformDistribution (α × β)).support.filter
        (fun w => p w.2), (uniformDistribution (α × β)).weight w) :
    Distribution.restrict (uniformDistribution (α × β)) (fun w => p w.2)
        hpos' =
      Distribution.prod (uniformDistribution α)
        (Distribution.restrict (uniformDistribution β) p hpos) := by
  classical
  have hpos'' : 0 < ∑ w ∈ (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).support.filter (fun w => p w.2),
      (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).weight w := by
    rw [← uniformDistribution_prod]
    exact hpos'
  rw [Distribution.restrict_congr (uniformDistribution_prod α β) hpos' hpos'']
  solve_by_elim [Distribution.restrict_prod_snd, uniformDistribution_isProbability]

/-! ## Conditioning the first factor of a product -/

/-- Restricting a product law to an event depending on the first factor alone
leaves the second factor unchanged and independent of the conditioned first
factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_prod_fst [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
    (hν : ν.IsProbability) (p : α → Prop) [DecidablePred p]
    (hpos : 0 < ∑ a ∈ μ.support.filter p, μ.weight a)
    (hpos' : 0 < ∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.1), (Distribution.prod μ ν).weight w) :
    Distribution.restrict (Distribution.prod μ ν) (fun w => p w.1) hpos' =
      Distribution.prod (Distribution.restrict μ p hpos) ν := by
  classical
  have hsupp : (Distribution.prod μ ν).support.filter (fun w => p w.1) =
      (μ.support.filter p) ×ˢ ν.support := by
    change (μ.support ×ˢ ν.support).filter (fun w => p w.1) =
      _
    ext w
    simp
    tauto
  have hmass : (∑ w ∈ (Distribution.prod μ ν).support.filter
        (fun w => p w.1), (Distribution.prod μ ν).weight w) =
      ∑ a ∈ μ.support.filter p, μ.weight a := by
    rw [hsupp, Finset.sum_product]
    simp_rw [Distribution.prod_weight, ← Finset.mul_sum, hν.weight_sum_eq_one, mul_one]
  apply Distribution.ext_of_support_of_weight hsupp
  funext w
  simp only [Distribution.prod_weight, Distribution.restrict, ite_mul, mul_ite, zero_mul, mul_zero]
  split
  · simp only [Distribution.prod_weight] at hmass
    rw [hmass]
    ring
  · rfl

/-- Conditioning a uniform product law on an event of its first factor leaves
the second factor uniform and independent.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem restrict_uniform_prod_fst [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] (p : α → Prop)
    [DecidablePred p]
    (hpos : 0 < ∑ a ∈ (uniformDistribution α).support.filter p,
      (uniformDistribution α).weight a)
    (hpos' : 0 < ∑ w ∈ (uniformDistribution (α × β)).support.filter
        (fun w => p w.1), (uniformDistribution (α × β)).weight w) :
    Distribution.restrict (uniformDistribution (α × β)) (fun w => p w.1)
        hpos' =
      Distribution.prod
        (Distribution.restrict (uniformDistribution α) p hpos)
        (uniformDistribution β) := by
  classical
  have hpos'' : 0 < ∑ w ∈ (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).support.filter (fun w => p w.1),
      (Distribution.prod (uniformDistribution α)
        (uniformDistribution β)).weight w := by
    rw [← uniformDistribution_prod]
    exact hpos'
  rw [Distribution.restrict_congr (uniformDistribution_prod α β) hpos' hpos'']
  solve_by_elim [Distribution.restrict_prod_fst, uniformDistribution_isProbability]

/-! ## Restriction of a push-forward -/

/-- Formalization-only auxiliary: restricting a push-forward distribution to a
decidable event is the push-forward of the restriction to the pre-image of
that event.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.restrict_map [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (f : α → β) (p : β → Prop) [DecidablePred p]
    (q : α → Prop) [DecidablePred q] (hq : ∀ a, q a ↔ p (f a))
    (hpos : 0 < ∑ b ∈ (μ.map f).support.filter p, (μ.map f).weight b)
    (hpos' : 0 < ∑ a ∈ μ.support.filter q, μ.weight a) :
    Distribution.restrict (μ.map f) p hpos =
      (Distribution.restrict μ q hpos').map f := by
  apply Distribution.ext_avg
  · ext b
    simp [Distribution.restrict, hq] <;> grind
  · intro test
    simp only [avgOver_restrict, MIPStarRE.LDT.Distribution.avgOver_map, hq]

end MIPStarRE.QPBT
