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
    (uniformDistribution alpha).map f =
        (uniformDistribution alpha).map (fun a => (e a).1) := by
      congr 1
      funext a
      exact hf a
    _ = ((uniformDistribution alpha).map e).map Prod.fst :=
      (Distribution.map_map _ _ _).symm
    _ = (uniformDistribution (beta × gamma)).map Prod.fst := by
      rw [uniformDistribution_map_equiv]
    _ = uniformDistribution beta := uniformDistribution_map_fst

/-! ## Nonemptiness of the support of a probability law -/

/-- A law of total mass one has a nonempty support.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.support_nonempty_of_isProbability {α : Type*}
    {μ : Distribution α} (hμ : μ.IsProbability) : μ.support.Nonempty := by
  rw [← Finset.card_pos]
  by_contra hcard
  have hempty : μ.support = ∅ := by
    rw [← Finset.card_eq_zero]
    omega
  have h1 := hμ.weight_sum_eq_one
  rw [hempty] at h1
  simp_all

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
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support.image f) ×ˢ ν.support = (μ.support ×ˢ ν.support).image _
    ext p
    rcases p with ⟨c, b⟩
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    grind
  · simp only [Distribution.avgOver_prod, Distribution.avgOver_map]

/-! ## The first marginal of a product -/

/-- The first marginal of a product whose second factor is a probability law
is the first factor.  Blueprint `lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (μ : Distribution α) (ν : Distribution β) (hν : ν.IsProbability) :
    (Distribution.prod μ ν).map Prod.fst = μ := by
  obtain ⟨b, hb⟩ := Distribution.support_nonempty_of_isProbability hν
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support ×ˢ ν.support).image Prod.fst = μ.support
    ext a
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    grind
  · simp only [Distribution.avgOver_prod, Distribution.avgOver_map,
      avgOver_const_of_isProbability, hν]

/-- Reading a function of the first factor of a product whose second factor is
a probability law is reading it on the first factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_of_fst {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (hν : ν.IsProbability) (h : α → γ) :
    (Distribution.prod μ ν).map (fun w => h w.1) = μ.map h := by
  rw [← Distribution.map_map (Distribution.prod μ ν) Prod.fst h,
    Distribution.prod_map_fst μ ν hν]

/-! ## A product as a dependent mixture -/

/-- A push-forward of a product is the dependent mixture, over the first
factor, of the push-forwards of the second factor.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.prod_map_eq_bind {α β γ : Type*} [DecidableEq α]
    [DecidableEq β] [DecidableEq γ] (μ : Distribution α) (ν : Distribution β)
    (g : α × β → γ) :
    (Distribution.prod μ ν).map g =
      Distribution.bind μ (fun a => ν.map (fun b => g (a, b))) := by
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (μ.support ×ˢ ν.support).image g =
      μ.support.biUnion (fun a => ν.support.image (fun b => g (a, b)))
    grind
  · simp only [Distribution.avgOver_prod, Distribution.avgOver_map, avgOver_bind]

/-! ## The support and the weight of a product -/

section

variable {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β)
include α β μ ν

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

end

/-! ## Push-forward along a bijection -/

/-- A push-forward along a bijection is identified by the supports and the
weights it compares: if the map matches the two supports and carries each
weight to the corresponding weight, and if it has a two-sided inverse, the
push-forward is the target law.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem Distribution.map_bijective_eq {α β : Type*} [DecidableEq α]
    [DecidableEq β] (μ : Distribution α) (ν : Distribution β) (f : α → β)
    (g : β → α) (hgf : ∀ a, g (f a) = a) (hfg : ∀ b, f (g b) = b)
    (hs : ∀ a, a ∈ μ.support ↔ f a ∈ ν.support)
    (hw : ∀ a, μ.weight a = ν.weight (f a)) :
    μ.map f = ν := by
  classical
  refine Distribution.ext_of_support_of_weight ?_ ?_
  · simp
    ext b
    simp
    constructor
    · grind
    · intro hb
      refine ⟨g b, (hs (g b)).mpr ?_, hfg b⟩
      rw [hfg b]
      assumption
  · funext b
    simp
    have hfilter : μ.support.filter (fun a => f a = b) =
        μ.support.filter (fun a => a = g b) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · grind
      · grind
    rw [hfilter, Finset.filter_eq' μ.support (g b)]
    by_cases hmem : g b ∈ μ.support
    · simp_all
    · rw [if_neg hmem, Finset.sum_empty]
      refine (ν.outsideSupport b ?_).symm
      simp_all

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
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change μ.support ×ˢ ν.support.image g = (μ.support ×ˢ ν.support).image _
    ext p
    rcases p with ⟨a, c⟩
    simp only [Finset.mem_product, Finset.mem_image, Prod.mk.injEq, Prod.exists]
    grind
  · simp only [Distribution.avgOver_prod, Distribution.avgOver_map]

/-! ## Uniform laws on products -/

/-- Formalization-only auxiliary: the uniform law on a product of two finite
types is the product of the uniform laws.  Blueprint
`lem:qld-sublines`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1063-1116`. -/
theorem uniformDistribution_prod (α β : Type*) [Fintype α] [DecidableEq α]
    [Nonempty α] [Fintype β] [DecidableEq β] [Nonempty β] :
    uniformDistribution (α × β) =
      Distribution.prod (uniformDistribution α) (uniformDistribution β) := by
  refine Distribution.ext_of_support_of_avgOver ?_ fun F => ?_
  · change (Finset.univ : Finset (α × β)) = (Finset.univ : Finset α).product (Finset.univ : Finset β)
    simp
  · rw [Distribution.avgOver_prod]
    exact avgOver_uniform_prod (fun a b => F (a, b))

/-! ## Conditioning one factor of a product -/

/-! ## Conditioning the first factor of a product -/

/-! ## Restriction of a push-forward -/

end MIPStarRE.QPBT
