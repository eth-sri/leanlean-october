module

public import MIPStarRE.Quantum.Measurement
public import MIPStarRE.Quantum.FiniteMatrix.BlockDiagonal
public import MIPStarRE.LDT.Basic.DistributionAvg
public import MIPStarRE.LDT.Basic.TensorPlacement
public import MIPStarRE.LDT.Preliminaries.FiniteFields

/-!
# Public helpers for the upstream LIDT interface

These finite-sum and measurement lemmas support the QPBT without modifying its LIDT dependency.
The marginal-state construction and rank-zero argument adapt the private proofs in
`LionSR/MIPStarRE`, commit `5fc363bc8b77b1a6bbdaaeea634f1b0f3ff0ad79`, module
`MIPStarRE.LDT.MakingMeasurementsProjective.LocalityPreservingRepair`.
The remaining lemmas are QPBT extensions of the upstream measurement and distribution APIs.
Their proofs use the public definitions and Mathlib finite-dimensional linear algebra.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- Summing a two-argument function on the fibers of `f` pulls the second argument back along `f`. -/
theorem Finset.sum_fiberwise_apply {A B M : Type*} [Fintype B] [DecidableEq B] [AddCommMonoid M]
    (s : Finset A) (f : A → B) (g : A → B → M) :
    (∑ b, ∑ a ∈ s.filter (fun a => f a = b), g a b) = ∑ a ∈ s, g a (f a) := by
  rw [← Finset.sum_fiberwise s f (fun a => g a (f a))]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a ha => by simp_all

namespace MIPStarRE.Quantum.Measurement
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β : Type*} [Fintype α] [Fintype β]

/-- A complete measurement is determined by its effects. -/
theorem ext {M N : Measurement α d} (h : ∀ a, M.effect a = N.effect a) :
    M = N := by
  cases M with
  | mk M hM =>
      cases N with
      | mk N hN =>
          cases M with
          | mk effectM posM leM =>
              cases N with
              | mk effectN posN leN =>
                  grind

/-- Relabeling along `f` and then along `g` is relabeling along `g ∘ f`: the
fiber of `g ∘ f` over `c` is the disjoint union of the fibers of `f` over the
fiber of `g` over `c`, and regrouping a finite sum of effects along it does not
change the sum. -/
theorem postprocess_comp {γ : Type*} [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (M : Measurement α d) (f : α → β) (g : β → γ) :
    (M.postprocess f).postprocess g = M.postprocess (fun a => g (f a)) := by
  classical
  refine ext fun c => ?_
  simp only [postprocess_effect]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  simp

/-- A weighted sum of relabeled effects is the original sum with weights
pulled back along the label map. -/
theorem sum_smul_postprocess [DecidableEq α] [DecidableEq β]
    (M : Measurement α d) (f : α → β) (c : β → ℂ) :
    ∑ b, c b • (M.postprocess f).effect b = ∑ a, c (f a) • M.effect a := by
  simp only [postprocess_effect, Finset.smul_sum, Finset.sum_fiberwise_apply]

end MIPStarRE.Quantum.Measurement

namespace MIPStarRE.LDT

section

variable {α : Type*}
include α

/-- Averaging scalar multiples of a fixed operator averages their coefficients
over the distribution's support. -/
theorem averageOperatorOverDistribution_smul_const {ι : Type*}
    [Fintype ι] [DecidableEq ι] (𝒟 : Distribution α) (c : α → ℂ)
    (A : MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun a => c a • A) =
      (∑ a ∈ 𝒟.support, (𝒟.weight a : ℂ) * c a) • A := by
  simp [averageOperatorOverDistribution, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a ha
  simp [← Complex.real_smul]

/-- A finite average can be summed on any superset of the support. -/
theorem avgOver_eq_sum_superset (μ : Distribution α) (f : α → ℝ)
    {s : Finset α} (hs : μ.support ⊆ s) : avgOver μ f = ∑ a ∈ s, μ.weight a * f a :=
  Finset.sum_subset hs fun a _ ha => by rw [μ.outsideSupport a ha, zero_mul]

/-- A finite average can be summed over the full finite type. -/
theorem avgOver_eq_sum_univ [Fintype α] (μ : Distribution α) (f : α → ℝ) :
    avgOver μ f = ∑ a, μ.weight a * f a :=
  avgOver_eq_sum_superset μ f (Finset.subset_univ _)

/-- A uniform average on a finite support is its normalized finite sum. -/
theorem avgOver_uniformOnFinset_eq_inv_card_mul_sum (s : Finset α) (f : α → ℝ) :
    avgOver (Distribution.uniformOnFinset s) f = (s.card : ℝ)⁻¹ * ∑ a ∈ s, f a := by
  classical
  simp only [avgOver, Distribution.uniformOnFinset_support, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a ha => by simp_all

/-- A uniform average over a finite type is its normalized finite sum. -/
theorem avgOver_uniform_eq_inv_card_mul_sum
    [Fintype α] [DecidableEq α] [Nonempty α] (f : α → ℝ) :
    avgOver (uniformDistribution α) f = (Fintype.card α : ℝ)⁻¹ * ∑ a, f a := by
  simpa only [uniformDistribution, Finset.card_univ] using
    avgOver_uniformOnFinset_eq_inv_card_mul_sum Finset.univ f

end

namespace Distribution.IsProbability

/-- A probability distribution has total weight one over any finite superset
of its explicit support. -/
theorem weight_sum_eq_one_of_subset {α : Type*}
    {𝒟 : Distribution α} (h𝒟 : 𝒟.IsProbability) {s : Finset α}
    (hsubset : 𝒟.support ⊆ s) :
    ∑ a ∈ s, 𝒟.weight a = 1 := have hsum := Finset.sum_subset hsubset fun a x ha ↦ 𝒟.outsideSupport a ha; hsum ▸ weight_sum_eq_one h𝒟

end Distribution.IsProbability
end MIPStarRE.LDT

namespace MIPStarRE.LDT.Preliminaries

variable {p : ℕ} [Fact p.Prime]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fourier orthogonality for the canonical character over an arbitrary finite
coordinate type. This is the finite-index reindexing of
`prop:fourier-fact-vector`. -/
theorem expect_ffChar_sum_mul (v : ι → F) :
    𝔼 u : (ι → F), ffChar (p := p) (F := F) (∑ i, u i * v i) =
      if v = 0 then (1 : ℂ) else 0 := by
  let eι := Fintype.equivFin ι
  let reindex : (ι → F) ≃ (Fin (Fintype.card ι) → F) :=
    { toFun := fun u j => u (eι.symm j)
      invFun := fun u i => u (eι i)
      left_inv := fun u => by
        funext i
        simp
      right_inv := fun u => by
        funext j
        simp }
  let v' : Fin (Fintype.card ι) → F := reindex v
  calc
    𝔼 u : (ι → F), ffChar (p := p) (F := F) (∑ i, u i * v i) =
        𝔼 u : (Fin (Fintype.card ι) → F),
          ffVecChar (p := p) (F := F) v' u := by
      refine Finset.expect_equiv reindex (by simp) ?_
      intro u _
      rw [ffVecChar_apply]
      congr 2
      exact Fintype.sum_equiv eι
        (fun i => u i * v i)
        (fun j => reindex u j * v' j)
        (fun i => by simp [reindex, v'])
    _ = if v' = 0 then (1 : ℂ) else 0 := fourier_fact_vector v'
    _ = if v = 0 then (1 : ℂ) else 0 := by
      have reindex_zero : reindex (0 : ι → F) = 0 := by
        ext j
        rfl
      by_cases hv : v = 0
      · subst v
        rw [show v' = 0 by exact reindex_zero]
        simp
      · have hv' : v' ≠ 0 := by
          intro hv'
          apply hv
          apply reindex.injective
          rw [reindex_zero]
          exact hv'
        simp [hv, hv']

/-- Sum form of canonical-character orthogonality over an arbitrary finite
coordinate type. -/
theorem sum_ffChar_sum_mul (v : ι → F) :
    ∑ u : ι → F, ffChar (p := p) (F := F) (∑ i, u i * v i) =
      if v = 0 then (Fintype.card (ι → F) : ℂ) else 0 := by
  rw [← Fintype.card_smul_expect, expect_ffChar_sum_mul]
  simp

end MIPStarRE.LDT.Preliminaries

namespace MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT
noncomputable section

end
end MIPStarRE.LDT.MakingMeasurementsProjective
