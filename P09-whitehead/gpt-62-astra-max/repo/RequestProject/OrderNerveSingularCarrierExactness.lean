module

public import RequestProject.OrderNerveSingularCarriers
public import RequestProject.TopologicalSingular.SupportedFillings

@[expose] public section

namespace FiniteChains.Comb
open TopologicalSingular

variable {P : Type} [PartialOrder P] {n : ℕ}

noncomputable def orderSingularCarrierChains
    (σ : Simplex (orderNerveRealization P) n) (k : ℕ) :=
  subChains (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
    Set (orderNerveRealization P)) k

theorem orderSingularCarrierChains_face
    (σ : Simplex (orderNerveRealization P) _) (i : Fin (n + 2)) (k : ℕ) :
    orderSingularCarrierChains (face i σ) k ≤ orderSingularCarrierChains σ k :=
  subChains_mono (orderNerveRealizationSubcomplex_mono (orderNerveSingularCarrier_face σ i)) k

variable (σ : Simplex (orderNerveRealization P) n)

theorem orderSingularCarrierChains_single (r : ℤ) :
    Finsupp.single σ r ∈ orderSingularCarrierChains σ n :=
  single_mem_subChains _ n σ r (orderNerveSingularSimplex_mem_carrier σ)

variable (hσ : (orderNerveSingularStarIndices σ).Nonempty)
include hσ

theorem orderSingularCarrierChains_cycle_bounds (k : ℕ)
    (c : Chain (orderNerveRealization P) _)
    (hc : c ∈ orderSingularCarrierChains σ _) (hz : boundary k c = 0) :
    ∃ b : Chain (orderNerveRealization P) _,
      b ∈ orderSingularCarrierChains σ _ ∧ boundary _ b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  apply contractible_supported_cycle_bounds <;> assumption

theorem orderSingularCarrierChains_zero_bounds
    (c : Chain (orderNerveRealization P) 0)
    (hc : c ∈ orderSingularCarrierChains σ 0) (hz : augmentation c = 0) :
    ∃ b : Chain (orderNerveRealization P) 1,
      b ∈ orderSingularCarrierChains σ 1 ∧ boundary 0 b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  apply connected_supported_zero_bounds <;> assumption

end FiniteChains.Comb
