import RequestProject.OrderNerveSingularCarriers
import RequestProject.TopologicalSingular.SupportedFillings


namespace FiniteChains.Comb
open TopologicalSingular

noncomputable def orderSingularCarrierChains {P} [PartialOrder P] {n}
    (σ : Simplex (orderNerveRealization P) n) k :=
  subChains (orderNerveRealizationSubcomplex P (orderNerveSingularCarrier σ) :
    Set (orderNerveRealization P)) k

theorem orderSingularCarrierChains_face {P} [PartialOrder P] {n}
    (σ : Simplex (orderNerveRealization P) (n + 1)) i k :
    orderSingularCarrierChains (face i σ) k ≤ orderSingularCarrierChains σ k :=
  subChains_mono (orderNerveRealizationSubcomplex_mono (orderNerveSingularCarrier_face σ i)) k

theorem orderSingularCarrierChains_single {P} [PartialOrder P] {n}
    (σ : Simplex (orderNerveRealization P) n) r :
    Finsupp.single σ r ∈ orderSingularCarrierChains σ n :=
  single_mem_subChains _ n σ r (orderNerveSingularSimplex_mem_carrier σ)

theorem orderSingularCarrierChains_cycle_bounds {P} [PartialOrder P] {n}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty) k
    c
    (hc : c ∈ orderSingularCarrierChains σ (k + 1)) (hz : boundary k c = 0) :
    ∃ b,
      b ∈ orderSingularCarrierChains σ (k + 2) ∧ boundary (k + 1) b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact contractible_supported_cycle_bounds _ k c hc hz

theorem orderSingularCarrierChains_zero_bounds {P} [PartialOrder P] {n}
    (σ : Simplex (orderNerveRealization P) n)
    (hσ : (orderNerveSingularStarIndices σ).Nonempty)
    c
    (hc : c ∈ orderSingularCarrierChains σ 0) (hz : augmentation c = 0) :
    ∃ b,
      b ∈ orderSingularCarrierChains σ 1 ∧ boundary 0 b = c := by
  letI := orderNerveSingularCarrier_subcomplex_contractible σ hσ
  exact connected_supported_zero_bounds _ c hc hz
