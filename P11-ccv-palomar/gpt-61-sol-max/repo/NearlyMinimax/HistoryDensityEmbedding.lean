module

public import NearlyMinimax.HistoryDensityTransport


@[expose] public section

/-!
# Exact polynomial transport through actual order embeddings
-/

noncomputable section
namespace NearlyMinimax

variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]

section
variable (f : A ↪o B)

theorem historyMaximalPieces_orderEmbedding_map  S :
    historyMaximalPieces (S.map f.toEmbedding) = (historyMaximalPieces S).map f.toEmbedding := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨hb, hm⟩ := mem_historyMaximalPieces.1 hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
    refine Finset.mem_map.2 ⟨x, mem_historyMaximalPieces.2 ⟨hx, ?_⟩, rfl⟩
    intro y hy hxy
    exact f.injective (hm (f y) (Finset.mem_map.2 ⟨y, hy, rfl⟩) (f.monotone hxy))
  · intro hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hb
    obtain ⟨hx, hm⟩ := mem_historyMaximalPieces.1 hx
    refine mem_historyMaximalPieces.2 ⟨Finset.mem_map.2 ⟨x, hx, rfl⟩, ?_⟩
    simp_all

theorem historyDeletionCoefficient_orderEmbedding_map  weight
    k S :
    historyDeletionCoefficient weight k (S.map f.toEmbedding) =
      historyDeletionCoefficient (weight ∘ f) k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ,
      historyMaximalPieces_orderEmbedding_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.map_erase, ih]
    rfl

theorem historyUpperDensity_orderEmbedding_map  weight
    S t :
    historyUpperDensity weight (S.map f.toEmbedding) t = historyUpperDensity (weight ∘ f) S t := by
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial
  rw [Finset.card_map]
  apply Finset.sum_congr rfl
  intro k hk
  rw [historyDeletionCoefficient_orderEmbedding_map]

theorem historyScaledUpperDensity_orderEmbedding_map  weight
    ρ S t :
    historyScaledUpperDensity weight ρ (S.map f.toEmbedding) t =
      historyScaledUpperDensity (weight ∘ f) ρ S t := historyUpperDensity_orderEmbedding_map f _ S t
end


end NearlyMinimax
