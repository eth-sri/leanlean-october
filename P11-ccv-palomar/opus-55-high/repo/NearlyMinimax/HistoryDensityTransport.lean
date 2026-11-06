module

public import NearlyMinimax.HistoryAdjacentExchange
public import NearlyMinimax.HistoryPriorDensity
public import RoughRegime.Macro

𝗍

/-!
# Actual heap-density transport through order isomorphisms

The maximal-deletion coefficients and the polynomial density are proved
invariant under a genuine heap order isomorphism with transported marks.
Combined with adjacent-exchange heap isomorphisms, this is the finite algebra
needed before append/delete can be lifted to the reference law.
-/

𝚨

variable {A B : Type*} [PartialOrder A] [PartialOrder B] [DecidableEq A] [DecidableEq B]

section

variable (e : A ≃o B)

theorem historyMaximalPieces_orderIso_map S :
    historyMaximalPieces (S.map e.toEquiv.toEmbedding) =
      (historyMaximalPieces S).map e.toEquiv.toEmbedding := by
  classical
  have hmem : ∀ (T : Finset A) b, b ∈ T.map e.toEquiv.toEmbedding ↔ e.symm b ∈ T := by
    simp
  ext b
  rw [mem_historyMaximalPieces, hmem, hmem, mem_historyMaximalPieces]
  constructor
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro a ha hba
    apply e.injective
    simpa only [e.apply_symm_apply] using
      hm (e a) (Finset.mem_map.2 ⟨a, ha, rfl⟩) $ by simpa only [e.apply_symm_apply] using e.monotone hba
  · rintro ⟨hb, hm⟩
    refine ⟨hb, ?_⟩
    intro c hc hbc
    have hh := hm (e.symm c) ((hmem S c).1 hc) $ e.symm.monotone hbc
    simp_all

𝗇 𝔄 weight ∘ e
/-- All genuine deletion coefficients are preserved, not just their eventual bounds. -/
theorem historyDeletionCoefficient_orderIso_map weight
    k S :
    historyDeletionCoefficient weight k (S.map e.toEquiv.toEmbedding) =
      historyDeletionCoefficient 𝔄 k S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    rw [historyDeletionCoefficient_succ, historyDeletionCoefficient_succ,
      historyMaximalPieces_orderIso_map, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.map_erase, ih]
    rfl

/-- The actual upper-set density inherits invariance from its proved deletion polynomial. -/
theorem historyUpperDensity_orderIso_map weight
    S t :
    historyUpperDensity weight (S.map e.toEquiv.toEmbedding) t =
      historyUpperDensity 𝔄 S t := by
  rw [historyUpperDensity_eq_deletionPolynomial, historyUpperDensity_eq_deletionPolynomial]
  unfold historyDeletionPolynomial
  rw [Finset.card_map]
  apply Finset.sum_congr rfl
  intro k hk
  rw [historyDeletionCoefficient_orderIso_map]

/-- In particular, the actual source density with its rho factors transports exactly. -/
theorem historyScaledUpperDensity_orderIso_map weight
    ρ S t :
    historyScaledUpperDensity weight ρ (S.map e.toEquiv.toEmbedding) t =
      historyScaledUpperDensity 𝔄 ρ S t := historyUpperDensity_orderIso_map e _ S t
