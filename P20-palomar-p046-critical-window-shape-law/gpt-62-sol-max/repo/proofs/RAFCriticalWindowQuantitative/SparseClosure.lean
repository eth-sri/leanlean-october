module

public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.HordijkSteelThreshold.ReversibleClosure
public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

/-- Food is short, and one enabled channel can at most double the length bound. -/
def LengthGrowth {N : ℕ} {R : Type*} (Q : ReversibleCRS (Molecule N) R) : Prop :=
  (∀ x ∈ Q.food, molLength x ≤ 2) ∧
  ∀ C r b, (∀ x ∈ C, molLength x ≤ b) →
    (Q.lhs r ⊆ C ∨ Q.rhs r ⊆ C) → ∀ x ∈ Q.lhs r ∪ Q.rhs r, molLength x ≤ 2*b

theorem split_growth (N : ℕ) : LengthGrowth (binaryPolymerCRS N 2) := by
  constructor
  · simp [binaryPolymerCRS, binaryFood]
  · simp [binaryPolymerCRS, Finset.insert_subset_iff]
    grind [reaction_length_add, molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct]

theorem quotient_growth (N : ℕ) : LengthGrowth (repositoryCRS N 2) := by
  constructor
  · exact (split_growth N).1
  · intro C r b hC
    obtain ⟨s,rfl⟩ := splitToQuotient_surjective N r
    rw [(quotient_sides (t := 2) s).1,
      (quotient_sides (t := 2) s).2]
    exact (split_growth N).2 C s b hC

/-- Grow a productive history while keeping all selected channels settled.
When a new channel is enabled, its endpoints and the old closure already
form a closed set for the enlarged history. -/
theorem long_target_productive_history {N : ℕ} {R : Type*} [DecidableEq R]
    (Q : ReversibleCRS (Molecule N) R) (hQ : LengthGrowth Q)
    (S : Finset R) (k : ℕ) (x : Molecule N) (hx : x ∈ fullClosure Q S)
    (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S ∧
      (∀ r ∈ T, Q.lhs r ∪ Q.rhs r ⊆ fullClosure Q T) ∧
      ∀ y ∈ fullClosure Q T, molLength y ≤ 2^(k+1) := by
  induction k with
  | zero =>
    refine ⟨∅, .nil, by simp, by simp, by simp, ?_⟩
    simpa [fullClosure_eq_food_of_no_seed Q ∅ (by simp)] using hQ.1
  | succ k ih =>
    have hp : 2^(k+1) < molLength x := by rw [pow_succ] at hlen; omega
    obtain ⟨T,hT,hcard,hTS,hsettled,hl⟩ := ih hp
    let C := fullClosure Q T
    obtain ⟨r,hr,he,hn⟩ : ∃ r ∈ S, (Q.lhs r ⊆ C ∨ Q.rhs r ⊆ C) ∧ ¬ Q.lhs r ∪ Q.rhs r ⊆ C := by
      by_contra! h
      exact hp.not_ge (hl x (fullClosure_least (fullClosure_food Q T) h hx))
    have hrT : r ∉ T := fun h => hn (hsettled r h)
    have hD : fullClosure Q (insert r T) ⊆ (C ∪ (Q.lhs r ∪ Q.rhs r)) := fullClosure_least
      ((fullClosure_food Q T).trans Finset.subset_union_left)
      (by grind)
    have hsub : C ⊆ fullClosure Q (insert r T) := fullClosure_mono Q (Finset.subset_insert ..)
    refine ⟨insert r T, .step hT hr hrT (by simpa [revClosureStep_eq_iff, RevClosed] using And.intro he hn),
      by simp_all, Finset.insert_subset hr hTS, ?_, ?_⟩
    · have hr := fullClosure_completes Q (S := insert r T) (Finset.mem_insert_self ..)
      grind
    · intro y hy
      have h := hQ.2 C r _ hl he y
      rw [pow_succ]
      grind

open Classical MeasureTheory unitInterval

def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r

def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem catalogue_sparse_bound {J : Type*} [Fintype J] {g : CutMap}
    (a : I) (r : ℕ) (C : FiniteCatalogue J (sparseWitnessCap r) g)
    (hC : LengthGrowth (C.crs 2)) :
    latentSurvival g a ≤ ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r := by
  refine ((latent_survival_le_escape g a _).trans_eq ((C.escape_restriction _ a).2 rfl).symm).trans ?_
  rw [← Finset.card_univ (α := J), ← Finset.card_powersetCard]
  refine measure_le_card_mul _ (blockEvent · True) ?_ ?_
  · rintro ω ⟨x,hx,hl⟩
    obtain ⟨T,_,hcard,hT,_,_⟩ := long_target_productive_history (C.crs 2) hC _ r x hx ((Nat.le_add_right _ 2).trans_lt hl)
    exact ⟨T, by simp [hcard], by simpa [blockEvent, Finset.subset_iff] using hT⟩
  · intro T hT
    simpa [← Measure.infinitePi_eq_pi, (Finset.mem_powersetCard.mp hT).2] using (iid_block a T True).2.le

theorem sparse_toReal {s : ENNReal} {a : I} {r c : ℕ}
    (h : s ≤ (c : ENNReal)*(toNNReal a : ENNReal)^r) : s.toReal ≤ (c : ℝ)*(a : ℝ)^r := by
  simpa using ENNReal.toReal_mono (by finiteness) h

/-- The quadratic certificate uses the channel count, not an enumeration of fields. -/
theorem worked_low_openness_bound (a : I) (ha : (a : ℝ) ≤ 1/10^20) :
    (staticSurvival a).toReal < 8/10^26 := by
  rw [staticSurvival_pullback]
  refine (sparse_toReal (catalogue_sparse_bound a 2 (splitCatalogue _) (split_growth _))).trans_lt ?_
  have := a.property.1
  grw [ha]
  norm_num [sparseWitnessCap, Nat.choose_two_right, Fin.sum_univ_eq_sum_range (fun i : ℕ => 2^(i+1)*i)]

end RAFCriticalWindowQuantitative
