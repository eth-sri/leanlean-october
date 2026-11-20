module
public import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation

/-! Productive histories, sparse witnesses and intensity flatness. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAF.Concrete RAF.Polymer RAFReactionQuotient OverlapCorrectedRAF.Source MeasureTheory unitInterval

inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

namespace Model
variable (M : Model) {n : ℕ}

/-- Build the history by adding an enabled channel at each step. We keep *both*
sides of every channel chosen so far in the current length box. This box then
bounds their full closure too, regardless of how many closure rounds are run. -/
theorem long_history (n k : ℕ) (S : Finset (M.Channel n)) (x : Molecule n)
    (hx : x ∈ Finset.univ.filter fun y => ∃ t, y ∈ revClosureAt (M.system n) S t) (hlen : 2^(k+1) < molLength x) :
    ∃ T, ProductiveHistory (M.system n) S k T ∧ T.card = k ∧ T ⊆ S := by
  let Q := M.system n
  let A k := binaryFood n (2^(k+1))
  have mono : Monotone A := by
    intro i j h; apply Finset.monotone_filter_right; intro _ _ hl
    exact hl.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have food k : Q.food ⊆ A k := mono (Nat.zero_le k)
  suffices ∃ T, (ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S) ∧
      ∀ r ∈ T, Q.lhs r ∪ Q.rhs r ⊆ A k by grind
  induction k with
  | zero => exact ⟨∅,⟨.nil,rfl,Finset.empty_subset _⟩,by simp⟩
  | succ k ih =>
    have hp : 2^(k+1) < molLength x := by rw [pow_succ] at hlen; omega
    obtain ⟨T,⟨hist,hk,hs⟩,ht⟩ := ih hp
    let C := fullClosure Q T
    have inc : C ⊆ A k := full_le Q T (food k) fun r hr =>
      let h := Finset.union_subset_iff.mp (ht r hr); iff_of_true h.1 h.2
    obtain ⟨r,hr,he⟩ : ∃ r ∈ S, ¬(Q.lhs r ⊆ C ↔ Q.rhs r ⊆ C) := by
      by_contra! hc
      have := inc (full_le Q S (full_food Q T) hc ((full_mem Q S x).mpr (Finset.mem_filter.mp hx).2))
      exact hp.not_ge (Finset.mem_filter.mp this).2
    have fresh : r ∉ T := fun h => he (full_closed Q T r h)
    have grows : revClosureStep Q {r} C ≠ C := fun h => he (((closed_iff Q {r} C).mpr h.le) r (by simp))
    refine ⟨insert r T,⟨.step hist hr fresh grows,by simp [fresh,hk],Finset.insert_subset hr hs⟩,?_⟩
    rw [Finset.forall_mem_insert]; refine ⟨?_,fun s h => (ht s h).trans (mono (Nat.le_succ k))⟩
    have either : Q.lhs r ⊆ A k ∨ Q.rhs r ⊆ A k := by grind [Finset.Subset.trans]
    simpa only [A,pow_succ,mul_left_comm,mul_comm] using (M.enabled_box r (2^(k+1)) either).2

end Model
def sparseWitnessCap (r : ℕ) : ℕ := 2*(2^(r+1)+2)
namespace Model
variable (M : Model)

def coefficient (r : ℕ) := (Fintype.card (M.Channel (sparseWitnessCap r))).choose r

theorem sparse_real (a : I) (r : ℕ) : (M.survival a).toReal ≤ (M.coefficient r : ℝ)*(a : ℝ)^r := by
  let K := 2^(r+1)
  let N := sparseWitnessCap r
  have hs := M.survival_le a (K+2)
  rw [M.escape_eq] at hs
  have h := hs.trans <| (measure_mono ?_).trans (finite_many_open_probability (M.Channel N) a r)
  · exact ENNReal.toReal_mono (by finiteness) h
  · rintro ω ⟨x,hx,hl⟩
    have len : K < molLength x := by omega
    obtain ⟨T,_,ht,hs⟩ := M.long_history N r _ x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨_,hx⟩⟩) len
    exact ht ▸ Finset.card_le_card hs
end Model
def splitSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (Reaction (sparseWitnessCap r))).choose r
def quotientSparseCoefficient (r : ℕ) : ℕ := (Fintype.card (RepositoryChannel (sparseWitnessCap r))).choose r

theorem Model.flatness (M : Model) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, ∀ h : 0 < t, t < δ →
      (M.survival (criticalOpenness t h)).toReal < ε*t^d := by
  let c : ℝ := M.coefficient (d+1)
  refine ⟨ε/(c+1), by positivity, ?_⟩
  intro t ht hδ
  let a := criticalOpenness t ht
  have ha : (a : ℝ) ≤ t := by change 1-Real.exp (-t) ≤ t; linarith [Real.add_one_le_exp (-t)]
  have hct : c*t < ε := by linarith [(lt_div_iff₀ (show 0 < c+1 by positivity)).mp hδ]
  calc
    _ ≤ c * (a : ℝ)^(d+1) := M.sparse_real a _
    _ ≤ c * t^(d+1) := by gcongr; grind
    _ = c*t * t^d := by grind
    _ < _ := mul_lt_mul_of_pos_right hct (pow_pos ht _)


/-- A fully symbolic certificate, requiring no enumeration of channel fields. -/
theorem worked_low_openness_bound (a : I) (ha : (a : ℝ) ≤ 1/10^20) :
    (staticSurvival a).toReal < 8/10^26 := by
  have hc : Model.split.coefficient 2 = 712483666919430 := by
    change (Fintype.card (RAF.Polymer.Reaction 20)).choose 2 = _
    simp only [Reaction,Word,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,Nat.choose_two_right]
    decide
  have hs := Model.split.sparse_real a 2
  rw [hc] at hs
  change (staticSurvival a).toReal ≤ _ at hs
  norm_num at hs
  linarith [pow_le_pow_left₀ a.2.1 ha 2]

end RAFCriticalWindowQuantitative
