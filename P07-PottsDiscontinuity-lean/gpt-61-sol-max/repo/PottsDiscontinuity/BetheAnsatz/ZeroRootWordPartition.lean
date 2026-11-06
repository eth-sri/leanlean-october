module
public import Mathlib

public import PottsDiscontinuity.BetheAnsatz.ZeroRootT1Aggregate
public import PottsDiscontinuity.BetheAnsatz.ZeroRootWordCancellationSum

/-!
# The finite index set of the zero-root T₁ residues

A surviving word has a unique ML edge, and the perturbed root occupies one of
its two endpoints. The two choices of endpoint are the two summands of a
canonical `T1PairIndex` pair.
-/

@[expose] public section



namespace PottsDiscontinuity.BetheAnsatz

/-- A fixed-amplitude word term with a unique ML edge incident to the slot
occupied by the distinguished root. `side = false` places the root at the
right endpoint; `side = true` places it at the left endpoint. -/
structure RootIncidentTermIndex (n : ℕ) (l : Fin (n + 1)) where
  edge : Option (Fin n)
  side : Bool
  σ : RootSlotPerm l (if side then t1EdgeLeft edge else t1EdgeRight edge)
  w : Fin (n + 1) → Bool
  hleft : w (t1EdgeLeft edge) = false
  hright : w (t1EdgeRight edge) = true
  hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
    k = t1EdgeLeft edge

@[ext]
theorem RootIncidentTermIndex.ext {n : ℕ} {l : Fin (n + 1)}
    {i j : RootIncidentTermIndex n l}
    (hedge : i.edge = j.edge) (hside : i.side = j.side)
    (hσ : i.σ.1 = j.σ.1) (hw : i.w = j.w) : i = j := by
  cases i with
  | mk edge side σ w hleft hright hunique =>
    aesop

noncomputable instance rootIncidentTermIndexFintype {n : ℕ} {l : Fin (n + 1)} :
    Fintype (RootIncidentTermIndex n l) := by
  classical
  apply Fintype.ofInjective
     fun i : RootIncidentTermIndex n l => (i.edge, i.side, i.σ.1, i.w) 
  intro i j hij
  simp only [Prod.mk.injEq] at hij
  rcases hij with ⟨hedge, hside, hσ, hw⟩
  exact RootIncidentTermIndex.ext hedge hside hσ hw

/-- Put the zero label at the right (false) or left (true) end of a pair's ML edge. -/
noncomputable def t1PairSideForward {n : ℕ} {l : Fin (n + 1)}
    (v : T1PairIndex n l × Bool) : RootIncidentTermIndex n l := by
  rcases v with ⟨i, side⟩
  cases side
  · exact ⟨i.edge, false, ⟨i.σ, i.hσ⟩, i.w, i.hleft, i.hright, i.hunique⟩
  · refine ⟨i.edge, true, ⟨i.σ * Equiv.swap (t1EdgeLeft i.edge)
      (t1EdgeRight i.edge), ?_⟩, i.w, i.hleft, i.hright, i.hunique⟩
    change i.σ (Equiv.swap (t1EdgeLeft i.edge) (t1EdgeRight i.edge)
      (t1EdgeLeft i.edge)) = l
    rw [Equiv.swap_apply_left]
    exact i.hσ

/-- Recover the canonical orientation, undoing the endpoint swap on the
member whose root is at the left endpoint. -/
noncomputable def rootIncidentToPair {n : ℕ} {l : Fin (n + 1)}
    (j : RootIncidentTermIndex n l) : T1PairIndex n l × Bool := by
  cases j with
  | mk edge side σ w hleft hright hunique =>
    cases side
    · exact ⟨⟨σ.1, w, edge, σ.2, hleft, hright, hunique⟩, false⟩
    · 
      exact ⟨⟨σ.1 * Equiv.swap (t1EdgeLeft edge) (t1EdgeRight edge),
        w, edge,  by
                    aesop , hleft, hright, hunique⟩, true⟩

/-- The canonical pair and a choice of which member carries the zero root. -/
noncomputable def t1PairSideEquiv {n : ℕ} {l : Fin (n + 1)} :
    T1PairIndex n l × Bool ≃ RootIncidentTermIndex n l where
  toFun := t1PairSideForward
  invFun := rootIncidentToPair
  left_inv := by
    rintro ⟨i, side⟩
    cases side
    · rfl
    · simp_all [t1PairSideForward, rootIncidentToPair]
  right_inv := by
    intro j
    cases j with
    | mk edge side σ w hleft hright hunique =>
      cases side <;> apply RootIncidentTermIndex.ext <;>
        simp [t1PairSideForward, rootIncidentToPair]

/-- The raw permutation and word underlying a root-incident index. -/
noncomputable def rootIncidentUnderlying {n : ℕ} {l : Fin (n + 1)}
    (i : RootIncidentTermIndex n l)  := (i.σ.1, i.w)

section

variable {n : ℕ}
include n

/-- The endpoints of a cyclic edge are distinct when the cycle has at least
two vertices. -/
theorem t1EdgeLeft_ne_right  (hn : 0 < n) (e : Option (Fin n)) :
    t1EdgeLeft e ≠ t1EdgeRight e := by
  cases e with
  | none =>
      grind [t1EdgeLeft, t1EdgeRight]
  | some a =>
      grind [t1EdgeLeft, t1EdgeRight]

/-- Forgetting the unique-edge and orientation witnesses is injective: the
word determines its unique ML edge, and the permutation determines which
endpoint carries the distinguished label. -/
theorem rootIncidentUnderlying_injective  {l : Fin (n + 1)}
    (hn : 0 < n) : Function.Injective (rootIncidentUnderlying (n := n) (l := l)) := by
  intro i j hij
  have hσ : i.σ.1 = j.σ.1 := congrArg Prod.fst hij
  have hw : i.w = j.w := congrArg Prod.snd hij
  
  have hedge  := t1EdgeLeftEquiv.injective (by
                                              symm
                                              apply i.hunique (t1EdgeLeft j.edge)
                                              · rw [hw]
                                                exact j.hleft
                                              · rw [hw, t1EdgeLeft_rotate]
                                                exact j.hright)
  have hroot : (if i.side then t1EdgeLeft i.edge else t1EdgeRight i.edge) =
       if j.side then t1EdgeLeft j.edge else t1EdgeRight j.edge  := by
    apply i.σ.1.injective
    grind
  
  exact RootIncidentTermIndex.ext hedge (by
                                           grind [t1EdgeLeft_ne_right]) hσ hw



/-- A nonconstant cyclic Boolean word has at least one ML edge. -/
theorem exists_cyclicML_of_nonconstant  (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false) :
    ∃ a, w a = false ∧ w (finRotate (n + 1) a) = true := by
  rcases nonconstant_word_has_ML w hL hM with ⟨a, ha, hb⟩ | ⟨ha, hb⟩
  all_goals aesop

/-- If all ML edges touch the zero-root slot, a nonconstant word determines
one unique edge and therefore a canonical root-incident T₁ term. -/
theorem exists_rootIncidentTerm_of_allMLIncident  {l : Fin (n + 1)}
    (r : Fin (n + 1)) (σ : RootSlotPerm l r) (w : Fin (n + 1) → Bool)
    (hL : w ≠ fun _ => true) (hM : w ≠ fun _ => false)
    (hAll : ∀ a, w a = false → w (finRotate (n + 1) a) = true →
      r = a ∨ r = finRotate (n + 1) a) :
    ∃ i : RootIncidentTermIndex n l, i.σ.1 = σ.1 ∧ i.w = w := by
  obtain ⟨a, ha, hb⟩ := exists_cyclicML_of_nonconstant w hL hM
  
  let edge := t1EdgeLeftEquiv.symm a
  have hleft : t1EdgeLeft edge = a := t1EdgeLeftEquiv.apply_symm_apply a
  have hright : t1EdgeRight edge = finRotate (n + 1) a := by
    rw [← t1EdgeLeft_rotate edge, hleft]
  have hunique : ∀ k, w k = false → w (finRotate (n + 1) k) = true →
      k = t1EdgeLeft edge := by
    simp_all <;> grind
  rcases (hAll a ha hb) with hrootL | hrootR
  · refine ⟨⟨edge, true, ⟨σ.1, ?_⟩, w, ?_, ?_, hunique⟩, rfl, rfl⟩
    all_goals grind
  · refine ⟨⟨edge, false, ⟨σ.1, ?_⟩, w, ?_, ?_, hunique⟩, rfl, rfl⟩
    all_goals grind

end

end PottsDiscontinuity.BetheAnsatz
