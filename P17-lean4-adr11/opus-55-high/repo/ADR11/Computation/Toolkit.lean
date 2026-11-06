module

public import ADR11.Computation.Engine
public import ADR11.SmallTrees

/-!
# A toolkit for explicit gene tree distributions of small species trees

Helpers used by the `msc` tactics of `ADR11.Rootings.Proofs`: comparing code lists as sets
(`sameSet`), polynomials given as lists of (rational coefficient, monomial) (`evalPoly`), and
`sum_eq_evalPoly_collect`, which collects the terms of a verified computation of
`ADR11.Computation.Engine` whose family has given codes.
-/

@[expose] public section

namespace ADR11.Computation

open Finset

/-! ### Certificates -/

/-- Whether two code lists have the same elements. -/
def sameSet (a b : List ℕ) : Bool := a.all (· ∈ b) && b.all (· ∈ a)

theorem decF_eq_iff_sameSet {n : ℕ} {a b : List ℕ} (ha : Valid n a) (hb : Valid n b) :
    decF n a = decF n b ↔ sameSet a b = true := by
  rw [decF_eq_iff ha hb]
  simp [sameSet, List.all_eq_true]

/-- The monomial without its trivial factors. -/
def normKey (k : List (ℕ × ℕ)) : List (ℕ × ℕ) := k.filter (·.2 != 0)

theorem monoVal_normKey {n : ℕ} (len : Finset (Fin n) → ℝ) (k : List (ℕ × ℕ)) :
    monoVal len (normKey k) = monoVal len k := by
  induction k with
  | nil => rfl
  | cons ae k ih =>
    by_cases h : ae.2 = 0
    · aesop
    · simp [normKey, h] at ih ⊢; rw [ih]

/-- The value of a polynomial given as a list of (coefficient, monomial). -/
noncomputable def evalPoly {n : ℕ} (len : Finset (Fin n) → ℝ) (P : List (ℚ × List (ℕ × ℕ))) :
    ℝ :=
  (P.map fun p => (p.1 : ℝ) * monoVal len p.2).sum

@[simp] theorem evalPoly_nil {n : ℕ} (len : Finset (Fin n) → ℝ) : evalPoly len [] = 0 := rfl

@[simp] theorem evalPoly_cons {n : ℕ} (len : Finset (Fin n) → ℝ) (p : ℚ × List (ℕ × ℕ))
    (P : List (ℚ × List (ℕ × ℕ))) :
    evalPoly len (p :: P) = (p.1 : ℝ) * monoVal len p.2 + evalPoly len P := rfl

/-- The (coefficient, monomial) pairs of the terms whose family has the codes `u`. -/
def collect (M : List CTerm) (u : List ℕ) : List (ℚ × List (ℕ × ℕ)) :=
  (M.filter fun τ => sameSet τ.forest u).map fun τ => (τ.coef, normKey τ.key)

theorem sum_eq_evalPoly_collect {m n : ℕ} (len : Finset (Fin n) → ℝ) (M : List CTerm)
    (u : List ℕ) (hM : ∀ τ ∈ M, Valid m τ.forest) (hu : Valid m u) :
    (M.map fun τ => if decF m τ.forest = decF m u then τ.val len else 0).sum =
      evalPoly len (collect M u) := by
  induction M with
  | nil => rfl
  | cons τ M ih =>
    have hiff := decF_eq_iff_sameSet (hM τ List.mem_cons_self) hu
    rw [List.map_cons, List.sum_cons, ih fun τ' h => hM τ' (List.mem_cons_of_mem _ h)]
    by_cases h : sameSet τ.forest u = true
    · rw [ite_eq_left (hiff.2 h)]
      simp [collect, h, CTerm.val, monoVal_normKey]
    · rw [ite_eq_right (fun h' => h (hiff.1 h'))]
      simp [collect, h]

end ADR11.Computation
