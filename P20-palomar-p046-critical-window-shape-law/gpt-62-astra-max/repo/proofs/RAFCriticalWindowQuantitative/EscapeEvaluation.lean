module
public import proofs.RAFCriticalWindowQuantitative.Models

/-! Exact finite-sum programs for rational escape and seed probabilities. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory unitInterval RAFReactionQuotient OverlapCorrectedRAF.Source RAF.Polymer RAF.Concrete
open scoped ENNReal

variable (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)

def rationalEventProbability
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

open Classical in
/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct (a : I) (ha : (q:ℝ) = a) (event : (J → Bool) → Bool) :
    ((RAFEmergenceApprox.Generic.colLaw J a)
      {ω | event (fun j => decide (ω j))}).toReal =
      (rationalEventProbability J q event : ℝ) := by
  classical
  let E := {ω : J → Prop | event (fun j => decide (ω j))}
  change (Measure.pi (fun _ : J => ambientCoordLaw a)).real E = _
  rw [← integral_indicator_one (Set.toFinite E).measurableSet,integral_fintype .of_finite]
  let e := Equiv.piCongrRight (fun _ : J => Equiv.propEquivBool.symm)
  rw [← e.sum_comp]
  simp [e,E,Equiv.propEquivBool,Set.indicator_apply,Measure.real,Measure.pi_singleton,rationalEventProbability]
  apply Finset.sum_congr rfl; intro ω _
  split <;> simp_all
  apply Finset.prod_congr rfl; intro j _
  cases ω j <;> simp [ambientCoordLaw,ha]

section
variable (N K : ℕ)
def splitEscapeBool (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

end
variable (q : ℚ) (K : ℕ)

def splitEscapeEval : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

variable (N L : ℕ) (q : ℚ)

def splitSeedBool (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

namespace Model
variable (M : Model) {N : ℕ}

def foodClosure (N : ℕ) (ω : M.Channel N → Bool) :=
  computedClosure N 2 (Finset.univ.filter fun r => ω (M.project r))

def evalStat (P : Finset (Molecule N) → Prop) [DecidablePred P] (q : ℚ) :=
  rationalEventProbability _ q (fun ω => decide (P (M.foodClosure N ω)))

def seedEval (N L : ℕ) := M.evalStat (binaryFood N L ⊆ ·)


abbrev escapeEval := M.pick splitEscapeEval quotientEscapeEval

variable (q : ℚ) (a : I) (ha : (q:ℝ) = a)

include ha in
theorem eval_stat (P : Finset (Molecule N) → Prop) [DecidablePred P] :
    (M.evalStat P q : ℝ) =
    (M.static N a {ω | P (M.closure 2 ω)}).toReal := by
  classical
  simpa [evalStat, static, foodClosure, M.closure_eq, ←full_eq_temporary, computedClosure, fullClosure] using
    (rationalEventProbability_correct _ q a ha (fun ω => decide (P (M.foodClosure N ω)))).symm

lemma escape_eq (a : I) (K : ℕ) : M.escapeProb a (K+2) =
    M.static (2*(K+2)) a {ω | hasLonger (K+2) (M.closure 2 ω)} := by
  rw [M.restrict_stat a 2 (hasLonger (K+2))]
  unfold escapeProb
  congr 1; ext ω
  exact escape_iff_large (by omega) _

include ha in
lemma escapeEval_eq (K : ℕ) : (M.escapeEval q K : ℝ) = (M.escapeProb a (K+2)).toReal := by
  rw [M.escape_eq]
  rw [← M.eval_stat q a ha (hasLonger (K+2))]
  cases M <;> simp only [escapeEval,pick,splitEscapeEval,quotientEscapeEval,evalStat] <;> congr 2 <;>
    funext ω <;> simp [hasLonger,quotientEscapeBool,splitEscapeBool,foodClosure,project] <;> congr!

end Model

end RAFCriticalWindowQuantitative
