module

public import proofs.HordijkSteelThreshold.ReversibleClosure
public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters
public import proofs.HordijkSteelThreshold.AmbientIndependence
public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk
public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFCriticalWindowQuantitative.SparseClosure

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAF.Polymer RAF.Concrete MeasureTheory unitInterval RAFReactionQuotient OverlapCorrectedRAF.Source
open scoped ENNReal

/-- A finite executable evaluator, using the literal source's closure iteration. -/
def computedClosure (N L : ℕ) (S : Finset (Reaction N)) : Finset (Molecule N) :=
  revClosureAt (binaryPolymerCRS N L) S (Fintype.card (Molecule N))

def rationalEventProbability (J : Type*) [Fintype J] [DecidableEq J] (q : ℚ)
    (event : (J → Bool) → Bool) : ℚ :=
  ∑ ω : J → Bool, if event ω then ∏ j, if ω j then q else 1-q else 0

open Classical in
/-- Exact probability semantics for an arbitrary executable Boolean event. -/
theorem rationalEventProbability_correct {J : Type*} [Fintype J] [DecidableEq J] {q : ℚ}
    (hq : 0 ≤ q) (hq1 : q ≤ 1) {event : (J → Bool) → Bool} {E : Set (J → Prop)}
    (he : ∀ ω : J → Prop, event (fun j => decide (ω j)) = true ↔ ω ∈ E) :
    (rationalEventProbability J q event : ℝ) =
      (finiteFieldLaw (rationalParameter q hq hq1) E).toReal := by
  let a := rationalParameter q hq hq1
  let e : (J → Bool) ≃ (J → Prop) := Equiv.piCongrRight (fun _ => Equiv.propEquivBool.symm)
  change _ = (finiteFieldLaw a).real E
  rw [← Set.coe_toFinset E, ← sum_measureReal_singleton, ← Set.filter_mem_univ_eq_toFinset,
    Finset.sum_filter, ← e.sum_comp]
  have hw (b : Bool) : (ambientCoordLaw a {↑b}).toReal = if b then (q : ℝ) else 1-q := by aesop
  simp [← he, rationalEventProbability, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod,
    hw, e, Equiv.propEquivBool, apply_ite, Rat.cast_prod]

def splitEscapeBool (N K : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (∃ x ∈ computedClosure N 2 (Finset.univ.filter (fun r => ω r)), K < molLength x)

def quotientEscapeBool (N K : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitEscapeBool N K (fun r => ω (splitToQuotient r))

def splitEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (Reaction (2*(K+2))) q (splitEscapeBool _ (K+2))

def quotientEscapeEval (q : ℚ) (K : ℕ) : ℚ :=
  rationalEventProbability (RepositoryChannel (2*(K+2))) q (quotientEscapeBool _ (K+2))

def splitSeedBool (N L : ℕ) (ω : Reaction N → Bool) : Bool :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool (N L : ℕ) (ω : RepositoryChannel N → Bool) : Bool :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval (N L : ℕ) (q : ℚ) : ℚ :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

scoped macro "prove_evaluator" : tactic => `(tactic|
  apply rationalEventProbability_correct <;> first | assumption |
    (intro
     simp only [splitEscapeBool, quotientEscapeBool, splitSeedBool, quotientSeedBool,
       Set.mem_ofPred_eq, FiniteCatalogue.closure,
       decide_eq_true_iff]
     first | rfl | (erw [fullClosure_quotient_pullback]; rfl)))

section
variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (K : ℕ)

theorem splitEscapeEval_correct :
    (splitEscapeEval q K : ℝ) =
      (latentEscapeProbability Prod.snd (rationalParameter q hq hq1) (K+2)).toReal := by
  rw [← ((splitCatalogue _).escape_restriction K (rationalParameter q hq hq1)).2 rfl]
  prove_evaluator

theorem quotientEscapeEval_correct :
    (quotientEscapeEval q K : ℝ) =
      (latentEscapeProbability quotientCut (rationalParameter q hq hq1) (K+2)).toReal := by
  rw [← ((quotientCatalogue _).escape_restriction K (rationalParameter q hq hq1)).2 rfl]
  prove_evaluator

end

/-- The enclosure of a real number by rational endpoints. -/
def Encloses (v : ℚ × ℚ) (x : ℝ) : Prop := (v.1 : ℝ) ≤ x ∧ x ≤ (v.2 : ℝ)

section
variable (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitEvaluationCap : ℕ :=
  let L := 10*seedIndex q hq hq1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def splitCertifiedInterval : ℚ × ℚ :=
  let e := splitEscapeEval q (splitEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

def quotientEvaluationCap : ℕ :=
  let hhalf : 0 < q/2 := rationalHalf_pos q hq
  let hhalf1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  let L := 10*seedIndex (q/2) hhalf hhalf1 (precisionIndex ε)
  recordCap L (recordIndex q hq hq1 L ε hε)

def quotientCertifiedInterval : ℚ × ℚ :=
  let e := quotientEscapeEval q (quotientEvaluationCap q hq hq1 ε hε-2)
  (e-ε/2,e)

end

section
variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitTotalInterval : ℚ × ℚ :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval : ℚ × ℚ :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

end

/-- Quantitative properties of the specified actual profile and executable programs. -/
structure ProfileGuarantees (S : I → ENNReal) (escape : I → ℕ → ENNReal)
    (evaluate : (q : ℚ) → 0 ≤ q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℚ × ℚ)
    (cap : (q : ℚ) → 0 < q → q ≤ 1 → (ε : ℚ) → 0 < ε → ℕ)
    (coefficient : ℕ → ℕ) : Prop where
  enclosure : ∀ q hq hq1 ε hε,
    let v := evaluate q hq hq1 ε hε
    (v.1 : ℝ) ≤ (S (rationalParameter q hq hq1)).toReal ∧
      (S (rationalParameter q hq hq1)).toReal ≤ (v.2 : ℝ) ∧ v.2-v.1 < ε
  uniform_error : ∀ q hq hq1 ε hε a, rationalParameter q (le_of_lt hq) hq1 ≤ a →
    (escape a (cap q hq hq1 ε hε)).toReal ≤ (S a).toReal+(ε : ℝ)/2
  power_bound : ∀ a r, (S a).toReal ≤ (coefficient r : ℝ)*(a : ℝ)^r
  intensity_flatness : ∀ d ε, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ lam : ℝ, ∀ hlam : 0 < lam, lam < δ → (S (criticalOpenness lam hlam)).toReal < ε*lam^d

/-- The same proof handles both catalogues. Only their seed input, mark map,
finite evaluator, and sparse coefficient differ. -/
private theorem profile_guarantees (g : CutMap)
    (b : ℚ → ℚ) (hb : ∀ q, 0 < q → 0 < b q ∧ b q ≤ q)
    (eval : ℚ → ℕ → ℚ) (heval : ∀ q hq hq1 K, (eval q K : ℝ) =
      (latentEscapeProbability g (rationalParameter q hq hq1) (K+2)).toReal)
    (C : ℕ → ℕ) (hC : ∀ a r, latentSurvival g a ≤ (C r : ENNReal)*(toNNReal a : ENNReal)^r) :
    let seed (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) := seedIndex (b q) (hb q hq).1 ((hb q hq).2.trans hq1)
    let cap (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε) :=
      let L := 10*seed q hq hq1 (precisionIndex ε)
      recordCap L (recordIndex q hq hq1 L ε hε)
    ProfileGuarantees (latentSurvival g) (latentEscapeProbability g)
      (fun q hq hq1 ε hε => if h : q = 0 then (0,0) else
        let e := eval q (cap q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε-2)
        (e-ε/2,e)) cap C := by
  intro seed cap
  have hp (a : I) (r : ℕ) := sparse_toReal (hC a r)
  refine (fun hu => ProfileGuarantees.mk ?_ hu hp ?_) ?_
  · intro q hq hq1 ε hε
    dsimp only
    split
    · subst q
      have := hC 0 1
      simp_all [rationalParameter]
    · rename_i hn
      have hpos := lt_of_le_of_ne hq (Ne.symm hn)
      let K := cap q hpos hq1 ε hε
      have he := heval q hq hq1 (K-2)
      rw [Nat.sub_add_cancel (show 2 ≤ K from recordCap_ge_two ..)] at he
      have h := hu q hpos hq1 ε hε (rationalParameter q hq hq1) le_rfl
      have hl := ENNReal.toReal_mono (measure_ne_top _ _) (latent_survival_le_escape g (rationalParameter q hq hq1) K)
      rw [← he] at h hl
      exact ⟨by push_cast; linarith, hl, by linarith⟩
  · -- Use one extra power of openness, which is at most the intensity.
    intro d ε hε
    let c : ℝ := C (d+1)
    refine ⟨ε/(c+1), by positivity, fun lam hlam hδ => ?_⟩
    let a := criticalOpenness lam hlam
    have ha : (a : ℝ) ≤ lam := by
      change 1-Real.exp (-lam) ≤ lam
      linarith [Real.add_one_le_exp (-lam)]
    refine (hp a (d+1)).trans_lt ?_
    have := a.property.1
    grw [ha]
    rw [pow_succ, ← mul_assoc, mul_right_comm c]
    gcongr
    linarith [(lt_div_iff₀ (show 0 < c+1 by positivity)).mp hδ]
  · intro q hq hq1 ε hε a ha
    let m := precisionIndex ε
    let k := seed q hq hq1 m
    obtain ⟨hk,hθ,hδ⟩ := selected_detourRisk (b q) (hb q hq).1 ((hb q hq).2.trans hq1) m a
      ((rationalParameter_mono (hb q hq).2).trans ha)
    have h := truncation g a k (recordIndex q hq hq1 (10*k) ε hε) hk hθ
    dsimp only at h
    grw [show 2*detourRisk a k ≤ (m : ENNReal)⁻¹ from le_self_add.trans hδ,
      blockFailure_anti ha (10*k+1)] at h
    have hi : (m : ENNReal)⁻¹ ≠ ∞ := by simp [m, precisionIndex]
    have hreal := ENNReal.toReal_mono (by finiteness) h
    simp (disch := finiteness) [ENNReal.toReal_add, rationalParameter] at hreal
    have hp := (Rat.cast_le (K := ℝ)).mpr (precisionIndex_error ε hε)
    have he := (Rat.cast_le (K := ℝ)).mpr (recordIndex_error q hq hq1 (10*k) ε hε)
    push_cast at hp he
    linarith

theorem splitProfile : ProfileGuarantees staticSurvival splitEscapeProbability
    splitTotalInterval splitEvaluationCap splitSparseCoefficient := by
  rw [show staticSurvival = latentSurvival Prod.snd from funext staticSurvival_pullback]
  exact profile_guarantees Prod.snd id (fun _ h => ⟨h,le_rfl⟩)
    splitEscapeEval splitEscapeEval_correct _
    (fun a r => catalogue_sparse_bound a r (splitCatalogue _) (split_growth _))

theorem quotientProfile : ProfileGuarantees quotientSurvival quotientEscapeProbability
    quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient := by
  delta quotientSurvival quotientEscapeProbability quotientField
  simp only [← quotientCut_relabel]
  exact profile_guarantees quotientCut (· / 2)
    (fun q h => ⟨rationalHalf_pos q h,div_le_self h.le one_le_two⟩)
    quotientEscapeEval quotientEscapeEval_correct _
    (fun a r => catalogue_sparse_bound a r (quotientCatalogue _) (quotient_growth _))

end RAFCriticalWindowQuantitative
