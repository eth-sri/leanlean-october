import proofs.RAF.Concrete.PolymerCRS
import proofs.RAFCriticalWindowQuantitative.EffectiveSeed
import proofs.HordijkSteelThreshold.InfiniteStaticLaw
import proofs.RAFReactionQuotient.QuotientMap
import proofs.RAFCriticalWindowQuantitative.GeometricCutoff
import proofs.RAFCriticalWindowQuantitative.EscapeEvaluation
import proofs.RAFCriticalWindowQuantitative.QuotientEffectiveBulk
import proofs.HordijkSteelThreshold.PositiveLowerPhase
import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
import proofs.RAFReactionQuotient.SourceBounds
import proofs.HordijkSteelThreshold.BoundedRAFProbability
import proofs.HordijkSteelThreshold.AmbientEscapeBound
import proofs.HordijkSteelThreshold.PositiveLowerPhase
import proofs.HordijkSteelThreshold.Gateway
import proofs.HordijkSteelThreshold.PolymerCounts
import proofs.RAF.Concrete.UniformModel
import proofs.RAFCriticalWindowQuantitative.SmallOpenness
import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
import proofs.RAFCriticalWindowQuantitative.QuotientCertifiedEvaluator
import proofs.RAFReactionQuotient.Resolution
import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure


namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory

variable (N L : ℕ)

def splitSeedBool  (ω : Reaction N → Bool)  :=
  decide (binaryFood N L ⊆ computedClosure N 2 (Finset.univ.filter (fun r => ω r)))

def quotientSeedBool  (ω : RepositoryChannel N → Bool)  :=
  splitSeedBool N L (fun r => ω (splitToQuotient r))

def splitSeedEval  (q : ℚ)  :=
  rationalEventProbability (Reaction N) q (splitSeedBool N L)

def quotientSeedEval  (q : ℚ)  :=
  rationalEventProbability (RepositoryChannel N) q (quotientSeedBool N L)

variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1)

theorem splitSeedEval_correct  :
    splitSeedEval N L q =
      (staticReactionMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ temporaryReactionClosure 2 (staticOpenReactions ω)}).toReal := by
  classical
  simpa [splitSeedEval, splitSeedBool, computedClosure_eq, staticOpenReactions,
    staticReactionMeasure, Measure.infinitePi_eq_pi] using
    (rationalEventProbability_correct (Reaction N) q hq hq1 (splitSeedBool N L)).symm

theorem quotientSeedEval_correct  :
    quotientSeedEval N L q =
      (quotientStaticMeasure N (rationalParameter q hq hq1)
        {ω | binaryFood N L ⊆ quotientClosure N 2 (quotientOpen ω)}).toReal := by
  classical
  simpa [quotientSeedEval, quotientSeedBool, splitSeedBool, computedClosure_eq, quotientStaticMeasure, quotientClosure_pullback, staticOpenReactions] using
    (rationalEventProbability_correct (RepositoryChannel N) q hq hq1 (quotientSeedBool N L)).symm

end RAFCriticalWindowQuantitative

namespace RAFCriticalWindowQuantitative




open HordijkSteelThreshold MeasureTheory RAF.Polymer RAF.Concrete unitInterval

variable (n K : ℕ) (lambda : ℝ)

theorem bounded_seed_probability_le_36 :
    ambientPiMeasure n lambda (boundedSeedCatalystEvent n K) ≤
      Fintype.card (Molecule K) * 36 *
        toNNReal (catalysisP n lambda) := by
  let J := ↥(binaryFood n K) × PolymerSeedReaction n 2
  let E : J → Set (AmbientCoord n → Prop) := fun j => {ω | ω (j.1.val,j.2.val)}
  have he : boundedSeedCatalystEvent n K = ⋃ j : J, E j := by
    ext ω
    simp [J, E, boundedSeedCatalystEvent, binaryFood]
  rw [he]
  calc
    _ ≤ ∑ j : J, ambientPiMeasure n lambda (E j) := measure_iUnion_fintype_le _ _
    _ = Fintype.card J * toNNReal (catalysisP n lambda) := by
      simp [E, ambient_coordinate_probability]
    _ ≤ _ := by
      apply mul_le_mul_left
      
      exact_mod_cast by

                       rw [Fintype.card_prod, Fintype.card_coe]
                       apply Nat.mul_le_mul (binaryFood_card_le_cutoff n K)
                       let f (r : PolymerSeedReaction n 2) : PolymerSeedReaction 4 2 :=
                         ⟨⟨⟨r.1.1.val, by
                           have h := (revSeedReaction_iff_factor_lengths r.1).mp r.2
                           change r.1.2.2.val + 1 ≤ 2 ∧ r.1.1.val - r.1.2.2.val ≤ 2 at h
                           omega⟩, r.1.2⟩, by
                           rw [revSeedReaction_iff_factor_lengths]
                           exact (revSeedReaction_iff_factor_lengths r.1).mp r.2⟩
                       exact (Fintype.card_le_of_injective f (by
                         intro r s h
                         grind)).trans (by decide)

abbrev ambient_raf_le_escape_add_seed_36   := by
  let E : Set (AmbientCoord n → Prop) := {ω | ∃ x ∈
    temporaryReactionClosure 2 (catalystActive ω Finset.univ), K < molLength x}
  
  exact (measure_mono (by
    intro ω hraf
    change ω ∈ E ∪ boundedSeedCatalystEvent n K
    simpa [E, boundedSeedCatalystEvent] using! (raf_escape_or_seed (binaryPolymerCRS n 2)
      (fun r x => ω (x,r)) molLength K hraf))).trans ((measure_union_le _ _).trans
    (add_le_add_right (bounded_seed_probability_le_36 n K lambda) _))



end RAFCriticalWindowQuantitative

namespace RAFEmergenceApprox
open RAF.Polymer RAF.Concrete HordijkSteelThreshold unitInterval

/-- The inherited lambda parametrization covers every homogeneous probability
at every nontrivial finite source size. -/
theorem catalysisP_covers_probability (n : ℕ) (hn : 2 ≤ n) (p : I) :
    catalysisP n (p * Fintype.card (Reaction n) / n) = p := by
  
  have hj : 0 < Fintype.card (Reaction n) := by rw [card_reactions_exact hn]; omega
  
  apply Subtype.ext
  have he : rawCatalysisP n (p * Fintype.card (Reaction n) / n) = p := by
    unfold rawCatalysisP
    field_simp
  change min 1 (max 0 (rawCatalysisP n _)) = p
  grind

end RAFEmergenceApprox

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold

def rationalPool (p : ℚ) (k : ℕ)  := 1-(1-p)^k

variable (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ)

include hp hp1 in
theorem rationalPool_nonneg  :
    0 ≤ rationalPool p k := sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith))

theorem rationalPool_le_one (p : ℚ) (hp1 : p ≤ 1) (k : ℕ) : rationalPool p k ≤ 1 := by simp_all [rationalPool]

theorem rationalPool_correct  :
    rationalParameter _ (rationalPool_nonneg p hp hp1 k) (rationalPool_le_one p hp1 k) =
      fixedPoolParameter (rationalParameter p hp hp1) k := by
  apply Subtype.ext
  simp [rationalParameter,rationalPool,fixedPoolParameter]

end RAFCriticalWindowQuantitative

namespace RAFCriticalWindowQuantitative

open HordijkSteelThreshold RAFReactionQuotient unitInterval





variable (q : ℚ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (ε : ℚ) (hε : 0 < ε)

def splitTotalInterval   :=
  if h : q = 0 then (0,0) else splitCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

def quotientTotalInterval   :=
  if h : q = 0 then (0,0) else quotientCertifiedInterval q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem splitTotalInterval_correct  :
    let v := splitTotalInterval q hq hq1 ε hε
    v.1 ≤ (staticSurvival (rationalParameter q hq hq1)).toReal ∧
      (staticSurvival (rationalParameter q hq hq1)).toReal ≤ v.2 ∧ v.2-v.1 < ε := by
  unfold splitTotalInterval
  split_ifs with h
  · subst q
    simp_all [rationalParameter,show staticSurvival 0 = 0 from by
                                  apply le_antisymm _ (by positivity)
                                  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using split_sparse_probability 0 1]
  · exact splitCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

theorem quotientTotalInterval_correct  :
    let v := quotientTotalInterval q hq hq1 ε hε
    v.1 ≤ (quotientSurvival (rationalParameter q hq hq1)).toReal ∧
      (quotientSurvival (rationalParameter q hq hq1)).toReal ≤ v.2 ∧ v.2-v.1 < ε := by
  unfold quotientTotalInterval
  split_ifs with h
  · subst q
    simp_all [rationalParameter,show quotientSurvival 0 = 0 from by
                                  apply le_antisymm _ (by positivity)
                                  simpa only [toNNReal_zero,ENNReal.coe_zero,zero_pow Nat.one_ne_zero,mul_zero] using quotient_sparse_probability 0 1]
  · exact quotientCertifiedInterval_correct q (lt_of_le_of_ne hq (Ne.symm h)) hq1 ε hε

open RAF.Polymer RAF.Concrete

noncomputable def splitCatalyticProbability (n : ℕ) (p : I)  :=
  uniformCatalysisMeasure n (p*Fintype.card (Reaction n)/n) (HasRAFEvent n)

variable (n m K : ℕ)

variable (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)

def splitSourceInterval    :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      Fintype.card (Molecule (K+2))*36*p)

def quotientSourceInterval    :=
  let hh  := rationalHalf_pos q hq
  let hh1  := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      Fintype.card (Molecule (K+2))*34*p)





theorem interval_comparison_error (P S lP uP lS uS : ℝ)
    (hP : lP ≤ P ∧ P ≤ uP) (hS : lS ≤ S ∧ S ≤ uS) :
    |P-S| ≤ max (uP-lS) (uS-lP) := by grind




inductive ProductiveHistory {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R]
    (Q : ReversibleCRS M R) (S : Finset R) : ℕ → Finset R → Prop
  | nil : ProductiveHistory Q S 0 ∅
  | step {k T r} : ProductiveHistory Q S k T → r ∈ S → r ∉ T →
      revClosureStep Q {r} (fullClosure Q T) ≠ fullClosure Q T →
      ProductiveHistory Q S (k+1) (insert r T)

variable {M R : Type*} [Fintype M] [DecidableEq M] [DecidableEq R] (Q : ReversibleCRS M R)



theorem long_target_productive_history  (length : M → ℕ)
    (hbound : ∀ T x, x ∈ fullClosure Q T → length x ≤ 2^(T.card+1))
    (S : Finset R) (k : ℕ) (x : M) (hx : x ∈ fullClosure Q S)
    (hlen : 2^(k+1) < length x) :
    ∃ T, ProductiveHistory Q S k T ∧ T.card = k ∧ T ⊆ S := by
  induction k with
  | zero => exact ⟨∅,ProductiveHistory.nil,Finset.card_empty,Finset.empty_subset _⟩
  | succ k ih =>
    obtain ⟨T,hT,hcard,hTS⟩ := ih (by rw [pow_succ] at hlen; omega)
    
    have hnot : x ∉ fullClosure Q T := by grind [pow_succ]
    let C := fullClosure Q T
    have hg : revClosureStep Q S C ≠ C := by
      intro he
      have hall : ∀ k, revClosureAt Q S k ⊆ C := by
        intro k
        induction k with
        | zero => exact revClosureAt_mono_stage Q T (Nat.zero_le _)
        | succ k ih =>
          exact (revClosureStep_mono Q Finset.Subset.rfl ih).trans (Finset.subset_of_eq he)
      exact hnot (hall _ hx)
    have hex : ∃ r ∈ S, revClosureStep Q {r} C ≠ C := by
      by_contra! h
      apply hg
      ext y
      simp_all [revClosureStep, Finset.ext_iff]
      aesop
    obtain ⟨r,hr,hgrow⟩ := hex
    have hrT : r ∉ T := by
      intro hrT
      have hs := closure_stable_at_card Q T
      change revClosureStep Q T C = C at hs
      grind [revClosureStep]
    exact ⟨insert r T,ProductiveHistory.step hT hr hrT hgrow,
      by simp_all,Finset.insert_subset hr hTS⟩





theorem power_bound_intensity_flatness (S : I → ℝ) (C : ℕ → ℕ)
    (hbound : ∀ a r, S a ≤ (C r : ℝ)*(a : ℝ)^r) (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ lam : ℝ, ∀ hlam : _, lam < δ →
      S (criticalOpenness lam hlam) < ε*lam^d := by
  let c : ℝ := C (d+1)
  refine ⟨ε/(c+1), by positivity, ?_⟩
  intro lam hlam hδ
  have ha : (criticalOpenness lam hlam : ℝ) ≤ lam := by
    change 1-Real.exp (-lam) ≤ lam
    linarith [Real.add_one_le_exp (-lam)]
  have hca : c*lam < ε := by
    have hx := (lt_div_iff₀ (by positivity : 0 < c+1)).mp hδ
    nlinarith
  have hb := (hbound (criticalOpenness lam hlam) (d+1)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (criticalOpenness lam hlam).property.1 ha _) (Nat.cast_nonneg _))
  rw [pow_succ] at hb
  nlinarith [mul_lt_mul_of_pos_right hca (pow_pos hlam d)]


open OverlapCorrectedRAF.Source MeasureTheory

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

def rationalIntervalError (source profile : ℚ × ℚ)  :=
  max (source.2-profile.1) (profile.2-source.1)

/-- The source contract uses actual catalytic inputs, not an assumed convergence rate. -/
def SourceGuarantees : Prop :=
  (∀ n m K, ∀ _hn : 4 ≤ n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(splitCatalyticProbability n (rationalParameter p hp hp1)).toReal -
      (staticSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (splitSourceInterval n m K p q hq hq1)
        (splitTotalInterval s hs hs1 ε hε) : ℝ)) ∧
  (∀ n m K, ∀ _hn : 0 < n, ∀ _hm : 0 < m,
    ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m),
    ∀ s hs hs1 ε hε,
    |(quotientRAFProbability n (rationalParameter p hp hp1)).toReal -
      (quotientSurvival (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (quotientSourceInterval n m K p q hq hq1)
        (quotientTotalInterval s hs hs1 ε hε) : ℝ))

/-- Compiled minimum quantitative/computability successor for both literal RAF models.
The programs are explicit definitions; no desired bound or validity oracle is assumed. -/
theorem quantitative_critical_window_resolution :
    ProfileGuarantees staticSurvival splitEscapeProbability
      splitTotalInterval splitEvaluationCap splitSparseCoefficient ∧
    ProfileGuarantees quotientSurvival quotientEscapeProbability
      quotientTotalInterval quotientEvaluationCap quotientSparseCoefficient ∧
    SourceGuarantees ∧
    (∀ N k S x, x ∈ temporaryReactionClosure (N := N) 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (binaryPolymerCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ N k S x, x ∈ quotientClosure N 2 S → 2^(k+1) < molLength x →
      ∃ T, ProductiveHistory (repositoryCRS N 2) S k T ∧ T.card = k ∧ T ⊆ S) ∧
    (∀ a : I, (a : ℝ) ≤ 1/10^20 → (staticSurvival a).toReal < 8/10^26)  := by
  refine ⟨⟨splitTotalInterval_correct, split_uniform_approximation, split_sparse_real,
      power_bound_intensity_flatness _ _ split_sparse_real⟩,
    ⟨quotientTotalInterval_correct, quotient_uniform_approximation, quotient_sparse_real,
      power_bound_intensity_flatness _ _ quotient_sparse_real⟩,
    ?_, ?_, ?_, (by
                                                             intro a ha
                                                             have h := split_sparse_real a 2
                                                             norm_num [splitSparseCoefficient, sparseWitnessCap,
                                                               card_reactions_exact (n := 20) (by norm_num), Nat.choose_two_right] at h
                                                             have hp := pow_le_pow_left₀ a.property.1 ha 2
                                                             linarith)⟩
  · constructor <;> intro n m K hn hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε
    all_goals
      let a := rationalParameter p hp hp1
      have hqpool : rationalParameter q hq.le hq1 ≤ fixedPoolParameter a (nearFullPoolSize n m) := by
        rw [← rationalPool_correct p hp hp1]
        exact Rat.cast_le (K := ℝ).mpr hpool
    · have hS := splitTotalInterval_correct s hs hs1 ε hε
      simp only [rationalIntervalError, Rat.cast_max, Rat.cast_sub]
      refine interval_comparison_error _ _ _ _ _ _ ?_ ⟨hS.1,hS.2.1⟩
      let lam : ℝ := a*Fintype.card (Reaction n)/n
      have he  := RAFEmergenceApprox.catalysisP_covers_probability n (by omega) a
      
      have hu := (le_of_eq (canonical_raf_measure_eq_ambient n lam)).trans
        ((ambient_raf_le_escape_add_seed_36 n (K+2) lam).trans (add_le_add_left
          ((le_of_eq (by
            have h := catalystPool_statistic (fun _ : Reaction n => catalysisP n lam) (Finset.univ : Finset (Molecule n))
              (fun S => ∃ x ∈ temporaryReactionClosure 2 S, K+2 < molLength x)
            rw [← ambient_columns_map] at h
            simpa only [Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] using! h)).trans (static_capped_escape_le n K _)) _))
      rw [← finite_static_escape_measure_eq] at hu
      rw [he] at hu
      have hlow := (ENNReal.toReal_mono (by finiteness) (show _ ≤
          (uniformCatalysisMeasure n lam) (HasRAFEvent n) + (m : ENNReal)⁻¹ from by
        refine (food_seed_mass_bound n _ m _ staticOpenReactions).trans
          (add_le_add ?_ (effective_static_bulk q hq hq1 m n (by omega)))
        rw [canonical_raf_measure_eq_ambient]
        have h := catalyst_raf_ge_static (binaryPolymerCRS n 2) (catalysisP n lam)
          (rationalParameter q hq.le hq1) m hm
          ((binaryFood_card_le_cutoff n 2).trans_lt hk) (he.symm ▸ hqpool)
        rw [← ambient_columns_map] at h
        change (staticReactionMeasure n _) {ω | NearFull m (computedClosure n 2 (staticOpenReactions ω))} ≤ _ at h
        simpa only [computedClosure_eq, Measure.map_apply (measurable_of_finite _) (Set.toFinite _).measurableSet] using! h)).trans ENNReal.toReal_add_le
      rw [← splitSeedEval_correct n _ q hq.le hq1] at hlow
      have hupp := (ENNReal.toReal_mono (by finiteness) hu).trans ENNReal.toReal_add_le
      rw [← rationalPool_correct p hp hp1,
        ← splitEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
      simp [← one_div] at hlow
      
      dsimp [splitSourceInterval, splitCatalyticProbability]
      push_cast
      constructor
      · 
        linarith
      · exact hupp
    · have hS := quotientTotalInterval_correct s hs hs1 ε hε
      simp only [rationalIntervalError, Rat.cast_max, Rat.cast_sub]
      refine interval_comparison_error _ _ _ _ _ _ ?_ ⟨hS.1,hS.2.1⟩
      
      have hnear := catalyst_raf_ge_static (repositoryCRS n 2) a (rationalParameter q hq.le hq1)
        m hm ((binaryFood_card_le_cutoff n 2).trans_lt hk) hqpool
      simp only [fullClosure_eq_quotient] at hnear
      change quotientStaticMeasure n _ {ω | NearFull m (quotientClosure n 2 (quotientOpen ω))} ≤ quotientRAFProbability n a at hnear
      have hl := (((show quotientStaticMeasure n _ {ω | binaryFood n _ ⊆ quotientClosure n 2 (quotientOpen ω)} ≤ _ from by
        simp_rw [quotientClosure_pullback]
        exact food_seed_mass_bound n _ m (quotientStaticMeasure n _) _).trans
                       (add_le_add hnear
          (effective_quotient_bulk q hq hq1 m _ le_rfl n hn))))
      
      have hlow := (ENNReal.toReal_mono (by unfold quotientRAFProbability quotientCatalyticLaw; finiteness) hl).trans ENNReal.toReal_add_le
      rw [← quotientSeedEval_correct n _ q hq.le hq1] at hlow
      have hupp := (ENNReal.toReal_mono (by unfold quotientStaticMeasure; finiteness) (quotient_raf_upper n K a)).trans ENNReal.toReal_add_le
      rw [← rationalPool_correct p hp hp1,
        ← quotientEscapeEval_correct _ (rationalPool_nonneg p hp hp1 _) (rationalPool_le_one p hp1 _) K] at hupp
      simp [← one_div] at hlow
      
      dsimp [quotientSourceInterval]
      push_cast
      constructor
      · linarith
      · exact hupp
  · intro N k S x hx hlen
    apply long_target_productive_history _ molLength _ S k x _ hlen
    · intro T y hy
      apply sparse_closure_length N T y
      rwa [← computedClosure_eq]
    · rwa [← computedClosure_eq] at hx
  · intro N k S x hx hlen
    apply long_target_productive_history _ molLength _ S k x _ hlen
    · intro T y hy
      exact quotient_sparse_closure_length N T y (by rwa [fullClosure_eq_quotient] at hy)
    · rwa [fullClosure_eq_quotient]

end RAFCriticalWindowQuantitative
