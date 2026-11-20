module

public import proofs.HordijkSteelThreshold.InfiniteStaticLaw
public import proofs.HordijkSteelThreshold.AmbientIndependence
public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.RAFEmergenceApprox.RAFBounds
public import proofs.RAFReactionQuotient.QuotientMap
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFCriticalWindowQuantitative.EffectiveBulk

@[expose] public section

namespace RAFReactionQuotient
open RAF.Polymer RAF.Concrete OverlapCorrectedRAF.Source unitInterval

def quotientRAFEvent (n : ℕ) : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability (n : ℕ) (p : I) : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

end RAFReactionQuotient

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold MeasureTheory RAF.Polymer RAF.Concrete unitInterval RAFReactionQuotient OverlapCorrectedRAF.Source
open RAFEmergenceApprox.Generic

noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)

open MeasureTheory.Measure ProbabilityTheory in
theorem splitCatalyticProbability_eq_law (n : ℕ) (hn : 2 ≤ n) (p : I) :
    splitCatalyticProbability n p = rafProbability (binaryPolymerCRS n 2) p := by
  let lam := (p : ℝ)*Fintype.card (Reaction n)/n
  have he : catalysisP n lam = p := by
    have : Nonempty (Reaction n) := ⟨⟨⟨1,hn⟩,0,0⟩⟩
    apply Subtype.ext
    change min 1 (max 0 (rawCatalysisP n lam)) = (p : ℝ)
    rw [show rawCatalysisP n lam = (p : ℝ) by unfold rawCatalysisP lam; field_simp (disch := positivity),
      max_eq_right p.property.1, min_eq_right p.property.2]
  let J := SeedCoord n ⊕ NonseedCoord n
  let f : J → Reaction n × Molecule n := Sum.elim (fun z => (z.2.val,z.1)) (fun z => (z.2.val,z.1))
  have hf : Function.Injective f := by
    rintro (x|x) (y|y) <;> grind
  let F := MeasurableEquiv.sumPiEquivProdPi (fun _ : J => Prop) ∘ (fun (ω : Reaction n × Molecule n → Prop) j => ω (f j))
  have hmap : (infinitePi fun _ : Reaction n × Molecule n => ambientCoordLaw p).map F = uniformCatalysisMeasure n lam := by
    dsimp only [F]
    rw [← map_map (by fun_prop) .of_discrete,
      map_infinitePi_infinitePi_of_inj hf, infinitePi_eq_pi,
      (measurePreserving_sumPiEquivProdPi (fun _ : J => ambientCoordLaw p)).map_eq]
    simp only [uniformCatalysisMeasure, he, setBernoulli_eq_map, Set.mem_univ, bernoulliMeasure_def,
      ambientCoordLaw, infinitePi_eq_pi]
    congr 1 <;> exact Measure.map_id.symm
  change uniformCatalysisMeasure n lam (HasRAFEvent n) = _
  erw [← hmap, map_apply .of_discrete .of_discrete]
  unfold rafProbability iidCatalysis law colLaw
  simp_rw [← infinitePi_eq_pi]
  rw [← infinitePi_map_curry (fun (_ : Reaction n) (_ : Molecule n) => ambientCoordLaw p),
    (MeasurableEquiv.curry _ _ _).map_apply]
  congr 1
  ext ω
  change (∃ S, IsRevRAF _ (catalysisOf (F ω)) S) ↔ _
  rw [show catalysisOf (F ω) = fun x r => ω (r,x) by
    funext x r; unfold catalysisOf; split <;> rfl]
  rfl

private theorem split_seed_count (n : ℕ) : Fintype.card (PolymerSeedReaction n 2) ≤ 36 := by
  let f (r : PolymerSeedReaction n 2) : PolymerSeedReaction 4 2 := by
    have h := r.property
    refine ⟨⟨⟨r.val.1.val,?_⟩,r.val.2⟩,?_⟩ <;>
      simp [RevSeedReaction, binaryPolymerCRS, Finset.insert_subset_iff, binaryFood] at h ⊢ <;>
      grind [reactionLeftLength, reactionRightLength, reactionProductLength]
  refine (Fintype.card_le_of_injective f ?_).trans_eq (by decide)
  rintro ⟨⟨k,c,i⟩,hk⟩ ⟨⟨l,d,j⟩,hl⟩ h
  grind

def rationalPool (p : ℚ) (k : ℕ) : ℚ := 1-(1-p)^k

section
variable (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ)

private abbrev rationalPoolPoint : I :=
  rationalParameter (rationalPool p k)
    (sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith)))
    (by simp_all [rationalPool])

private theorem rationalPool_correct :
    rationalPoolPoint p hp hp1 k = fixedPoolParameter (rationalParameter p hp hp1) k := by
  ext
  simp [rationalPoolPoint, rationalParameter, rationalPool, fixedPoolParameter]

end

section
variable (n m K : ℕ) (p q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)

def splitSourceInterval : ℚ × ℚ :=
  (splitSeedEval n (10*seedIndex q hq hq1 m) q - 1/m,
    splitEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*36*p)

def quotientSourceInterval : ℚ × ℚ :=
  let hh : 0 < q/2 := rationalHalf_pos q hq
  let hh1 : q/2 ≤ 1 := rationalHalf_le_one q hq hq1
  (quotientSeedEval n (10*seedIndex (q/2) hh hh1 m) q - 1/m,
    quotientEscapeEval (rationalPool p (Fintype.card (Molecule n))) K +
      (Fintype.card (Molecule (K+2)) : ℚ)*34*p)

end

private theorem catalogue_enclosure {J : Type*} [Fintype J] {n m K c : ℕ}
    {g : CutMap} (C : FiniteCatalogue J n g)
    (hc : Fintype.card {r // RevSeedReaction (C.crs 2) r} ≤ c)
    {p q b : ℚ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1)
    (hb : 0 < b) (hbq : b ≤ q) (hm : 0 < m)
    {s e : ℚ} :
    let k := nearFullPoolSize n m
    let L := 10*seedIndex b hb (hbq.trans hq1) m
    let p' := rationalParameter p hp hp1
    let q' := rationalParameter q hq.le hq1
    6 < k → q ≤ rationalPool p k →
    (s : ℝ) = (finiteFieldLaw q' {ω | binaryFood n L ⊆ C.closure 2 ω}).toReal →
    (e : ℝ) = (latentEscapeProbability g (rationalPoolPoint p hp hp1 (Fintype.card (Molecule n))) (K+2)).toReal →
    Encloses (s-1/m, e+(Fintype.card (Molecule (K+2)) : ℚ)*c*p) (rafProbability (C.crs 2) p').toReal := by
  intro k L p' q' hk hpool hs he
  rw [rationalPool_correct p hp hp1] at he
  constructor
  · simp [hs, one_div]
    rw [← ENNReal.toReal_natCast m, ← ENNReal.toReal_inv]
    refine ENNReal.toReal_le_add ?_ (measure_ne_top _ _) (by finiteness)
    refine measure_le_add_of_cover ?_ (raf_mass_lower (C.crs 2) k p' q' 
        (((binaryFood_card_le_cutoff n 2).trans (by decide)).trans_lt hk)
        (by unfold k nearFullPoolSize; grw [Nat.sub_le, Nat.mul_div_le])
        (rationalPool_correct p hp hp1 k ▸ rationalParameter_mono hpool))
      (effective_bulk b hb (hbq.trans hq1) m _ (rationalParameter_mono hbq) C)
    intro ω hω
    have h := Finset.card_mono (fullClosure_least (Q := C.crs L) hω (fullClosure_completes (C.crs 2)))
    exact or_iff_not_imp_right.mpr fun hn => (le_of_not_gt hn).trans h
  · simpa [he, p', rationalParameter, -Fintype.card_sigma] using ENNReal.toReal_le_add
      ((raf_escape_upper (C.crs 2) p' (K+2) c hc).trans
        (add_le_add (C.escape_restriction K _).1 le_rfl)) (measure_ne_top _ _) (by finiteness)

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ :=
  max (source.2-profile.1) (profile.2-source.1)

theorem interval_comparison_error {P S : ℝ} {u v : ℚ × ℚ}
    (hu : Encloses u P) (hv : Encloses v S) : |P-S| ≤ (rationalIntervalError u v : ℝ) := by
  simp only [rationalIntervalError, Rat.cast_max, Rat.cast_sub, abs_eq_max_neg, neg_sub]
  exact max_le_max (sub_le_sub hu.2 hv.1) (sub_le_sub hv.2 hu.1)

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

theorem source_guarantees : SourceGuarantees := by
  constructor <;> intro n m K hn hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε
  · rw [splitCatalyticProbability_eq_law n (by omega)]
    exact interval_comparison_error (catalogue_enclosure (splitCatalogue n) (split_seed_count n)
      hp hp1 hq hq1 hq le_rfl hm hk hpool
      (by prove_evaluator) (splitEscapeEval_correct _ _ _ K))
      (And.imp_right And.left (splitProfile.enclosure s hs hs1 ε hε))
  · exact interval_comparison_error (catalogue_enclosure (quotientCatalogue n) (repository_seed_count n)
      hp hp1 hq hq1 (rationalHalf_pos q hq)
      (div_le_self hq.le one_le_two) hm hk hpool
      (by prove_evaluator) (quotientEscapeEval_correct _ _ _ K))
      (And.imp_right And.left (quotientProfile.enclosure s hs hs1 ε hε))

end RAFCriticalWindowQuantitative
