module
public import proofs.RAF.Concrete.UniformModel
public import proofs.RAFCriticalWindowQuantitative.CertifiedEvaluator
public import proofs.RAFEmergenceApprox.GenericHistory

/-! Bounds for finite catalytic networks under explicit input conditions. -/

@[expose] public section

namespace RAFReactionQuotient
open Classical OverlapCorrectedRAF.Source RAF.Concrete RAF.Polymer MeasureTheory unitInterval
variable (n : ℕ) (p : I)
noncomputable def quotientCatalyticLaw :=
  RAFEmergenceApprox.Generic.law (X := Molecule n) (fun _ : RepositoryChannel n => p)

def quotientRAFEvent : Set (RepositoryChannel n → Molecule n → Prop) :=
  {ω | ∃ S, IsRevRAF (repositoryCRS n 2) (fun x j => ω j x) S}

noncomputable def quotientRAFProbability : ENNReal :=
  quotientCatalyticLaw n p (quotientRAFEvent n)

end RAFReactionQuotient

namespace RAFCriticalWindowQuantitative
open Classical RAF RAF.Polymer RAF.Concrete RAFReactionQuotient OverlapCorrectedRAF.Source
open MeasureTheory HordijkSteelThreshold unitInterval RAFEmergenceApprox.Generic

noncomputable def splitCatalyticProbability (n : ℕ) (p : I) : ENNReal :=
  uniformCatalysisMeasure n ((p : ℝ)*Fintype.card (Reaction n)/n) (HasRAFEvent n)

private def sampleIndex {n : ℕ} (z : Reaction n × Molecule n) : SeedCoord n ⊕ NonseedCoord n :=
  if h : RevSeedReaction (binaryPolymerCRS n 2) z.1 then .inl (z.2,⟨z.1,h⟩) else .inr (z.2,⟨z.1,h⟩)

def rationalIntervalError (source profile : ℚ × ℚ) : ℚ := max (source.2-profile.1) (profile.2-source.1)

/- For a fixed finite source and cutoff, compare the two probabilities using
independently chosen rational inputs and their certified intervals. -/
set_option quotPrecheck false in
local notation "CompareAt " n:arg m:arg K:arg P:arg S:arg bounds:arg eval:arg =>
  ∀ _hm : 0 < m, ∀ p hp hp1 q hq hq1, ∀ _hk : 6 < nearFullPoolSize n m,
    ∀ _hpool : q ≤ rationalPool p (nearFullPoolSize n m), ∀ s hs hs1 ε hε,
    |(P n (rationalParameter p hp hp1)).toReal - (S (rationalParameter s hs hs1)).toReal| ≤
      (rationalIntervalError (bounds n m K p q hq hq1) (eval s hs hs1 ε hε) : ℝ)

namespace Model

variable (M : Model)
noncomputable abbrev raf := M.pick splitCatalyticProbability quotientRAFProbability
abbrev valid (n : ℕ) := M.pick (4 ≤ n) (0 < n)
abbrev census := M.pick 36 34

/-- A seed channel embeds in the ordered food pairs, with just the canonical
pairs retained in the quotient census. -/
lemma seed_count (n : ℕ) : (Finset.univ.filter (RevSeedReaction (M.system n))).card ≤ M.census := by
  let G := {z : Molecule 2 × Molecule 2 // M = split ∨
    displayedConcat z.1 z.2 ≠ displayedConcat z.2 z.1 ∨ moleculePrecedes z.1 z.2}
  have hc : Fintype.card G = M.census := by cases M <;> decide
  let A := {r // RevSeedReaction (M.system n) r}
  have len (r : A) : molLength (M.view r.val).val.1 ≤ 2 ∧ molLength (M.view r.val).val.2 ≤ 2 :=
    (M.enabled_box r.val 2 r.property).1
  let f (r : A) : G := ⟨(lowerMolecule _ (len r).1,lowerMolecule _ (len r).2),by
    cases M with
    | split => exact Or.inl rfl
    | quotient => exact Or.inr r.val.property.2⟩
  rw [←Fintype.card_subtype]
  apply (Fintype.card_le_of_injective f ?_).trans_eq hc
  intro r s he
  have h := congrArg Subtype.val he
  simp only [f,Prod.mk.injEq] at h
  exact Subtype.ext (M.view_inj (Subtype.ext (Prod.ext (lower_inj h.1) (lower_inj h.2))))

noncomputable abbrev actual (n : ℕ) (p : I) := iid (Molecule n) (M.Channel n) p (rafEvent (M.system n))

variable (n m K : ℕ) (hn : M.valid n) (hm : 0 < m)
include hn in
lemma raf_eq (p : I) : M.raf n p = M.actual n p := by
  unfold actual
  cases M with
  | split =>
    have hi : Function.Injective (@sampleIndex n) := by
      intro a b; simp only [sampleIndex]; split <;> split <;> grind
    change splitCatalyticProbability n p = _
    unfold splitCatalyticProbability uniformCatalysisMeasure
    rw [RAFEmergenceApprox.catalysisP_covers_probability n (by omega)]
    rw [← (split_sets (S := SeedCoord n) (D := NonseedCoord n) p).finite_event,
      ← (iid_rows p sampleIndex hi).finite_event (rafEvent _)]
    congr 1; ext ω
    simp only [Set.mem_preimage,HasRAFEvent,rafEvent,Set.mem_ofPred_eq]
    have he : catalysisOf ({s | ω (.inl s)}, {d | ω (.inr d)}) = fun x r => ω (sampleIndex (r,x)) := by
      funext x r
      by_cases h : RevSeedReaction (binaryPolymerCRS n 2) r <;> simp [catalysisOf,sampleIndex,h]
    rw [he]; rfl
  | quotient => rfl

include hm in
theorem barrier (p q : I) (hk : 6 < nearFullPoolSize n m) (hpool : q ≤ fixedPoolParameter p (nearFullPoolSize n m)) :
    M.static n q {ω | ¬ deficit m (M.closure 2 ω)} ≤ M.actual n p := by
  let Q := M.system n
  let k := nearFullPoolSize n m
  have hfood : Q.food.card ≤ 6 := (binaryFood_card_le_cutoff n 2).trans (by decide)
  apply le_trans _ (pool_barrier Q k (hfood.trans_lt hk) hpool)
  apply measure_mono
  intro ω h
  change k ≤ (fullClosure (M.system n) _).card
  let S := M.closure 2 ω
  have hmiss : Sᶜ.card ≤ Fintype.card (Molecule n)/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using le_of_not_gt h)
  have := Nat.div_mul_le_self (Fintype.card (Molecule n)) m
  have := Finset.card_add_card_compl S
  change (m-1)*_ ≤ S.card; rw [Nat.sub_one_mul,Nat.mul_comm m]; omega

theorem raf_upper (p : I) : M.actual n p ≤ M.escapeProb (fixedPoolParameter p (Fintype.card (Molecule n))) (K+2) +
    (Fintype.card (Molecule (K+2)) : ENNReal)*M.census*(toNNReal p : ENNReal) := by
  let Q := M.system n
  let C := binaryFood n (K+2)
  let A := Finset.univ.filter (RevSeedReaction Q)
  have hc := M.seed_count n
  let large := fun S => hasLonger (K+2) (fullClosure Q S)
  have hu := hit_bound p C A
  apply (measure_alternatives (A := {ω | large (catalystActive ω Finset.univ)}) _ ?_).trans (add_le_add ?_ (hu.trans ?_))
  · rintro ω ⟨S,hS⟩ h
    obtain ⟨r,hr,hseed⟩ := exists_rev_seed_of_foodGenerated Q S hS.1 hS.2.1
    have act := (active_iff Q ω S).mpr hS.2.2
    have hc := full_mono Q (act.trans (catalystActive_mono ω (Finset.subset_univ _)))
    obtain ⟨x,hx,ho⟩ := (mem_catalystActive ..).mp (act hr)
    exact ⟨r,by simpa [A] using hseed,x,by simpa [C,binaryFood] using le_of_not_gt fun hl => h ⟨x,hc hx,hl⟩,ho⟩
  · rw [pool_stat p Finset.univ large,Finset.card_univ]
    change M.static n _ {ω | hasLonger (K+2) (M.closure 2 ω)} ≤ _
    rw [M.restrict_stat _ 2 (hasLonger (K+2))]
    exact measure_mono fun _ h => escape_of_large h
  · gcongr
    exact_mod_cast binaryFood_card_le_cutoff n (K+2)

variable (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (q : ℚ) (hq : 0 < q) (hq1 : q ≤ 1)
def source :=
  (M.seedEval n (M.seedLength ⟨q,hq,hq1⟩ m) q - 1/m,
    M.escapeEval (rationalPool p (Fintype.card (Molecule n))) K + (Fintype.card (Molecule (K+2)) : ℚ)*M.census*p)

include hn in
lemma source_case : CompareAt n m K M.raf M.survival M.source M.total := by
  intro hm p hp hp1 q hq hq1 hk hpool s hs hs1 ε hε
  rw [M.raf_eq n hn]
  let a := rationalParameter p hp hp1
  let b := rationalParameter q hq.le hq1
  let L := M.seedLength ⟨q,hq,hq1⟩ m
  have pool k : (rationalPool p k : ℝ) = fixedPoolParameter a k := by simp [a,rationalParameter,rationalPool,fixedPoolParameter]
  have hl := M.barrier n m hm a b hk ((Rat.cast_le.mpr hpool).trans_eq (pool _))
  have hb := M.bulk (n := n) ⟨q,hq,hq1⟩ m b le_rfl
  have hseed : M.static n b {ω | binaryFood n L ⊆ M.closure 2 ω} ≤ M.actual n a+(m : ENNReal)⁻¹ := by
    apply (measure_alternatives _ ?_).trans (add_le_add hl hb)
    intro ω hseed hmass
    have hs : M.closure L ω ⊆ M.closure 2 ω :=
      full_le (M.system n L) _ hseed (full_closed (M.system n) _)
    exact (Classical.not_not.mp hmass).trans_le (Nat.mul_le_mul_left m (Finset.card_le_card (Finset.compl_subset_compl.mpr hs)))
  have hlow := ENNReal.toReal_le_add hseed (measure_ne_top _ _) (by simp [Nat.ne_of_gt hm])
  have hu := ENNReal.toReal_le_add (M.raf_upper n K a) (measure_ne_top _ _) (by finiteness)
  obtain ⟨hl,hh,_⟩ := M.total_correct s hs hs1 ε hε
  have eqL : (M.seedEval n L q : ℝ) = _ := M.eval_stat q b rfl (binaryFood n L ⊆ ·)
  have eqU := M.escapeEval_eq _ _ (pool (Fintype.card (Molecule n))) K
  simp only [rationalIntervalError,source,Rat.cast_max,Rat.cast_sub,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_one,abs_le]
  simp only [←eqL,ENNReal.toReal_inv,ENNReal.toReal_natCast] at hlow
  simp only [←eqU,ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.coe_toReal,coe_toNNReal] at hu
  simp only [one_div]
  change _ ≤ _ + _ * (p:ℝ) at hu
  constructor
  · exact (neg_le_neg (le_max_right _ _)).trans (by linarith only [hlow,hh])
  · exact le_trans (by linarith only [hu,hl]) (le_max_left _ _)
end Model
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

def SourceGuarantees : Prop :=
  (∀ n m K, 4 ≤ n → CompareAt n m K splitCatalyticProbability staticSurvival splitSourceInterval splitTotalInterval) ∧
  (∀ n m K, 0 < n → CompareAt n m K quotientRAFProbability quotientSurvival quotientSourceInterval quotientTotalInterval)
end RAFCriticalWindowQuantitative
