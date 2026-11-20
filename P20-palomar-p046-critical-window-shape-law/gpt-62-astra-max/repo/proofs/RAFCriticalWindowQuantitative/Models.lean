module
public import proofs.RAFCriticalWindowQuantitative.BulkGrowth
public import proofs.RAFReactionQuotient.InfiniteDock
public import proofs.RAFCriticalWindowQuantitative.ApproximationParameters

/-! Physical channel models, finite marginals, seed continuation and uniform truncation. -/

@[expose] public section

namespace RAFCriticalWindowQuantitative
open HordijkSteelThreshold RAFReactionQuotient OverlapCorrectedRAF.Source
open MeasureTheory ProbabilityTheory RAFEmergenceApprox.Generic RAF.Polymer RAF.Concrete unitInterval

inductive Model | split | quotient deriving DecidableEq

variable (a : I) (K : ℕ)
noncomputable def splitEscapeProbability : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (currySplitField ω) w}
noncomputable def quotientEscapeProbability : ENNReal :=
  infiniteSplitPi a {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (quotientField ω) w}

/-- Transport a rational geometric failure budget to the actual field,
whose openness may be strictly larger than the rational lower input. -/
lemma geometric_budget {b e : ℚ} {a : I} {c i r : ℕ} (hb : 0 ≤ b) (ha : (b:ℝ) ≤ a)
    (h : (c:ℚ)*(1-b^i)^r ≤ e) : (c:ENNReal)*(missRate a i)^r ≤ ENNReal.ofReal (e:ℝ) := by
  rw [←ENNReal.ofReal_toReal (a := (c:ENNReal)*_) (by finiteness)]
  apply ENNReal.ofReal_le_ofReal
  have hr := (Rat.cast_le (K := ℝ)).mpr h; push_cast at hr
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,miss_toReal]
  apply le_trans _ hr; gcongr; exact sub_nonneg.mpr (pow_le_one₀ a.2.1 a.2.2)

namespace Model

variable (M : Model)
abbrev pick {α : Sort*} (s q : α) : α := match M with
  | split => s
  | quotient => q

variable (n : ℕ)
abbrev Channel := M.pick (Reaction n) (RepositoryChannel n)
instance : Fintype (M.Channel n) := by cases M <;> infer_instance
instance : DecidableEq (M.Channel n) := by cases M <;> infer_instance

variable {n}
def project : Reaction n → M.Channel n := match M with
  | split => id
  | quotient => splitToQuotient

def marks : ChannelMap := M.pick ⟨id,fun _ => rfl,by intros; rfl⟩
  ⟨canonicalIndex,canonicalIndex_product,fun w i h => by simp [canonicalIndex,show ¬w.length-i < i by omega]⟩

noncomputable abbrev static (n : ℕ) (a : I) := colLaw (M.Channel n) a
def system (n : ℕ) (L := 2) : ReversibleCRS (Molecule n) (M.Channel n) :=
  let Q : ReversibleCRS _ (M.Channel n) := match M with
    | split => binaryPolymerCRS n 2
    | quotient => repositoryCRS n 2
  {Q with food := binaryFood n L}

open Classical
noncomputable abbrev closure (L : ℕ) (ω : M.Channel n → Prop) := fullClosure (M.system n L) (Finset.univ.filter ω)

def view : M.Channel n → OrderedChannel n := match M with
  | split => splitToOrdered
  | quotient => fun j => ⟨j.val,j.property.1⟩

lemma view_inj : Function.Injective (@view M n) := by
  cases M with
  | split =>
    intro r s h; apply literalSplitCoordinate_injective n
    simpa only [view,orderedCoordinate_split] using congrArg orderedCoordinate h
  | quotient => exact fun _ _ e => Subtype.ext (congrArg (fun j : OrderedChannel n => j.val) e)

/-- If either side lies in a length box, both factors lie in the box,
and even the product lies in the doubled box. -/
lemma enabled_box (r : M.Channel n) (k : ℕ)
    (h : RevSeedReaction (M.system n k) r) :
    (molLength (M.view r).val.1 ≤ k ∧ molLength (M.view r).val.2 ≤ k) ∧
    (M.system n).lhs r ∪ (M.system n).rhs r ⊆ binaryFood n (2*k) := by
  cases M
  all_goals simp [RevSeedReaction,system,view,splitToOrdered,binaryPolymerCRS,repositoryCRS,binaryFood,Finset.insert_subset_iff,concatMolecule] at *
  · have := reaction_length_add r; omega
  · omega

lemma closure_eq (L : ℕ) (ω : M.Channel n → Prop) :
    M.closure L ω = temporaryReactionClosure L (Finset.univ.filter (ω ∘ M.project)) := by
  rw [←full_eq_temporary]; cases M with
  | split => rfl
  | quotient =>
    rw [closure,fullClosure,fullClosure,← Finset.image_univ_of_surjective (splitToQuotient_surjective n),Finset.filter_image]
    exact split_closure_eq_quotient L _ _

/-- Restricting to the distinct physical channels gives the finite product law. -/
theorem restrict_stat (a : I) {N : ℕ} (L : ℕ) (P : Finset (Molecule N) → Prop) :
    M.static N a {ω | P (M.closure L ω)} = infiniteSplitPi a {ω |
      P (temporaryReactionClosure L (restrictedSplitReactions N (M.marks.field ω)))} := by
  let f := orderedCoordinate ∘ M.view (n := N)
  have loc (r : Reaction N) : f (M.project r) = M.marks.index (literalSplitCoordinate r) := by
    cases M; exact orderedCoordinate_split _; exact (canonicalIndex_split r).symm
  rw [static,←(iid_read a f ((orderedCoordinate_injective _).comp M.view_inj)).finite_event]
  congr 1; ext ω
  change P (M.closure L _) ↔ _
  simp only [M.closure_eq,Function.comp_apply,loc]; rfl

noncomputable abbrev survival := M.pick staticSurvival quotientSurvival
noncomputable def escapeProb (a : I) (K : ℕ) := infiniteSplitPi a (M.marks.escape K)

lemma survival_eq (a : I) : M.survival a = infiniteSplitPi a {ω | ReversibleUnbounded 2 (M.marks.field ω)} := by
  cases M with
  | split => exact (MeasurableEquiv.curry (List Bool) ℕ Prop).map_apply _
  | quotient => rfl

lemma survival_le (a : I) (K : ℕ) : M.survival a ≤ M.escapeProb a K := by
  rw [M.survival_eq]; exact measure_mono fun _ h => h K

open ChannelMap
/-- Rational lower input, including the evidence needed by the seed search. -/
abbrev LowerRate := Set.Ioc (0:ℚ) 1
variable (q : LowerRate)

def seedInput : LowerRate := M.pick q ⟨q/2,rationalHalf_pos _ q.2.1,rationalHalf_le_one _ q.2.1 q.2.2⟩
lemma seedInput_le : M.seedInput q ≤ q := by cases M <;> change _ ≤ (q:ℚ) <;> grind [seedInput]

def trials (m : ℕ) := seedIndex (M.seedInput q) (M.seedInput q).2.1 (M.seedInput q).2.2 m
def seedLength (m : ℕ) := 10*M.trials q m

abbrev deficit {N : ℕ} (m : ℕ) (S : Finset (Molecule N)) := Fintype.card (Molecule N) < m*Sᶜ.card

variable (m : ℕ) (a : I) (ha : ((q:ℚ):ℝ) ≤ a)
include ha
/-- Numerical consequences of the executable seed test for the physical parameter. -/
lemma seed_ok :
    let k := M.trials q m
    0 < k ∧ 2*err a k ≤ 2⁻¹ ∧ 2*err a k ≤ (m:ENNReal)⁻¹ ∧ m*(3*err a k) ≤ (m:ENNReal)⁻¹ := by
  let b := M.seedInput q
  let k := M.trials q m
  obtain ⟨hk,test⟩ : seedTest b m k := Nat.find_spec (p := seedTest b m) _
  let co := molecularContourConstant*(m*(m+1)+1)
  have hba : ((b:ℚ):ℝ) ≤ a := (Rat.cast_le.mpr (M.seedInput_le q)).trans ha
  have test' : (co:ℚ)*(1-(b:ℚ)^2)^k ≤ 1 := by dsimp [co]; push_cast; linarith only [test]
  have bound : (co:ENNReal)*err a k ≤ 1 := by simpa using geometric_budget b.2.1.le hba test'
  have budget (c d : ℕ) (hc : c*d ≤ 4*(m*(m+1)+1)) : (c:ENNReal)*err a k ≤ (d:ENNReal)⁻¹ := by
    rw [ENNReal.le_inv_iff_mul_le,mul_right_comm]; apply le_trans _ bound; gcongr
    exact_mod_cast hc.trans (Nat.mul_le_mul_right _ (by decide : 4 ≤ molecularContourConstant))
  refine ⟨hk,budget 2 2 ?_,budget 2 m ?_,?_⟩
  · nlinarith
  · nlinarith
  · simpa [mul_assoc] using budget (m*3) m (by nlinarith)

lemma bulk {n : ℕ} :
    M.static n a {ω | deficit m (M.closure (M.seedLength q m) ω)} ≤ (m : ENNReal)⁻¹ := by
  obtain ⟨hk,hs,_,hm'⟩ := M.seed_ok q m a ha
  refine (deficit_bound _ _ ?_).trans hm'; intro x
  rw [M.restrict_stat a _ (x ∉ ·)]
  simpa only [Gen,finite_word_iff,seedLength] using M.marks.missing_word (N := n) a hk hs (moleculeWord x)
    (List.length_pos_iff.mpr (moleculeWord_nonempty x)) (moleculeWord_cap x)

/-- A finite escape either acquired the seed or missed one of its words.
Once acquired, extinction requires a failed growth block. -/
theorem truncation (r : ℕ) :
    let L := M.seedLength q m
    M.escapeProb a (recordCap L r) ≤ M.survival a + (m : ENNReal)⁻¹ + 2^(L+1)*(missRate a (L+1))^r := by
  let L := M.seedLength q m
  obtain ⟨hk,ht,hb,_⟩ := M.seed_ok q m a ha
  refine le_trans (b := infiniteSplitPi a (M.marks.seed L (recordCap L r)) + _) ?_ (add_le_add ?_ (M.marks.seed_failure a L r))
  · exact measure_alternatives _ fun _ he hn => ⟨he,hn⟩
  rw [M.survival_eq]
  apply (measure_alternatives _ ?_).trans (add_le_add le_rfl ((defects_mass a hk ht).trans hb))
  intro ω hs hn; exact Classical.not_not.mp fun hg => hn (M.marks.unbounded_of_seed hk hg hs)

end Model
end RAFCriticalWindowQuantitative
