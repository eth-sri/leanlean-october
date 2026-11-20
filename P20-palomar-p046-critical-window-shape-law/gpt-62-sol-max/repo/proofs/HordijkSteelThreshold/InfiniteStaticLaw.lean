module

public import proofs.HordijkSteelThreshold.BinaryReactionSplit
public import proofs.HordijkSteelThreshold.AmbientIndependence
import Mathlib.Logic.Function.DependsOn
public import proofs.HordijkSteelThreshold.ReversibleClosure

@[expose] public section

namespace HordijkSteelThreshold
open MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval RAFCriticalWindowQuantitative
open scoped ENNReal

abbrev InfiniteSplitEnvironment := List Bool → Nat → Prop

/-- Ordinary reversible generation in the countable word universe. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field (u ++ v)
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field (u ++ v))
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v

/-- Reuse the same derivations with capped food and closed channels above `N`. -/
abbrev FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :=
  InfiniteReversibleGenerated (min L N) (fun w k => w.length ≤ N ∧ field w k)

theorem InfiniteReversibleGenerated.rebase {L K : ℕ} {f g : InfiniteSplitEnvironment} {w : List Bool}
    (h : InfiniteReversibleGenerated L f w)
    (hf : ∀ u, u ≠ [] → u.length ≤ L → InfiniteReversibleGenerated K g u)
    (ho : ∀ u v, f (u++v) u.length → g (u++v) u.length) :
    InfiniteReversibleGenerated K g w := by
  induction h <;> grind [InfiniteReversibleGenerated.ligate, InfiniteReversibleGenerated.left,
    InfiniteReversibleGenerated.right]

section
variable {N M L : ℕ} {f : InfiniteSplitEnvironment} {w : List Bool}

theorem finiteReversibleGenerated_mono_cap (hNM : N ≤ M)
    (h : FiniteReversibleGenerated N L f w) : FiniteReversibleGenerated M L f w :=
  h.rebase (fun _ hn hl => .food hn (hl.trans (min_le_min_left L hNM)))
    (fun _ _ ht => ⟨ht.1.trans hNM,ht.2⟩)

theorem finiteReversibleGenerated_to_infinite
    (h : FiniteReversibleGenerated N L f w) :
    InfiniteReversibleGenerated L f w :=
  h.rebase (fun _ hn hl => .food hn (hl.trans (min_le_left ..))) (fun _ _ ho => ho.2)

theorem finiteReversibleGenerated_length_le
    (h : FiniteReversibleGenerated N L f w) : w.length ≤ N := by
  cases h <;> grind

end

def ReversibleUnbounded (L : ℕ) (field : InfiniteSplitEnvironment) : Prop :=
  ∀ K : ℕ, ∃ w, K < w.length ∧ InfiniteReversibleGenerated L field w

noncomputable def restrictedSplitReactions (N : ℕ) (field : InfiniteSplitEnvironment) :
    Finset (Reaction N) := openChannels
      (fun r => field (moleculeWord (reactionProduct r)) (reactionLeftLength r))

theorem moleculeWord_nonempty {N : ℕ} (x : Molecule N) : moleculeWord x ≠ [] := by
  grind [moleculeWord_length, molLength]

theorem moleculeWord_cap {N : ℕ} (x : Molecule N) : (moleculeWord x).length ≤ N := by
  rw [moleculeWord_length]
  exact x.1.isLt

/-- The capped word closure, represented in the literal reaction catalogue. -/
noncomputable abbrev literalClosure (N L : ℕ) (f : InfiniteSplitEnvironment) :=
  fullClosure (binaryPolymerCRS N L) (restrictedSplitReactions N f)

theorem finiteReversible_iff_literalClosure {N L : ℕ} (f : InfiniteSplitEnvironment) (w : List Bool) :
    FiniteReversibleGenerated N L f w ↔
    ∃ x ∈ literalClosure N L f, moleculeWord x = w := by
  let S := restrictedSplitReactions N f
  let C (u : List Bool) := ∃ x ∈ fullClosure (binaryPolymerCRS N L) S, moleculeWord x = u
  constructor
  · intro h
    change C w
    have hm (x : Molecule N) : C (moleculeWord x) ↔ x ∈ fullClosure (binaryPolymerCRS N L) S :=
      by simp [-Sigma.exists, C, moleculeWord_injective.eq_iff]
    have hn {u : List Bool} (h : C u) : u ≠ [] := by grind [moleculeWord_nonempty]
    have ends (u v : List Bool) (hu : u ≠ []) (hv : v ≠ [])
        (hopen : (u++v).length ≤ N ∧ f (u++v) u.length) (h : (C u ∧ C v) ∨ C (u++v)) :
        C u ∧ C v ∧ C (u++v) := by
      obtain ⟨r,hl,hr,hp⟩ := source_append_split u v
        (List.length_pos_iff.mpr hu) (List.length_pos_iff.mpr hv) (by simpa using hopen.1)
      have hS : r ∈ S := (mem_openChannels _ _).2 (by
        rw [hp, ← molLength_reactionLeft, ← moleculeWord_length, hl]
        exact hopen.2)
      rw [←hp, ←hl, ←hr] at h ⊢
      simp only [hm] at h ⊢
      have hs := fullClosure_completes (binaryPolymerCRS N L) hS
      simp only [binaryPolymerCRS, Finset.union_subset_iff, Finset.insert_subset_iff,
        Finset.singleton_subset_iff] at hs
      exact and_assoc.mp (hs h)
    induction h with
    | @food u hne hL =>
      let x := sourceWordMolecule u (List.length_pos_iff.mpr hne) (hL.trans (min_le_right ..))
      exact ⟨x, fullClosure_food _ S (by simpa [binaryPolymerCRS, binaryFood, x] using hL.trans (min_le_left L N)), by simp [x]⟩
    | _ => grind
  · rintro ⟨x,hx,rfl⟩
    let C := openChannels (fun y : Molecule N => FiniteReversibleGenerated N L f (moleculeWord y))
    apply (mem_openChannels _ _).mp (fullClosure_least (C := C) ?_ ?_ hx)
    · simp [C, binaryPolymerCRS, binaryFood, Finset.subset_iff, ← moleculeWord_length]
      grind [moleculeWord_nonempty, moleculeWord_cap, InfiniteReversibleGenerated.food]
    · simp [RevClosed, C, binaryPolymerCRS, Finset.insert_subset_iff, restrictedSplitReactions]
      grind [reaction_words_append, moleculeWord_nonempty, moleculeWord_cap, moleculeWord_length,
        molLength_reactionLeft, InfiniteReversibleGenerated.ligate,
        InfiniteReversibleGenerated.left, InfiniteReversibleGenerated.right]

noncomputable def literalSplitCoordinate {N : ℕ} (r : Reaction N) : List Bool × ℕ :=
  (moleculeWord (reactionProduct r), reactionLeftLength r)

def currySplitField (ω : (List Bool × ℕ) → Prop) : InfiniteSplitEnvironment :=
  fun w k => ω (w,k)

theorem measurable_currySplitField : Measurable currySplitField :=
  (MeasurableEquiv.curry _ _ _).measurable

noncomputable def infiniteSplitPi (a : I) : Measure ((List Bool × ℕ) → Prop) :=
  Measure.infinitePi (fun _ => ambientCoordLaw a)

noncomputable def infiniteStaticMeasure (a : I) : Measure InfiniteSplitEnvironment :=
  (infiniteSplitPi a).map currySplitField

noncomputable instance infiniteSplitPi_probability (a : I) : IsProbabilityMeasure (infiniteSplitPi a) := by
  unfold infiniteSplitPi
  infer_instance

abbrev SplitIndex := List Bool × ℕ
abbrev SplitField := (List Bool × ℕ) → Prop

/-- Relabel a cut within one product word, never across products. -/
abbrev CutMap := SplitIndex → ℕ

def CutMap.relabel (g : CutMap) (z : SplitIndex) : SplitIndex := (z.1, g z)

def pullbackField (g : CutMap) (ω : SplitField) : InfiniteSplitEnvironment :=
  fun w k => ω (g.relabel (w,k))

/-- Failure probability of a trial requiring all `k` coordinates to be open. -/
noncomputable def blockFailure (a : I) (k : ℕ) : ENNReal := 1-(toNNReal a : ENNReal)^k

@[simp, aesop (rule_sets := [finiteness]) safe]
theorem blockFailure_ne_top (a : I) (k : ℕ) : blockFailure a k ≠ ∞ := by
  unfold blockFailure
  finiteness

@[simp] theorem blockFailure_toReal (a : I) (k : ℕ) :
    (blockFailure a k).toReal = 1-(a : ℝ)^k := by
  rw [blockFailure, ENNReal.toReal_sub_of_le (pow_le_one₀ zero_le (by exact_mod_cast a.property.2)) (by simp)]
  simp

theorem failure_ratio_mono (a : I) : Monotone (blockFailure a) :=
  fun _ _ h => tsub_le_tsub_left (pow_le_pow_of_le_one (by positivity)
    (by exact_mod_cast a.property.2) h) 1

theorem blockFailure_anti {a b : I} (h : a ≤ b) (k : ℕ) : blockFailure b k ≤ blockFailure a k :=
  tsub_le_tsub_left (pow_le_pow_left' (by exact_mod_cast h) _) _

/-- A trial fails if not every required channel in its block is open. -/
def trialFailure {J : Type*} (T : Finset J) : Set (J → Prop) := (blockEvent T True)ᶜ

theorem iid_block_failure {C : Type*} (a : I) (T : Finset C) :
    MeasurableSet (trialFailure T) ∧
      (Measure.infinitePi fun _ : C => ambientCoordLaw a) (trialFailure T) = blockFailure a T.card := by
  obtain ⟨hm, h⟩ := iid_block a T True
  exact ⟨hm.compl, by rw [trialFailure, measure_compl hm (measure_ne_top _ _), measure_univ, h,
    ambientCoordLaw_true, blockFailure]⟩

/-- A prefix event is measurable and independent of trials outside its prefix. -/
theorem split_prefix_law (a : I) (P : Finset SplitIndex) (E : Set SplitField)
    (hE : DependsOn E (P : Set SplitIndex)) : MeasurableSet E ∧
      ∀ T : Finset SplitIndex, Disjoint P T →
        infiniteSplitPi a (E ∩ trialFailure T) = infiniteSplitPi a E * blockFailure a T.card := by
  obtain ⟨A,rfl⟩ := dependsOn_iff_exists_comp.mp hE
  refine ⟨MeasurableSet.of_discrete.preimage (by fun_prop), ?_⟩
  intro T hPT
  have h := ((iIndepFun_infinitePi (P := fun _ : SplitIndex => ambientCoordLaw a) (fun _ => measurable_id)).indepFun_finset
    P T hPT (fun _ => measurable_pi_apply _)).measure_inter_preimage_eq_mul
    A ({η | ∀ z, η z = True}ᶜ : Set (T → Prop)) .of_discrete .of_discrete
  rw [← (iid_block_failure a T).2]
  simpa only [Set.preimage_compl, Set.preimage_ofPred_eq, Subtype.forall] using! h

/-- The first record above a completed prefix occurs by twice that prefix. -/
theorem escape_has_bounded_record {L B : ℕ} (hLB : L ≤ B)
    {field : InfiniteSplitEnvironment}
    (h : ∃ w, B < w.length ∧ InfiniteReversibleGenerated L field w) :
    ∃ v, B < v.length ∧ v.length ≤ 2*B ∧ FiniteReversibleGenerated v.length L field v := by
  obtain ⟨w,hw,h⟩ := h
  by_contra he
  suffices h' : FiniteReversibleGenerated B L field w from hw.not_ge (finiteReversibleGenerated_length_le h')
  clear hw
  induction h with
  | food hn hL => exact .food hn (le_min hL (hL.trans hLB))
  | @ligate u v _ _ ho hu hv =>
    by_cases hlen : (u++v).length ≤ B
    · exact .ligate hu hv ⟨hlen,ho⟩
    · have := finiteReversibleGenerated_length_le hu
      have := finiteReversibleGenerated_length_le hv
      exact (he ⟨u++v, by omega, by grind, .ligate
        (finiteReversibleGenerated_mono_cap (by omega) hu)
        (finiteReversibleGenerated_mono_cap (by omega) hv) ⟨le_rfl,ho⟩⟩).elim
  | left hu hv _ ho ih => exact .left hu hv ih ⟨finiteReversibleGenerated_length_le ih,ho⟩
  | right hu hv _ ho ih => exact .right hu hv ih ⟨finiteReversibleGenerated_length_le ih,ho⟩

noncomputable def staticSurvival (a : I) : ENNReal :=
  infiniteStaticMeasure a {field | ReversibleUnbounded 2 field}

def latentEscapeEvent (g : CutMap) (K : ℕ) : Set SplitField :=
  {ω | ∃ w, K < w.length ∧ InfiniteReversibleGenerated 2 (pullbackField g ω) w}

noncomputable abbrev latentEscapeProbability (g : CutMap) (a : I) (K : ℕ) : ENNReal :=
  infiniteSplitPi a (latentEscapeEvent g K)

noncomputable abbrev latentSurvival (g : CutMap) (a : I) : ENNReal :=
  infiniteSplitPi a {ω | ReversibleUnbounded 2 (pullbackField g ω)}

theorem latent_survival_le_escape (g : CutMap) (a : I) (K : ℕ) :
    latentSurvival g a ≤ latentEscapeProbability g a K :=
  measure_mono fun _ h => h K

/-- A finite catalogue read in the common latent field, with its closure
restriction valid for every food cutoff. -/
structure FiniteCatalogue (J : Type*) [Fintype J] (N : ℕ) (g : CutMap) where
  coordinate : J → SplitIndex
  injective : Function.Injective coordinate
  fix_short (z : SplitIndex) : 2*z.2 ≤ z.1.length → g z = z.2
  chemistry : ReversibleCRS (Molecule N) J
  restrict : ∀ L ω, fullClosure {chemistry with food := binaryFood N L}
    (openChannels (fun j => ω (coordinate j))) =
    literalClosure N L (pullbackField g ω)

variable {J : Type*} [Fintype J] {N : ℕ} {g : CutMap}

abbrev FiniteCatalogue.crs (C : FiniteCatalogue J N g) (L : ℕ) : ReversibleCRS (Molecule N) J :=
  {C.chemistry with food := binaryFood N L}

noncomputable abbrev FiniteCatalogue.closure (C : FiniteCatalogue J N g) (L : ℕ) (ω : J → Prop) :=
  fullClosure (C.crs L) (openChannels ω)

theorem FiniteCatalogue.measure_closure (C : FiniteCatalogue J N g) (a : I) (L : ℕ)
    (E : Finset (Molecule N) → Prop) :
    finiteFieldLaw a {q | E (C.closure L q)} = infiniteSplitPi a
      {ω | E (literalClosure N L (pullbackField g ω))} := by
  rw [finiteFieldLaw, ← Measure.infinitePi_eq_pi, ← Measure.map_infinitePi_infinitePi_of_inj (P := fun _ => ambientCoordLaw a) C.injective,
    Measure.map_apply (by fun_prop) .of_discrete]
  simp [Set.preimage_ofPred_eq, FiniteCatalogue.closure, FiniteCatalogue.crs, C.restrict, infiniteSplitPi]

theorem FiniteCatalogue.escape_restriction (C : FiniteCatalogue J N g) (K : ℕ) (a : I) :
    let m := finiteFieldLaw a {q | ∃ x ∈ C.closure 2 q, K+2 < molLength x}
    let u := latentEscapeProbability g a (K+2)
    m ≤ u ∧ (N = 2*(K+2) → m = u) := by
  dsimp only [latentEscapeProbability, latentEscapeEvent]
  rw [C.measure_closure a 2 (fun C => ∃ x ∈ C, K+2 < molLength x)]
  refine ⟨measure_mono ?upper, fun hN => le_antisymm (measure_mono ?upper) (measure_mono ?_)⟩
  · rintro ω ⟨x,hx,hK⟩
    exact ⟨moleculeWord x, by simpa using hK, finiteReversibleGenerated_to_infinite
      ((finiteReversible_iff_literalClosure _ _).2 ⟨x,hx,rfl⟩)⟩
  · intro ω hω
    obtain ⟨w,hw,hcap,hgen⟩ := escape_has_bounded_record (Nat.le_add_left 2 K) hω
    obtain ⟨x,hx,rfl⟩ := (finiteReversible_iff_literalClosure _ _).1
      (finiteReversibleGenerated_mono_cap (hcap.trans_eq hN.symm) hgen)
    exact ⟨x,hx,by simpa using hw⟩

noncomputable def splitCatalogue (N : ℕ) : FiniteCatalogue (Reaction N) N Prod.snd :=
  ⟨literalSplitCoordinate, by
    intro r s h
    have hprod := moleculeWord_injective (congrArg Prod.fst h)
    rcases r with ⟨i,c,k⟩
    rcases s with ⟨j,d,l⟩
    obtain rfl : i = j := congrArg Sigma.fst hprod
    grind [literalSplitCoordinate, reactionProduct, reactionLeftLength],
    fun _ _ => rfl, binaryPolymerCRS N 0,
    fun _ _ => rfl⟩

theorem staticSurvival_pullback (a : I) : staticSurvival a = latentSurvival Prod.snd a :=
  (MeasurableEquiv.curry _ _ _).map_apply _

end HordijkSteelThreshold
