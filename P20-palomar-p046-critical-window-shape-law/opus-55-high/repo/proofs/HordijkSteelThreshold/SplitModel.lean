module

public import proofs.HordijkSteelThreshold.ReversibleEscapeProbability
public import proofs.HordijkSteelThreshold.StaticSeedClosure

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory RAF.Polymer RAF.Concrete unitInterval Filter
open scoped ENNReal

variable (g : List Bool × ℕ → List Bool × ℕ)

/-- The split environment read through a coordinate map. -/
def fieldOf  (ω : List Bool × ℕ → Prop) :
    InfiniteSplitEnvironment :=
  fun w k => ω $ g (w,k)

theorem measurable_fieldOf  : Measurable (fieldOf g) :=
  by unfold fieldOf; fun_prop

/-- A finite iid coordinate model read through the infinite split field. -/
structure SplitModel where
  C : ℕ → Type
  [fin : ∀ N, Fintype $ C N]
  c : ∀ {N}, C N → List Bool × ℕ
  π : ∀ {N}, Reaction N → C N
  g : List Bool × ℕ → List Bool × ℕ
  hc : ∀ N, Function.Injective $ @c N
  hg : ∀ N (r : Reaction N), g (moleculeWord $ reactionProduct r, reactionLeftLength r) = c (π r)

attribute [instance] SplitModel.fin


namespace SplitModel
variable (M : SplitModel)

noncomputable abbrev μ (N : ℕ) (a : I) : Measure (M.C N → Prop) := Measure.pi fun _ => ambientCoordLaw a

variable (a : I)

noncomputable abbrev ν  : Measure InfiniteSplitEnvironment := (infiniteSplitPi a).map $ fieldOf M.g

variable (N L : ℕ)

noncomputable def cl  (q : M.C N → Prop) : Finset (Molecule N) :=
  temporaryReactionClosure L $ staticOpenReactions fun r => q $ M.π r

theorem transfer  (a : I) (P : Finset (Molecule N) → Prop) :
    M.μ N a {q | P $ M.cl N L q} =
      infiniteSplitPi a {ω | P $ temporaryReactionClosure L $ restrictedSplitReactions N $ fieldOf M.g ω} := by
  have hi : iIndepFun (fun z ω => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  have h : (infiniteSplitPi a).map (fun ω j => ω $ M.c j) = M.μ N a := by
    rw [(hi.precomp $ M.hc N).map_fun_eq_pi_map $ fun j => (measurable_pi_apply $ M.c j).aemeasurable]
    simp_rw [infiniteSplitPi, Measure.infinitePi_map_eval]
  rw [← h, Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet]
  simp only [cl, restrictedSplitReactions, fieldOf, M.hg]
  rfl


theorem ν_apply  {s : Set InfiniteSplitEnvironment} (hs : MeasurableSet s) :
    M.ν a s = infiniteSplitPi a (fieldOf M.g ⁻¹' s) :=
  Measure.map_apply (measurable_fieldOf _) hs

theorem ν_RU  : M.ν a {field | ReversibleUnbounded 2 field} =
    infiniteSplitPi a {ω | ReversibleUnbounded 2 $ fieldOf M.g ω} := M.ν_apply a $ measurableSet_reversibleUnbounded 2

variable (K : ℕ)

def esc  : Set (M.C (2*(K+2)) → Prop) := {q | ∃ x ∈ M.cl _ 2 q, K+2 < molLength x}

theorem capped_le (N K : ℕ) (a : I) : M.μ N a {q | ∃ x ∈ M.cl N 2 q, K+2 < molLength x} ≤
    infiniteSplitPi a {ω | ∃ w, K+2 < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf M.g ω) w} := by
  rw [M.transfer N 2 a (∃ x ∈ ·, K+2 < molLength x)]
  exact measure_mono fun ω ⟨x, hx, hl⟩ => ⟨moleculeWord x, by rwa [moleculeWord_length],
    finiteReversibleGenerated_to_infinite $ literalClosure_to_finiteReversible _ x hx⟩

theorem escape_eq  (a : I) :
    infiniteSplitPi a {ω | ∃ w, K+2 < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf M.g ω) w} =
      M.μ _ a (M.esc K) := by
  rw [esc, M.transfer _ 2 a (∃ x ∈ ·, K+2 < molLength x)]
  congr 1
  ext ω
  refine (reversible_escape_iff_cap (by omega) _).trans ⟨fun ⟨w, hw, hg⟩ => ?_, fun ⟨x, hx, hl⟩ =>
    ⟨_, by rwa [moleculeWord_length], literalClosure_to_finiteReversible _ x hx⟩⟩
  obtain ⟨x, hx, rfl⟩ := finiteReversible_to_literalClosure hg
  exact ⟨x, hx, by rwa [← moleculeWord_length]⟩

theorem survival_le  (a : I) :
    infiniteSplitPi a {ω | ReversibleUnbounded 2 $ fieldOf M.g ω} ≤ M.μ _ a (M.esc K) :=
  M.escape_eq K a ▸ measure_mono fun _ h => h _


theorem esc_tendsto  : Tendsto (fun K => infiniteSplitPi a
    {ω | ∃ w, K+2 < w.length ∧ InfiniteReversibleGenerated 2 (fieldOf M.g ω) w}) atTop
      (nhds $ M.ν a {field | ReversibleUnbounded 2 field}) := by
  refine (reversible_escape_probability_tendsto (M.ν a) 2).congr fun K => ?_
  rw [M.ν_apply a $ measurableSet_reversibleEscapeEvent 2 K]
  simp only [Set.preimage, reversibleEscapeEvent_iff]


theorem seed_tendsto (L : ℕ) (a : I) (seed : Finset $ List Bool) :
    Tendsto (fun N => M.μ N a {q | ∀ w ∈ seed, ∃ x ∈ M.cl N L q, moleculeWord x = w}) atTop
      (nhds $ M.ν a {field | ∀ w ∈ seed, InfiniteReversibleGenerated L field w}) := by
  refine (finite_seed_probability_tendsto (M.ν a) L seed).congr fun N => ?_
  rw [M.ν_apply a $ measurableSet_finite_seed N L seed,
    M.transfer N L a (∀ w ∈ seed, ∃ x ∈ ·, moleculeWord x = w)]
  simp only [Set.preimage_ofPred_eq, finiteReversible_iff_literalClosure]

end SplitModel

/-- The literal split model. -/
noncomputable abbrev splitModel : SplitModel where
  C := Reaction
  c := literalSplitCoordinate
  π := id
  g := id
  hc := literalSplitCoordinate_injective
  hg _ _ := rfl

theorem staticSurvival_le (K : ℕ) (a : I) : staticSurvival a ≤ splitModel.μ _ a (splitModel.esc K) :=
  (splitModel.ν_RU a).trans_le $ splitModel.survival_le K a

end HordijkSteelThreshold
