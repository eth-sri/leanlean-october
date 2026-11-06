module

public import proofs.HordijkSteelThreshold.InfiniteStaticLaw

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal

abbrev SplitField := (List Bool × ℕ) → Prop

def SplitPrefixDetermined (P : Finset (List Bool × ℕ)) (E : Set SplitField) : Prop :=
  ∀ ω η, (∀ z ∈ P, ω z = η z) → (ω ∈ E ↔ η ∈ E)

theorem split_prefix_event_representation (P : Finset (List Bool × ℕ)) (E : Set SplitField)
    (hE : SplitPrefixDetermined P E) :
    ∃ e : (P → Prop) → Prop, E = {ω | e (fun z => ω z.val)} :=
  ⟨fun η => (fun z => if h : z ∈ P then η ⟨z, h⟩ else False) ∈ E,
    Set.ext fun _ => hE _ _ fun z hz => by simp [hz]⟩

theorem split_prefix_failure_measure (a : I) (P T : Finset (List Bool × ℕ))
    (hPT : Disjoint P T) (E : Set SplitField) (hE : SplitPrefixDetermined P E) :
    infiniteSplitPi a (E ∩ {ω | ¬ ∀ z ∈ T, ω z}) =
      infiniteSplitPi a E * (1-(toNNReal a : ENNReal)^T.card) := by
  obtain ⟨e, rfl⟩ := split_prefix_event_representation P E hE
  have hi : iIndepFun (fun z (ω : SplitField) => ω z) (infiniteSplitPi a) :=
    iIndepFun_infinitePi fun _ => measurable_id
  have hind := (hi.indepFun_finset P T hPT fun z => measurable_pi_apply z).comp
    (measurable_of_finite e) (measurable_of_finite fun η : T → Prop => ¬ ∀ z, η z)
  have hp := hind.measure_inter_preimage_eq_mul {True} {True} (.singleton True) (.singleton True)
  have heT : {ω : SplitField | ∀ z ∈ T, ω z} = ⋂ z ∈ T, (fun ω : SplitField => ω z) ⁻¹' {True} := by ext; simp
  have hm : MeasurableSet {ω : SplitField | ∀ z ∈ T, ω z} :=
    heT ▸ MeasurableSet.biInter (Finset.countable_toSet T) fun z _ => (MeasurableSet.singleton True).preimage (measurable_pi_apply z)
  have hcoord (z : List Bool × ℕ) : infiniteSplitPi a {ω | ω z} = (toNNReal a : ENNReal) := by
    have he := congrArg (fun μ : Measure Prop => μ {True})
      (Measure.infinitePi_map_eval (fun _ : List Bool × ℕ => ambientCoordLaw a) z)
    rw [Measure.map_apply (measurable_pi_apply z) (.singleton True)] at he
    simpa [infiniteSplitPi, ambientCoordLaw] using he
  have hopen : infiniteSplitPi a {ω | ∀ z ∈ T, ω z} = (toNNReal a : ENNReal)^T.card := by
    rw [heT, hi.measure_inter_preimage_eq_mul T (fun _ _ => .singleton True)]
    simp only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true, hcoord, Finset.prod_const]
  have hfail : infiniteSplitPi a {ω | ¬ ∀ z ∈ T, ω z} = 1 - (toNNReal a : ENNReal)^T.card := by
    change infiniteSplitPi a ({ω | ∀ z ∈ T, ω z}ᶜ) = _
    rw [measure_compl hm (measure_ne_top _ _), measure_univ, hopen]
  simpa only [Function.comp_def, Subtype.forall, Set.preimage,
    Set.mem_singleton_iff, eq_iff_iff, iff_true, hfail] using hp

end HordijkSteelThreshold
