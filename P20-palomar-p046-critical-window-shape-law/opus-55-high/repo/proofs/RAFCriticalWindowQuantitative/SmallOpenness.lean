module

public import proofs.RAFCriticalWindowQuantitative.FiniteOpenCount
public import proofs.RAFCriticalWindowQuantitative.QuotientSparseClosure
public import proofs.HordijkSteelThreshold.StaticParameterMonotonicity
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound
public import proofs.HordijkSteelThreshold.StaticClosureMass
public import proofs.HordijkSteelThreshold.AmbientEscapeBound
public import proofs.HordijkSteelThreshold.SourceTerminalRAF
public import proofs.HordijkSteelThreshold.RecordCylinderDeficit
public import proofs.HordijkSteelThreshold.RecordTargetTrial
public import proofs.HordijkSteelThreshold.SplitPrefixIndependence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import proofs.HordijkSteelThreshold.StaticEventContinuity
public import proofs.HordijkSteelThreshold.NearFullPoolAsymptotics
public import proofs.HordijkSteelThreshold.SourceStaticRAFBound
public import proofs.RAFReactionQuotient.FiniteApproximation
public import proofs.RAFReactionQuotient.SeedBulk

@[expose] public section

namespace RAFCriticalWindowQuantitative
open Classical HordijkSteelThreshold RAFReactionQuotient RAF.Polymer RAF.Concrete
open OverlapCorrectedRAF.Source MeasureTheory unitInterval
open scoped ENNReal

variable (r : ℕ)

def sparseWitnessCap  : ℕ := 2*(2^(r+1)+2)

def splitSparseCoefficient  : ℕ := (Fintype.card $ Reaction $ sparseWitnessCap r).choose r

def quotientSparseCoefficient  : ℕ := (Fintype.card $ RepositoryChannel $ sparseWitnessCap r).choose r

open Classical in

theorem sparse_of {J : Type*} [Fintype J] {S : ENNReal} {a : I} {r : ℕ} {E : Set $ J → Prop}
    (hS : S ≤ Measure.pi (fun _ => ambientCoordLaw a) E)
    (hE : ∀ ω ∈ E, 2^(r+1) < 2^((Finset.univ.filter fun j => ω j).card+1)) :
    S ≤ ((Fintype.card J).choose r : ENNReal)*(toNNReal a : ENNReal)^r :=
  hS.trans $ (measure_mono fun ω h => (Nat.succ_lt_succ_iff.mp $ (Nat.pow_lt_pow_iff_right
    one_lt_two).mp $ hE ω h).le).trans $ finite_many_open_probability J a r

variable (a : I)

theorem split_sparse_probability  (r : ℕ) :
    staticSurvival a ≤ (splitSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r :=
  sparse_of (staticSurvival_le _ a) fun _ ⟨x,hx,hl⟩ =>
    (Nat.lt_of_add_right_lt hl).trans_le $ split_closure_length _ x hx

theorem quotient_sparse_probability  (r : ℕ) :
    quotientSurvival a ≤ (quotientSparseCoefficient r : ENNReal)*(toNNReal a : ENNReal)^r :=
  sparse_of (quotientModel.survival_le _ a) fun ω ⟨x,hx,hl⟩ =>
    (Nat.lt_of_add_right_lt hl).trans_le $ quotient_closure_length (quotientOpen ω) x $ by rwa [quotientClosure_pullback]


theorem sparse_real {S : I → ENNReal} {c : ℕ → ℕ}
    (hsp : ∀ a r, S a ≤ (c r : ENNReal)*(toNNReal a : ENNReal)^r) (a : I) (r : ℕ) :
    (S a).toReal ≤ (c r : ℝ)*(a : ℝ)^r := by
  simpa using ENNReal.toReal_mono (by finiteness) $ hsp a r

end RAFCriticalWindowQuantitative
