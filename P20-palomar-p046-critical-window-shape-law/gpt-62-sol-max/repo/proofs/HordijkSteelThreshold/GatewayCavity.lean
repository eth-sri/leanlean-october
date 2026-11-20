module

public import proofs.HordijkSteelThreshold.GatewayProbability

@[expose] public section

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer RAF.Concrete

/-- The catalysis relation obtained from bulk coordinates alone.  Every edge
whose target is a gateway reaction is deleted. -/
def bulkCatalysis {n : Nat} (bulk : Set (NonseedCoord n)) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then False
  else (x, ⟨r, h⟩) ∈ bulk

def GatewayForced {n : Nat} (J : Finset (PolymerSeedReaction n 2))
    (r : Reaction n) : Prop :=
  ∃ h : RevSeedReaction (binaryPolymerCRS n 2) r, (⟨r, h⟩ : PolymerSeedReaction n 2) ∈ J

/-- A `J`-seeded RAF uses a private external catalyst exactly for reactions
in `J`; every other catalytic witness must come from the internally generated
closure and a nongateway coordinate.  Encoding the external catalyst as the
`GatewayForced` disjunct avoids changing the molecule universe. -/
def IsGatewaySeededRAF {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) (S : Finset (Reaction n)) : Prop :=
  S.Nonempty ∧
    RevFoodGenerated (binaryPolymerCRS n 2) S ∧
    ∀ r ∈ S, GatewayForced J r ∨
      ∃ x k, x ∈ revClosureAt (binaryPolymerCRS n 2) S k ∧ bulkCatalysis bulk x r

noncomputable def gatewaySeededRAFFamily {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) : Finset (Finset (Reaction n)) := by
  classical
  exact Finset.univ.filter (IsGatewaySeededRAF bulk J)

@[simp] theorem mem_gatewaySeededRAFFamily {n : Nat} (bulk : Set (NonseedCoord n))
    (J : Finset (PolymerSeedReaction n 2)) (S : Finset (Reaction n)) :
    S ∈ gatewaySeededRAFFamily bulk J ↔ IsGatewaySeededRAF bulk J S := by
  classical
  simp [gatewaySeededRAFFamily]

/-- Gateway reactions used by a concrete reaction set, retaining their proof
that they lie on the food boundary. -/
noncomputable def gatewayPart {n : Nat} (S : Finset (Reaction n)) :
    Finset (PolymerSeedReaction n 2) := by
  classical
  exact Finset.univ.filter fun r => r.1 ∈ S

@[simp] theorem mem_gatewayPart {n : Nat} (S : Finset (Reaction n))
    (r : PolymerSeedReaction n 2) : r ∈ gatewayPart S ↔ r.1 ∈ S := by
  classical
  simp [gatewayPart]

theorem revClosureStep_mono {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    revClosureStep Q S A ⊆ revClosureStep Q T B := by
  intro x hx
  simp only [revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with hxA | ⟨r, hrS, hx⟩
  · exact Or.inl (hAB hxA)
  · right
    refine ⟨r, hST hrS, ?_⟩
    rcases hx with hx | hx
    · by_cases hEnabled : RevEnabledLhs Q A r
      · have hEnabled' : RevEnabledLhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx
    · by_cases hEnabled : RevEnabledRhs Q A r
      · have hEnabled' : RevEnabledRhs Q B r := fun y hy => hAB (hEnabled hy)
        simp [hEnabled] at hx
        simp [hEnabled', hx]
      · simp [hEnabled] at hx

theorem revClosureAt_mono_reactions {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) {S T : Finset R} (hST : S ⊆ T) :
    ∀ k, revClosureAt Q S k ⊆ revClosureAt Q T k := by
  intro k
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
      exact revClosureStep_mono Q hST ih

theorem GatewayForced.mono {n : Nat}
    {J K : Finset (PolymerSeedReaction n 2)} (hJK : J ⊆ K)
    {r : Reaction n} (hr : GatewayForced J r) : GatewayForced K r := by
  obtain ⟨hseed, hrJ⟩ := hr
  exact ⟨hseed, hJK hrJ⟩

end HordijkSteelThreshold
