module

public import OAI.NumberTheory.DirichletL.Moments.FirstSecondActiveErrorGates
public import OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalFamily

@[expose] public section

namespace OAI.SevenEighths

open scoped Classical
open HeckeFamily ConcreteTraceCRT CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving)
open CompletedGauss CanonicalQuadraticSieve
open RayFourExpansion CenteredMomentSectorLocalization CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- The supported error packets formed by attaching an admissible prime power
and using its bounded moving conductor. -/
abbrev ForCanonicalErrors {α : Type*} [Fintype α] [DecidableEq α]
    (src : Input α) (C R0 : Ideal O) (B : actualAllocations src.pools C)
    (τ : Character) (t Z sigma cost : ℝ)
    (P : ∀ (prime : O) (k : ℕ)
      (Bp : actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1))),
      Character → RayCharacter → ℝ → Input (CenteredMomentCommonProfile.liveIndices Bp.val) → Prop) : Prop :=
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=0 ∨ k=5 ∨ k=6) →
    sigma/6≤Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^(k+1)),
    ∀(υ:Character)(χerr:RayCharacter)(v0:ℝ),
    υ.modulus.absNorm≤CenteredMomentAmplificationRadicalFamily.radicalBound
      (CenteredMomentChildRows.childCharacter τ χerr) fixedBadMask prime
      (CenteredMomentAmplificationActiveFactor.errorMovingExponent k) →
    (υ.modulus.absNorm:ℝ)≤cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z (k+1)) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) (k+1) Bp υ v0 →
    P prime k Bp υ χerr v0 input

end OAI.SevenEighths
