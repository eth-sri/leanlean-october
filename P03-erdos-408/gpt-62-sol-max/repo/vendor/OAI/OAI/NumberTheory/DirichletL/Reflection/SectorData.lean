module

public import OAI.NumberTheory.DirichletL.Reflection.SourceFamily

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

/-- The coprimality, residue characteristic, and factorization conditions
for applying a sector estimate at level `Nlevel`. -/
abbrev WithSectorFamilies (Nlevel : Eis) (G : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis → PrimeFamily σ) (result : Prop) : Prop :=
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) → result

structure SectorArithmetic (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows, Admissible K)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0) where
  referenceIndex : Type (max u v)
  [referenceFintype : Fintype referenceIndex]
  referencePrimes : PrimeFamily referenceIndex
  referenceArithmetic : ControlledStratumArithmetic referencePrimes.generator N a c mode
  completion : ∀ K : rows, ∀ P : Pset, IsCoprime K.val P.val →
    ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode
  fixedFactor_eq : ∀ K P hp, (completion K P hp).fixedFactor=referenceArithmetic.fixedFactor
  cuspColumn_eq : ∀ K P hp u m n b,
    actualCuspColumn (completion K P hp) s hc u m n b=actualCuspColumn referenceArithmetic s hc u m n b

/-- Quantify over the allowable row and slot families in a fixed sector. -/
abbrev ForSectorRows (Nlevel : Eis) (G : PrimeFamily φ)
    {a c₀ : Eis} {mode : Bool}
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (result : ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K),
        SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀ → Prop) : Prop :=
  ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis → PrimeFamily σ)
      (hrows : ∀ K ∈ rows, Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      WithSectorFamilies Nlevel G rows Pset S <| result rows Pset S hrows E

/-- Dyadic norm ranges and the unit bounds on the two weights. -/
abbrev ForDyadicWeights (rows Pset : Finset (Ideal Eis)) (QK QP : ℝ)
    (result : ℝ → (Ideal Eis → ℂ) → (Ideal Eis → ℂ) → Prop) : Prop :=
  ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) → result θ r aw

attribute [instance] SectorArithmetic.referenceFintype

end
end SevenEighths.InverseReflectedPhase

end OAI
