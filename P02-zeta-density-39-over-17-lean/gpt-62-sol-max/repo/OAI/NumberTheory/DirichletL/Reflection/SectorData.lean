module
public import OAI.NumberTheory.DirichletL.Reflection.SourceSectors

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

/-- Local arithmetic needed for each reflected row. -/
abbrev WithRowPrimes (N : Eis) (G : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (P : Prop) : Prop :=
  (∀ f, IsCoprime (Ideal.span {N}) (G.ideal f)) →
  (∀ f, ringChar (Eis ⧸ G.ideal f) ≠ 2) →
  (∀ K ∈ rows, (∀ f, IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {N}) K) → P

/-- Arithmetic hypotheses on the row and column families of a sector. -/
abbrev WithSectorPrimes (N : Eis) (G : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis → PrimeFamily σ) (P : Prop) : Prop :=
  WithRowPrimes N G rows <|
  (∀ I ∈ Pset, (∏ b, (S I).ideal b) = I) →
  (∀ I ∈ Pset, Pairwise (Function.onFun IsCoprime (G.sum (S I)).ideal)) →
  (∀ I ∈ Pset, ∀ b, IsCoprime (Ideal.span {N}) ((G.sum (S I)).ideal b)) →
  (∀ I ∈ Pset, ∀ b, ringChar (Eis ⧸ (G.sum (S I)).ideal b) ≠ 2) → P

/-- The same arithmetic for a family of columns indexed by actual tuples,
whose ideal product is determined by the tuple. -/
abbrev WithMemberPrimes {ι : Type*} (N : Eis) (G : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (S : ι → PrimeFamily σ) (P : Prop) : Prop :=
  WithRowPrimes N G rows <|
  (∀ p, Pairwise (Function.onFun IsCoprime (G.sum (S p)).ideal)) →
  (∀ p b, IsCoprime (Ideal.span {N}) ((G.sum (S p)).ideal b)) →
  (∀ p b, ringChar (Eis ⧸ (G.sum (S p)).ideal b) ≠ 2) → P

/-- The row coprimalities together with the slotwise admissibility hypotheses
for a family assembled from lists of primes. -/
abbrev WithListPrimes (N : Eis) (G : PrimeFamily φ) (rows : Finset (Ideal Eis))
    (lists : σ → Finset (Ideal Eis)) (P : Prop) : Prop :=
  WithRowPrimes N G rows <|
  (∀ i, ∀ p ∈ lists i, IsCoprime (Ideal.span {N}) p) →
  (∀ i, ∀ p ∈ lists i, ringChar (Eis ⧸ p) ≠ 2) → P

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

attribute [instance] SectorArithmetic.referenceFintype

end
end SevenEighths.InverseReflectedPhase

end OAI
