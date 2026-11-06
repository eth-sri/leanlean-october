module

public import OAI.NumberTheory.DirichletL.Hecke.PrimeNonprincipal
public import OAI.NumberTheory.DirichletL.Hecke.PrimeScale
public import OAI.NumberTheory.DirichletL.Hecke.DetectorFamilyInclusion

@[expose] public section

namespace OAI

noncomputable section

namespace SevenEighths.HeckeDetectorPrimeFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

structure RowData (M : Ideal O) where
  m : O
  u : O
  m_ne_zero : m≠0
  u_ne_zero : u≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m
  modulus_le : M≤Ideal.span {m}

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

end SevenEighths.HeckeDetectorPrimeFamily

end

end OAI
