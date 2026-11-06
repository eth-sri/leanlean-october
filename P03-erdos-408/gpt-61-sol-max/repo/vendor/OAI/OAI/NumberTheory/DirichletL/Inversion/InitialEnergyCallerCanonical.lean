module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCaller

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open SevenEighths.InverseMoment SevenEighths.InverseInitialArithmetic
open SevenEighths.InverseInitialQuotientGeometry SevenEighths.InverseInitialClippedColumns
namespace SevenEighths.InverseInitialEnergyCallerCanonical

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def child (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (j : ActualEisensteinCubic.O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild)  :=
  finiteCanonicalMarkedRow p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

omit [DecidableEq σ] in
theorem energy_eq_normalized  pool   Ψ   j 
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
     W   X   J   T 
     labels   rows 
     {Z}  (hZ : 0<Z)  F  :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
    Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  change ((idealDivisors t).card:ℝ)^J *
    columnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t) slots lists a
      labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X = _
  rw [columnEnergy_normalization p hp hcop hg pool Ψ (j*primaryGenerator t)
    slots lists a labels rows _ W X hZ F]
  ring

omit [DecidableEq σ] in
theorem energy_le_moment  pool   Ψ   j 
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
     W   X   J   T 
     labels   rows 
     {Z}  (hZ : 0<Z)  F B 
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergy p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖child p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  rw [energy_eq_normalized p hp hcop hg pool Ψ j slots lists a W X J T labels rows hZ F,
    mul_assoc, Finset.sum_mul]
  bound

theorem sqrt_pair_mass  M B₁ B₂  (hM : 0≤M) :
    Real.sqrt (M*B₁)*Real.sqrt (M*B₂) = M*(Real.sqrt B₁*Real.sqrt B₂) := by
  rw [Real.sqrt_mul hM,Real.sqrt_mul hM]
  grind

end SevenEighths.InverseInitialEnergyCallerCanonical

end

end OAI
