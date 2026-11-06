module
public import OAI.NumberTheory.DirichletL.Detector.GramPrimaryLattice
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι]

section
variable (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (C k d : O) (hCd : λ₀^2∣C*d-1) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r})) (P : ι→ Id) [∀i,(P i).IsMaximal] (hg : ∀i,λ₀∉P i) (c : ι→ℕ)
include S hS hbad σ C k d hCd u a b r hr P hg c
lemma jointExtension_zero_off_primary_left
    (n m : O) (hn : ¬(Supported (Ideal.span {n}) ∧ λ₀^2∣n-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  pm_1077 n hn
  simp only [jointExtension,jointFixed,hz,zero_mul]

lemma jointExtension_zero_off_primary_right
    (n m : O) (hm : ¬(Supported (Ideal.span {m}) ∧ λ₀^2∣m-1)) :
    jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)=0 := by
  pm_1077 m hm
  pm_382 jointExtension jointFixed hz star_zero mul_zero zero_mul

theorem jointExtension_ideal_lattice (W : O→ O→ℂ) :
    (∑'I : SupportedIdeal,∑'J : SupportedIdeal,
      jointExtension S hS σ C k u a b r hr P hg c (d*primaryGenerator I.val) (d*primaryGenerator J.val)*
        W (primaryGenerator I.val) (primaryGenerator J.val))=
      ∑'n : O,∑'m : O,jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m := by
  apply primary_ideal_pair_tsum (fun n m=>jointExtension S hS σ C k u a b r hr P hg c (d*n) (d*m)*W n m)
  pm_5572 hn jointExtension_zero_off_primary_left
  pm_5572 hm jointExtension_zero_off_primary_right
end

end SevenEighths.ProbeGramCommon
end

end OAI
