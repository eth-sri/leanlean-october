module

public import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialResidualPool
open CanonicalQuadraticSieve CanonicalRowCompletion
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow

theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal ActualEisensteinCubic.O)(j:Ideal ActualEisensteinCubic.O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (by positivity)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (by positivity) le_rfl,hcover⟩

end SevenEighths.InverseInitialResidualPool

end

end OAI
