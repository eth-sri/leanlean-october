module

public import OAI.NumberTheory.PrimeGaps.WeightMoments

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics



open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable def subsetEnumeration {h n : ℕ}
    (S : {S : Finset (Fin h) // S.card=n}) : Fin n ↪ Fin h :=
  S.1.orderEmbOfFin S.2 |>.toEmbedding

noncomputable def unorderedBlock {n : ℕ} (X h a : ℕ)
    (F : (Fin n → ℝ) → ℝ) (m : ℕ) : ℝ :=
  ∑ S : {S : Finset (Fin h) // S.card=n},
    divisorSum X F m (fun i => a+(subsetEnumeration S i:ℕ))

end LargePrimeGaps

end OAI
