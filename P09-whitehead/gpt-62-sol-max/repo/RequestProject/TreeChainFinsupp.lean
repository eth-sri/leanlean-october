module

public import RequestProject.TreeChainTopological
public import RequestProject.TreeCoverAcyclic
public import RequestProject.PresentationChainFinsupp

@[expose] public section

/-! Necessity for arbitrary connected cellular two-complexes and arbitrary cellular chains. -/

namespace FiniteChains.Comb
universe u

structure TopChainFS (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- Every stage is connected. -/
  conn : ∀ r, IsConnected (X r)
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → ZeroPi2 (inc r)

end FiniteChains.Comb
