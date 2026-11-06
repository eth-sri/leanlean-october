module

public import RequestProject.TreeChainTopological
public import RequestProject.TreeCoverNecessityFinsupp
public import RequestProject.PresChainTopologicalFinsupp

@[expose] public section

/-! Necessity for arbitrary connected cellular two-complexes and arbitrary cellular chains. -/

namespace FiniteChains.Comb

structure TopChainFS (K : Complex2.{u}) (n : ℕ) where
  /-- The stages of the chain. -/
  X : ℕ → Complex2.{u}
  /-- The inclusion of `X r` in `X (r + 1)`. -/
  inc : ∀ r, Hom (X r) (X (r + 1))
  incV : ∀ r, Function.Injective (inc r).onV
  incE : ∀ r, Function.Injective (inc r).onE
  incF : ∀ r, Function.Injective (inc r).onF
  /-- Every stage is connected. -/
  conn : ∀ r, IsConnected (X r)
  /-- The inclusion of `K` in the first stage. -/
  base : Hom K (X 0)
  baseV : Function.Injective base.onV
  baseE : Function.Injective base.onE
  baseF : Function.Injective base.onF
  /-- **The inclusion `X r ⊂ X (r + 1)` is zero on `π₂`.** -/
  zero_pi2 : ∀ r, r < n → ZeroPi2 (inc r)

namespace TopChainFS

variable {K : Complex2.{u}} {n : ℕ} (c : TopChainFS K n) (T₀ : SpanningTree K)

end TopChainFS

end FiniteChains.Comb
