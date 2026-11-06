module

public import proofs.HordijkSteelThreshold.InfiniteLigation

@[expose] public section

namespace HordijkSteelThreshold

/-- Ordinary reversible generation in the countable word universe. Unlike
the older ligation-only exploration, this includes recovery of both factors. -/
inductive InfiniteReversibleGenerated (L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} (hne : w ≠ []) (hL : w.length ≤ L) :
      InfiniteReversibleGenerated L field w
  | ligate {u v} (hu : InfiniteReversibleGenerated L field u)
      (hv : InfiniteReversibleGenerated L field v) (ho : field (u ++ v) u.length) :
      InfiniteReversibleGenerated L field $ u ++ v
  | left {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field $ u ++ v)
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field u
  | right {u v} (hu : u ≠ []) (hv : v ≠ [])
      (hp : InfiniteReversibleGenerated L field $ u ++ v)
      (ho : field (u ++ v) u.length) : InfiniteReversibleGenerated L field v

inductive FiniteReversibleGenerated (N L : ℕ) (field : InfiniteSplitEnvironment) :
    List Bool → Prop
  | food {w} : w ≠ [] → w.length ≤ L → w.length ≤ N → FiniteReversibleGenerated N L field w
  | ligate {u v} : FiniteReversibleGenerated N L field u → FiniteReversibleGenerated N L field v →
      field (u ++ v) u.length → (u ++ v).length ≤ N → FiniteReversibleGenerated N L field (u ++ v)
  | left {u v} : u ≠ [] → v ≠ [] → FiniteReversibleGenerated N L field (u ++ v) →
      field (u ++ v) u.length → FiniteReversibleGenerated N L field u
  | right {u v} : u ≠ [] → v ≠ [] → FiniteReversibleGenerated N L field (u ++ v) →
      field (u ++ v) u.length → FiniteReversibleGenerated N L field v

theorem finiteReversibleGenerated_mono_cap {N M L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool} (hNM : N ≤ M)
    (h : FiniteReversibleGenerated N L field w) :
    FiniteReversibleGenerated M L field w := by
  induction h <;> grind [FiniteReversibleGenerated]

theorem finiteReversibleGenerated_to_infinite {N L : ℕ}
    {field : InfiniteSplitEnvironment} {w : List Bool}
    (h : FiniteReversibleGenerated N L field w) : InfiniteReversibleGenerated L field w := by
  induction h <;> grind [InfiniteReversibleGenerated]

variable {L : ℕ} {field : InfiniteSplitEnvironment} {w : List Bool}

/-- Every reversible generation has a finite cap certificate, but this cap
need not be the target's length: cleavage can first require a longer product. -/
theorem infiniteReversibleGenerated_finite_certificate
    (h : InfiniteReversibleGenerated L field w) :
    ∃ N, FiniteReversibleGenerated N L field w := by
  induction h with
  | @ligate u v _ _ ho ihu ihv =>
    obtain ⟨⟨N, hN⟩, M, hM⟩ := And.intro ihu ihv
    exact ⟨max (max N M) (u ++ v).length, .ligate
      (finiteReversibleGenerated_mono_cap (by omega) hN)
      (finiteReversibleGenerated_mono_cap (by omega) hM) ho $ by omega⟩
  | food => tauto
  | _ => grind [FiniteReversibleGenerated]

theorem infiniteReversibleGenerated_iff_finite_certificate  :
    InfiniteReversibleGenerated L field w ↔ ∃ N, FiniteReversibleGenerated N L field w :=
  ⟨infiniteReversibleGenerated_finite_certificate,
    fun ⟨_, h⟩ => finiteReversibleGenerated_to_infinite h⟩

end HordijkSteelThreshold
