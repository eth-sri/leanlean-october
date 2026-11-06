module

public import HypoellipticAleksandrov.Parabolic.GenericPreLiftWeakDerivativeFamilyAddTwo
public import HypoellipticAleksandrov.Parabolic.SmoothScalarWeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.PrecompactCoordinateDerivativeMajorants
public import HypoellipticAleksandrov.Parabolic.ParabolicW12WeakDerivativeFamily
public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeLocalL2StrongJet

/-!
# Higher-order nested product-box chains

This module constructs the finite chain of precompact spatial sets and strict
time intervals used by the higher-order interior bootstrap.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal MatrixOrder Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic

/-- The transparent geometric certificate for a full higher-order chain of
nested time--velocity product boxes. -/
def IsHigherOrderNestedProductBoxChain
    (d N : ℕ)
    (q₀ s₀ s₁ q₁ : ℝ)
    (Ω O₀ O : PDE.VelocityRegion d)
    (left right : ℕ → ℝ)
    (spatial : ℕ → PDE.VelocityRegion d) : Prop :=
  left 0 = q₀ ∧
  right 0 = q₁ ∧
  spatial 0 = O₀ ∧
  left (N + 2) = s₀ ∧
  right (N + 2) = s₁ ∧
  spatial (N + 2) = O ∧
  (∀ k, k ≤ N + 2 →
    IsOpen (spatial k) ∧
    (spatial k).Nonempty ∧
    IsCompact (closure (spatial k)) ∧
    closure (spatial k) ⊆ Ω ∧
    left k < right k) ∧
  (∀ k, k < N + 2 →
    left k < left (k + 1) ∧
    left (k + 1) < right (k + 1) ∧
    right (k + 1) < right k ∧
    closure (spatial (k + 1)) ⊆ spatial k)

/-- Strictly nested outer and target product boxes supply a full finite chain
of precompact open intermediate product boxes. -/
theorem exists_higherOrderNestedProductBoxChain
    (d N : ℕ)
    (q₀ s₀ s₁ q₁ : ℝ)
    (Ω O₀ O : PDE.VelocityRegion d)
    (hq₀s₀ : q₀ < s₀)
    (hs₀s₁ : s₀ < s₁)
    (hs₁q₁ : s₁ < q₁)
    (hO₀open : IsOpen O₀)
    (hO₀compact : IsCompact (closure O₀))
    (hO₀Ω : closure O₀ ⊆ Ω)
    (hOopen : IsOpen O)
    (hOne : O.Nonempty)
    (hOcompact : IsCompact (closure O))
    (hOO₀ : closure O ⊆ O₀) :
    ∃ (left right : ℕ → ℝ)
      (spatial : ℕ → PDE.VelocityRegion d),
      IsHigherOrderNestedProductBoxChain
        d N q₀ s₀ s₁ q₁ Ω O₀ O left right spatial := by
  induction N generalizing q₀ q₁ O₀ with
  | zero =>
      obtain ⟨V, hVopen, hOV, hVO₀, hVcompact⟩ :=
        exists_open_between_and_isCompact_closure hOcompact hO₀open hOO₀
      let left  := fun k =>
        match k with
        | 0 => q₀
        | 1 => (q₀ + s₀) / 2
        | _ => s₀
      let right  := fun k =>
        match k with
        | 0 => q₁
        | 1 => (s₁ + q₁) / 2
        | _ => s₁
      let spatial  := fun k =>
        match k with
        | 0 => O₀
        | 1 => V
        | _ => O
      refine ⟨left, right, spatial, ?_⟩




      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
      · intro k hk
        interval_cases k <;>
          simp only [left, right, spatial] <;>
          constructor
        · exact hO₀open
        · exact ⟨(hOne.mono ((subset_closure : O ⊆ closure O).trans hOO₀)), hO₀compact, hO₀Ω, by linarith⟩
        · exact hVopen
        · exact ⟨(hOne.mono ((subset_closure : O ⊆ closure O).trans hOV)), hVcompact, (hVO₀.trans (subset_closure.trans hO₀Ω)), by linarith⟩
        · exact hOopen
        · exact ⟨hOne, hOcompact, (hOO₀.trans (subset_closure.trans hO₀Ω)), hs₀s₁⟩
      · intro k hk
        interval_cases k <;> simp only [left, right, spatial]
        · exact ⟨by linarith, by linarith, by linarith, hVO₀⟩
        · exact ⟨by linarith, hs₀s₁, by linarith, hOV⟩
  | succ N ih =>
      obtain ⟨V, hVopen, hOV, hVO₀, hVcompact⟩ :=
        exists_open_between_and_isCompact_closure hOcompact hO₀open hOO₀


      obtain ⟨left', right', spatial', hchain⟩ := ih
        ((q₀ + s₀) / 2) ((s₁ + q₁) / 2) V
        (by linarith) (by linarith) hVopen hVcompact (hVO₀.trans (subset_closure.trans hO₀Ω)) hOV
      let left  := fun k =>
        match k with
        | 0 => q₀
        | k + 1 => left' k
      let right  := fun k =>
        match k with
        | 0 => q₁
        | k + 1 => right' k
      let spatial  := fun k =>
        match k with
        | 0 => O₀
        | k + 1 => spatial' k
      rcases hchain with
        ⟨hleft0, hright0, hspatial0, hleftEnd, hrightEnd, hspatialEnd,
          hboxes, hsteps⟩
      refine ⟨left, right, spatial, ?_⟩

      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact hleftEnd
      · exact hrightEnd
      · exact hspatialEnd
      · intro k hk
        cases k with
        | zero =>
            exact ⟨hO₀open, (hOne.mono ((subset_closure : O ⊆ closure O).trans hOO₀)), hO₀compact, hO₀Ω, by
              simp only [left, right]
              linarith⟩
        | succ k =>
            simpa only [left, right, spatial] using hboxes k (by omega)
      · intro k hk
        cases k with
        | zero =>
            simp only [left, right, spatial]
            rw [hleft0, hright0, hspatial0]
            exact ⟨by linarith, by linarith, by linarith, hVO₀⟩
        | succ k =>
            simpa only [Nat.add_assoc, left, right, spatial] using hsteps k (by omega)

/-- Extract the complete geometric input for one adjacent step of a
higher-order nested product-box chain. -/
theorem IsHigherOrderNestedProductBoxChain.step
    {d N : ℕ} {q₀ s₀ s₁ q₁ : ℝ}
    {Ω O₀ O : PDE.VelocityRegion d}
    {left right : ℕ → ℝ}
    {spatial : ℕ → PDE.VelocityRegion d}
    (h : IsHigherOrderNestedProductBoxChain
      d N q₀ s₀ s₁ q₁ Ω O₀ O left right spatial)
    {k : ℕ} (hk : k < N + 2) :
    left k < left (k + 1) ∧
    left (k + 1) < right (k + 1) ∧
    right (k + 1) < right k ∧
    IsOpen (spatial k) ∧
    IsOpen (spatial (k + 1)) ∧
    (spatial (k + 1)).Nonempty ∧
    IsCompact (closure (spatial (k + 1))) ∧
    closure (spatial (k + 1)) ⊆ spatial k := by
  rcases h with ⟨_, _, _, _, _, _, hboxes, hsteps⟩
  rcases hsteps k hk with ⟨hleft, hmiddle, hright, hclosure⟩


  rcases hboxes k (by omega) with ⟨hkOpen, _, _, _, _⟩
  rcases hboxes (k + 1) (by omega) with ⟨hk1Open, hk1ne, hk1compact, _, _⟩
  exact ⟨hleft, hmiddle, hright, hkOpen, hk1Open, hk1ne, hk1compact, hclosure⟩

end HypoellipticAleksandrov.Parabolic
