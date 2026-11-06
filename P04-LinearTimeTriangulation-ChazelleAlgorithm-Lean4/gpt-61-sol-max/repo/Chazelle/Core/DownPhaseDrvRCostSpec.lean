module

public import Chazelle.Core.DownPhaseDrvRRegSpec
public import Chazelle.Core.DownPhaseDrvRObl

/-!
# Down-phase driver: the cost arithmetic of one level (D11)

One level at merge grade `μ` (`LevelSpec`) has the budget `κ (K + 1) (lemma41Nat μ + 1)`.  Its
parts cost, per region (there are `K + 1`):

* host RAM: a constant; region procedure: `κ_R (lemma41Nat μ + 1)` (`RegionSpec`);
* extraction: `κ_X (#chords of N_R + 1)`, with `#chords of N_R ≤ lvNch μ` (Lemma 2.3 with cap
  `regCap`, at most `10 · 2^μ + 8` host points, granularity `≥ γ₀ = 3 · 2^(⌈βμ⌉+10)`); the kept
  lists have at most `lvNch μ` triples each, so `K₁ + 1 ≤ (K + 1) (lvNch μ + 1)` chords after the
  splice;
* splice: `κ (K₁ + #arcs + 1) (⌈log₂ (4 · max |Lx_r|)⌉ + 1)`;
* restoration rounds (`RoundsSpec` with the interior oracles of `IntOraclesSpec`, at
  `γ_r = lvGr μ = 2^(⌈βμ⌉+12)`): `κ (K₁ + 1) F(γ_r) G(γ_r) (H(γ_r) + ⌈log₂ γ_r⌉ + 1)`,
  `F = shCost κo`, `G = cuCost κo`, `H = cutGran`.

**`LvCostSpec`** is the arithmetic that bounds all of these by `κ (lemma41Nat μ + 1)` per region
(the `2^(74μ/75)` of Lemma 4.1: `lvNch μ ≈ 2^(60μ/75)`, `F(γ_r) ≈ μ 2^(11μ/75)`, `G(γ_r) ≈ μ`,
`H(γ_r) ≈ 2^(3μ/75)`; the tools are those of `Lemma41Bridge`), and the size threshold `n₀` of the
levels (`γ_r`, `γ₀ + 129` and the weight bound of `Inv(λ)` stay below `n - 1`).
-/

namespace Chazelle.Core

namespace DrvR

@[expose] public section

/-- The bound on the chords of a region map at merge grade `μ` (Lemma 2.3, granularity `γ₀`). -/
noncomputable def lvNch (μ : ℕ) : ℕ :=
  140 * (regCap + 2) * (20 * 2 ^ μ + 17) / (3 * 2 ^ (Cost.ceilBeta μ + 10) + 1)

/-- The weight bound `γ_r = 2^(⌈βμ⌉+12)` of `Inv(μ)` (the rounds' semigranularity). -/
noncomputable def lvGr (μ : ℕ) : ℕ := 2 ^ (Cost.ceilBeta μ + 12)

/-- **The cost arithmetic of one level (D11).** -/
def LvCostSpec : Prop :=
  (∃ n₀ : ℕ, ∀ n, n₀ ≤ n → 2 ^ (Cost.ceilBeta (topGrade n) + 13) + 200 ≤ n) ∧
  ∀ κo : ℕ, ∃ κ : ℕ, ∀ μ, 15 ≤ μ →
    lvNch μ ≤ κ * (lemma41Nat μ + 1) ∧
    (lvNch μ + 1) * (Nat.clog 2 (4 * lvNch μ + 4) + 1) ≤ κ * (lemma41Nat μ + 1) ∧
    (lvNch μ + 1) * shCost κo (lvGr μ) * cuCost κo (lvGr μ) *
        (cutGran (lvGr μ) + Nat.clog 2 (lvGr μ) + 1) ≤ κ * (lemma41Nat μ + 1)

end

end DrvR

end Chazelle.Core
