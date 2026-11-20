module
public import OAI.NumberTheory.DirichletL.Energy.Bands
public import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
public import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
public import OAI.NumberTheory.DirichletL.Moments.CanonicalFirst
public import OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
public import OAI.NumberTheory.DirichletL.Moments.SourceLiveColumn

@[expose] public section

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace OAI.SevenEighths.CanonicalSources
open HeckeFamily CanonicalQuadraticSieve CompletedGauss CenteredMomentCommonRadialData CenteredMomentAllocatedRayDictionary CenteredMomentNaturalFixedRaySource CenteredMomentEnergyBands CenteredMomentCanonicalFirst CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum

local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The zero-frequency and positive-frequency estimates of the preceding width band. -/
abbrev WithBands (W : ℝ → ℂ) (bslot a b L Lslot lo hi Mcap κ Z : ℝ)
    (η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ))
    (P : ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ εchild C₀ C₁ : ℝ, 0 ≤ C₀ → 0 ≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ → P εchild C₀ C₁

/-- Width, line and frequency constraints on the slot parameters. -/
abbrev WithSlotGeometry {ι : Type*} (Lslot lo hi : ℝ)
    (P : (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ → ℝ → Prop) : Prop :=
  ∀ (w σ freq : ι → ℝ) (height mesh : ℝ), 0 ≤ mesh →
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → (∀ i, w i ≤ Lslot) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) → 0 ≤ height → (∀ i, |freq i| ≤ height) →
    P w σ freq height mesh

/-- A bounded source matching the chosen slot parameters and radial support. -/
abbrev WithMatchedSource (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq lows highs : α → ℝ) (W : ℝ → ℂ) (bslot Z Mslot : ℝ)
    (N : ℕ) (lower upper b : ℝ) (P : Input α → Prop) : Prop :=
  ∀ src : Input α, Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀ i, src.hi i ≤ bslot) → (∀ i, src.M i ≤ Mslot) →
    (∀ i, src.lo i = lows i) → (∀ i, src.hi i = highs i) →
    Fintype.card α ≤ N → lower ≤ src.lower → src.upper ≤ upper →
    0 ≤ src.b₁ → 0 ≤ src.b₂ → src.b₁ ≤ max 1 b → src.b₂ ≤ max 1 b → P src

/-- The height character on a frozen allocation of a common prime column. -/
abbrev WithColumn (src : Input α)
    (P : ∀ (C D _R0 : Ideal O), Finset (CommonIndex C D) →
      actualAllocations src.pools C → Character → ℝ → Prop) : Prop :=
  ∀ (C D R0 : Ideal O), ∀ _hC : Supported C, ∀ _hD : Supported D,
    primeSupport C = primeSupport D →
    ∀ (E : Finset (CommonIndex C D)) (B : actualAllocations src.pools C) (τ : Character) (t : ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P ≠ 0 →
    τ.modulus = src.η.modulus * Ideal.span {fixedBadMask} * Ideal.span {(72 : O)} *
      Ideal.span {ActualEisensteinCubic.primeSubsetGenerator (fun P : CommonIndex C D => P.val) E *
        activeConductor C D} → P C D R0 E B τ t

/-- The wide-source argument uses lower bounds on the four lengths; the
narrow-source argument instead uses a smaller bound for the volume. -/
abbrev SourceRegime {ι : Type*} [Fintype ι] (high : Bool) (src : Input ι)
    (Z declared width : ℝ) : Prop :=
  if high then width ≤ declared ∧ Z^(width/4) ≤ src.X₁ ∧ Z^(width/4) ≤ src.X₂ ∧
    Z^(width/4) ≤ src.Y₁ ∧ Z^(width/4) ≤ src.Y₂
  else Real.logb Z (CenteredMomentAmplificationChildInput.volume src) ≤ 5*declared/6

/-- Geometry and fixed parameters shared by the main and error source estimates. -/
structure Geometry (α : Type*) where
  Wslot : ℝ→ℂ
  (aslot bslot Mcap Lslot εremove lo hi κ : ℝ)
  (a b Mslot εmask : ℝ)
  hMslot : 0≤Mslot
  hεmask : 0<εmask
  haPlain : 0<a
  hbPlain : 0≤b
  L : ℝ
  hL : 0≤L
  degree : ℕ
  S : Finset (ℕ×ℕ)
  ha : 0<aslot
  hWs : Function.support Wslot⊆Set.Icc aslot bslot
  hW : ContDiff ℝ ∞ Wslot
  hMcap : 0≤Mcap
  hLs : 0≤Lslot
  hε : 0<εremove
  hκsmall : (1/6:ℝ)≤κ
  hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta
  hκ : 2*HeckeZeroSupremum.beta-1≤κ
  N : ℕ
  (lower upper a0 θsource : ℝ)
  hlower : 0<lower
  hupper : 1≤upper
  ha0 : 0<a0
  hθsource : 0<θsource
  (lows highs : α→ℝ)
  hhighs : ∀i,0≤highs i

def Geometry.restrict (g : Geometry α) (J : Finset α) : Geometry J :=
  { g with lows := fun i => g.lows i.val, highs := fun i => g.highs i.val,
           hhighs := fun i => g.hhighs i.val }
/-- Restrict the arithmetic conductor to a proper nonzero divisor of 72. -/
abbrev WithInternalModulus (P : Character → Ideal O → Prop) : Prop :=
  ∀η₀:Character,∀Q:Ideal O,Q≤M →
    internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} → P η₀ Q

/-- The band, slot and source data, in the order needed by the analytic reductions. -/
abbrev WithSourceFrame {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : Geometry α) (η₀ : Character) (Q : Ideal O) (θ : ι → RayQuotient.Characters M H)
    (lows highs : ι → ℝ) (Z : ℝ)
    (P : ℝ → ℝ → ℝ → (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ → ℝ → Input ι → Prop) : Prop :=
  WithBands (α:=α) M H hH g.Wslot g.bslot g.a g.b g.L g.Lslot g.lo g.hi g.Mcap g.κ Z η₀ Q g.degree g.S
    fun εchild C₀ C₁ =>
  WithSlotGeometry g.Lslot g.lo g.hi fun w σ freq height mesh =>
  WithMatchedSource M H hH η₀ θ w σ freq lows highs g.Wslot g.bslot Z g.Mslot g.N g.lower g.upper g.b
    fun src => P εchild C₀ C₁ w σ freq height mesh src

end OAI.SevenEighths.CanonicalSources
