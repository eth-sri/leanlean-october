module

public import OAI.NumberTheory.DirichletL.Energy.CanonicalWindow
public import OAI.NumberTheory.DirichletL.Energy.Bands
public import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary

@[expose] public section

namespace OAI.SevenEighths

open scoped Classical
open HeckeFamily CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

/-- The common Gaussian coefficient constants and the scale threshold for
each admissible small conductor. -/
abbrev WithGaussianConstants (M : Ideal O)
    (P : ℕ → Finset (ℕ × ℕ) → ℕ → ℝ → ℕ → Finset (ℕ × ℕ) → Finset (ℕ × ℕ) →
      ℝ → ℝ → ℝ → ℝ → Character → Ideal O → ℝ → ℝ → Prop) : Prop :=
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0<Cc ∧
    ∃J:ℕ,∃Sp Sf:Finset (ℕ×ℕ),(0,0)∈Sp ∧
    ∃Cm Ce Cd Ct:ℝ,0<Cm ∧ 0≤Ce ∧ 0<Cd ∧ 0<Ct ∧
    ForSmallInternalConductors M fun η₀ Q =>
    ∃Kc:ℝ,0<Kc ∧ ∃Z₀:ℝ,1<Z₀ ∧ P n T dc Cc J Sp Sf Cm Ce Cd Ct η₀ Q Kc Z₀

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (cfg : CanonicalEnergyWindow α) (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Apply an estimate to both child-band bounds at the declared window. -/
abbrev AcrossCanonicalBands (Z : ℝ) (η₀ : Character) (Q : Ideal O)
    (P : ℝ → ℝ → ℝ → Prop) : Prop :=
    ∀εchild:ℝ,WithChildBands (α := α) M H hH cfg.Wslot cfg.bslot cfg.a cfg.b cfg.L cfg.Lslot cfg.lo cfg.hi cfg.Mcap εchild cfg.κ Z η₀ Q cfg.degree cfg.S fun C₀ C₁ => P εchild C₀ C₁

/-- The ray sources fitting the canonical window. -/
abbrev ForCanonicalRaySources (η₀ : Character) (θ : α → RayQuotient.Characters M H)
    (w σ freq : α → ℝ) (Z : ℝ) (P : Input α → Prop) : Prop :=
    ForBoundedRaySources M H hH η₀ θ w σ freq cfg.lows cfg.highs cfg.Wslot cfg.bslot Z cfg.Mslot cfg.lower cfg.upper cfg.b cfg.N fun src => P src

end OAI.SevenEighths
