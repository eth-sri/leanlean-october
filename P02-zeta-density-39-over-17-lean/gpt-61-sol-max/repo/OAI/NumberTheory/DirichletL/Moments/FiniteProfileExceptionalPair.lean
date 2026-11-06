module
public import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalAmplitude
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalAmplitudePair

@[expose] public section

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentEligibleEnergy

open ConcretePrimeRowBridge
open scoped HeckeO
universe u
structure Profiles (lo hi:ℝ) where
  profile : Fin 2→𝓢(ℝ,ℂ)
  support : ∀i,Function.support (profile i:ℝ→ℂ)⊆Set.Icc lo hi

def Profiles.control {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : ℝ :=
  sourceControl R (p.profile 0)*sourceControl R (p.profile 1)

lemma Profiles.control_nonneg {lo hi:ℝ} (p:Profiles lo hi) (R:Finset (ℕ×ℕ)) : 0≤p.control R :=
  mul_nonneg (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

variable {lo hi:ℝ}
def ProfileAdmissible {ι:Type u} [Fintype ι] (s:Data ι) (p:Profiles lo hi)
    (Q:Ideal O) (Z B r:ℝ) (z:O):Prop:=
  (∀i,1≤ s.P i) ∧ s.m≠0 ∧ s.A≠0 ∧ z≠0 ∧ goodLambda∣s.m ∧ (2:O)∣s.m ∧
  (HeckeRowClosure.rowConductorBound s.η s.m 1 (s.A*z):ℝ)≤Z^B ∧
  CenteredExceptionalProfile.FixedInducingRow s.η Q s.m s.A z ∧
  s.W₁=p.profile 0 ∧ s.W₂=p.profile 1 ∧
  Z^r≤ s.X₁ ∧ Z^r≤ s.X₂ ∧ Z^r≤ s.Y₁ ∧ Z^r≤ s.Y₂






