module
public import OAI.NumberTheory.DirichletL.Moments.FirstSeededGaussianPower

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstNestedSeededGaussianPower
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentFirstSeededGaussianPower

abbrev NestedIndex (α:Type*) := ΣT:Finset α,Finset T

def emptyIndex : NestedIndex ι := ⟨∅,∅⟩

abbrev actual_nested_subsets_seeded_gaussian_power (wlo whi:ℝ)(hwlo:0<wlo)(hwhi:0≤whi)
    (lo hi:ι→ℝ)(hhi:∀i,0≤hi i)(W:𝓢(ℝ,ℂ))(J₁ J₂:ℕ)
    (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (hb₁ : 1≤b₁) (hb₂ : 1≤b₂)
    (ε δ θ B Bseed ξ saving:ℝ)(hε:0<ε)(hδ:0<δ)(hθ:0<θ)(hB:0≤B)(hξ:0<ξ) :=
  gen_subsets_seeded_gaussian_power emptyIndex (fun T => T.2) (fun _ i => i.val.val)
    wlo whi hwlo hwhi lo hi hhi W J₁ J₂ N b b₁ b₂ hb hb₁ hb₂
    ε δ θ B Bseed ξ saving hε hδ hθ hB hξ

