/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/PathWords.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Ported to the Lean module system; proofs simplified for the radian configuration.
-/
module

public import Mathlib

@[expose] public noncomputable section

namespace OAI.EuclideanRamsey

/-- Use the zero letter as basepoint. Its image in the corner group will be
normalized to the identity. -/
abbrev LetterGroup := FreeGroup {z : ℂ // z ≠ 0}
def atom (z : ℂ) : LetterGroup := if h : z=0 then 1 else FreeGroup.of ⟨z,h⟩
@[simp] lemma atom_zero : atom 0 = 1 := by simp [atom]
@[simp] lemma atom_coe (z : {z : ℂ // z ≠ 0}) : atom z = FreeGroup.of z := by grind +locals
/-- Extend an arbitrary letter map to the free group by normalizing its basepoint. -/
def letterLift {G : Type*} [Group G] (f : ℂ → G) : LetterGroup →* G :=
  FreeGroup.lift (fun z => f z * (f 0)⁻¹)
@[simp] lemma letterLift_atom {G : Type*} [Group G] (f : ℂ → G) (z : ℂ) :
    letterLift f (atom z) = f z * (f 0)⁻¹ := by by_cases h : z=0 <;> simp [letterLift,atom,h]
variable {ι : Type*}

/-- A row is the similarity `z ↦ b + c*z`, possibly constant. -/
abbrev Sim := ℂ × ℂ
def value (z : ℂ) (p : Sim) := p.2+p.1*z
@[simp] abbrev weight (p : Sim) := Complex.normSq p.1
abbrev Rows := Multiset Sim
def energy : Rows →+ ℝ := Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom weight)
abbrev Strings := FreeMonoid ℂ
def word (z : ℂ) (l : List Sim) := FreeMonoid.ofList (l.map (value z))

inductive Path (a : ι → ℂ) : (ι → LetterGroup) → ℝ → Prop
  | diag (g : LetterGroup) : Path a (fun _ => g) 0
  | copy (p : Sim) : Path a (fun i => atom (value (a i) p)) (weight p)
  | mul {u v lmb μ} : Path a u lmb → Path a v μ → Path a (u*v) (lmb+μ)
lemma Path.nonneg {a : ι → ℂ} {w lmb} (h : Path a w lmb) : 0≤lmb := by
  induction h <;> first | positivity | exact Complex.normSq_nonneg _

variable {a : ι → ℂ}

lemma Path.list {α : Type*} (l : List α) {w : α → ι → LetterGroup} {c : α → ℝ}
    (h : ∀ p, Path a (w p) (c p)) : Path a (fun i => (l.map (w · i)).prod) (l.map c).sum := by
  induction l with
  | nil => exact .diag 1
  | cons p _ ih => exact (h p).mul ih

/-- Two costs at a common endpoint with an arbitrarily wide ratio. -/
def Wide (a : ι → ℂ) := ∀ r > (0:ℝ), ∃ w u v, Path a w u ∧ Path a w v ∧ v < r*u

end OAI.EuclideanRamsey
