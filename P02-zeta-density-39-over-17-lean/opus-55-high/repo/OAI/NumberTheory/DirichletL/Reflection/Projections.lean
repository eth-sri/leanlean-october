module
public import OAI.NumberTheory.DirichletL.Reflection.Moving

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {a c : Eis} {mode : Bool}

def actualRowPhase (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceRowPhase s (F.sum (PrimeFamily.residual K hK)).generator_ne_zero
    (F.sum (PrimeFamily.residual K hK)).generator_good (Sum.elim jF (fun _ => 1))
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

def actualSlotPhase (F : PrimeFamily φ) (S : PrimeFamily σ) (jF : φ → ℕ)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ) : ℂ :=
  sourceSlotPhase s (F.sum S).generator_ne_zero (F.sum S).generator_good
    (Sum.elim jF (fun _ => 0)) (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m

omit [Fintype σ] in
set_option hygiene false in
macro "pf_91" x1:term:max x2:ident x3:ident x4:term:max x5:term:max x6:ident x7:ident x8:ident : tactic => `(tactic| (
  classical
  let f : φ ⊕ $x1:term → φ ⊕ (PrimeIndex K ⊕ σ) := Sum.elim Sum.inl (Sum.inr ∘ $x2:ident)
  have hf : Function.Injective f := by
    intro i k h
    cases i <;> cases k <;> simp_all [f]
  have he := $x3:ident s (F.reflected K hK S).generator_ne_zero
    (F.reflected K hK S).generator_good (reflectedExponent jF) f hf
    (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m
  have hp : (fun i => (F.reflected K hK S).generator (f i)) =
      (F.sum $x4:term).generator := by
    funext i
    cases i <;> rfl
  have hj : (fun i => reflectedExponent jF (f i)) = Sum.elim jF (fun _ => $x5:term) := by
    funext i
    cases i <;> rfl
  have hh := $x6:ident s
    (fun i => (F.reflected K hK S).generator_ne_zero (f i))
    (fun i => (F.reflected K hK S).generator_good (f i))
    (F.sum $x4:term).generator_ne_zero
    (F.sum $x4:term).generator_good
    _ _ (Finset.univ.image Sum.inr) (Finset.univ.image Sum.inl) u m hp hj
  rw [he] at hh
  simpa only [$x7:ident,$x8:ident,frozenIndices,Finset.image_image,
    Function.comp_def,f,Sum.elim_inl,Sum.elim_inr] using hh))
section
variable (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (S : PrimeFamily σ) (jF : φ → ℕ) (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (u : Eisˣ) (m : ℕ)
include F K hK S jF s u m
omit [Fintype σ] in
theorem sourceRowPhase_eq_actual :
    sourceRowPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (residualIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualRowPhase F K hK jF s u m := by pf_91 (PrimeIndex K) Sum.inl sourceRowPhase_transport (PrimeFamily.residual K hK) 1 sourceRowPhase_congr_functions actualRowPhase residualIndices

theorem sourceSlotPhase_eq_actual :
    sourceSlotPhase s (F.reflected K hK S).generator_ne_zero
      (F.reflected K hK S).generator_good (reflectedExponent jF)
      (slotIndices φ (PrimeIndex K) σ) (frozenIndices φ (PrimeIndex K) σ) u m =
      actualSlotPhase F S jF s u m := by pf_91 σ Sum.inr sourceSlotPhase_transport S 0 sourceSlotPhase_congr_functions actualSlotPhase slotIndices
end

end
end SevenEighths.InverseReflectedPhase

end OAI
