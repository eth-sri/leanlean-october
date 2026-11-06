module

public import Mathlib

@[expose] public noncomputable section

open Matrix

/-- Matrices used throughout the normalizer argument. -/
notation "Mat₂" R:max => Matrix (Fin 2) (Fin 2) R
notation:max "SL₂" R:max => Matrix.SpecialLinearGroup (Fin 2) R
notation:max "↑ₘ" g:max => ((g : SL₂ ℝ) : Mat₂ ℝ)

namespace NormalizerLean


local notation "castR" => SpecialLinearGroup.map (Int.castRingHom ℝ)

variable (N : ℕ) [NeZero N]

def toR (Γ : Subgroup SL₂ ℤ) :=
  Γ.map castR

def Gamma0R :=
  (CongruenceSubgroup.Gamma0 N).map castR

def projSL (A : Mat₂ ℝ) : SL₂ ℝ :=
  if hA : 0 < A.det then
    ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩
  else 1

def hPart :=
  2 ^ min 3 (N.factorization 2 / 2) * 3 ^ min 1 (N.factorization 3 / 2)

def IsAtkinLehner (Q : ℕ) g :=
  ∃ x y z w, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    ↑ₘg =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, y; N * z, Q * w]

abbrev NormG (Γ : Subgroup SL₂ ℝ) : Subgroup SL₂ ℝ :=
  Subgroup.normalizer Γ

abbrev BG Γ :=
  NormG Γ ⧸ Γ.subgroupOf (NormG Γ)

/-- The lower-right entry, as a unit modulo the level. -/
def unitMap :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

variable (Δ : Subgroup (ZMod N)ˣ)

def GammaDelta : Subgroup SL₂ ℤ where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧
    ∃ u ∈ Δ, u.val = γ 1 1}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro γ γ' ⟨h0, u, hu, hγ⟩ ⟨h0', u', hu', hγ'⟩
    refine ⟨Subgroup.mul_mem _ h0 h0', u * u', Subgroup.mul_mem _ hu hu', ?_⟩
    have hc := CongruenceSubgroup.Gamma0_mem.1 h0
    have e : (γ * γ') 1 1 = γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Units.val_mul, hγ, hγ', e]
    push_cast
    rw [hc, zero_mul, zero_add]
  inv_mem' := by
    rintro γ ⟨h0, u, hu, hγ⟩
    refine ⟨Subgroup.inv_mem _ h0, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have hc := CongruenceSubgroup.Gamma0_mem.1 h0
    have hdet : (γ 0 0 : ZMod N) * γ 1 1 = 1 := by
      have h := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h
      rw [hc, mul_zero, sub_zero] at h
      exact h
    have e : γ⁻¹ 1 1 = γ 0 0 := by
      simp [Matrix.adjugate_fin_two]
    rw [e]
    rw [← hγ] at hdet
    exact Units.inv_eq_of_mul_eq_one_left hdet

def GammaDeltaR := toR (GammaDelta N Δ)

def epsDelta :=
  haveI := Classical.decPred (· ∈ Δ)
  Nat.gcd N ((Finset.univ.filter (· ∈ Δ)).gcd fun d : (ZMod N)ˣ => d.val.val ^ 2 - 1)

def hDelta :=
  ∏ p ∈ N.primeFactors, p ^ min ((epsDelta N Δ).factorization p) (N.factorization p / 2)

def IsNewmanFormH (h : ℕ) g :=
  ∃ a b c d e, 0 < e ∧ e ∣ N / h ^ 2 ∧
    a * d * (e : ℤ) ^ 2 - b * c * Nat.cast (N / h ^ 2) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ↑ₘg =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, b / h; N * c / h, d * e]

abbrev ofZ (γ : SL₂ ℤ) := castR γ

/-- An integral special-linear matrix, viewed as a real matrix. -/
notation:max "↑ᶻ" g:max => ↑ₘ(ofZ g)

def Gamma0Plus :=
  Subgroup.closure {g | ∃ Q, Q ∣ N ∧ IsAtkinLehner N Q g}

def nDelta := N / hDelta N Δ ^ 2

def MDelta :=
  (Gamma0Plus (nDelta N Δ)).map
    (MulAut.conj (projSL !![hDelta N Δ, 0; 0, 1])⁻¹).toMonoidHom

def IsGamma0Reps (R : Set SL₂ ℤ) :=
  ∀ σ, ∃! r, r ∈ R ∧ σ * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N

def IsHermiteN (a b d : ℕ) :=
  0 < a ∧ 0 < d ∧ a * d ∣ N ∧ b < d ∧ Nat.gcd (Nat.gcd a b) d = 1

def hermMat (a b d : ℕ) : Mat₂ ℝ := !![a, b; 0, d]

def IsPmOneMod {N} m (d : (ZMod N)ˣ) :=
  (ZMod.cast d.val : ZMod m) = 1 ∨ (ZMod.cast d.val : ZMod m) = -1

end NormalizerLean

attribute [simp] Fin.exists_fin_succ_pi Fin.univ_succ Finsupp.single_apply
  Subgroup.mem_subgroupOf NormalizerLean.hermMat Matrix.vecMul dotProduct NeZero.ne NeZero.pos
  Matrix.mul_apply Matrix.natCast_apply Matrix.intCast_apply
