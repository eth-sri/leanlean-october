module

public import Mathlib

@[expose] public section

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

def Gamma0R (N : ℕ) : Subgroup SL(2, ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (SpecialLinearGroup.map (Int.castRingHom ℝ))

def projSL (A : Matrix (Fin 2) (Fin 2) ℝ) : SL(2, ℝ) :=
  if hA : 0 < A.det then
    ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩
  else 1

def hPart (N : ℕ) : ℕ :=
  2 ^ min 3 (N.factorization 2 / 2) * 3 ^ min 1 (N.factorization 3 / 2)

def IsAtkinLehner (N Q : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ x y z w : ℤ, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w]

def toR (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℝ) :=
  Γ.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

abbrev NormG (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Γ : Set SL(2, ℝ))

abbrev BG (Γ : Subgroup SL(2, ℝ)) : Type :=
  NormG Γ ⧸ Γ.subgroupOf (NormG Γ)

def GammaDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧
    ∃ u ∈ Δ, (u : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro γ γ' ⟨h0, u, hu, hγ⟩ ⟨h0', u', hu', hγ'⟩
    refine ⟨Subgroup.mul_mem _ h0 h0', u * u', Subgroup.mul_mem _ hu hu', ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have e : ((γ * γ') 1 1 : ℤ) = γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Units.val_mul, hγ, hγ', e]
    push_cast
    rw [hc, zero_mul, zero_add]
  inv_mem' := by
    rintro γ ⟨h0, u, hu, hγ⟩
    refine ⟨Subgroup.inv_mem _ h0, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 h0
    have hdet : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have h := congrArg (fun x : ℤ => (x : ZMod N)) γ.2
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one] at h
      rw [hc, mul_zero, sub_zero] at h
      exact h
    have e : (γ⁻¹ 1 1 : ℤ) = γ 0 0 := by
      simp [Matrix.adjugate_fin_two]
    rw [e]
    rw [← hγ] at hdet
    exact Units.inv_eq_of_mul_eq_one_left hdet

def GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) := toR (GammaDelta N Δ)

def epsDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  haveI := Classical.decPred (· ∈ Δ)
  Nat.gcd N ((Finset.univ.filter (· ∈ Δ)).gcd fun d : (ZMod N)ˣ => (d : ZMod N).val ^ 2 - 1)

def hDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  ∏ p ∈ N.primeFactors, p ^ min ((epsDelta N Δ).factorization p) (N.factorization p / 2)

def IsNewmanFormH (N h : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ N / h ^ 2 ∧
    a * d * (e : ℤ) ^ 2 - b * c * ((N / h ^ 2 : ℕ) : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / h; (N : ℝ) * c / h, (d : ℝ) * e]

abbrev ofZ (γ : SL(2, ℤ)) : SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ) γ

def Gamma0Plus (n : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.closure {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}

def nDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ := N / hDelta N Δ ^ 2

def MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) :=
  (Gamma0Plus (nDelta N Δ)).map
    (MulAut.conj (projSL !![(hDelta N Δ : ℝ), 0; 0, 1])⁻¹).toMonoidHom

def IsGamma0Reps (N : ℕ) (R : Set SL(2, ℤ)) : Prop :=
  ∀ σ : SL(2, ℤ), ∃! r : SL(2, ℤ), r ∈ R ∧ σ * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N

def IsHermiteN (N a b d : ℕ) : Prop :=
  0 < a ∧ 0 < d ∧ a * d ∣ N ∧ b < d ∧ Nat.gcd (Nat.gcd a b) d = 1

def hermMat (a b d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![(a : ℝ), b; 0, d]

def IsPmOneMod {N : ℕ} (m : ℕ) (d : (ZMod N)ˣ) : Prop :=
  (ZMod.cast (d : ZMod N) : ZMod m) = 1 ∨ (ZMod.cast (d : ZMod N) : ZMod m) = -1

end

end NormalizerLean
