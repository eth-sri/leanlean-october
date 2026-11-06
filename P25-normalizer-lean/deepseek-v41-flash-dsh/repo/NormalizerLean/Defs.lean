module

public import Mathlib


@[expose] public section

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions

The definitions of the handover note `~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).
They were moved verbatim from `Statements.lean` (frozen at commit 11358c3), so that the proof files can
approval.  The conventions are explained in `Statements.lean`.

This file holds the definitions of all six parts: those of Parts 2–6 follow, moved verbatim from
`NormalizerDelta/Defs.lean`, `DefsExtra.lean`, `DefsXN.lean`, `DefsCartan.lean` and `DefsGeneral.lean`, which
now only import this file.  They are in one file because the Comparator challenges (`Challenge/*.lean`) copy
them: Lean shares the auxiliary `_proof_n` lemmas of a file between its declarations, so a copy compiles to the
same constants as the library only if it keeps the library's order; each challenge copies whole parts of this
file, in order.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Definitions -/

/-- Γ₀(N) as a subgroup of SL₂(ℝ): the image of Mathlib's `CongruenceSubgroup.Gamma0 N ≤ SL(2, ℤ)`. -/
def Gamma0R (N : ℕ) : Subgroup SL(2, ℝ) :=
  (CongruenceSubgroup.Gamma0 N).map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The image in SL₂(ℝ) of a real 2×2 matrix `A` of positive determinant: `(det A)^{-1/2} • A`.
Junk value `1` if `det A ≤ 0`; below it is only applied to matrices of positive determinant. -/
def projSL (A : Matrix (Fin 2) (Fin 2) ℝ) : SL(2, ℝ) :=
  if hA : 0 < A.det then
    ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩
  else 1

/-- h(N) = 2^{min(3, ⌊v₂(N)/2⌋)} · 3^{min(1, ⌊v₃(N)/2⌋)}.  By `hPart_isGreatest` this is the largest
divisor of 24 whose square divides N. -/
def hPart (N : ℕ) : ℕ :=
  2 ^ min 3 (N.factorization 2 / 2) * 3 ^ min 1 (N.factorization 3 / 2)

/-- `g` is an Atkin–Lehner element w_Q of level N:
`g = (1/√Q)·[[Qx, y], [Nz, Qw]]` with `x y z w : ℤ` and `Q²xw − Nyz = Q`.
No divisibility is built in: the theorems below add the hypothesis `Q ∣ N`, which then forces
Q ∥ N.  That hypothesis is essential: for N = 4, Q = 8 the element (1/√8)·[[0, 1], [−8, 0]]
satisfies the equation but does not normalize Γ₀(4).  For Q = 0 the predicate is false. -/
def IsAtkinLehner (N Q : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ x y z w : ℤ, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w]

/-- The image in SL₂(ℝ) of a subgroup of SL₂(ℤ). -/
def toR (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℝ) :=
  Γ.map (SpecialLinearGroup.map (Int.castRingHom ℝ))

/-- The normalizer of Γ in SL₂(ℝ). -/
abbrev NormG (Γ : Subgroup SL(2, ℝ)) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Γ : Set SL(2, ℝ))

/-- **Nor_{SL₂(ℝ)}(Γ) / Γ.** -/
abbrev BG (Γ : Subgroup SL(2, ℝ)) : Type :=
  NormG Γ ⧸ Γ.subgroupOf (NormG Γ)

instance (Γ : Subgroup SL(2, ℝ)) : (Γ.subgroupOf (NormG Γ)).Normal :=
  Subgroup.normal_in_normalizer

/-- Γ_Δ(N) = {γ ∈ Γ₀(N) : γ₁₁ mod N ∈ Δ} ≤ SL₂(ℤ), for a subgroup Δ ≤ (ℤ/N)ˣ.
(`γ 1 1` is the lower right entry.  For γ ∈ Γ₀(N) it is a unit mod N, since det γ = 1.) -/
def GammaDelta (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ CongruenceSubgroup.Gamma0 N ∧
    ∃ u ∈ Δ, (u : ZMod N) = ((γ 1 1 : ℤ) : ZMod N)}
  one_mem' := ⟨Subgroup.one_mem _, 1, Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro γ γ' ⟨h0, u, hu, hγ⟩ ⟨h0', u', hu', hγ'⟩
    refine ⟨Subgroup.mul_mem _ h0 h0', u * u', Subgroup.mul_mem _ hu hu', ?_⟩
    have hc := CongruenceSubgroup.Gamma0_mem.1 h0
    have e : ((γ * γ') 1 1 : ℤ) = γ 1 0 * γ' 0 1 + γ 1 1 * γ' 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Units.val_mul, hγ, hγ', e]
    push_cast
    rw [hc, zero_mul, zero_add]
  inv_mem' := by
    rintro γ ⟨h0, u, hu, hγ⟩
    refine ⟨Subgroup.inv_mem _ h0, u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have hc := CongruenceSubgroup.Gamma0_mem.1 h0
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

/-- Γ_Δ(N) in SL₂(ℝ). -/
def GammaDeltaR (N : ℕ) (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) := toR (GammaDelta N Δ)

/-- ε_Δ = gcd(N, d² − 1 : d ∈ Δ), with d running over the representatives
`(d : ZMod N).val ∈ [0, N)`.  The truncated subtraction is harmless: for N ≥ 2 a unit has
`val ≥ 1`, and for N = 1 the result is gcd(1, ·) = 1 anyway. -/
def epsDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  haveI := Classical.decPred (· ∈ Δ)
  Nat.gcd N ((Finset.univ.filter (· ∈ Δ)).gcd fun d : (ZMod N)ˣ => (d : ZMod N).val ^ 2 - 1)

/-- h_Δ = ∏_{p ∣ N} p^{min(v_p(ε_Δ), ⌊v_p(N)/2⌋)}. -/
def hDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ :=
  ∏ p ∈ N.primeFactors, p ^ min ((epsDelta N Δ).factorization p) (N.factorization p / 2)

/-- `g` has the form of the generalized Newman bound, with parameter h (and n = N/h²):
`g = ±(1/√e)·[[ae, b/h], [Nc/h, de]]` with `a b c d : ℤ`, `e ≥ 1`, `e ∣ n`, `ade² − bcn = e`.
(Together with e ∣ n, the equation forces e ∥ n.  The sign ± is there because we work in SL₂(ℝ).)
For h = h(N) this is `IsNewmanForm N`.  The statements only use h = h(N) or h = h_Δ, which are ≥ 1
with h² ∣ N, so the divisions by h and the ℕ-division N / h² are exact. -/
def IsNewmanFormH (N h : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ (a b c d : ℤ) (e : ℕ), 0 < e ∧ e ∣ N / h ^ 2 ∧
    a * d * (e : ℤ) ^ 2 - b * c * ((N / h ^ 2 : ℕ) : ℤ) = e ∧
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (g : Matrix (Fin 2) (Fin 2) ℝ) =
        (ε / Real.sqrt e) •
          !![(a : ℝ) * e, (b : ℝ) / h; (N : ℝ) * c / h, (d : ℝ) * e]

/-- The image in SL₂(ℝ) of an integer matrix. -/
abbrev ofZ (γ : SL(2, ℤ)) : SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ) γ

/-- Γ₀(n)⁺ ≤ SL₂(ℝ): the subgroup generated by the Atkin–Lehner elements w_Q of level n, Q ∣ n
(for Q = 1 these are the elements of Γ₀(n)). -/
def Gamma0Plus (n : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.closure {g | ∃ Q : ℕ, Q ∣ n ∧ IsAtkinLehner n Q g}

/-- n_Δ = N / h_Δ². -/
def nDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : ℕ := N / hDelta N Δ ^ 2

/-- M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D, D = diag(h_Δ, 1) (rescaled into SL₂(ℝ) by `projSL`). -/
def MDelta (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) : Subgroup SL(2, ℝ) :=
  (Gamma0Plus (nDelta N Δ)).map
    (MulAut.conj (projSL !![(hDelta N Δ : ℝ), 0; 0, 1])⁻¹).toMonoidHom

/-! ## The σH coset description -/

/-- `R` is a set of representatives of the right cosets Γ₀(N)σ of SL₂(ℤ). -/
def IsGamma0Reps (N : ℕ) (R : Set SL(2, ℤ)) : Prop :=
  ∀ σ : SL(2, ℤ), ∃! r : SL(2, ℤ), r ∈ R ∧ σ * r⁻¹ ∈ CongruenceSubgroup.Gamma0 N

/-- H = [[a, b], [0, d]] is one of the Hermite forms of `aut_orders.py`: a, d ≥ 1, a d ∣ N, 0 ≤ b < d,
gcd(a, b, d) = 1. -/
def IsHermiteN (N a b d : ℕ) : Prop :=
  0 < a ∧ 0 < d ∧ a * d ∣ N ∧ b < d ∧ Nat.gcd (Nat.gcd a b) d = 1

/-- The real matrix [[a, b], [0, d]]. -/
def hermMat (a b d : ℕ) : Matrix (Fin 2) (Fin 2) ℝ := !![(a : ℝ), b; 0, d]

/-! ## The cases i)–iii) of `hDelta_eq_hPart_iff` -/

/-- d ≡ ±1 (mod m), for a unit d mod N (reduction by `ZMod.cast`; used with m ∣ N). -/
def IsPmOneMod {N : ℕ} (m : ℕ) (d : (ZMod N)ˣ) : Prop :=
  (ZMod.cast (d : ZMod N) : ZMod m) = 1 ∨ (ZMod.cast (d : ZMod N) : ZMod m) = -1


/-! ## Type abbreviations for the proofs -/

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2Z := Matrix (Fin 2) (Fin 2) ℤ
abbrev SL2R := SL(2, ℝ)
abbrev SL2Z := SL(2, ℤ)
abbrev SG (N : ℕ) := Subgroup (ZMod N)ˣ

/-! ## Matrix-entry tactic abbreviations -/

macro "mx" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j <;> simp)

macro "mx" "[" es:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j <;> simp [$es,*])

macro "ms" "[" es:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| ext i j <;> fin_cases i <;> fin_cases j <;> simp [$es,*] <;>
    field_simp <;> (try rw [Real.sq_sqrt (Nat.cast_nonneg _)]) <;> ring)


end

end NormalizerLean
