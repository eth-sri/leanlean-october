module

public import Mathlib

@[expose] public section

/-!
# B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N): definitions

The definitions of the handover note `~/automorphisms_X1/notes/2026-10-02-lean-BN-handover.md` (§4).
They were moved verbatim from `Statements.lean` (frozen at commit 11358c3), so that the proof files can
import them and `Statements.lean` can import the proofs.  No definition changes without the user's
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

/-- The normalizer of Γ₀(N) in SL₂(ℝ). -/
abbrev Norm0 (N : ℕ) : Subgroup SL(2, ℝ) :=
  Subgroup.normalizer (Gamma0R N : Set SL(2, ℝ))

/-- **B(N) = Norm_{SL₂(ℝ)}(Γ₀(N)) / Γ₀(N).** -/
abbrev B (N : ℕ) : Type :=
  Norm0 N ⧸ (Gamma0R N).subgroupOf (Norm0 N)

instance (N : ℕ) : ((Gamma0R N).subgroupOf (Norm0 N)).Normal :=
  Subgroup.normal_in_normalizer

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

/-- m_p = p^{v_p(N)}, the exact power of `p` dividing `N`. -/
def mPart (N p : ℕ) : ℕ := p ^ N.factorization p

/-- S_k = [[1, 1/k], [0, 1]]. -/
def S (k : ℕ) : SL(2, ℝ) :=
  ⟨!![1, (k : ℝ)⁻¹; 0, 1], by simp [det_fin_two]⟩

/-- `g` is an Atkin–Lehner element w_Q of level N:
`g = (1/√Q)·[[Qx, y], [Nz, Qw]]` with `x y z w : ℤ` and `Q²xw − Nyz = Q`.
No divisibility is built in: the theorems below add the hypothesis `Q ∣ N`, which then forces
Q ∥ N.  That hypothesis is essential: for N = 4, Q = 8 the element (1/√8)·[[0, 1], [−8, 0]]
satisfies the equation but does not normalize Γ₀(4).  For Q = 0 the predicate is false. -/
def IsAtkinLehner (N Q : ℕ) (g : SL(2, ℝ)) : Prop :=
  ∃ x y z w : ℤ, (Q : ℤ) ^ 2 * x * w - N * y * z = Q ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt Q)⁻¹ • !![(Q : ℝ) * x, (y : ℝ); (N : ℝ) * z, (Q : ℝ) * w]

/-! ### Presentations -/

/-- The two generators of a local presentation. -/
inductive LGen
  | w
  | s
  deriving DecidableEq

/-- `[x, y] = x⁻¹ y⁻¹ x y` (blueprint convention, not Mathlib's `⁅x, y⁆`). -/
def bracket {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

namespace Words

/-- The word `w`. -/
abbrev w : FreeGroup LGen := FreeGroup.of .w
/-- The word `s`. -/
abbrev s : FreeGroup LGen := FreeGroup.of .s
/-- `r = w s⁻¹ w`, an abbreviation, not a generator [BA]. -/
abbrev r : FreeGroup LGen := w * s⁻¹ * w

end Words

end

end NormalizerLean

-- Part 2, moved verbatim from `NormalizerDelta/Defs.lean`.

/-!
# Normalizers of Γ_Δ(N), Γ(N) and ±Γ₁(N): definitions

Definitions for the second project in `~/normalizer_lean` (plan:
`~/automorphisms_X1/notes/2026-10-08-lean-delta-plan.md`).  The B(N) definitions of
`NormalizerLean/Defs.lean` (`Gamma0R`, `IsAtkinLehner`, `projSL`, `hPart`, …) are reused unchanged.

Conventions (as for B(N)).
* Every quotient is the honest one: Nor_{SL₂(ℝ)}(Γ) / Γ for a subgroup Γ ≤ SL₂(ℝ) (`BG`).
* Modular automorphism groups are quotients in PSL₂(ℝ).  For a group Γ ∋ −1 the
  SL₂(ℝ)-quotient is the same group; for Γ(N) and Γ₁(N), which do not contain −1 when N ≥ 3, the
  modular automorphism group of the curve is the quotient for ±Γ (`pmGammaR`, `pmGamma1R`).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## Normalizer quotients -/

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

/-! ## Γ_Δ(N) -/

/-- Γ_Δ(N) = {γ ∈ Γ₀(N) : γ₁₁ mod N ∈ Δ} ≤ SL₂(ℤ), for a subgroup Δ ≤ (ℤ/N)ˣ.
(`γ 1 1` is the lower right entry.  For γ ∈ Γ₀(N) it is a unit mod N, since det γ = 1.) -/
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

/-! ## s_Δ and ι_Q -/

/-! ## Γ(N) and SL₂(ℤ) -/

/-- {±1} ≤ SL₂(ℤ/N) (trivial for N ≤ 2, where −1 = 1). -/
def pmOneSL (N : ℕ) : Subgroup SL(2, ZMod N) := Subgroup.zpowers (-1)

instance (N : ℕ) : (pmOneSL N).Normal where
  conj_mem n hn g := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * (-1 : SL(2, ZMod N)) = -1 * g := by rw [mul_neg, neg_mul, mul_one, one_mul]
    rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

/-- The image in SL₂(ℝ) of an integer matrix. -/
abbrev ofZ (γ : SL(2, ℤ)) : SL(2, ℝ) := SpecialLinearGroup.map (Int.castRingHom ℝ) γ

/-! ## ±Γ₁(N) -/

end

end NormalizerLean

-- Part 3, moved verbatim from `NormalizerDelta/DefsExtra.lean`.

/-!
# Additions (2026-10-09): M_Δ, the σH coset description, the cases i)–iii), and B₀(N)

Definitions for the statements in `StatementsExtra.lean` (the user approved these additions).
`NormalizerDelta/Defs.lean` and the 34 statements of `Statements.lean` are unchanged.

* M_Δ = D⁻¹ Γ₀(n_Δ)⁺ D, with D = diag(h_Δ, 1) and Γ₀(n)⁺ the subgroup generated
  by all Atkin–Lehner elements of level n (Q = 1 gives Γ₀(n)).
* The coset description used by `aut_orders.py`: representatives σ of Γ₀(N)\SL₂(ℤ) and Hermite forms
  H = [[a, b], [0, d]], a d ∣ N, 0 ≤ b < d, gcd(a, b, d) = 1.
* B₀(N) of the sporadic-points paper (Derickx–Najman, `2511.09015`, §3): there
  B₀(N) := Norm_{GL₂⁺(ℚ)}(Γ₀(N))/Γ₀(N).  Read literally this quotient is infinite (it contains the
  scalars); the intended group is the quotient by Γ₀(N)·ℚ^×.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ## M_Δ -/

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

/-! ## B₀(N) -/

/-- SL₂(ℤ) → GL₂⁺(ℚ). -/
abbrev toGLPosQ : SL(2, ℤ) →* GLPos (Fin 2) ℚ :=
  SpecialLinearGroup.toGLPos.comp (SpecialLinearGroup.map (Int.castRingHom ℚ))

/-- Γ₀(N) in GL₂⁺(ℚ). -/
def Gamma0Q (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := (CongruenceSubgroup.Gamma0 N).map toGLPosQ

/-- The normalizer of Γ₀(N) in GL₂⁺(ℚ). -/
abbrev Norm0Q (N : ℕ) : Subgroup (GLPos (Fin 2) ℚ) := Subgroup.normalizer (Gamma0Q N : Set (GLPos (Fin 2) ℚ))

instance (N : ℕ) : ((Gamma0Q N).subgroupOf (Norm0Q N)).Normal := Subgroup.normal_in_normalizer

end

end NormalizerLean

-- Part 4, moved verbatim from `NormalizerDelta/DefsXN.lean`.

/-!
# X(N) additions (2026-10-10): definitions

Definitions for `StatementsXN.lean`: Γ(N), SL₂(ℤ) and normalizers inside GL₂⁺(ℚ), for the GL₂⁺(ℚ) form of the
modular automorphism group of X(N) (as for B₀(N) in `DefsExtra.lean`).  `NormalizerDelta/Defs.lean`,
`DefsExtra.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

end

end NormalizerLean

-- Part 5, moved verbatim from `NormalizerDelta/DefsCartan.lean`.

/-!
# Cartan modular curves (2026-10-10): definitions

The groups Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H} (they depend only on H ∩ SL₂(ℤ/N)) of the split and non-split Cartan
subgroups H and of their normalizers, defined by congruence conditions on the entries of γ = [[a, b], [c, d]]:
* Γ_sp(N): γ ≡ [[*, 0], [0, *]] mod N (C_sp = diagonal matrices);
* Γ_sp⁺(N): γ ≡ [[*, 0], [0, *]] or [[0, *], [*, 0]] mod N (diagonal or antidiagonal; for N = p an odd prime this is
  the normalizer C_sp⁺(p) of C_sp(p); for composite N it is in general a proper subgroup of the normalizer, and the
  statements use it only at prime level);
* Γ_ns(N, ε): γ ≡ [[a, εc], [c, a]] mod N (C_ns = {[[x, εy], [y, x]]}, the non-split Cartan subgroup when N = p is
  an odd prime and ε is not a square mod p, i.e. F_p[√ε]^× in the basis 1, √ε);
* Γ_ns⁺(N, ε): γ ≡ [[a, εc], [c, a]] or [[a, −εc], [c, −a]] mod N (C_ns⁺ = C_ns ∪ C_ns·diag(1, −1)).
Different non-squares ε give SL₂(ℤ)-conjugate groups.  Convention: Dose–Lido–Mercuri (arXiv:2005.09009) define Γ_H
with a transpose, so their Γ_{C_ns(ξ)} is `GammaNs p ξ⁻¹` here.
The curves are X_sp(N), X_sp⁺(N), X_ns(p), X_ns⁺(p); as before their modular automorphism groups are
`BG (toR Γ)` (all four groups contain −1).  `NormalizerDelta/Defs.lean` and all earlier statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

end

end NormalizerLean

-- Part 6, moved verbatim from `NormalizerDelta/DefsGeneral.lean`.

/-!
# General modular curves (2026-10-10): definitions

Definitions for `StatementsGeneral.lean`.  A modular curve of level N is X_H = Γ_H\ℍ* for a subgroup H ≤ SL₂(ℤ/N),
Γ_H = {γ ∈ SL₂(ℤ) : γ mod N ∈ H}.  (For H ≤ GL₂(ℤ/N) with det H = (ℤ/N)ˣ, as in Dose–Lido–Mercuri,
arXiv:2610.08998, Γ_H only depends on H ∩ SL₂(ℤ/N); every congruence subgroup Γ ⊇ Γ(N) is a Γ_H,
`GammaH_map`.)  The statements are about `BG (toR (GammaH N H))` = Nor(Γ_H)/Γ_H.  For −1 ∈ H this is the modular
automorphism group of X_H; for −1 ∉ H the curve's group is the one for H ⊔ {±1} (as for Γ(N) and Γ₁(N) in
`NormalizerDelta/Defs.lean`).

The local conditions are about the reduction of H modulo q ∣ N, computed entrywise with `ZMod.cast`
(for q ∣ N this is the reduction map ℤ/N → ℤ/q; the statements only use it for q ∣ N, or where q ∣ N follows
from the other hypotheses):
* `FixesLine H q v`: every h ∈ H maps v ∈ (ℤ/q)² to a multiple of v;
* `IsBorelMod H q`: H mod q lies in a Borel subgroup, i.e. fixes the line spanned by a unimodular vector
  (for q = p^k: a vector with v mod p ≠ 0);
* `IsSplitMod H q`: H mod q lies in a split Cartan subgroup, i.e. fixes the lines spanned by v and w with
  det [v w] a unit (equivalently: H mod q is conjugate in GL₂(ℤ/q) into the diagonal matrices);
* `FixesUniqueLine H` (prime level): H fixes exactly one line of F_p².
`NormalizerDelta/Defs.lean` and all earlier definitions and statements are unchanged.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-- The normalizer N(H) of H in SL₂(ℤ/N). -/
abbrev NormH {N : ℕ} (H : Subgroup SL(2, ZMod N)) : Subgroup SL(2, ZMod N) :=
  Subgroup.normalizer (H : Set SL(2, ZMod N))

instance {N : ℕ} (H : Subgroup SL(2, ZMod N)) : (H.subgroupOf (NormH H)).Normal :=
  Subgroup.normal_in_normalizer

end

end NormalizerLean

/-! # Part 7: the normalizer of Γ_Δ(N) for every Δ

Definitions of `NormalizerDelta/StatementsStar.lean` (2026-10-19).  For N ≥ 1 and a subgroup Δ ≤ (ℤ/N)ˣ:
h*_Δ is the largest h such that h² ∣ N, d² ≡ 1 (mod h) for all d ∈ Δ, and Δ contains the kernel of
(ℤ/N)ˣ → (ℤ/(N/h))ˣ; n*_Δ = N/h*_Δ²; D* = diag(h*_Δ, 1).  The statements say that Nor(Γ_Δ(N)) lies between
D*⁻¹Γ₀(n*)D* and D*⁻¹Γ₀(n*)⁺D*, and which Atkin–Lehner elements of level n* it contains. -/

namespace NormalizerLean

noncomputable section

end

end NormalizerLean
