import RequestProject.CoverChainComplex


/-!
# The boundaries of the cover are the Fox vectors of the relator subgroup

`RequestProject/CoverChainComplex.lean` identifies the cycles of the chain complex of the
cover `K_N` with the Fox vectors of the elements of `Ñ` (the Crowell exact sequence).  This
file identifies the boundaries: the image of `∂₂` consists exactly of the Fox vectors of
the elements of the normal closure `R = ⟪r_1, …, r_m⟫` of the relators.

Together the two statements describe the first homology of the cover completely:

  `H₁(K_N) = 0 ⟺ every element of Ñ has the Fox vector of an element of R`,

which is the algebraic form of `H₁(K_N) = N/[N, N]` up to the classical fact (Magnus) that
the Fox vector map has kernel exactly `[Ñ, Ñ]`.
-/

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]
variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

variable {Nsub ρ}

omit [Fintype α] in
/-- A `ℤ[Q]`-multiple of the Fox vector of an element of a normal subgroup `P ≤ Ñ` is again
the Fox vector of an element of `P`. -/
theorem exists_mem_smul_foxVec {P : Subgroup (FreeGroup α)} [P.Normal] (hP : P ≤ Nsub)
    {r : FreeGroup α} (hr : r ∈ P) (x : CoverRing Nsub) :
    ∃ w ∈ P, x • foxVec Nsub r = foxVec Nsub w := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => aesop
  | add x₁ x₂ h₁ h₂ =>
      obtain ⟨w₁, hw₁, e₁⟩ := h₁
      obtain ⟨w₂, hw₂, e₂⟩ := h₂
      exact ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, by
        rw [foxVec_mul (hP hw₁), ← e₁, ← e₂, add_smul]⟩
  | single q n =>
      obtain ⟨f, rfl⟩ := q.exists_rep
      have hconj := Subgroup.Normal.conj_mem ‹P.Normal› r hr f
      refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
      have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
          = n • proj Nsub (grp f) := by
        rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [foxVec_zpow (Nsub := Nsub) (hP hconj) n, foxVec_conj (Nsub := Nsub) (hP hr),
        hsingle, smul_assoc]

variable (Nsub ρ)
