module

public import NormalizerLean.AtkinLehner

@[expose] public section

/-!
# T1 in general: matrices of Newman's form (8′) normalize Γ₀(N) ([Nw §1])

With N = e·m·h² (h = h(N), n = N/h² = e·m), g = (ε/√e)·G, G = [[ae, b/h], [Nc/h, de]], and
γ = [[x, y], [Nz, x + hf]] ∈ Γ₀(N) (t ≡ x mod h because units mod h ∣ 24 square to 1),
G γ adj(G) = e·M with M the explicit integer matrix below (checked in sympy first).
Also `conjGamma0n_le_normalizer`: D⁻¹Γ₀(n)D consists of (8′)-matrices with e = 1.
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

/-! ### D⁻¹Γ₀(n)D -/

theorem coe_projSL (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) :
    ((projSL A : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt A.det)⁻¹ • A := by
  have : projSL A = ⟨(Real.sqrt A.det)⁻¹ • A, by
      rw [det_smul, Fintype.card_fin, inv_pow, Real.sq_sqrt hA.le, inv_mul_cancel₀ hA.ne']⟩ :=
    dif_pos hA
  rw [this]

end

end NormalizerLean
