module

public import NormalizerLean.Local

@[expose] public section

/-!
# T6, part 1: B_p ≅ B(m_p) ((12) of [BA])

Fix p ∣ N, a = v_p(N), m = m_p = pᵃ, and an Atkin–Lehner element w for m at level N (it is also one
at level m). For the local presentation P = ⟨w, s | localRels p a⟩ and F : w ↦ w, s ↦ S_{h(m)}:

* α : P → B(N), u ↦ [F(u)]_N, is well defined by the embedding argument (12) (Stage 1);
* its range is B_p = ⟨[w_{m_p}], [S_{h(m_p)}]⟩;
* α is injective: if F(u) ∈ Γ₀(N) ⊆ Γ₀(m), then u = 1 in P, because P → B(m), u ↦ [F(u)]_m, is
  the T5 isomorphism (its generators have the same classes as Fricke's);
* φ = (T5 iso) ∘ α⁻¹ : B_p → B(m) sends the class of g mod Γ₀(N) to the class of g mod Γ₀(m).
-/

open Matrix MatrixGroups

namespace NormalizerLean

noncomputable section

open Words

instance neZero_mPart {N p : ℕ} [Fact p.Prime] : NeZero (mPart N p) :=
  ⟨mPart_ne_zero Fact.out⟩

section

variable {N p : ℕ} [NeZero N] {wg : SL(2, ℝ)} (hw : IsAtkinLehner N (mPart N p) wg)

include hw

variable (hp : p ∈ N.primeFactors)

include hp

end

end

end NormalizerLean
