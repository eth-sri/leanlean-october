module

public import Chazelle.Core.MergeAsmLoop
public import Chazelle.Core.NFLocateHost

/-!
# WP-F merge assembly, part 5: the copied model descriptor

A chain descriptor whose host layout lies below `E` survives any change of the memory at or
above `E`, and can be copied (five words) to another place: `hostAt_agree`,
`chainDescAt_copy`, `chainWF_copy`.  The model descriptor built by `descS` (`0`, then the copy)
describes the chain model and is well formed (`modelDesc_copy`).
-/

namespace Chazelle.Core

namespace MergeAsm

open Machine SignK

@[expose] public section

abbrev hostAt_agree := @HostAt.agree

abbrev chainDescAt_copy := @ChainDescAt.copy

abbrev chainWF_copy := @ChainWF.copy

/-- **The copied model descriptor**: `m' A = 0` and the five words of the chain descriptor at
`bw` copied to `A + 1` describe the chain model and are well formed below any `E' ≥ A + 6`. -/
theorem modelDesc_copy {P : Polygon} {m m' : ℕ → ℕ} {bw A E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) (hEA : E ≤ A)
    (he : MemEqBelow E m' m) (h0 : m' A = 0)
    (hc : ∀ j, j < 5 → m' (A + 1 + j) = m (bw + j)) (hE' : A + 6 ≤ E') :
    ModelDescAt m' A (Qof P) (chainModel C) ∧ ModelDescWF P E' m' A := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hC
  refine ⟨Or.inl ⟨h0, H, C, chainDescAt_copy hC hEb he hc, rfl⟩, by omega, fun _ => ?_⟩
  exact chainWF_copy hwf hC he hc (by omega) (by omega)

/-- **The model descriptor survives** a change of the memory at or above `E` (for a descriptor
of a chain model built as above). -/
theorem modelDesc_agree {P : Polygon} {m m' : ℕ → ℕ} {A E : ℕ} {H : Host} {C : Chain}
    (hwf : ModelDescWF P E m A) (h0 : m A = 0) (hC : ChainDescAt m (A + 1) (Qof P) H C)
    (he : MemEqBelow E m' m) :
    ModelDescAt m' A (Qof P) (chainModel C) ∧ ModelDescWF P E m' A ∧
      ChainDescAt m' (A + 1) (Qof P) H C ∧ m' A = 0 := by
  obtain ⟨hw, hd, hc⟩ := hwf.transportChain h0 hC he le_rfl
  exact ⟨Or.inl ⟨hd, H, C, hc, rfl⟩, hw, hc, hd⟩

/-- The number of edges of a chain with a well-formed descriptor: `2 m + 2 ≤ 128 n`. -/
theorem chain_m_le {P : Polygon} {E : ℕ} {m : ℕ → ℕ} {bw : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) : 2 * C.m + 2 ≤ 128 * P.n := by
  obtain ⟨hl, hHW, -, -⟩ := hwf.2 H C hC
  have h1 := C.add_one_le
  have hQ : (Qof P).n = P.n := shear_n _ _
  have h2 : C.P.n = (H.pts P.n).length := by
    rw [hC.2.1, ← hQ]; simp [Host.poly, Polygon.n]
  have h3 := Host.pts_length_le hHW
  have h4 : H.length * P.n ≤ 64 * P.n := Nat.mul_le_mul_right _ hl
  omega

end

end MergeAsm

end Chazelle.Core
