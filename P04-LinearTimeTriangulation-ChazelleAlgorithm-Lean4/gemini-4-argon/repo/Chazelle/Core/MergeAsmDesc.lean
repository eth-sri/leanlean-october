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

/-- A host layout below `E` survives a change of the memory at or above `E`. -/
theorem hostAt_agree {m m' : ℕ → ℕ} {h E : ℕ} {H : Host} (hH : HostAt m h H)
    (hE : h + 3 * H.length + 4 ≤ E) (he : ∀ a, a < E → m' a = m a) : HostAt m' h H := by
  obtain ⟨h0, h1⟩ := hH
  refine ⟨by rwa [he _ (by omega)], fun i hi => ?_⟩
  have := h1 i hi
  revert this
  cases H.getD i (.run 0 0) with
  | run a l =>
    intro h; simp only at h ⊢
    rwa [he _ (by omega), he _ (by omega), he _ (by omega)]
  | pt x =>
    cases x with
    | vtx j => intro h; simp only at h ⊢; rwa [he _ (by omega), he _ (by omega)]
    | onEdge e j =>
      intro h; simp only at h ⊢
      rwa [he _ (by omega), he _ (by omega), he _ (by omega)]

/-- **Copying a chain descriptor** (host layout below `E`, the five words copied to `d`). -/
theorem chainDescAt_copy {m m' : ℕ → ℕ} {bw d E : ℕ} {Q : Polygon} {H : Host} {C : Chain}
    (hC : ChainDescAt m bw Q H C) (hE : m bw + 3 * H.length + 4 ≤ E)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j)) :
    ChainDescAt m' d Q H C := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hC
  have c0 := hc 0 (by omega)
  have c1 := hc 1 (by omega)
  have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega)
  have c4 := hc 4 (by omega)
  simp only [add_zero] at c0
  refine ⟨?_, h1, by rwa [c1], by rwa [c2], by rwa [c3],
    by rwa [c4]⟩
  rw [c0]
  exact hostAt_agree h0 hE he

/-- **A well-formed copy of a chain descriptor.** -/
theorem chainWF_copy {P : Polygon} {m m' : ℕ → ℕ} {bw d E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hc : ∀ j, j < 5 → m' (d + j) = m (bw + j))
    (hd : d + 5 ≤ E') (hEE : E ≤ E') : ChainWF P E' m' d := by
  obtain ⟨hl, hHW, hEb, hs⟩ := hwf.2 H C hC
  refine ⟨hd, fun H' C' hC' => ?_⟩
  have c0 : m' d = m bw := by simpa using hc 0 (by omega)
  have hH' : HostAt m' (m bw) H := hostAt_agree hC.1 hEb he
  have hHH : H' = H := NFLoc.hostAt_unique (by rw [← c0]; exact hC'.1) hH'
  subst hHH
  refine ⟨hl, hHW, by rw [c0]; omega, ?_⟩
  have e1 : C'.s = C.s := by rw [← hC'.2.2.1, ← hC.2.2.1, hc 1 (by omega)]
  have e2 : C'.P = C.P := by rw [hC'.2.1, hC.2.1]
  rwa [e1, e2]

/-- **The copied model descriptor**: `m' A = 0` and the five words of the chain descriptor at
`bw` copied to `A + 1` describe the chain model and are well formed below any `E' ≥ A + 6`. -/
theorem modelDesc_copy {P : Polygon} {m m' : ℕ → ℕ} {bw A E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw (Qof P) H C) (hEA : E ≤ A)
    (he : ∀ a, a < E → m' a = m a) (h0 : m' A = 0)
    (hc : ∀ j, j < 5 → m' (A + 1 + j) = m (bw + j)) (hE' : A + 6 ≤ E') :
    ModelDescAt m' A (Qof P) (chainModel C) ∧ ModelDescWF P E' m' A := by
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hC
  refine ⟨Or.inl ⟨h0, H, C, chainDescAt_copy hC hEb he hc, rfl⟩, by omega, fun _ => ?_⟩
  exact chainWF_copy hwf hC he hc (by omega) (by omega)

/-- **The model descriptor survives** a change of the memory at or above `E` (for a descriptor
of a chain model built as above). -/
theorem modelDesc_agree {P : Polygon} {m m' : ℕ → ℕ} {A E : ℕ} {H : Host} {C : Chain}
    (hwf : ModelDescWF P E m A) (h0 : m A = 0) (hC : ChainDescAt m (A + 1) (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) :
    ModelDescAt m' A (Qof P) (chainModel C) ∧ ModelDescWF P E m' A ∧
      ChainDescAt m' (A + 1) (Qof P) H C ∧ m' A = 0 := by
  have hcw : ChainWF P E m (A + 1) := hwf.2 h0
  obtain ⟨-, -, hEb, -⟩ := hcw.2 H C hC
  have hA6 := hwf.1
  have hc : ∀ j, j < 5 → m' (A + 1 + j) = m (A + 1 + j) := fun j hj => he _ (by omega)
  have hC' := chainDescAt_copy hC hEb he hc
  have h0' : m' A = 0 := by rwa [he _ (by omega)]
  exact ⟨Or.inl ⟨h0', H, C, hC', rfl⟩, ⟨hA6, fun _ => chainWF_copy hcw hC he hc (by omega) le_rfl⟩,
    hC', h0'⟩

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
