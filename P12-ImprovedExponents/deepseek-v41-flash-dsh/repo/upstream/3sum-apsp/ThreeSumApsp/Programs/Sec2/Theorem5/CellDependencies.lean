/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.TacticsShort

/-!
# The memory map of Theorem 5: what depends on which cells

SharedReady.dirs lists the cells of the directory that the solver reads. SharedTables are the tables
of the shared block without the directory and the encodings; they depend only on the cells between
these two (SharedTables.congr), and all that the shared stage leaves behind depends only on the
cells of the shared block, without the last of the 32 cells of the directory, which the shared stage
does not use (SharedReady.congr, SharedReady.of_agree).
-/

public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The directory -/

variable {p : Par} {hmL : p.m ≤ p.L} {aX aY b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ}
  {Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ} {μ μ' : ℕ → ℤ}

/-! ## Only the shared block matters -/

/-- The tables lie between the directory and the encodings: they are still there in a memory that
agrees on these cells. -/
theorem SharedTables.congr {p : Par} {b0 : ℕ} {μ μ' : ℕ → ℤ} (h : SharedTables p b0 μ)
    (he : ∀ x, p.aP3 b0 ≤ x → x < p.aENCA b0 → μ' x = μ x) : SharedTables p b0 μ' := by
  have hplaces := p.places b0
  have lp : ∀ b, (powList b (p.L + 1)).length = p.L + 1 := fun b => length_powList b _
  have lphi := Spec.length_phiFlat
  have lpsi := Spec.length_psiFlat
  refine
    { p3 := h.p3.congr fun i hi => he _ tac_omega (by rw [lp] at hi; omega)
      p4 := h.p4.congr fun i hi => he _ tac_omega (by rw [lp] at hi; omega)
      p7 := h.p7.congr fun i hi => he _ tac_omega (by rw [lp] at hi; omega)
      p10 := h.p10.congr fun i hi => he _ tac_omega (by rw [lp] at hi; omega)
      phi := h.phi.congr fun i hi => he _ tac_omega tac_omega
      psi := h.psi.congr fun i hi => he _ tac_omega tac_omega
      mask := fun s hs => (h.mask s hs).congr fun i hi => he _ tac_omega ?_
      band := fun I hI => (he _ tac_omega tac_omega).trans (h.band I hI)
      block := fun I hI => (he _ tac_omega tac_omega).trans (h.block I hI)
      dig3 := fun I hI => (h.dig3 I hI).congr fun i hi => he _ tac_omega ?_
      dig4 := fun x hx => (h.dig4 x hx).congr fun i hi => he _ tac_omega ?_ }
  · rw [List.length_map, Spec.length_unrank] at hi
    have := Nat.mul_add_lt_mul hs hi
    omega
  · have := Nat.mul_add_lt_mul hI (show i < p.Lo by simpa [ThreeSumApsp.digitList] using hi)
    omega
  · have := Nat.mul_add_lt_mul hx (show i < p.m by simpa [ThreeSumApsp.digitList] using hi)
    omega

end Light.Sec2