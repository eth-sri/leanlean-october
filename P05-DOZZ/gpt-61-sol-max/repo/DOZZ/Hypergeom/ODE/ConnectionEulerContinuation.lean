/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Hypergeom.ODE.ConnectionRealBox
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
/-! Real Euler regions determine the connection coefficients on their entire nonresonant domain. -/
public section
open Set
namespace DOZZ.Proofs

private theorem noninteger_open : IsOpen gaussConnectionIntegerRangeᶜ :=
  Complex.isometry_intCast.isClosedEmbedding.isClosed_range.isOpen_compl

private theorem noninteger_connected : IsPreconnected gaussConnectionIntegerRangeᶜ :=
  (Set.Countable.isPathConnected_compl_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; norm_num)
    (Set.countable_range fun n : ℤ => (n : ℂ))).isConnected.isPreconnected

private theorem noninteger_neg {z : ℂ} (hz : z ∈ gaussConnectionIntegerRangeᶜ) :
    -z ∈ gaussConnectionIntegerRangeᶜ := by
  rintro ⟨n, hn⟩
  exact hz ⟨-n, by simp_all⟩

variable {f g : ℂ × ℂ × ℂ → ℂ} (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p) (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)

include f g hf hg in
private theorem gaussConnection_eq_of_real_box
    
    {cl ch dl dh al ah c₀ δ₀ a₀ : ℝ}
    (hC : ∀ {x : ℝ}, x ∈ Ioo cl ch → (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hD : ∀ {x : ℝ}, x ∈ Ioo dl dh → (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ)
    (hc₀ : c₀ ∈ Ioo cl ch) (hδ₀ : δ₀ ∈ Ioo dl dh) (ha₀ : a₀ ∈ Ioo al ah)
    (heq : ∀ c ∈ Ioo cl ch, ∀ δ ∈ Ioo dl dh, ∀ a ∈ Ioo al ah,
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a))
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) : f p = g p := by
  have h := gaussConnection_eqOn_of_real_box hf hg
    noninteger_open noninteger_open isOpen_univ
    noninteger_connected noninteger_connected isPreconnected_univ
    (fun _ h => h) (fun _ h => h) hC hD (fun _ => mem_univ _)
    hc₀ hδ₀ ha₀ heq
  have hc : p.2.2 ∈ gaussConnectionIntegerRangeᶜ := by
    simpa [gaussConnectionIntegerRange, eq_comm] using hp.1
  have hd : p.2.2 - p.1 - p.2.1 ∈ gaussConnectionIntegerRangeᶜ := by
    simpa [gaussConnectionIntegerRange, eq_comm] using hp.2
  have ht : gaussConnectionCoordinates p.2.2 (p.2.2 - p.1 - p.2.1) p.1 = p := by
    rcases p with ⟨a, b, c⟩
    simp [gaussConnectionCoordinates]
    ring
  grind

include f g hf hg in
/-- A holomorphic parameter identity on the positive-excess Euler region holds everywhere. -/
theorem gaussConnection_eq_of_positiveEuler 
    (heq : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c - a - b → c < 1 →
      (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ →
      ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ → f (a, b, c) = g (a, b, c))
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) : f p = g p := by
  have hC {x : ℝ} (hx : x ∈ Ioo (11/16 : ℝ) (13/16)) :=
    euler_ofReal_noninteger (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hD {x : ℝ} (hx : x ∈ Ioo (3/16 : ℝ) (5/16)) :=
    euler_ofReal_noninteger (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  apply gaussConnection_eq_of_real_box hf hg hC hD
    (al := 3/16) (ah := 5/16) (c₀ := 3/4) (δ₀ := 1/4) (a₀ := 1/4)
    (by norm_num) (by norm_num) (by norm_num) ?_ hp
  intro c hc δ hd a ha
  have hδ : c - a - (c - δ - a) = δ := by ring
  have h := heq a (c - δ - a) c (by linarith [ha.1])
    (by linarith [hc.1, hd.2, ha.2]) (by rw [hδ]; linarith [hd.1])
    (by linarith [hc.2]) (hC hc) (by rw [hδ]; exact hD hd)
  simpa [gaussConnectionCoordinates] using h

include f g hf hg in
/-- The analogous identity theorem for the negative-excess Euler region. -/
theorem gaussConnection_eq_of_negativeEuler 
    (heq : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c - a → 0 < c - b → c - a - b < 0 → c < 1 →
      (c : ℂ) ∈ gaussConnectionIntegerRangeᶜ →
      ((c - a - b : ℝ) : ℂ) ∈ gaussConnectionIntegerRangeᶜ → f (a, b, c) = g (a, b, c))
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) : f p = g p := by
  have hC {x : ℝ} (hx : x ∈ Ioo (11/16 : ℝ) (13/16)) :=
    euler_ofReal_noninteger (x := x) (by linarith [hx.1]) (by linarith [hx.2])
  have hD {x : ℝ} (hx : x ∈ Ioo (-(5/16) : ℝ) (-(3/16))) :
      (x : ℂ) ∈ gaussConnectionIntegerRangeᶜ := by
    simpa only [Complex.ofReal_neg, neg_neg] using noninteger_neg
      (euler_ofReal_noninteger (x := -x) (by linarith [hx.2]) (by linarith [hx.1]))
  apply gaussConnection_eq_of_real_box hf hg hC hD
    (al := 7/16) (ah := 9/16) (c₀ := 3/4) (δ₀ := -1/4) (a₀ := 1/2)
    (by norm_num) (by norm_num) (by norm_num) ?_ hp
  intro c hc δ hd a ha
  have hδ : c - a - (c - δ - a) = δ := by ring
  have h := heq a (c - δ - a) c (by linarith [ha.1])
    (by linarith [hc.1, hd.2, ha.2]) (by linarith [hc.1, ha.2])
    (by linarith [hd.1, ha.1]) (by rw [hδ]; linarith [hd.2])
    (by linarith [hc.2]) (hC hc) (by rw [hδ]; exact hD hd)
  simpa [gaussConnectionCoordinates] using h

end DOZZ.Proofs
