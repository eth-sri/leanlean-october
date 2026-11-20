module
public import Mathlib

@[expose] public section
noncomputable section
namespace TaoTrudgianYang2025

/-- Numerator and denominator degrees of a monomial in `X, H, M, N`. -/
structure WindowMonomial where
  (x h m n xd hd md nd : ℕ)

abbrev WindowMonomial.value (e : WindowMonomial) (X M N H : ℝ) : ℝ :=
  X^e.x*H^e.h*M^e.m*N^e.n/(X^e.xd*H^e.hd*M^e.md*N^e.nd)

abbrev WindowMonomial.exponent (e : WindowMonomial) (ℓ u ν h : ℝ) : ℝ :=
  e.x+e.h*h+e.m*u+e.n*ν-(e.xd+e.hd*h+e.md*ℓ+e.nd*ν)

theorem WindowMonomial.le_rpow {X M N H ℓ u ν h ξ : ℝ} {k : ℕ}
    (hX : 1 ≤ X) (hMl : X^ℓ ≤ M) (hMu : M ≤ X^u)
    (hNl : X^ν/2 ≤ N) (hNu : N ≤ X^ν) (hHl : X^h/2 ≤ H) (hHu : H ≤ X^h)
    (e : WindowMonomial) (hdeg : e.hd+e.nd ≤ k) (hpow : e.exponent ℓ u ν h ≤ ξ) :
    e.value X M N H ≤ (2:ℝ)^k * X^ξ := by
  have hx := zero_lt_one.trans_le hX
  have hm := (Real.rpow_pos_of_pos hx ℓ).trans_le hMl
  have hn := (div_pos (Real.rpow_pos_of_pos hx ν) (by norm_num)).trans_le hNl
  have hh := (div_pos (Real.rpow_pos_of_pos hx h) (by norm_num)).trans_le hHl
  calc
    _ ≤ X^e.x*(X^h)^e.h*(X^u)^e.m*(X^ν)^e.n /
        (X^e.xd*(X^h/2)^e.hd*(X^ℓ)^e.md*(X^ν/2)^e.nd) := by
          dsimp only [WindowMonomial.value]
          gcongr
    _ = (2:ℝ)^(e.hd+e.nd)*(X^e.x*(X^h)^e.h*(X^u)^e.m*(X^ν)^e.n /
        (X^e.xd*(X^h)^e.hd*(X^ℓ)^e.md*(X^ν)^e.nd)) := by
          rw [pow_add]
          simp only [div_pow]
          field_simp
    _ = (2:ℝ)^(e.hd+e.nd)*X^(e.exponent ℓ u ν h) := by
          simp only [WindowMonomial.exponent, ←Real.rpow_mul_natCast hx.le]
          rw [←Real.rpow_natCast X e.x, ←Real.rpow_natCast X e.xd]
          rw [←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_sub hx]
          congr 2
          ring
    _ ≤ _ := by
          gcongr
          · norm_num

/-- Sum the window estimates for a list of monomials, including constant terms. -/
theorem WindowMonomial.sum_le_rpow {X M N H ℓ u ν h ξ : ℝ} {k : ℕ}
    (hX : 1 ≤ X) (hMl : X^ℓ ≤ M) (hMu : M ≤ X^u)
    (hNl : X^ν/2 ≤ N) (hNu : N ≤ X^ν) (hHl : X^h/2 ≤ H) (hHu : H ≤ X^h)
    (es : List WindowMonomial)
    (hs : ∀ e ∈ es, e.hd+e.nd ≤ k ∧ e.exponent ℓ u ν h ≤ ξ) :
    (es.map (fun e => e.value X M N H)).sum ≤ (es.length:ℝ)*((2:ℝ)^k*X^ξ) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := hs e (by simp)
    have ht := ih (fun a ha => hs a (List.mem_cons_of_mem e ha))
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul, add_comm] using
      add_le_add ht (e.le_rpow hX hMl hMu hNl hNu hHl hHu he.1 he.2)

theorem bound_of_moment_window {p j : ℕ} {S C W A P X ε β ζ δ D : ℝ}
    (hp : p ≠ 0) (hX : 1 ≤ X) (hC : 0 ≤ C) (hW : 0 ≤ W) (hδ : 0 ≤ δ) (hD : 1 ≤ D)
    (hmom : S^p ≤ C*W^j*X^ε*P)
    (hpoly : P ≤ A*X^((p:ℝ)*β-ε-ζ)) (hlog : (C*A)*W^j ≤ X^ζ) :
    S ≤ D*X^(β+δ) := by
  have hx:=zero_lt_one.trans_le hX
  have hmoment:S^p ≤ (X^β)^p := calc
    _ ≤ C*W^j*X^ε*P := hmom
    _ ≤ C*W^j*X^ε*(A*X^((p:ℝ)*β-ε-ζ)) := by gcongr
    _ = ((C*A)*W^j)*X^ε*X^((p:ℝ)*β-ε-ζ) := by ring
    _ ≤ X^ζ*X^ε*X^((p:ℝ)*β-ε-ζ) := by gcongr
    _ = (X^β)^p := by
      rw [←Real.rpow_add hx, ←Real.rpow_add hx, ←Real.rpow_mul_natCast hx.le]
      congr 1
      ring
  exact (le_of_pow_le_pow_left₀ hp (by positivity) hmoment).trans
    ((Real.rpow_le_rpow_of_exponent_le hX (le_add_of_nonneg_right hδ)).trans
      (le_mul_of_one_le_left (by positivity) hD))

end TaoTrudgianYang2025
