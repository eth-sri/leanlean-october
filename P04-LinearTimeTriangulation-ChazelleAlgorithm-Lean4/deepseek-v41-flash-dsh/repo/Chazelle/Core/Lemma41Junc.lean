module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Desc
public import Chazelle.Core.Lemma41Host

/-!
# WP-J, part 9: junctions of consecutive chains and the descriptor of their union

* `chain_eq`: chains are determined by polygon, start and length;
* `jOf`: the junction of two consecutive chains, with `left = C₁`, `right = C₂`;
* `descWhole`: from descriptors of `C₁` and `C₂` on one host, the words `host, s₁, m₁ + m₂` and the
  top index and bit chosen by the height comparison of the two tops form a descriptor of the union.
-/

namespace Chazelle.Core.L41

open Chazelle Chazelle.Merge

@[expose] public section

theorem chain_eq {C C' : Chain} (h1 : C.P = C'.P) (h2 : C.s = C'.s) (h3 : C.m = C'.m) : C = C' := by
  cases C; cases C'; simp only at h1 h2 h3; subst h1 h2 h3; rfl

/-- The junction of two chains, `C₂` following `C₁`. -/
def jOf (C₁ C₂ : Chain) (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) : Junction := Junction.ofChains C₁ C₂ h

theorem jOf_left (C₁ C₂ : Chain) (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) : (jOf C₁ C₂ h).left = C₁ :=
  chain_eq rfl rfl rfl

theorem jOf_right {C₁ C₂ : Chain} (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) (hP : C₂.P = C₁.P)
    (hs : C₂.s = C₁.s + C₁.m) : (jOf C₁ C₂ h).right = C₂ :=
  chain_eq hP.symm hs.symm rfl

theorem jOf_whole_s {C₁ C₂ : Chain} (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.s = C₁.s := rfl

theorem jOf_whole_m {C₁ C₂ : Chain} (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.m = C₁.m + C₂.m := rfl

theorem jOf_whole_P {C₁ C₂ : Chain} (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.P = C₁.P := rfl

/-- **The descriptor of the union.** -/
theorem descWhole {m : ℕ → ℕ} {Q : Polygon} {H : Host} {C₁ C₂ : Chain} {B₁ B₂ B : ℕ}
    (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) (hP : C₂.P = C₁.P) (hs : C₂.s = C₁.s + C₁.m)
    (h1 : ChainDescAt m B₁ Q H C₁) (h2 : ChainDescAt m B₂ Q H C₂)
    (e0 : m B = m B₁) (e1 : m (B + 1) = C₁.s) (e2 : m (B + 2) = C₁.m + C₂.m)
    (e3 : m (B + 3) = if (C₂.top).2 ≤ (C₁.top).2 then C₁.topIdx else C₁.m + C₂.topIdx)
    (e4 : m (B + 4) = if (C₂.top).2 ≤ (C₁.top).2 then m (B₁ + 4) else m (B₂ + 4)) :
    ChainDescAt m B Q H (jOf C₁ C₂ h).whole := by
  set J := jOf C₁ C₂ h with hJ
  have hl : J.left = C₁ := jOf_left C₁ C₂ h
  have hr : J.right = C₂ := jOf_right h hP hs
  obtain ⟨a0, a1, -, -, -, a5⟩ := h1
  obtain ⟨-, -, -, -, -, b5⟩ := h2
  refine ⟨by rw [e0]; exact a0, by rw [jOf_whole_P]; exact a1, e1, e2, ?_, ?_⟩
  · rw [e3, whole_topIdx J, hl, hr]; rfl
  · Ξ e4, whole_sideBeta J, hl, hr
    split_ifs
    · exact a5
    · exact b5

end

end Chazelle.Core.L41
