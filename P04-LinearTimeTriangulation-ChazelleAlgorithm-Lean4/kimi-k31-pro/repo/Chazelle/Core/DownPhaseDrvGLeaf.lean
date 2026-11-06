module

public import Chazelle.Core.DownPhaseDrvGStep
public import Chazelle.Rwx
public import Chazelle.RewriteTactics

/-!
# Down-phase driver, region procedure (D5), part 7: leaves and loops with frames

* `forLoopF`: a counted loop whose iterations have a frame has the frame (with the loop's own
  step count);
* `JunOK n H s`: the host point `s` is strictly inside a run of `H` (a valid junction,
  `DownMath.sharedGeneric_run`);
* `leaf_facts`: a leaf `(s, len, a)` of `hostLeaves n C 0 H`: `1 ≤ len ≤ C`, no wrap-around, its
  points are the vertices `a, …, a + len` of `Q`, both its ends are junctions.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

theorem frame_refl (B : Finset ℕ) (c : Config) (k : ℕ) : Frame B c c k :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_refl _, by omega⟩

/-- **A counted loop with frames.** -/
theorem forLoopF {P : Polygon} {W : ℕ} {ir nr : ℕ} {body : Stmt} {B : Finset ℕ}
    (Inv : ℕ → Config → Prop) (Kb N : ℕ)
    (hI : ∀ j c, Inv j c → WordsBounded W c ∧ c.nreg ir = j ∧ c.nreg nr = N)
    (hbody : ∀ j c, j < N → Inv j c →
      ∃ c' k, Exec P W body c c' k ∧ Inv (j + 1) c' ∧ k ≤ Kb ∧ Frame B c c' k)
    {j : ℕ} {c : Config} (hc : Inv j c) (hj : j ≤ N) :
    ∃ c' k, Exec P W (.whileLtN ir nr body) c c' k ∧ Inv N c' ∧
      k ≤ (Kb + 2) * (N - j) + 2 ∧ Frame B c c' k := by
  induction hn : N - j generalizing j c with
  | zero =>
    have hjN : j = N := by omega
    subst hjN
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    exact ⟨c, 2, .whileLtN_false (by rwo [h1, h2]) hw, hc, by omega, frame_refl B c 2⟩
  | succ t ih =>
    obtain ⟨hw, h1, h2⟩ := hI j c hc
    have hlt : j < N := by omega
    obtain ⟨c₁, k₁, e₁, hI₁, hk₁, f₁⟩ := hbody j c hlt hc
    obtain ⟨c', k₂, e₂, hI', hk₂, f₂⟩ := ih hI₁ (by omega) (by omega)
    refine ⟨c', k₁ + 2 + k₂, .whileLtN_true (by rwx [h1, h2]) e₁ e₂, hI', ?_, ?_⟩
    · rwo [Nat.mul_succ]
    · have := f₁.trans f₂
      rw [Finset.union_self] at this
      exact this.mono (le_refl _) (by omega)

/-- **A junction**: the host point `s` is strictly inside a run item. -/
def JunOK (n : ℕ) (H : Host) (s : ℕ) : Prop :=
  ∃ H₁ a ℓ H₂ k, H = H₁ ++ HostItem.run a ℓ :: H₂ ∧ 1 ≤ k ∧ k < ℓ ∧ s = (H₁.pts n).length + k

/-- **The facts about a leaf.** -/
theorem leaf_facts {n C : ℕ} (hC : 1 ≤ C) (hn : 1 ≤ n) {H : Host} (hwf : HostWF n H)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ hostLeaves n C 0 H) :
    1 ≤ x.1 ∧ 1 ≤ x.2.1 ∧ x.2.1 ≤ C ∧ x.2.2 + x.2.1 + 1 ≤ n ∧
      x.1 + x.2.1 + 1 ≤ (H.pts n).length ∧
      (∀ k, k ≤ x.2.1 → (H.pts n).getD (x.1 + k) (.vtx 0) = .vtx (x.2.2 + k)) ∧
      JunOK n H x.1 ∧ JunOK n H (x.1 + x.2.1) := by
  obtain ⟨H₁, a, ℓ, H₂, rfl, h1, h2, h3, h4, h5, h6⟩ := mem_hostLeaves hC hn H 0 hwf x hx
  rw [Nat.zero_add] at h1 h2 h6
  have hlen := DownMath.pts_append_run_length n H₁ H₂ a ℓ
  refine ⟨by omega, h3, h4, h5, by omega, fun k hk => ?_,
    ⟨H₁, a, ℓ, H₂, x.1 - (H₁.pts n).length, rfl, by omega, by omega, by omega⟩,
    ⟨H₁, a, ℓ, H₂, x.1 + x.2.1 - (H₁.pts n).length, rfl, by omega, by omega, by omega⟩⟩
  have e := DownMath.pts_append_run n H₁ H₂ a ℓ (k := x.1 - (H₁.pts n).length + k) (by omega)
  rw [show (H₁.pts n).length + (x.1 - (H₁.pts n).length + k) = x.1 + k by omega] at e
  rw [e, h6]
  congr 1
  rw [show a + (x.1 - (H₁.pts n).length + k) = a + (x.1 - (H₁.pts n).length) + k by omega,
    Nat.add_mod, Nat.mod_eq_of_lt (show k < n by omega)]
  exact Nat.mod_eq_of_lt (by omega)

end

end DrvG

end Chazelle.Core
