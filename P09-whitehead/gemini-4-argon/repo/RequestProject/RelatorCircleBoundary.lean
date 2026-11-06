module

public import RequestProject.RelatorCircleEdges

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool)) (j : J)

theorem relatorCircleNext_injective : Function.Injective (relatorCircleNext w j) := by
  intro k l he
  have he' : (k.val + 1) % (w j).length = (l.val + 1) % (w j).length := congrArg Fin.val he
  have := k.isLt; have := l.isLt
  apply Fin.ext
  by_cases hks : k.val + 1 < (w j).length <;> by_cases hls : l.val + 1 < (w j).length
  · rw [Nat.mod_eq_of_lt hks, Nat.mod_eq_of_lt hls] at he'; omega
  · rw [Nat.mod_eq_of_lt hks, show l.val + 1 = (w j).length by omega, Nat.mod_self] at he'; omega
  · rw [show k.val + 1 = (w j).length by omega, Nat.mod_self, Nat.mod_eq_of_lt hls] at he'; omega
  · omega

theorem relatorCircle_cycle_ext
    (c d : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) c = 0)
    (hd : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) d = 0)
    (hpos : 0 < (w j).length)
    (he : c (relatorCircleEdge0 w j ⟨0, hpos⟩) =
      d (relatorCircleEdge0 w j ⟨0, hpos⟩)) : c = d := by
  classical
  have hbdry (k : Fin (w j).length) (x : StrictOrdEdge (RelatorCircle w j) →₀ ℤ) :
      (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) x) (relatorCirclePoint w j k .cedgL) =
        x (relatorCircleEdge0 w j k) + x (relatorCircleEdge1 w j k) ∧
      (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) x) (relatorCirclePoint w j k .cmid) =
        -x (relatorCircleEdge1 w j k) - x (relatorCircleEdge2 w j k) ∧
      (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) x) (relatorCirclePoint w j k .cedgR) =
        x (relatorCircleEdge2 w j k) + x (relatorCircleEdge3 w j k) ∧
      (Comb.bdry1 (strictOrderCx (RelatorCircle w j)) x)
        (relatorCirclePoint w j (relatorCircleNext w j k) .cor) =
        -x (relatorCircleEdge0 w j (relatorCircleNext w j k)) - x (relatorCircleEdge3 w j k) := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add _ _ hx hy =>
        refine ⟨by simp only [map_add, Finsupp.add_apply, hx.1, hy.1]; ring,
          by simp only [map_add, Finsupp.add_apply, hx.2.1, hy.2.1]; ring,
          by simp only [map_add, Finsupp.add_apply, hx.2.2.1, hy.2.2.1]; ring,
          by simp only [map_add, Finsupp.add_apply, hx.2.2.2, hy.2.2.2]; ring⟩
    | single e _ =>
        obtain ⟨l, rfl | rfl | rfl | rfl⟩ := relatorCircle_edge_cases w j e
        all_goals
          by_cases h : l = k
          · subst l
            simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
              relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
              Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc]
          · have hv : l.val ≠ k.val := fun he => h (Fin.ext he)
            have hn : (relatorCircleNext w j l).val ≠ (relatorCircleNext w j k).val :=
              fun he => h (relatorCircleNext_injective w j (Fin.ext he))
            simp [Comb.bdry1, strictOrderCx, relatorCircleEdge0, relatorCircleEdge1,
              relatorCircleEdge2, relatorCircleEdge3, relatorCirclePoint, TCirc.pt,
              Finsupp.single_apply, RelatorCircle, StrictOrdEdge, TCirc, hv, hn]
  have hall (x : StrictOrdEdge (RelatorCircle w j) →₀ ℤ)
      (hx : Comb.bdry1 (strictOrderCx (RelatorCircle w j)) x = 0) (k : Fin (w j).length) :
      let a := x (relatorCircleEdge0 w j ⟨0, hpos⟩)
      x (relatorCircleEdge0 w j k) = a ∧
      x (relatorCircleEdge1 w j k) = -a ∧
      x (relatorCircleEdge2 w j k) = a ∧
      x (relatorCircleEdge3 w j k) = -a := by
    have hcoeff (k : Fin (w j).length) :
        x (relatorCircleEdge1 w j k) = -x (relatorCircleEdge0 w j k) ∧
        x (relatorCircleEdge2 w j k) = x (relatorCircleEdge0 w j k) ∧
        x (relatorCircleEdge3 w j k) = -x (relatorCircleEdge0 w j k) ∧
        x (relatorCircleEdge0 w j (relatorCircleNext w j k)) = x (relatorCircleEdge0 w j k) := by
      obtain ⟨hl, hm, hr, hk⟩ := hbdry k x
      rw [hx, Finsupp.zero_apply] at hl hm hr hk; omega
    have hi : ∀ n (hn : n < (w j).length),
        x (relatorCircleEdge0 w j ⟨n, hn⟩) = x (relatorCircleEdge0 w j ⟨0, hpos⟩) := by
      intro n; induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        have hp : n < (w j).length := by omega
        rw [← show relatorCircleNext w j ⟨n, hp⟩ = ⟨n + 1, hn⟩ from Fin.ext (Nat.mod_eq_of_lt hn),
          (hcoeff ⟨n, hp⟩).2.2.2]
        exact ih hp
    have h0 := hi k.val k.isLt
    have h := hcoeff k
    exact ⟨h0, h.1.trans (congrArg Neg.neg h0), h.2.1.trans h0, h.2.2.1.trans (congrArg Neg.neg h0)⟩
  ext e
  obtain ⟨k, rfl | rfl | rfl | rfl⟩ := relatorCircle_edge_cases w j e <;>
    have hck := hall c hc k <;> have hdk := hall d hd k <;> dsimp only at hck hdk
  · exact hck.1.trans (he.trans hdk.1.symm)
  · exact hck.2.1.trans ((congrArg Neg.neg he).trans hdk.2.1.symm)
  · exact hck.2.2.1.trans (he.trans hdk.2.2.1.symm)
  · exact hck.2.2.2.trans ((congrArg Neg.neg he).trans hdk.2.2.2.symm)

end FiniteChains.PresModel
