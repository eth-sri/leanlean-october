/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ImprovedExponents.PrunedProgram.Boxes.Tile

@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

/-- A grid of disjoint pages, one for each pair of bands. -/
structure Grid where
  (L m t n ca cb cur box base : ℕ)
  (A B : ℕ → Leaf L → ℤ)

namespace Grid
variable (x : Grid)
abbrev idx (i j : ℕ) := i*x.n+j
abbrev cells := x.n*x.n*stride x.L
abbrev page (i j : ℕ) := x.base + x.idx i j * stride x.L
abbrev tile (i j : ℕ) : Tile := ⟨x.L,x.m,x.t,x.ca+i*10^x.L,x.cb+j*10^x.L,x.cur,x.box,x.page i j,x.A i,x.B j⟩

abbrev Done (ν : ℕ → ℤ) (k : ℕ) := ∀ i < x.n, ∀ j < x.n, x.idx i j < k → (x.tile i j).Complete ν
abbrev Far (μ ν : ℕ → ℤ) := SameOn (fun u => u < x.cur ∨ x.base+x.cells ≤ u) μ ν
structure Safe (lim : Limits) (μ : ℕ → ℤ) : Prop where
  std : Std lim
  sizes : x.t ≤ x.m ∧ x.m ≤ x.L
  order : x.ca+x.n*10^x.L ≤ x.cb ∧ x.cb+x.n*10^x.L ≤ x.cur ∧ x.cur+x.L ≤ x.box ∧
    x.box+x.L ≤ x.base ∧ x.base+x.cells < lim.space
  bounds : ∃ a b : ℤ, (∀ i τ, |x.A i τ| ≤ a) ∧ (∀ j τ, |x.B j τ| ≤ b) ∧ 10^x.m*(a*b) ≤ lim.word
  segA : ∀ i < x.n, SegOn x.m μ (x.ca+i*10^x.L) (x.A i)
  segB : ∀ j < x.n, SegOn x.m μ (x.cb+j*10^x.L) (x.B j)

variable {x} {i j : ℕ} {lim : Limits} {μ ν ν' : ℕ → ℤ}
theorem room (hi : i < x.n) (hj : j < x.n) : x.page i j + stride x.L ≤ x.base+x.cells :=
  Nat.add_assoc .. ▸ Nat.add_le_add_left (Nat.mul_add_le_mul (by nlinarith) le_rfl) _

theorem Safe.tileSafe (H : x.Safe lim μ) (hi : i < x.n) (hj : j < x.n) : (x.tile i j).Safe lim := by
  obtain ⟨a,b,ha,hb,hw⟩ := H.bounds
  have hp := H.order; have hr := room hi hj (x:=x)
  have := Nat.mul_add_le_mul hi (le_refl (10^x.L)); have := Nat.mul_add_le_mul hj (le_refl (10^x.L))
  exact ⟨H.std,H.sizes,by dsimp [tile,page] at *; omega, a,b,ha i,hb j,hw⟩

private theorem advance (H : x.Safe lim μ) (hi : i < x.n) (hj : j < x.n)
    (old : x.Done ν (x.idx i j)) (far : x.Far μ ν) (new : (x.tile i j).Complete ν')
    (writes : Fill.kept (x.tile i j) ν ν') : x.Done ν' (x.idx i j+1) ∧ x.Far μ ν' := by
  have hp := H.order; have hr := room hi hj (x:=x)
  change SameOutside3 ν ν' x.cur x.L x.box x.L (x.page i j) (stride x.L) at writes
  constructor
  · intro i' hi' j' hj' h
    by_cases eq : x.idx i' j' = x.idx i j
    · have eqI : i'=i := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h|h
        · have := Nat.mul_add_lt_mul h hj'; unfold idx at eq; omega
        · have := Nat.mul_add_lt_mul h hj; unfold idx at eq; omega
      subst i'; have eqJ : j'=j := by simpa [idx] using eq
      exact eqJ ▸ new
    · have lt : x.idx i' j' < x.idx i j := by omega
      have sep : x.idx i' j'*stride x.L + stride x.L ≤ x.idx i j*stride x.L := Nat.mul_add_le_mul lt le_rfl
      refine Tile.Holds.keep (old i' hi' j' hj' lt) ?_
      intro u hu; apply writes; change Inside (x.page i' j') (stride x.L) u at hu
      simp only [page] at *; rcases hu with ⟨_,_⟩; exact by grind
  · apply far.then writes; intro u hu
    refine ⟨hu,?_⟩; rcases hu with h|h <;> simp only [page] at * <;> exact by grind

slots 0 EncA EncB N T Cur Box Base Levels Mt Row Col Ret
abbrev args (x : Grid) : List ℤ := [x.ca,x.cb,x.n,(10^x.L:ℕ),x.cur,x.box,x.base,x.L,(x.m-x.t:ℕ)]
abbrev shape (x : Grid) (i j : ℕ) (r : ℤ) (ν : ℕ → ℤ) : State := ⟨frame (args x ++ [(i:ℤ),j,r]),ν⟩

def entry : Stmt := .call Proc.tile [v EncA +' v Row *' v T,v EncB +' v Col *' v T,
  v Base +' (v Row *' v N +' v Col) *' (v T *' v T),v Cur,v Box,v Levels,v Mt] Ret

def body : Stmt := .for Row (v N) (.for Col (v N) entry)

/-- The two counted loops only touch the current tile. In particular all previously
filled pages remain available and the two input arrays are not modified. -/
theorem spec {P d} (K : Passes lim P) (fText : P[Proc.fillList]? = some Fill.body)
    (tText : P[Proc.tile]? = some Tile.body) (H : x.Safe lim μ) (hd : d+4 ≤ lim.depth) :
    Ends lim P d body ⟨frame (args x),μ⟩ (tAllTiles x.L x.m x.t x.n) fun σ =>
      x.Done σ.mem (x.n*x.n) ∧ x.Far μ σ.mem := by
  have hp := H.order; light_facts H.std
  have one : 1 ≤ 10^x.L := by grind
  have hn := Nat.le_mul_of_pos_right x.n one
  let I k ν := x.Done ν k ∧ x.Far μ ν
  let T := tTile x.L x.m x.t
  refine Ends.forShape (fun i (s : ℕ × ℤ) ν => shape x i s.1 s.2 ν) (fun i => I (i*x.n)) x.n
    (x.n*(T+70)+15) (0,0) ⟨fun _ _ _ _ h => by omega,SameOn.refl⟩ ?_ ?_
    (first := by rw [update_frame_setLocal]; exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
    (hT := by unfold tAllTiles; dsimp [T]; grind)
  · rintro i ⟨j,r⟩ ν hi ⟨old,far⟩
    refine Ends.forShape (shape x i) (fun j => I (x.idx i j)) x.n (T+60) r (by simpa [idx,I] using And.intro old far) ?_ ?_
      (hT:=by simp; nlinarith)
    · intro j r ν hj hI
      obtain ⟨old,far⟩ := hI
      have hs := H.tileSafe hi hj
      have ht := hs.layout
      have left := Nat.mul_add_le_mul hi (le_refl (10^x.L)); have right := Nat.mul_add_le_mul hj (le_refl (10^x.L))
      have ds : 0 < stride x.L := Nat.mul_pos one one
      have os := Nat.le_mul_of_pos_right (x.idx i j) ds
      have enough := room hi hj (x:=x)
      simp only [tile,page,idx,stride] at ht os enough
      have sa : SegOn x.m ν (x.ca+i*10^x.L) (x.A i) := (H.segA i hi).keep (μ':=ν) (by light_keep)
      have sb := (H.segB j hj).keep (μ':=ν) (by light_keep)
      zify at ht left right os
      have non : (0:ℤ) ≤ (i*x.n+j : ℤ) * (10^x.L * 10^x.L) := by positivity
      have ten : (0:ℤ) ≤ 10^x.L := by positivity
      have n1 : (0:ℤ) ≤ 10^x.L * 10^x.L := by positivity
      have n2 : (0:ℤ) ≤ i*x.n := by positivity
      have n3 : (0:ℤ) ≤ i*10^x.L := by positivity
      have n4 : (0:ℤ) ≤ j*10^x.L := by positivity
      have step := Tile.spec K fText hs sa sb (d:=d+1) (by omega)
      light_call (Meets.of_body (Q:=fun _ ν' => (x.tile i j).Complete ν' ∧ Fill.kept (x.tile i j) ν ν') tText step)
        using Tile.args,tile,idx,page,stride,T with r' ν' ⟨filled,hk⟩
      exact ⟨r',ν',rfl,advance H hi hj old far filled hk⟩
    · intro r' ν' h; exact ⟨(x.n,r'),ν',rfl,by simpa [idx,Nat.succ_mul] using h⟩
  · intro _ _ h; exact h

end Grid
end Light.Sec4.BoxTable
