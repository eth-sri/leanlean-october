/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Trace.Algebra
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import ThreeSumApsp.Spec.Sec3.Problems

@[expose] public section
namespace Light.Sec3.Trace
open ThreeSumApsp ThreeSumApsp.Spec Finset

/-- The indicator of a residue, padded to any larger square by zero. -/
def mark (n : ℕ) (a : ℕ → ℕ → ℤ) (v : ℤ) : Mat := fun i j => if i<n ∧ j<n ∧ a i j = v then 1 else 0

def key (p s t : ℕ) : ℤ := if s+t=0 then 0 else if s+t≤p then ↑p-(s+t:ℕ) else 2*↑p-(s+t:ℕ)

theorem key_eq {p s t : ℕ} (hs : s<p) (ht : t<p) : (resid p (-(s+t:ℕ):ℤ) : ℤ) = key p s t := by
  rw [resid_cast (by omega)]
  unfold key; split_ifs with h h'
  · simp [h]
  · have e : -((s+t:ℕ):ℤ) = (p-(s+t:ℕ):ℤ) - p := by ring
    rw [e,Int.sub_emod_right,Int.emod_eq_of_lt] <;> omega
  · have e : -((s+t:ℕ):ℤ) = (2*(p:ℤ)-(s+t:ℕ))-p-p := by ring
    rw [e,Int.sub_emod_right,Int.sub_emod_right,Int.emod_eq_of_lt] <;> omega

def mat (n p : ℕ) (L : List ℤ) : Mat := fun i j => resid p (entry n L i j)

def part (n N p : ℕ) (A B C : Mat) (s t : ℕ) :=
  tri N (mark n A s) (mark n B t) (mark n C (key p s t))

theorem part_bound (n N p : ℕ) (A B C : Mat) (s t : ℕ) : |part n N p A B C s t| ≤ (N:ℤ)^3 := by
  have one X v : Bdd N (mark n X v) 1 := fun i _ j _ => by simp [mark]; split_ifs <;> norm_num
  simpa only [part,Nat.mul_one] using abs_tri (one A s) (one B t) (one C (key p s t))

private theorem reduceSum {n N : ℕ} (h : n≤N) (f : ℕ → ℤ) (hout : ∀ i : ℕ, n ≤ i → f i = 0) :
    ∑ i ∈ range N, f i = ∑ i ∈ range n, f i := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [sum_range_add]; simp [hout]

private theorem cross (m n : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℤ) :
    ∑ r ∈ range m, ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, f r i j k =
    ∑ i ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, ∑ r ∈ range m, f r i j k := by
  rw [sum_comm]; apply sum_congr rfl; intros; rw [sum_comm]; apply sum_congr rfl; intros; rw [sum_comm]

private theorem test {p : ℕ} (hp : 0<p) (x y z : ℤ) :
    ((resid p z:ℤ) = key p (resid p x) (resid p y)) ↔ z+y+x ≡ 0 [ZMOD (p:ℤ)] := by
  rw [← key_eq (resid_lt hp.ne' x) (resid_lt hp.ne' y), Nat.cast_inj]
  have mx : x ≡ (resid p x:ℤ) [ZMOD (p:ℤ)] := (resid_eq_iff hp.ne' x (resid_lt hp.ne' x)).1 rfl
  have my : y ≡ (resid p y:ℤ) [ZMOD (p:ℤ)] := (resid_eq_iff hp.ne' y (resid_lt hp.ne' y)).1 rfl
  have mh : (-(↑(resid p x + resid p y):ℤ)) ≡ -(x+y) [ZMOD (p:ℤ)] := by simpa using (mx.add my).neg.symm
  rw [resid_eq_iff hp.ne' z (resid_lt hp.ne' _)]
  have mr : (-(↑(resid p x + resid p y):ℤ)) ≡ (resid p (-(↑(resid p x + resid p y):ℤ)):ℤ) [ZMOD (p:ℤ)] :=
    (resid_eq_iff hp.ne' _ (resid_lt hp.ne' _)).1 rfl
  have eqv : z ≡ (resid p (-↑(resid p x + resid p y)):ℤ) [ZMOD (p:ℤ)] ↔ z ≡ -(x+y) [ZMOD (p:ℤ)] := ⟨fun h => (h.trans mr.symm).trans mh,fun h => (h.trans mh.symm).trans mr⟩
  rw [eqv]
  constructor
  · intro h; simpa [add_assoc, add_comm, add_left_comm] using h.add_right (x+y)
  · intro h; simpa [add_assoc, add_comm, add_left_comm] using h.sub_right (x+y)

private theorem kron {p x y : ℕ} (hx : x<p) (hy : y<p) (f : ℕ → ℕ → ℤ) :
    ∑ s ∈ range p, ∑ t ∈ range p, (if x=s then 1 else 0)*(if y=t then 1 else 0)*f s t = f x y := by
  rw [sum_eq_single x]
  · rw [sum_eq_single y] <;> simp_all <;> grind
  · intro a _ ha; simp [Ne.symm ha]
  · simp [hx]

theorem total {n N p : ℕ} (hp : 0<p) (hn : n≤N) (ab bc ac : List ℤ) :
    ∑ s ∈ range p, ∑ t ∈ range p, part n N p (mat n p ac) (mat n p bc) (mat n p ab) s t =
    ((triOf n ab bc ac).countZeroMod p : ℤ) := by
  simp only [part, tri, cross p N]
  rw [reduceSum hn _ (fun i hi => by simp [mark,Nat.not_lt.mpr hi])]
  rw [TriangleInstance.countZeroMod, Finset.card_filter, Nat.cast_sum]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_range]
  apply sum_congr rfl; intro i _
  rw [reduceSum hn _ (fun j hj => by simp [mark,Nat.not_lt.mpr hj]),sum_range]
  apply sum_congr rfl; intro j _
  rw [reduceSum hn _ (fun k hk => by simp [mark,Nat.not_lt.mpr hk]),sum_range]
  apply sum_congr rfl; intro k _
  simp only [mark, i.isLt,j.isLt,k.isLt,true_and,mat,Nat.cast_inj, kron (resid_lt hp.ne' _) (resid_lt hp.ne' _),test hp]
  simp [TriangleInstance.S,triOf,add_assoc,add_comm,add_left_comm]
end Light.Sec3.Trace
