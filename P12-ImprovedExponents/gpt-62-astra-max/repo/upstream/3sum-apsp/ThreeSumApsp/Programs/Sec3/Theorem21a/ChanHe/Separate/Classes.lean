/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Nodes
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Time
import all ThreeSumApsp.Sec3.Theorem21a.ChanHe.Collisions

/-! Separate *positions* rather than handling repeated input values separately.
A prime not dividing the product of the three index differences separates a
witness into three disjoint residue classes. Only polylogarithmically many
moduli and classes need be tried, independently of the values at those indices. -/

@[expose] public section
namespace Light.Sec3.ChanHe.Separate
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
open private card_prime_divisors_le from ThreeSumApsp.Sec3.Theorem21a.ChanHe.Collisions

theorem separates {n : ℕ} {i j k : Fin n} (a : i ≠ j) (b : j ≠ k) (c : i ≠ k) :
    ∃ p ≤ bound n, 0 < p ∧ i.val%p ≠ j.val%p ∧ j.val%p ≠ k.val%p ∧ i.val%p ≠ k.val%p := by
  let d (x y : Fin n) := (x.val:ℤ)-y.val
  have nz (x y : Fin n) (h : x ≠ y) : d x y ≠ 0 := by dsimp [d]; omega
  have small (x y : Fin n) : |d x y| ≤ (n:ℤ) := by simp [d, abs_le]; omega
  let z := d i j * d j k * d i k
  have hz : |z| ≤ 2*(n^3:ℕ) := calc
    |z| = |d i j| * |d j k| * |d i k| := by simp [z,abs_mul]
    _ ≤ (n:ℤ)*n*n := by gcongr <;> apply small
    _ ≤ _ := by push_cast; nlinarith [show 0 ≤ (n:ℤ)^3 by positivity]
  let M := mPar 0 (n^3)
  let Q := Nat.primesLE M
  have count := card_prime_divisors_le (Q:=Q) (fun _ h => Nat.prime_of_mem_primesLE h)
    (mul_ne_zero (mul_ne_zero (nz i j a) (nz j k b)) (nz i k c)) hz
  have big := wPar_le_card_primesLE 0 (n^3)
  change _ ≤ #Q at big
  simp only [wPar,Nat.sqrt_zero,Nat.zero_add,mul_one] at big
  have pos : 0 < Lam (n^3) := Nat.succ_pos _
  obtain ⟨p,hp,hn⟩ : ∃ p ∈ Q, ¬ (p:ℤ) ∣ z := by
    by_contra! h
    have heq : Q.filter (fun p : ℕ => (p:ℤ) ∣ z) = Q := filter_eq_self.2 h
    change #(Q.filter (fun p : ℕ => (p:ℤ) ∣ z)) ≤ _ at count
    rw [heq] at count; omega
  have diff {x y : Fin n} (h : ¬ (p:ℤ) ∣ d x y) : x.val%p ≠ y.val%p := fun he =>
    h ((natCast_dvd_sub_iff_emod_eq ..).2 (by exact_mod_cast he))
  refine ⟨p, (Nat.le_of_mem_primesLE hp).trans ?_, (Nat.prime_of_mem_primesLE hp).pos,
    diff (fun h => hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)),
    diff (fun h => hn (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)),
    diff (fun h => hn (dvd_mul_of_dvd_right h _))⟩
  simp only [M,mPar,wPar,Nat.sqrt_zero,Nat.zero_add,mul_one,bound,width]
  gcongr; exact Nat.log_le_self ..

/-- Values in the first `j` positions of a progression, clipped to the array. -/
def slice (x : ℕ → ℤ) (n q r j : ℕ) :=
  ((range j).filter (fun i => r+i*q<n)).image fun i => x (r+i*q)

theorem slice_succ (x : ℕ → ℤ) (n q r j : ℕ) : slice x n q r (j+1) =
    if r+j*q<n then insert (x (r+j*q)) (slice x n q r j) else slice x n q r j := by
  simp [slice,range_add_one,filter_insert]; split <;> simp

theorem mem_slice {x : ℕ → ℤ} {n q r : ℕ} {v : ℤ} (hr : r<q) : v ∈ slice x n q r n ↔
    ∃ i : Fin n, i.val%q=r ∧ x i.val=v := by
  simp only [slice,mem_image,mem_filter,mem_range]
  constructor
  · rintro ⟨j,⟨_,h⟩,hv⟩; exact ⟨⟨_,h⟩,by simp [Nat.mod_eq_of_lt hr],hv⟩
  · rintro ⟨i,rfl,rfl⟩
    exact ⟨i/q,⟨(Nat.div_le_self ..).trans_lt i.isLt,by simp [Nat.mod_add_div']⟩,
      by simp [Nat.mod_add_div']⟩

/-- Four gaps describe three *different* residues in increasing order and a
modulus larger than all of them. No invalid selections are sent to the solver. -/
def hit (x : ℕ → ℤ) (n a b c d : ℕ) :=
  let s := a+b+1; let t := s+c+1; let q := t+d+1
  HasSol (slice x n q a n) (slice x n q s n) (slice x n q t n)

theorem correct (x : ℕ → ℤ) (n : ℕ) : ThreeSum (fun i : Fin n => x i) ↔
    ∃ a < bound n, ∃ b < bound n, ∃ c < bound n, ∃ d < bound n, hit x n a b c d := by
  constructor
  · rintro ⟨i,j,k,a,b,c,h⟩
    change x i+x j+x k=0 at h
    obtain ⟨q,hq,hpos,hij,hjk,hik⟩ := separates a b c
    let r (i : Fin n) := i.val%q
    have hr (i : Fin n) : r i<q := Nat.mod_lt _ hpos
    have win (i j k : Fin n) (h₁ : r i < r j) (h₂ : r j < r k) (hs : x i+x j+x k=0) :
        ∃ a < bound n, ∃ b < bound n, ∃ c < bound n, ∃ d < bound n, hit x n a b c d := by
      have := hr k
      refine ⟨r i,by omega,r j-r i-1,by omega,r k-r j-1,by omega,q-r k-1,by omega,?_⟩
      have s : r i+(r j-r i-1)+1=r j := by omega
      have t : r j+(r k-r j-1)+1=r k := by omega
      simp only [hit,s,t,show r k+(q-r k-1)+1=q by omega]
      exact ⟨_,(mem_slice (hr i)).2 ⟨i,rfl,rfl⟩,_,(mem_slice (hr j)).2 ⟨j,rfl,rfl⟩,
        _,(mem_slice (hr k)).2 ⟨k,rfl,rfl⟩,hs⟩
    change r i ≠ r j at hij; change r j ≠ r k at hjk; change r i ≠ r k at hik
    rcases lt_or_gt_of_ne hij with h₁|h₁ <;> rcases lt_or_gt_of_ne hjk with h₂|h₂ <;>
      rcases lt_or_gt_of_ne hik with h₃|h₃
    all_goals first
      | omega
      | (apply win i j k <;> omega)
      | (apply win i k j <;> omega)
      | (apply win j i k <;> omega)
      | (apply win j k i <;> omega)
      | (apply win k i j <;> omega)
      | (apply win k j i <;> omega)
  · rintro ⟨a,_,b,_,c,_,d,_,u,hu,v,hv,w,hw,hs⟩
    obtain ⟨i,hi,rfl⟩ := (mem_slice (by omega)).1 hu
    obtain ⟨j,hj,rfl⟩ := (mem_slice (by omega)).1 hv
    obtain ⟨k,hk,rfl⟩ := (mem_slice (by omega)).1 hw
    exact ⟨i,j,k,by rintro rfl; omega,by rintro rfl; omega,by rintro rfl; omega,hs⟩
end Light.Sec3.ChanHe.Separate
