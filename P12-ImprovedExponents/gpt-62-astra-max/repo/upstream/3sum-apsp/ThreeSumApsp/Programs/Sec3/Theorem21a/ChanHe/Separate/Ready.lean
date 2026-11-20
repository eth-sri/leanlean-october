/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Separate.Job

@[expose] public section
namespace Light.Sec3.ChanHe.Separate.Job
open ThreeSumApsp ThreeSumApsp.ChanHe Finset
variable (w : Job)
abbrev need (r : ℕ → ℕ → Need) := nodesNeed r w.n w.V w.m w.f
structure Fits (lim : Limits) (r : ℕ → ℕ → Need) : Prop where
  srcEnd : w.src+w.n ≤ w.base
  npos : 1 ≤ w.n
  Vpos : 1 ≤ w.V
  mag : ∀ i<w.n, |w.x i| ≤ w.V
  bitmap : w.top+2*w.V+1 ≤ lim.space
  index : 4*w.B+w.n*(4*w.B) ≤ lim.space
  nodes : w.top+(w.need r).cells ≤ lim.space
  word : (w.need r).word ≤ lim.word
  space : (lim.space:ℤ) ≤ lim.word

structure Ready (μ ν : ℕ → ℤ) : Prop where
  input : ∀ i<w.n, ν (w.src+i)=w.x i
  primes : PrimesAt ν w.base w.np w.m
  zero : ZeroAt ν w.cnt (w.m*w.m)
  kept : Kept μ ν w.base

variable {w} {μ ν τ : ℕ → ℤ} {lim : Limits} {r : ℕ → ℕ → Need}

private theorem prEnd : w.base+w.np ≤ w.cnt := Nat.add_le_add_left (Nat.card_primesLE_le _) _

theorem Ready.keep (h : w.Ready μ ν) (H : w.Fits lim r) (k : Kept ν τ w.out) : w.Ready μ τ := by
  have orig := H.srcEnd
  have hp := prEnd (w:=w)
  have order : w.cnt+w.m*w.m = w.out := rfl
  refine ⟨fun i hi => (k _ (by omega)).trans (h.input i hi),⟨rfl,h.primes.2.congr ?_⟩,
    fun t ht => (k _ (by omega)).trans (h.zero t ht),h.kept.then k fun _ _ => by omega⟩
  intro i hi; simp only [List.length_map,length_sort] at hi
  change i<w.np at hi; exact k _ (by omega)

theorem Fits.view (H : w.Fits lim r) {dst q z : ℕ} (left : w.out ≤ dst) (right : dst+w.n ≤ w.top)
    (hz : z ≤ q) (hq : q ≤ 4*w.B) : (w.view dst q z).Room lim := by
  have order : w.base+w.m+w.m*w.m = w.out := rfl
  have := H.srcEnd; have := H.bitmap; have := H.index; have := H.space
  have := Nat.mul_le_mul_left w.n hq
  refine ⟨by change w.src+w.n ≤ dst; omega, by change dst+w.n ≤ lim.space; omega,
    by change z+w.n*q ≤ lim.space; omega,?_,H.space,by omega⟩
  intro i hi
  suffices aux : ∀ (t v : ℕ) (x : ℤ), dst+w.n ≤ t → t+2*v+1 ≤ lim.space → |x| ≤ v →
      let k := ((t:ℤ)+v+x).toNat
      dst+w.n ≤ k ∧ k<lim.space ∧ (k:ℤ)=(t:ℤ)+v+x by
    simpa only [View.key,Job.view,bias,Nat.cast_add] using aux w.top w.V (w.x i) right H.bitmap (H.mag i hi)
  intros t v x h₁ h₂ h; dsimp; rw [abs_le] at h; omega

private theorem slot_size (dst q z : ℕ) : (w.slot dst q z).len ≤ w.n :=
  card_image_le.trans ((card_filter_le ..).trans (card_range _).le)

theorem Fits.slot (H : w.Fits lim r) {dst q z : ℕ} (left : w.out ≤ dst) (right : dst+w.n ≤ w.top)
    (hs : SetAt τ dst (w.slot dst q z).len (w.slot dst q z).set) : (w.slot dst q z).Ok τ w.env := by
  have le := slot_size (w:=w) dst q z
  refine ⟨hs,le,?_, by change dst+_ ≤ w.top; omega,.inr left⟩
  rintro y hy
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
  exact H.mag _ (mem_filter.mp hi).2

theorem Ready.nodePre (h : w.Ready μ τ) (H : w.Fits lim r) {q a b c d : ℕ}
    (A : SetAt τ w.out (w.slot w.out q a).len (w.slot w.out q a).set)
    (B : SetAt τ (w.out+w.n) (w.slot (w.out+w.n) q b).len (w.slot (w.out+w.n) q b).set)
    (C : SetAt τ (w.out+w.n+w.n) (w.slot (w.out+w.n+w.n) q c).len (w.slot (w.out+w.n+w.n) q c).set)
    (hd : d+(w.need r).depth ≤ lim.depth) : NodesPre lim r τ (w.node q a b c) (Lam w.V) w.f d := by
  have e : w.cnt+w.m*w.m=w.out := rfl
  have t : w.out+3*w.n=w.top := rfl
  have hp := prEnd (w:=w)
  have big := wPar_le_card_primesLE w.n w.V
  have positive : 0 < wPar w.n w.V := by unfold wPar Lam; positivity
  have primes : (Nat.primesLE w.m).Nonempty := card_pos.mp (positive.trans_le big)
  exact ⟨⟨⟨h.primes,h.zero,by change w.base+w.np ≤ w.top; omega,by change w.cnt+w.m*w.m ≤ w.top; omega,.inl hp⟩,
    H.slot le_rfl (by omega) A,H.slot (by omega) (by omega) B,H.slot (by omega) (by omega) C⟩,
    H.Vpos,(card_pos.mpr primes).trans_le (Nat.card_primesLE_le _),rfl,primes,
    ⟨H.word,H.nodes,H.space,hd⟩⟩

theorem node_iff {q a b c d : ℕ} (hp : NodesPre lim r τ (w.node q a b c) (Lam w.V) w.f d)
    (hn : 1 ≤ w.n) : HasSol (slice w.x w.n q a w.n) (slice w.x w.n q b w.n) (slice w.x w.n q c w.n) ↔
      (w.node q a b c).Yes (Lam w.V) w.f :=
  reduction_correct hn ⟨hp.mem.set₁.le,hp.mem.set₂.le,hp.mem.set₃.le,
    hp.mem.set₁.bdd,hp.mem.set₂.bdd,hp.mem.set₃.bdd⟩
end Light.Sec3.ChanHe.Separate.Job
