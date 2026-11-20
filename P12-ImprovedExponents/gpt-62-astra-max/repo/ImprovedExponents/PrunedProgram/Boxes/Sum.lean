/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ImprovedExponents.PrunedProgram.Boxes.Radix

@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

/-- A string with one digit replaced, in the memory. -/
private theorem segN_set {μ μ' : ℕ → ℤ} {a p} {l} (h : SegN μ a l)
    (hp : p < l.length) (x : ℕ) (hx : μ' (a + p) = x) (ho : ∀ b, b ≠ a + p → μ' b = μ b) :
    SegN μ' a (l.set p x) := by
  intro i hi
  have hi' : i < l.length := by simpa using hi
  by_cases hip : i = p
  · subst hip
    simp [hx]
  · rw [ho _ (by omega), SegN.getElem h hi']
    grind

/-! Read the ten children of a box from its page of base-11 addresses. -/
namespace Reg
slots 0 Page Box Len Pivot Saved Index Sum Code
end Reg
open Reg

def sumRound : Stmt := .store (v Box +' v Pivot) (v Index) ;;
  .call Proc.lookup [v Box,v Len] Code ;; .set Sum (v Sum +' M (v Page +' v Code))
def sumBody : Stmt := .set Saved (M (v Box +' v Pivot)) ;; .for Index (k 10) sumRound ;;
  .store (v Box +' v Pivot) (v Saved) ;; .set 0 (v Sum)

/-- `read` need only describe valid entries, not the initial contents of unused cells. -/
def SumSpec (lim : Limits) (P : Program) := ∀ (page box p : ℕ) (l : List ℕ) (f : List ℕ → ℤ)
    (μ : ℕ → ℤ), p < l.length → SegN μ box l → (∀ d ∈ l, d < 11) →
    box + l.length ≤ page → page + 11^l.length < lim.space →
    (∀ d < 10, μ (page + ofDigitList 11 (l.set p d)) = f (l.set p d)) →
    (∀ j ≤ 10, |((tenValues f l p).take j).sum| ≤ lim.word) →
    ∀ d, d+1 ≤ lim.depth → Meets lim P Proc.sumTen d [page,box,l.length,p] μ (tSumTen l.length)
      fun z ν => z = (tenValues f l p).sum ∧ ν = μ

theorem sum_spec {lim : Limits} {P : Program} (hP : P[Proc.sumTen]? = some sumBody)
    (code : RadixSpec lim P Proc.lookup 11) (std : Std lim) : SumSpec lim P := by
  intro page box p l f μ hp seg digits sep room read fits d hd
  refine .of_body hP ?_
  light_facts std
  have saved := seg.getElem hp
  let vals := tenValues f l p
  let shape := fun (j : ℕ) (z : ℤ) ν =>
    (⟨frame [page, box, l.length, p, (l[p] : ℕ), j, (vals.take j).sum, z], ν⟩ : State)
  let I := fun (_ : ℕ) ν => SameOn (· ≠ box+p) μ ν
  have hpow : (11:ℤ)^l.length ≤ lim.word := by grind
  have hroom := (Nat.le_add_right page (11^l.length)).trans room.le
  have hbox := sep.trans_lt ((Nat.le_add_right page _).trans_lt room)
  unfold sumBody tSumTen
  light_set (l[p] : ℕ) using saved
  let Inv (j : ℕ) (σ : State) := ∃ z ν, σ = shape j z ν ∧ I j ν
  refine Ends.next (10*(tHorner l.length+36)+6)
    (Ends.for Inv 10 (tHorner l.length+28) ?start ?round ?done ?bound (by omega) (by simp; omega))
    (by simp [tLookup,tHorner]; omega)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl⟩
    rw [update_frame_setLocal, ← frame_append_zeros _ 2]; rfl
  case bound => rintro _ _ _ _ ⟨_,_,rfl,_⟩; exact ⟨by simp; omega,rfl⟩
  case round =>
    rintro j _ hj _ ⟨z,ν,rfl,same⟩
    have hsum := fits (j+1) (by omega)
    have hs : (vals.take (j+1)).sum = (vals.take j).sum + f (l.set p j) :=
      List.sum_take_map_range_succ _ hj
    rw [hs] at hsum
    unfold shape sumRound
    light_store (box+p) j
    have eqv : I j (Function.update ν (box+p) j) := same.write (by simp) _
    have ds : ∀ v ∈ l.set p j, v < 11 := by grind
    have key := segN_set seg hp j (by simp) eqv
    light_call (code box l.length _ _ key (by simp) ds hbox hpow _ (by omega)) with _ _ ⟨rfl,rfl⟩
    have addr := ofDigitList_lt _ ds; rw [List.length_set] at addr
    have val := (eqv (page+ofDigitList 11 (l.set p j)) (by omega)).trans (read j hj)
    rw [← val] at hs hsum
    rw [abs_le] at hsum
    light_set ((vals.take (j+1)).sum) using hs
    exact ⟨rfl,_,_,by rw [update_frame_setLocal]; rfl,eqv⟩
  case done =>
    rintro _ _ ⟨z,ν,rfl,same⟩
    have restore : Function.update ν (box+p) (l[p] : ℕ) = μ := by
      funext i; by_cases h : i = box+p
      · subst i; simpa using saved.symm
      · simpa [Function.update_of_ne h] using same i h
    unfold shape
    light_store (box+p) (l[p] : ℕ) using tHorner,tLookup
    light_set ((vals.take 10).sum) using tHorner,tLookup
    have hlen : vals.length = 10 := by simp [vals,tenValues]
    exact by tauto

end Light.Sec4.BoxTable
