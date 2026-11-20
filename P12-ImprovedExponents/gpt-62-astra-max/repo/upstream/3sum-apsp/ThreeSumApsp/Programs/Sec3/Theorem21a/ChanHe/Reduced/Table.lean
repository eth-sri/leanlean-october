/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Slots

@[expose] public section
namespace Light.Sec3.ChanHe.RepTable
open ThreeSumApsp ThreeSumApsp.ChanHe

slots 0 Len Src Mod Sign Width Dst Free Padding I R

def round (p : ℕ) : Stmt :=
  let val := M (v Src +' v I)
  let cell := v Dst +' v R
  .call p [v Sign *' val,v Mod,v Free] R ;;
  .ite (val <' M cell) (.store cell val) .skip

def body (p : ℕ) : Stmt := pass I (v Width) (v Dst) (v Padding) ;; .for I (v Len) (round p)

structure Args where
  (src M C dst fr V : ℕ)
  (sg : ℤ)

abbrev Args.regs (a : Args) (l : ℕ) : List ℤ := [l,a.src,a.M,a.sg,a.C,a.dst,a.fr,Limit a.V]
abbrev Args.loc (a : Args) (l : ℕ) (i r : ℤ) := frame (a.regs l ++ [i,r])

structure Ready (a : Args) (lim : Limits) (d : ℕ) (S : Finset ℤ) (μ : ℕ → ℤ) (l : ℕ) : Prop where
  set : SetAt μ a.src l S
  bound : Bdd a.V S
  positive : 1≤a.M
  width : a.M≤a.C
  sign : a.sg=1 ∨ a.sg= -1
  input : a.src+l ≤ a.dst
  output : a.dst+a.C ≤ a.fr
  ok : (emodNeed a.V a.M).Ok lim a.fr (d+1)

def StateOf (a : Args) (S : Finset ℤ) (μ ν : ℕ → ℤ) :=
  (∀ r<a.C, ν (a.dst+r)=rep S a.M a.V a.sg r) ∧ KeptBut μ ν a.fr a.dst a.C

variable {a : Args} {μ ν : ℕ → ℤ} {S : Finset ℤ} {lim : Limits} {P : Program} {p e d l : ℕ}

private theorem step {B : Finset ℤ} (h : StateOf a B μ ν) (z : ℤ) (k : ℕ) (hk : k=residue a.M a.sg z)
    (fit : k<a.C) : StateOf a (insert z B) μ
      (if z < ν (a.dst+k) then Function.update ν (a.dst+k) z else ν) := by
  subst k
  refine ⟨fun r hr => ?_,?_⟩
  · by_cases eqr : r=residue a.M a.sg z
    · subst r; split_ifs <;> simp_all [rep_insert,h.1 _ fit,min_def] <;> omega
    · rw [rep_insert,if_neg eqr]; split_ifs <;> simp_all [Function.update_of_ne (by omega : a.dst+r ≠ a.dst+residue a.M a.sg z),h.1 r hr]
  · split_ifs
    · intro b hb; rw [Function.update_of_ne (by rcases hb.2 with hb|hb <;> omega), h.2 _ hb]
    · exact h.2

/-- Initialize one entire table to padding, then lower just the bucket of each input. -/
theorem spec (text : P[p]?=some (body e)) (em : EmodSpec lim P e) (h : Ready a lim d S μ l) :
    Meets lim P p d (a.regs l) μ (tRep a.C l a.V) fun _ ν => StateOf a S μ ν := by
  obtain ⟨L,rfl,seg,_,rfl⟩ := h.set
  have inp := h.input; have out := h.output; have ok := h.ok; have hw := ok.space; have room := ok.cells; have word := ok.word; have hd := ok.depth
  simp only [emodNeed] at room word hd
  let I (i : ℕ) := StateOf a (L.take i).toFinset μ
  refine .of_body text (Ends.seq (13*a.C+6) (L.length*(tEmod a.V+45)+6) ?_ (by unfold tRep; omega))
  refine Ends.pass (fun _ => Limit a.V) (fun _ _ => ⟨trivial,by simp⟩) ?_ hw (by omega) rfl rfl
  let ν₀ := wrote μ a.dst (fun _ => Limit a.V) a.C
  have start : I 0 ν₀ := ⟨fun r hr => by simp [ν₀,wrote_done hr,rep_empty], fun r hr => wrote_rest hr.2⟩
  rw [update_frame_setLocal]
  refine Ends.forShape (fun j (r : ℤ) ν => ⟨a.loc L.length j r,ν⟩) I L.length (tEmod a.V+37) 0 start ?_ ?_
    (first:=by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT:=by simp; ring_nf; omega)
  · intro j r ν hj st
    have read := (st.2 (a.src+j) (show _ by exact ⟨by omega,Or.inl (by omega)⟩)).trans (seg j hj)
    have hz := h.bound _ (List.mem_toFinset.mpr (List.getElem_mem hj))
    have hsg : |a.sg*L[j]| ≤ a.V := by rcases h.sign with q|q <;> simpa [q] using hz
    have key := residue_cast h.positive a.sg L[j]; have small := (residue_lt h.positive a.sg L[j]).trans_le h.width
    generalize eqk : residue a.M a.sg L[j] = k at key small
    have eq : (L.take (j+1)).toFinset = insert L[j] (L.take j).toFinset := by rw [List.take_succ_eq_append_getElem hj]; ext; simp only [Finset.mem_insert, List.mem_toFinset, List.mem_append, List.mem_singleton]; tauto
    have zz := abs_le.mp hsg
    unfold round
    light_call (em (d+1) a.fr a.V a.M (a.sg*L[j]) ν h.positive hsg ok) using read, hz with _ η ⟨rfl,keep⟩
    rw [← key]
    have keepT : StateOf a (L.take j).toFinset μ η := ⟨fun q hq => (keep _ (by omega)).trans (st.1 _ hq), fun b hb => (keep b hb.1).trans (st.2 b hb)⟩
    have val := (keep (a.src+j) (by omega)).trans read
    have fin := step keepT L[j] k eqk.symm small
    by_cases hit : L[j]<η (a.dst+k) <;> simp only [hit,ite_true,ite_false] at fin
    · apply Ends.block (hT:=by simp; omega)
      refine Stmt.Runs.ite_pos ?_ (by simp [val,hit])
      refine ⟨by light_side, k,Function.update η (a.dst+k) L[j],?_,?_⟩
      · simp [val,update_frame_setLocal,Args.loc,Args.regs]
      · simpa [I,eq] using fin
    · exact Ends.block (Stmt.Runs.ite_neg ⟨trivial,k,η,rfl,by simpa [I,eq] using fin⟩ (by simp [val,hit])) (by simp; omega)
  · intro _ _ st; simpa [I] using st

end Light.Sec3.ChanHe.RepTable
