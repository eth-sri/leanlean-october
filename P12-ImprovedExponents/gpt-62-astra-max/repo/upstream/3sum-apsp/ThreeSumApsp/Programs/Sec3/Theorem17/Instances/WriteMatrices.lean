/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Slots

public import ThreeSumApsp.Lang.Lib.NextPair
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Instances

/-! The matrices of a piece are filled in a single traversal. For middle vertex
`j` the two counters of `nextPair` hold `j / p` and `j % p`, and an inner loop
tabulates the entries at that vertex. Only the address strides and the residue
test differ between X and Y. -/

@[expose] public section
namespace Light.Sec3
open ThreeSumApsp ThreeSumApsp.Spec
variable {lim : Limits} {P : Program} {d : ℕ}

/-- The residues R of the n² weights, all below p, stand at res.  The matrix has m = D n cells at
base, apart from the residues.  The piece {c0, …, c0 + len - 1} lies within the n vertices, and its
len p labels within the D middle vertices. -/
structure WritePre (lim : Limits) (μ : ℕ → ℤ) (base m res n D p c0 len : ℕ) (R : List ℕ) :
    Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  seg : SegN μ res R
  length : R.length = n * n
  lt : ∀ r ∈ R, r < p
  n_pos : 0 < n
  p_pos : 0 < p
  piece : c0 + len ≤ n
  spaceM : base + m < lim.space
  spaceR : res + n * n < lim.space
  spaceP : 2 * p < lim.space
  apart : Apart base m res (n * n)

namespace WritePre

variable {μ μ' : ℕ → ℤ} {base m res n D p c0 len : ℕ} {R : List ℕ}

section
variable (pre : WritePre lim μ base m res n D p c0 len R)
include pre

/-- The number n of vertices fits in a word. -/
theorem n_le_word : (n : ℤ) ≤ lim.word := by
  have := pre.hw
  have := pre.spaceR
  nlinarith

/-- The place of the weight between the vertex u and the c-th member c0 + c of the piece. -/
theorem index_lt {u c : ℕ} (hu : u < n)
    (hc : c < len) : u * n + c0 + c < n * n := by
  have := pre.piece
  nlinarith

/-- The residues can be read at any time. -/
theorem read (h : SameOutside μ μ' base m) {i : ℕ}
    (hi : i < n * n) : μ' (res + i) = (R.getD i 0 : ℕ) := by
  have hap := pre.apart
  have hil := pre.length ▸ hi
  rw [h _ (by omega), pre.seg _ (by simpa using hil), List.getElem_map,
    List.getD_eq_getElem _ 0 hil]

/-- The residues are below p. -/
theorem getD_lt {i : ℕ} (hi : i < n * n) :
    R.getD i 0 < p := by
  have hil := pre.length ▸ hi
  rw [List.getD_eq_getElem _ 0 hil]
  exact pre.lt _ (List.getElem_mem hil)

end
end WritePre

namespace MatrixWrite
slots 0 Dst Res N Dim Prime C₀ Len Rho J C S U
structure Args where
  (dst res n D p c₀ len rho : ℕ)

abbrev Args.regs (a : Args) (j c s u : ℤ) : List ℤ :=
  [a.dst,a.res,a.n,a.D,a.p,a.c₀,a.len,a.rho,j,c,s,u]
def Args.offset (a : Args) (x : Bool) (j u : ℕ) := if x then u*a.D+j else j*a.n+u
def Args.val (a : Args) (x : Bool) (R : List ℕ) (j u : ℕ) : ℤ :=
  let r := R.getD (u*a.n+a.c₀+j/a.p) 0
  if j/a.p<a.len ∧ j%a.p = (if x then (r+a.rho)%a.p else (a.p-r)%a.p) then 1 else 0

def cell (x : Bool) : Stmt :=
  let addr := v Dst +' (if x then v U *' v Dim +' v J else v J *' v N +' v U)
  let r := M (v Res +' (v U *' v N +' v C₀ +' v C))
  let hit := Stmt.store addr (k 1)
  let miss := Stmt.store addr (k 0)
  let (l,h) := if x then (r +' v Rho, v S) else (r +' v S, k 0)
  .ite (v C <' v Len) (.ite (l =' h) hit (.ite (l =' h +' v Prime) hit miss)) miss

def body (x : Bool) : Stmt := .for J (v Dim) (.for U (v N) (cell x) ;; nextPair C S Prime)

def cost (n D : ℕ) := 100*(n+1)*(D+1)

variable {a : Args} {R : List ℕ} {x : Bool} {μ ν : ℕ → ℤ}
abbrev Pre (lim : Limits) (μ : ℕ → ℤ) (a : Args) (R : List ℕ) :=
  WritePre lim μ a.dst (a.D*a.n) a.res a.n a.D a.p a.c₀ a.len R

structure Built (a : Args) (x : Bool) (R : List ℕ) (μ ν : ℕ → ℤ) (k : ℕ) : Prop where
  rest : SameOutside μ ν a.dst (a.D*a.n)
  atIdx : ∀ j < a.D, ∀ u < a.n, j*a.n+u<k → ν (a.dst + a.offset x j u) = a.val x R j u

private theorem bound {j u} (hj : j<a.D) (hu : u<a.n) : a.offset x j u < a.D*a.n := by
  cases x <;> simp [Args.offset,Nat.mul_comm a.D a.n] <;> first | exact Nat.mul_add_lt_mul hu hj | simpa [Nat.mul_comm] using Nat.mul_add_lt_mul hj hu

private theorem Built.step {j u} (h : Built a x R μ ν (j*a.n+u)) (hj : j<a.D) (hu : u<a.n) :
    Built a x R μ (Function.update ν (a.dst+a.offset x j u) (a.val x R j u)) (j*a.n+u+1) := by
  have := bound (x:=x) hj hu
  refine ⟨h.rest.update ⟨by omega,by omega⟩ _, fun j' hj' u' hu' hk => ?_⟩
  by_cases e : a.offset x j' u' = a.offset x j u
  · have ee : j'=j ∧ u'=u := by
      cases x
      · exact Nat.mul_add_inj_of_lt hu' hu e
      · exact (Nat.mul_add_inj_of_lt hj' hj e).symm
    obtain ⟨rfl,rfl⟩ := ee; simp
  · rw [Function.update_of_ne (by omega)]; apply h.atIdx _ hj' _ hu'
    by_contra! ge
    have := Nat.mul_add_inj_of_lt hu' hu (by omega : j'*a.n+u'=j*a.n+u)
    grind

private theorem modTest {r s ρ p : ℕ} (hr : r<p) (hs : s<p) (hρ : ρ<p) :
    (s = (r+ρ)%p ↔ r+ρ=s ∨ r+ρ=s+p) ∧ (s = (p-r)%p ↔ r+s=0 ∨ r+s=p) := by
  constructor
  · by_cases h : r+ρ<p
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · by_cases e : r=0
    · simp [e]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem one (pre : Pre lim μ a R) (hρ : a.rho<a.p) {j u : ℕ} (hj : j<a.D) (hu : u<a.n)
    (same : SameOutside μ ν a.dst (a.D*a.n)) :
    Ends lim P d (cell x) ⟨frame (a.regs j (j/a.p:ℕ) (j%a.p:ℕ) u),ν⟩ (cell x).blockCost fun τ =>
      τ = ⟨frame (a.regs j (j/a.p:ℕ) (j%a.p:ℕ) u), Function.update ν (a.dst+a.offset x j u) (a.val x R j u)⟩ := by
  have hw := pre.hw; have room := pre.spaceM; have sp := pre.spaceP; have sr := pre.spaceR
  have fit := bound (x:=x) hj hu
  have s := Nat.mod_lt j pre.p_pos
  let i := u*a.n+a.c₀+j/a.p
  have adr : ((a.res:ℤ)+(u*a.n+a.c₀+ ↑(j/a.p:ℕ))).toNat=a.res+i := by exact_mod_cast rfl
  have uv : 0 ≤ (u:ℤ)*a.n := by positivity
  have ud : 0 ≤ (u:ℤ)*a.D := by positivity
  have jn : 0 ≤ (j:ℤ)*a.n := by positivity
  have outA (b c e : ℕ) : ((a.dst:ℤ)+(b*c+e)).toNat=a.dst+(b*c+e) := by exact_mod_cast rfl
  apply Ends.block (hT:=le_rfl)
  dsimp only [Args.val, i] at adr ⊢
  generalize j/a.p = c at adr ⊢
  generalize j%a.p = t at s ⊢
  by_cases hc : c<a.len
  · have hi := pre.index_lt hu hc
    have read := pre.read same hi
    have hr := pre.getD_lt hi
    generalize R.getD (u*a.n+a.c₀+c) 0 = r at read hr ⊢
    obtain ⟨hx,hy⟩ := modTest hr s hρ
    cases x <;> simp only [Args.offset,Bool.false_eq_true, ↓reduceIte] at fit <;>
      zify at fit hi sr room sp <;> push_cast at * <;>
      simp [cell,Args.offset,Stmt.Runs,adr,outA,read,hc,Limits.Addr,abs_le,hx,hy] <;>
      split_ifs <;> (repeat' first | constructor | intro) <;> try omega
  · cases x <;> simp only [Args.offset,Bool.false_eq_true, ↓reduceIte] at fit <;>
      zify at fit room <;>
      simp [cell,Args.offset,Stmt.Runs,outA,hc,Limits.Addr,abs_le] <;> omega

/-- One sweep over the middle vertices; the inner loop writes the whole column (or row). -/
theorem sweep (pre : Pre lim μ a R) (hρ : a.rho<a.p) :
    Ends lim P d (body x) ⟨frame (a.regs 0 0 0 0),μ⟩ (cost a.n a.D) fun τ =>
      Built a x R μ τ.mem (a.D*a.n) := by
  have hw := pre.hw; have sm := pre.spaceM; have sp := pre.spaceP
  have hd := Nat.le_mul_of_pos_right a.D pre.n_pos; have hn := pre.n_le_word
  have cb : (cell x).blockCost≤75 := by cases x <;> decide
  let I (j : ℕ) (τ : State) := ∃ (u : ℤ) (ν : ℕ → ℤ), τ = ⟨frame (a.regs j (j/a.p:ℕ) (j%a.p:ℕ) u),ν⟩ ∧ Built a x R μ ν (j*a.n)
  refine Ends.for I a.D (a.n*83+20) ?_ ?_ ?_ ?_ (by omega) (by simp [cost]; nlinarith)
  · refine ⟨0, μ, by simp [update_frame_setLocal], .refl, ?_⟩; simp
  · rintro j _ hj - ⟨u,ν,rfl,b⟩
    refine Ends.seq (a.n*83+6) 14 (Ends.forFrame (fun u ν => Built a x R μ ν (j*a.n+u)) a.n b ?_ ?_
      (hT:=by simp; nlinarith [Nat.mul_le_mul_left a.n cb])) (by omega)
    · intro k ν hk h
      apply (one pre hρ hj hk h.rest).mono le_rfl
      rintro _ rfl; exact ⟨rfl,h.step hj hk⟩
    · intro ν hb
      apply Ends.nextPair (t:=j) (n:=a.p) ?_ pre.p_pos (by omega) (by omega) rfl rfl rfl
      exact ⟨rfl, a.n, ν, by simp [update_frame_setLocal], by rwa [Nat.succ_mul]⟩
  · rintro _ - ⟨_,_,rfl,h⟩; exact h
  · rintro j _ _ - ⟨_,_,rfl,_⟩; simp
end MatrixWrite

open MatrixWrite
abbrev writeXBody := body true
abbrev writeYBody := body false

variable {μ : ℕ → ℤ} {b res n D p c0 len rho : ℕ} {R : List ℕ}

theorem writeX_spec (pre : WritePre lim μ b (n*D) res n D p c0 len R) (hρ : rho<p) :
    Ends lim P d writeXBody ⟨frame [b,res,n,D,p,c0,len,rho],μ⟩ (cost n D) fun τ =>
      Seg τ.mem b (xList n D p c0 len rho R) ∧ SameOutside μ τ.mem b (n*D) := by
  rw [Nat.mul_comm n D] at pre ⊢
  let a : Args := ⟨b,res,n,D,p,c0,len,rho⟩
  have eqf : frame [↑b,↑res,↑n,↑D,↑p,↑c0,↑len,↑rho] = frame (a.regs 0 0 0 0) := (frame_append_zeros _ 4).symm
  rw [eqf]; apply (sweep (x:=true) (a:=a) pre hρ).mono le_rfl
  intro τ h; refine ⟨fun i hi => ?_,h.rest⟩
  have hi' : i<n*D := by simpa [xList] using hi
  obtain ⟨u,hu,j,hj,rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul hi'
  simpa [xList,Args.offset,Args.val,a,Nat.mul_add_div_of_lt hj,Nat.mul_add_mod_of_lt hj] using
    h.atIdx j hj u hu (Nat.mul_add_lt_mul hj hu)

theorem writeY_spec (pre : WritePre lim μ b (D*n) res n D p c0 len R) :
    Ends lim P d writeYBody ⟨frame [b,res,n,D,p,c0,len],μ⟩ (cost n D) fun τ =>
      Seg τ.mem b (yList n D p c0 len R) ∧ SameOutside μ τ.mem b (D*n) := by
  let a : Args := ⟨b,res,n,D,p,c0,len,0⟩
  have eqf : frame [↑b,↑res,↑n,↑D,↑p,↑c0,↑len] = frame (a.regs 0 0 0 0) := (frame_append_zeros _ 5).symm
  rw [eqf]; apply (sweep (x:=false) (a:=a) pre pre.p_pos).mono le_rfl
  intro τ h; refine ⟨fun i hi => ?_,h.rest⟩
  have hi' : i<D*n := by simpa [yList] using hi
  obtain ⟨j,hj,u,hu,rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul hi'
  simpa [yList,Args.offset,Args.val,a,Nat.mul_add_div_of_lt hu,Nat.mul_add_mod_of_lt hu] using
    h.atIdx j hj u hu (Nat.mul_add_lt_mul hj hu)

end Light.Sec3
