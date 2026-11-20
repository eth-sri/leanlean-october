module

public import ImprovedExponents.AllEdges.Scale.Refinement
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Passes
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section
namespace ImprovedExponents.AllEdges.Scale
open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

structure Procs where
  (ae aff tr down bump : ℕ)

namespace Reg
slots 0 N U A B Out Q Sz U9 Power Levels Round Ret QY R RY Neg Flags Free Sz2
end Reg
open Reg

/-- Q and R each span two matrices: the high bits and the scaled remainders
of the shifted left matrix and the shifted, transposed right matrix. -/
def init : Stmt :=
  .set Sz (v N *' v N) ;; .set U9 (k 9 *' v U) ;;
  .set QY (v Q +' v Sz) ;; .set R (v QY +' v Sz) ;; .set RY (v R +' v Sz) ;;
  .set Neg (v RY +' v Sz) ;; .set Flags (v Neg +' v Sz) ;; .set Free (v Flags +' v Sz) ;;
  .set Sz2 (k 2 *' v Sz) ;; .set Power (k 1) ;; .set Levels (k 0)

def powers : Stmt := .while (v Power ≤' k 3 *' v U) (
  .set Power (k 2 *' v Power) ;; .set Levels (v Levels +' k 1))

def prep (p : Procs) : Stmt :=
  .call p.aff [v Sz,v A,k 1,v U,v R] Ret ;;
  .call p.tr [v N,v B,v U,v RY] Ret ;;
  .call p.aff [v Sz2,v R,k 0,k 0,v Q] Ret ;;
  .call p.aff [v Sz,v A,k 0,k 0,v Out] Ret

/-- Ask if the current lower bound is attained. Bump the missed cells. -/
def query (p : Procs) : Stmt :=
  .call p.aff [v Sz,v Out,k 0 -' k 1,k 0,v Neg] Ret ;;
  .call p.ae [v N,v U9,v Neg,v QY,v Q,v Flags,v Free] Ret ;;
  .call p.bump [v Sz,k 1,v Flags,v Out] Ret

def move (p : Procs) : Stmt := .call p.down [v Sz2,v Q,v R,v Power] Ret ;;
  .call p.aff [v Sz,v Out,k 2,k 0,v Out] Ret

def round (p : Procs) : Stmt := move p ;; query p ;; query p

def body (p : Procs) : Stmt := init ;; powers ;; prep p ;; .for Round (v Levels) (round p) ;;
  .call p.aff [v Sz,v Out,k 1,k 0 -' k 2 *' v U,v Out] Ret

def need (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  let s := r n (9*U)
  ⟨24*U + 20 + s.word, 6*(n*n) + s.cells, s.depth + 1⟩

abbrev qTime (T : ℕ → ℕ → ℕ) (x : MatInst) := T x.n (9*x.U) + 70*(area x+1)
abbrev rTime (T : ℕ → ℕ → ℕ) (x : MatInst) := 2*qTime T x + 120*(area x+1)

def time (T : ℕ → ℕ → ℕ) (n U : ℕ) := (aeLevels U + 4) * (2*T n (9*U) + 500*(n*n+1))

abbrev locs (x : MatInst) (fr : ℕ) (pw lv i r : ℤ) : List ℤ :=
  [x.n,x.U,x.a,x.b,x.c,fr,area x,(9*x.U : ℕ),pw,lv,i,r,(fr+area x : ℕ),
    (fr+2*area x : ℕ),(fr+3*area x : ℕ),(fr+4*area x : ℕ),(fr+5*area x : ℕ),
    (fr+6*area x : ℕ),(2*area x : ℕ)]

structure Ctx (P S : Program) (p : Procs) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves aeTask P p.ae T r
  aff : (P++S)[p.aff]? = some affineBody
  tr : (P++S)[p.tr]? = some transposeBody
  down : (P++S)[p.down]? = some prefDownBody
  bump : (P++S)[p.bump]? = some bumpBody
  pre : x.Pre μ fr
  ok : (need r x.n x.U).Ok lim fr d

variable {P S p T r lim d x μ fr} (C : Ctx P S p T r lim d x μ fr)
include C

theorem Ctx.places : (lim.space : ℤ) ≤ lim.word ∧
    24*(x.U:ℤ)+20+(r x.n (9*x.U)).word ≤ lim.word ∧
    fr+(6*area x+(r x.n (9*x.U)).cells) ≤ lim.space ∧ d+((r x.n (9*x.U)).depth+1) ≤ lim.depth ∧
    1 ≤ x.U ∧ 1 ≤ area x ∧ x.n ≤ area x ∧ x.A.length = area x ∧ x.B.length = area x ∧
    x.a+area x ≤ fr ∧ x.b+area x ≤ fr ∧ x.c+area x ≤ fr ∧
    (data x).length = 2*area x ∧ 3*x.U < 2^aeLevels x.U ∧ 2^aeLevels x.U ≤ 6*x.U :=
  ⟨C.ok.space,by exact_mod_cast C.ok.word,C.ok.cells,C.ok.depth,C.pre.U_pos,
   Nat.mul_pos C.pre.n_pos C.pre.n_pos,Nat.le_mul_self _,C.pre.lenA,C.pre.lenB,
   C.pre.belowA,C.pre.belowB,C.pre.belowC,by simp [data,left,right,area,C.pre.lenA,two_mul],
   lt_two_pow_aeLevels _,two_pow_aeLevels_le C.pre.U_pos⟩

theorem init_spec : Ends lim (P++S) d init ⟨frame [x.n,x.U,x.a,x.b,x.c,fr],μ⟩ init.blockCost
    (· = ⟨frame (locs x fr 1 0 0 0),μ⟩) := by
  have := C.places; have hs : (0 : ℤ) ≤ (x.n : ℤ) * x.n := by positivity
  have sqm : ((area x : ℕ):ℤ) = (x.n:ℤ)*x.n := Nat.cast_mul ..
  unfold init
  light_set (area x : ℕ) using area
  light_set (9*x.U : ℕ)
  light_set (fr+area x : ℕ)
  light_set (fr+2*area x : ℕ)
  light_set (fr+3*area x : ℕ)
  light_set (fr+4*area x : ℕ)
  light_set (fr+5*area x : ℕ)
  light_set (fr+6*area x : ℕ)
  light_set (2*area x : ℕ)
  light_set 1
  light_set 0
  rfl

theorem powers_spec : Ends lim (P++S) d powers ⟨frame (locs x fr 1 0 0 0),μ⟩ (20*aeLevels x.U+10)
    (· = ⟨frame (locs x fr (2^aeLevels x.U : ℕ) (aeLevels x.U) 0 0),μ⟩) := by
  have hplaces := C.places
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (locs x fr (2^i : ℕ) i 0 0), μ⟩)
    (aeLevels x.U) rfl ?_ ?_ (by simp; omega)
  · rintro i _ hi rfl
    have hpow : 2^(i+1) ≤ 2^aeLevels x.U := Nat.pow_le_pow_right (by decide) hi
    have hlt : i+1 < 2^(i+1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize h : 2^i = w at hpow hlt ⊢
    exact ⟨by light_side,by simp; omega,by light_side,
      by simp [pow_succ',h,update_frame_setLocal,locs]⟩
  · rintro _ rfl; generalize 2^aeLevels x.U = w at hplaces ⊢
    exact ⟨by light_side,by simp; omega,rfl⟩

/-- The data and the bounds threading the loop; only the result buffer can have changed below fr. -/
structure Mem (x : MatInst) (μ : ℕ → ℤ) (fr ℓ e : ℕ) (ν : ℕ → ℤ) : Prop where
  prefixes : Seg ν fr ((data x).map (prefQ ℓ))
  rest : Seg ν (fr+2*area x) ((data x).map (prefR (aeLevels x.U) ℓ))
  lower : ∃ L, Lower x ℓ L e ∧ Seg ν x.c L
  kept : KeptBut μ ν fr x.c (area x)

abbrev loc (x : MatInst) (fr : ℕ) (i v : ℤ) :=
  frame (locs x fr (2^aeLevels x.U : ℕ) (aeLevels x.U) i v)

def Stage (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) (i : ℤ) (ℓ e : ℕ) (σ : State) :=
  ∃ v ν, σ = ⟨loc x fr i v,ν⟩ ∧ Mem x μ fr ℓ e ν

end ImprovedExponents.AllEdges.Scale
