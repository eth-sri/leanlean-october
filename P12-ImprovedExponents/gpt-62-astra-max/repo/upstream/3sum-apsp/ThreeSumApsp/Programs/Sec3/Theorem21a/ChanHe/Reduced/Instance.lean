/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Representatives

/-! A three-table modular-sum instance. Split `i` as `a t+b`, and `j+b` as
`s t+c`. For fixed shift `s` this is one triangle `(a,b,c)` of side `t`:
the three lookups use `at+b`, `st+c-b` and `(a+s)t+c` respectively. Only
the last needs reduction modulo `M`, by at most one subtraction. -/
@[expose] public section
namespace Light.Sec3.HashTriangle
open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec

structure Job where
  (t M U base : ℕ)
  values : Fin 3 → ℕ → ℤ

abbrev Job.hit (x : Job) := modSum x.M (x.values 0) (x.values 1) (x.values 2)
abbrev Job.area (x : Job) := x.t*x.t
abbrev block (base area : ℕ) (h : Fin 3) := base+h.val*area

structure Pre (x : Job) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  positive : 1 ≤ x.M
  cap : x.M ≤ x.area
  magnitude : 1 ≤ x.U
  bound : ∀ h i, i < x.M → |x.values h i| ≤ x.U
  cells : ∀ h i, i < x.M → μ (block x.base x.area h+i) = x.values h i
  below : x.base+3*x.area ≤ fr

abbrev Job.args (x : Job) : List ℤ := [x.t,x.U,x.M,x.base]
noncomputable def task : Task where
  Inst := Job
  size := Job.t
  bound := Job.U
  args := Job.args
  Pre := Pre
  Post x μ fr r ν := r=flag x.hit ∧ Kept μ ν fr

abbrev Job.fill (x : Job) : ℕ := 2*x.U+1

def pick (x : Job) (h : Fin 3) (z : ℤ) : ℤ := if 0≤z ∧ z<x.M then x.values h z.toNat else x.fill

def index (h : Fin 3) (t s i j : ℤ) := if h=0 then i*t+j else if h=1 then s*t+j-i else (i+s)*t+j

def entry (x : Job) (s : ℕ) (h : Fin 3) (i j : ℕ) :=
  let z := index h x.t s i j
  pick x h (if h=2 ∧ x.M≤z then z-x.M else z)

abbrev flat (t : ℕ) (A : ℕ → ℕ → ℤ) := (List.range (t*t)).map fun p => A (p/t) (p%t)

def instanceAt (x : Job) (fr s : ℕ) : TriInst :=
  let w h := flat x.t (entry x s h)
  ⟨x.t,x.fill,block fr x.area 0,block fr x.area 1,block fr x.area 2,w 0,w 1,w 2⟩

def yesAt (x : Job) (s : ℕ) := ∃ a<x.t, ∃ b<x.t, ∃ c<x.t,
  entry x s 0 a b+entry x s 1 b c+entry x s 2 a c=0

private theorem get {t i j} (A : ℕ→ℕ→ℤ) (hi : i<t) (hj : j<t) :
    (flat t A).getD (i*t+j) 0 = A i j := by
  rw [flat,List.getD_map_range _ (Nat.mul_add_lt_mul hi hj),Nat.mul_add_div_of_lt hj,Nat.mul_add_mod_of_lt hj]

theorem yes_iff (x : Job) (fr s : ℕ) :
    (triOf x.t (instanceAt x fr s).AB (instanceAt x fr s).BC (instanceAt x fr s).AC).HasZeroTriangle ↔ yesAt x s := by
  let T := triOf x.t (instanceAt x fr s).AB (instanceAt x fr s).BC (instanceAt x fr s).AC
  have cell (a b c : Fin x.t) : T.IsZeroTriangle a b c ↔
      entry x s 0 a b+entry x s 1 b c+entry x s 2 a c=0 := by
    simp only [T,TriangleInstance.IsZeroTriangle,TriangleInstance.S,triOf,instanceAt,
      get _ a.isLt b.isLt,get _ b.isLt c.isLt,get _ a.isLt c.isLt]
  constructor
  · rintro ⟨a,b,c,e⟩; exact ⟨a,a.isLt,b,b.isLt,c,c.isLt,(cell ..).mp e⟩
  · rintro ⟨a,ha,b,hb,c,hc,e⟩; exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,(cell ..).mpr e⟩

variable {x : Job} {μ : ℕ → ℤ} {fr : ℕ}

private theorem picked (H : Pre x μ fr) (h : Fin 3) (z : ℤ) :
    pick x h z=x.fill ∨ (0≤z ∧ z<x.M ∧ pick x h z=x.values h z.toNat ∧ |pick x h z|≤x.U) := by
  by_cases v : 0≤z ∧ z<x.M
  · simpa [pick,v] using Or.inr (H.bound h z.toNat (by omega) : |x.values h z.toNat| ≤ x.U)
  · simp [pick,v]

theorem entry_fits (H : Pre x μ fr) (s : ℕ) (h : Fin 3) (i j : ℕ) : |entry x s h i j|≤x.fill := by
  let q := index h x.t s i j
  change |pick x h (if h=2 ∧ x.M≤q then q-x.M else q)|≤x.fill
  generalize (if h=2 ∧ x.M≤q then q-x.M else q) = z
  rcases picked H h z with e|⟨_,_,_,e⟩
  · rw [e,abs_of_nonneg (Nat.cast_nonneg _)]
  · change _ ≤ ((2*x.U+1:ℕ):ℤ); omega

private def wrap (M w : ℕ) : ℤ := if (M:ℤ)≤w then (w:ℤ)-M else w
private theorem wrapped {M w : ℕ} (h : w<2*M) : wrap M w=((w%M:ℕ):ℤ) := by
  unfold wrap; split_ifs with e
  · rw [Nat.mod_eq_sub_mod (show M≤w by omega),Nat.mod_eq_of_lt (by omega)]; omega
  · rw [Nat.mod_eq_of_lt (by omega)]

private theorem hitAt (s : ℕ) : yesAt x s ↔ ∃ a<x.t, ∃ b<x.t, ∃ c<x.t,
    pick x 0 (a*x.t+b:ℕ)+pick x 1 ((s*x.t+c:ℕ)-(b:ℤ))+pick x 2 (wrap x.M ((a+s)*x.t+c))=0 := by
  simp [yesAt,entry,index,wrap]

private theorem sound (H : Pre x μ fr) {s : ℕ} : yesAt x s → x.hit := by
  rw [hitAt]; rintro ⟨a,ha,b,hb,c,hc,eq⟩
  generalize ei : a*x.t+b=i at eq
  generalize ev : s*x.t+c=v at eq
  generalize ew : (a+s)*x.t+c=w at eq
  have ar : w+b=i+v := by rw [← ei,← ev,← ew]; ring
  rcases picked H 0 i with e|⟨_,hi,e,ae⟩ <;>
    rcases picked H 1 ((v:ℤ)-b) with f|⟨hv,hj,f,af⟩ <;>
    rcases picked H 2 (wrap x.M w) with g|⟨_,_,g,ag⟩
  all_goals try (simp only [Job.fill,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,abs_le] at *; omega)
  have ix : i+((v:ℤ)-b).toNat=w := by omega
  have key := wrapped (by omega : w<2*x.M)
  rw [key,Int.toNat_natCast] at g
  -- Retain the original argument of the lookup on the left.
  rw [e,f,key,g,Int.toNat_natCast] at eq
  exact ⟨i,by omega,((v:ℤ)-b).toNat,by omega,by rwa [ix]⟩

private theorem complete (H : Pre x μ fr) : x.hit → ∃ s<x.t+1, yesAt x s := by
  rintro ⟨i,hi,j,hj,eq⟩
  have room : x.M ≤ x.t*x.t := H.cap; have m := H.positive
  obtain ⟨a,ha,b,hb,rfl⟩ := Nat.exists_eq_mul_add_of_lt_mul (hi.trans_le room)
  have top : j+b<(x.t+1)*x.t := by rw [Nat.succ_mul]; omega
  obtain ⟨s,hs,c,hc,ev⟩ := Nat.exists_eq_mul_add_of_lt_mul top
  have ey : ((s*x.t+c:ℕ):ℤ)-b=j := by omega
  have ew : (a+s)*x.t+c=a*x.t+b+j := by rw [Nat.add_mul]; omega
  refine ⟨s,hs,(hitAt s).2 ⟨a,ha,b,hb,c,hc,?_⟩⟩
  have valid (h : Fin 3) (v : ℕ) (hv : v<x.M) : pick x h v=x.values h v := by
    unfold pick; rw [if_pos ⟨Nat.cast_nonneg _,by exact_mod_cast hv⟩,Int.toNat_natCast]
  rwa [ey,ew,wrapped (by omega),valid _ _ hi,valid _ _ hj,valid _ _ (Nat.mod_lt _ m)]

theorem hit_iff (H : Pre x μ fr) : x.hit ↔ ∃ s<x.t+1, yesAt x s :=
  ⟨complete H, fun ⟨_,_,h⟩ => sound H h⟩
end Light.Sec3.HashTriangle
