module
public import ImprovedExponents.AllEdges.Scale.Program

@[expose] public section
namespace ImprovedExponents.AllEdges.Scale
open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

variable {P S p T r lim d x μ fr} (C : Ctx P S p T r lim d x μ fr)
include C
open Reg

/-- The same affine pass is used to initialize, negate, double and unshift a buffer. -/
theorem Ctx.map {ν src l} (h : Seg ν src l) (hb : AbsLe l (4*x.U)) (m c : ℤ) (dst : ℕ)
    (hm : |m| ≤ 2 := by norm_num) (hc : |c| ≤ 2*x.U := by simp [abs_le] <;> omega)
    (hs : src+l.length ≤ lim.space := by omega) (hd : dst+l.length ≤ lim.space := by omega)
    (ha : src+l.length ≤ dst ∨ dst ≤ src := by omega) :
    Meets lim (P++S) p.aff (d+1) [l.length,src,m,c,dst] ν (20*l.length+6)
      fun _ ν' => Seg ν' dst (affL m c l) ∧ SameOutside ν ν' dst l.length := by
  have := C.places
  apply affine_forward C.aff h C.ok.space hs hd ha
  intro z hz
  have H := mul_le_mul hm (hb z hz) (abs_nonneg _) (by decide : (0:ℤ) ≤ 2)
  rw [← abs_mul] at H
  have := abs_add_le (m*z) c; omega

theorem Ctx.prep_spec : Ends lim (P++S) d (prep p) ⟨loc x fr 0 0,μ⟩ (170*(area x+1))
    (Stage x μ fr 0 (aeLevels x.U) 0) := by
  have pre := C.pre; have places := C.places; have ha := pre.apartA
  have hA : AbsLe x.A (4*x.U) := fun z hz => (pre.leA z hz).trans (by omega)
  have hD : AbsLe (data x) (4*x.U) := fun z hz => abs_le.mpr (by have := data_range pre z hz; omega)
  have lZ : (data x).length = 2*area x := by omega
  have sq : (area x : ℤ) = (x.n:ℤ)*x.n := Nat.cast_mul ..
  have := pre.lenA; have := pre.lenB
  unfold prep
  light_call (C.map pre.segA hA 1 x.U (fr+2*area x)) using pre.lenA with v₁ ν₁ ⟨s₁,o₁⟩
  light_call (transpose_meets C.tr (c := x.U) (dst := fr+3*area x) pre.segB.keep pre.lenB
    (by omega) (by grind) fun z hz => by have := abs_le.mp (pre.leB z hz); rw [abs_le]; omega)
    using pre.lenA, area, pow_two with v₂ ν₂ ⟨s₂,o₂⟩
  have sZ : Seg ν₂ (fr+2*area x) (data x) := by
    rw [data,seg_append,show (left x).length = area x by simp [left,pre.lenA,area],
      show fr + 2*area x + area x = fr+3*area x by omega]
    exact ⟨s₁.keep (by light_keep [pre.lenA]),s₂⟩
  light_call (C.map sZ hD 0 0 fr) using lZ,pre.lenA with v₃ ν₃ ⟨s₃,o₃⟩
  light_call (C.map pre.segA.keep hA 0 0 x.c) using lZ,pre.lenA with v₄ ν₄ ⟨s₄,o₄⟩
  have small (z) (hz : z ∈ data x) : 0 ≤ z ∧ z < 2^aeLevels x.U := by
    have H := data_range pre z hz
    have : 3*(x.U:ℤ) < 2^aeLevels x.U := by exact_mod_cast by omega
    omega
  have Qeq : (data x).map (prefQ (aeLevels x.U)) = affL 0 0 (data x) :=
    List.map_congr_left fun z hz => by simp [prefQ_start (small z hz).1 (small z hz).2]
  refine ⟨v₄,ν₄,rfl,?_⟩
  refine ⟨Qeq ▸ s₃.keep (by light_keep [lZ]), by rw [map_prefR_start small]; exact sZ.keep (by light_keep [lZ]),
    ⟨_,start pre,s₄⟩,fun c hc => ?_⟩
  light_keep

/-- The oracle instance: negate the current lower bound and compare it to the two prefix arrays. -/
def instanceAt (x : MatInst) (fr ℓ : ℕ) (L : List ℤ) : AeInst :=
  ⟨x.n,9*x.U,fr+4*area x,fr+area x,fr,fr+5*area x, affL (-1) 0 L,
    (right x).map (prefQ ℓ), (left x).map (prefQ ℓ)⟩

theorem Ctx.oracle_pre {ν ℓ e L} (a : Lower x ℓ L e) (q : Seg ν fr ((data x).map (prefQ ℓ)))
    (s : Seg ν (fr+4*area x) (affL (-1) 0 L)) : (instanceAt x fr ℓ L).Pre ν (fr+6*area x) := by
  have pre := C.pre; have := C.places
  simp only [data,List.map_append,seg_append,List.length_map,left,length_affL,pre.lenA] at q
  have bounds : ∀ z ∈ (data x).map (prefQ ℓ), |z| ≤ ((9*x.U:ℕ):ℤ) := by
    intro z hz; have H := absLe_map_prefQ (data_range pre) ℓ z hz; rw [abs_le]; push_cast; omega
  simp only [data,List.map_append,List.mem_append] at bounds
  refine
    { n_pos := pre.n_pos
      segAB := s
      segAC := q.1
      segBC := q.2
      leAB := ?_
      leAC := by tauto
      leBC := fun z hz => bounds z (.inr hz)
      U_pos := ?_, lenAB := ?_, lenAC := ?_, lenBC := ?_, belowAB := ?_, belowAC := ?_,
      belowBC := ?_, belowOut := ?_, apartAB := ?_, apartBC := ?_, apartAC := ?_ } <;>
    try (simp [instanceAt, a.len, area, left, right, pre.lenA, Apart] <;> omega)
  intro z hz; obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have := a.bounded pre v hv; simp [instanceAt]; omega

theorem Ctx.query_spec {i ℓ e σ} (st : Stage x μ fr i ℓ (e+1) σ) :
    Ends lim (P++S) d (query p) σ (qTime T x) (Stage x μ fr i ℓ e) := by
  obtain ⟨v,ν,rfl,q,s,⟨L,a,ls⟩,keep⟩ := st
  have places := C.places; have len := a.len; have hL := a.bounded C.pre
  have lZ : (data x).length = 2*area x := by omega
  have lQ : ((data x).map (prefQ ℓ)).length = 2 * area x := by simpa using lZ
  have lR : ((data x).map (prefR (aeLevels x.U) ℓ)).length = 2 * area x := by simpa using lZ
  unfold query
  light_call (C.map ls hL (-1) 0 (fr+4*area x)) using len with v₁ ν₁ ⟨ns,o₁⟩
  have pre := C.oracle_pre a (q.keep (by light_keep [lZ])) ns
  have ok : (r x.n (9*x.U)).Ok lim (fr+6*area x) (d+1) :=
    by constructor <;> omega
  light_call (C.solver.meets S _ _ pre ok) using instanceAt,aeTask,len with v₂ ν₂ ⟨fs,o₂⟩
  change Seg ν₂ (fr+5*area x) (answers x ℓ L) at fs
  change KeptBut ν₁ ν₂ (fr+6*area x) (fr+5*area x) (area x) at o₂
  light_call (bump_meets C.bump 1 fs (ls.keep (by light_keep)) ⟨answers_length,len⟩
    (by omega) (by grind) answers_bits hL (by simp; omega))
    using len,area,pow_two,instanceAt,aeTask with v₃ ν₃ ⟨bs,o₃⟩
  exact ⟨v₃,ν₃,rfl,q.keep (by light_keep [lZ]),s.keep (by light_keep [lZ]),
    ⟨_,probe C.pre a,bs⟩,by light_keep⟩

theorem Ctx.move_spec {i ℓ σ} (hℓ : ℓ+1 ≤ aeLevels x.U) (st : Stage x μ fr i (ℓ+1) 0 σ) :
    Ends lim (P++S) d (move p) σ (110*(area x+1)) (Stage x μ fr i ℓ 2) := by
  obtain ⟨v,ν,rfl,q,s,⟨L,a,ls⟩,keep⟩ := st
  have places := C.places; have len := a.len
  have lZ : (data x).length = 2*area x := by omega
  have hp : (2:ℤ)^aeLevels x.U ≤ 6*x.U := by exact_mod_cast by omega
  have pre : PrefPre lim ν fr (fr+2*area x) (2^aeLevels x.U)
      ((data x).map (prefQ (ℓ+1))) ((data x).map (prefR (aeLevels x.U) (ℓ+1))) := by
    refine ⟨q,s,by simp,C.ok.space,by simp only [List.length_map,lZ]; omega,by simp only [List.length_map,lZ]; omega,by simp only [List.length_map,lZ]; omega,by omega,?_,?_⟩
    · rintro z hz; have := absLe_map_prefQ (data_range C.pre) (ℓ+1) z hz
      simp only [abs_le] at *; omega
    · rintro _ hz; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hz
      have := prefR_nonneg (aeLevels x.U) (ℓ+1) z; have := prefR_lt hℓ z
      simp only [abs_le]; omega
  have sq : (area x : ℤ) = (x.n:ℤ)*x.n := Nat.cast_mul ..
  have lA := C.pre.lenA
  have lQ : ((data x).map (prefQ ℓ)).length = 2 * area x := by simpa using lZ
  have lR : ((data x).map (prefR (aeLevels x.U) ℓ)).length = 2 * area x := by simpa using lZ
  unfold move
  light_call (prefDown_meets C.down pre) using List.length_map,lZ,lA,area,pow_two with v₁ ν₁ ⟨q',s',o₁⟩
  rw [zipWith_shiftQ hℓ] at q'; rw [map_shiftR hℓ] at s'
  have below : Kept ν ν₁ fr := fun j hj => o₁ _ (Or.inl hj) (Or.inl (by omega))
  light_call (C.map (ls.keep (by light_keep)) (a.bounded C.pre) 2 0 x.c) using len,lZ,lA,area,pow_two
    with v₂ ν₂ ⟨ds,o₂⟩
  exact ⟨v₂,ν₂,rfl,q'.keep (by light_keep [lZ]),s'.keep (by light_keep [lZ]),
    ⟨_,double a,ds⟩, by light_keep⟩

theorem Ctx.round_spec {i ℓ σ} (hℓ : ℓ+1 ≤ aeLevels x.U) (st : Stage x μ fr i (ℓ+1) 0 σ) :
    Ends lim (P++S) d (round p) σ (rTime T x) (Stage x μ fr i ℓ 0) := by
  unfold round
  refine Ends.next _ ((C.move_spec hℓ st).mono le_rfl fun _ st₁ => ?_) (by simp only [rTime,qTime]; omega)
  refine Ends.next _ ((C.query_spec st₁).mono le_rfl fun _ st₂ => ?_) (by simp only [rTime,qTime]; omega)
  exact (C.query_spec st₂).mono (by simp only [rTime,qTime]; omega) fun _ => id

theorem Ctx.rounds_spec {ν res} (hm : Mem x μ fr (aeLevels x.U) 0 ν) :
    Ends lim (P++S) d (.for Round (v Levels) (round p)) ⟨loc x fr 0 res,ν⟩
      (aeLevels x.U * (rTime T x + 8) + 6) (Stage x μ fr (aeLevels x.U) 0 0) := by
  have := C.places; have := Nat.lt_two_pow_self (n := aeLevels x.U)
  refine Ends.for (fun t => Stage x μ fr t (aeLevels x.U-t) 0) (aeLevels x.U) (rTime T x)
    ⟨res,ν,by rw [update_frame_setLocal]; rfl, by simpa using hm⟩ ?_ (fun _ _ h => by simpa using h)
    (by rintro _ _ _ _ ⟨_,_,rfl,_⟩; exact ⟨trivial,rfl⟩) (by omega) (by simp; ring_nf; omega)
  intro t σ ht _ st
  obtain ⟨ℓ,hℓ⟩ : ∃ ℓ, aeLevels x.U - t = ℓ+1 := by simp_all
  rw [hℓ] at st
  rw [show aeLevels x.U-(t+1) = ℓ by omega]
  refine (C.round_spec (by omega) st).mono le_rfl ?_
  rintro _ ⟨v',ν',rfl,hm'⟩
  exact ⟨rfl,v',ν',by rw [update_frame_setLocal]; rfl,hm'⟩

end ImprovedExponents.AllEdges.Scale
