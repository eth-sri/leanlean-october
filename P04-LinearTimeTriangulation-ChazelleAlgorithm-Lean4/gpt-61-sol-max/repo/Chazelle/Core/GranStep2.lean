module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranStep

/-!
# WP-F, part 8: one step of the worklist — the removal

`St.remove c μ` removes the live chord `c` from the state: `c` dies, the class `Y = s1 c` is
merged into `X = s0 c` (the exit list of `X` becomes `newEx c`, the exits of both classes except
`c`, its weight `μ`, the chords of `Y` are relabelled to `X`), the counts at the two positions of
`c` drop by one, the positions whose count drops to `0` are unlinked from the ring, and the new
exits are pushed on the worklist.  `Inv.remove`: if `c` is removable (`Inv.removable_iff`) and
`μ = st.mu E c`, the invariant is preserved.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

namespace St

variable (E : Env) (st : St)

/-- The exit list of the merged class. -/
def newEx (c : ℕ) : List ℕ :=
  (st.exl (st.s0 c)).filter (· != c) ++ (st.exl (st.s1 c)).filter (· != c)

/-- Unlink position `d` from the ring `(nxt, prv)`. -/
def unl (r : (ℕ → ℕ) × (ℕ → ℕ)) (d : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  (Function.update r.1 (r.2 d) (r.1 d), Function.update r.2 (r.1 d) (r.2 d))

/-- The ring after unlinking the dying positions of `c`. -/
def ring2 (c : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let r1 := if st.cnt (st.nd0 c) = 1 then unl (st.nxt, st.prv) (st.nd0 c) else (st.nxt, st.prv)
  if st.cnt (st.nd1 c) = 1 then unl r1 (st.nd1 c) else r1

/-- **The removal of chord `c`**, the merged class getting the weight `μ`. -/
def remove (c μ : ℕ) : St where
  live := Function.update st.live c 0
  s0 := fun d => if d ∈ st.exl (st.s1 c) ∧ d ≠ c ∧ st.s0 d = st.s1 c then st.s0 c else st.s0 d
  s1 := fun d => if d ∈ st.exl (st.s1 c) ∧ d ≠ c ∧ st.s1 d = st.s1 c then st.s0 c else st.s1 d
  nd0 := st.nd0
  nd1 := st.nd1
  deg := Function.update st.deg (st.s0 c) (st.newEx c).length
  wt := Function.update st.wt (st.s0 c) μ
  ex := fun x t => if x = st.s0 c ∧ t < (st.newEx c).length then (st.newEx c).getD t 0
    else st.ex x t
  cnt := Function.update (Function.update st.cnt (st.nd0 c) (st.cnt (st.nd0 c) - 1)) (st.nd1 c)
    (st.cnt (st.nd1 c) - 1)
  nxt := (st.ring2 c).1
  prv := (st.ring2 c).2
  eg := st.eg
  pz := st.pz
  stk := fun t => if st.top - 1 ≤ t ∧ t < st.top - 1 + (st.newEx c).length then
    (st.newEx c).getD (t - (st.top - 1)) 0 else st.stk t
  top := st.top - 1 + (st.newEx c).length
  nlive := st.nlive - 1

end St

variable {E : Env} {st : St}

/-! ## Basic facts about the removal -/

section Removal

variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E)
include hE h hc

omit hE h hc in
theorem rm_L (_hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (μ : ℕ) : (st.remove c μ).L E = st.L E \ {c} := by
  ext i
  simp only [St.L, St.remove, mem_sdiff, mem_ofPred_eq, mem_singleton_iff]
  ram_grind

theorem rm_F (μ : ℕ) : (st.remove c μ).F E = st.F E \ {cs E.M E.Q E.N c} := by
  unfold St.F
  rw [rm_L hE h hc]
  exact fam_diff hE hc

omit hE h hc in
/-- The exit lists of the two classes of `c`. -/
theorem exl_X (_hE : E.Good) (h : Inv E st)
    (hc : c ∈ st.L E) : ∀ i, i ∈ st.exl (st.s0 c) ↔ i ∈ st.L E ∧
    TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s0 c)) :=
  (h.cls _ ⟨c, hc, Or.inl rfl⟩).2.2.2.1

omit hE h hc in
theorem exl_Y (_hE : E.Good) (h : Inv E st)
    (hc : c ∈ st.L E) : ∀ i, i ∈ st.exl (st.s1 c) ↔ i ∈ st.L E ∧
    TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s1 c)) :=
  (h.cls _ ⟨c, hc, Or.inr rfl⟩).2.2.2.1

end Removal

/-- The degree of a region counted by a duplicate-free list of record indices. -/
theorem deg_list (hE : E.Good) {L' : Set ℕ} (hL' : ∀ i ∈ L', i < E.K) {Z : Set Point}
    {l : List ℕ} (hnd : l.Nodup)
    (hl : ∀ i, i ∈ l ↔ i ∈ L' ∧ TouchesIn E.M.D (cs E.M E.Q E.N i) Z) :
    l.length = E.M.deg (fam E.M E.Q E.N L') Z := by
  unfold Model.deg
  have e : {d | d ∈ fam E.M E.Q E.N L' ∧ TouchesIn E.M.D d Z} =
      (fun i => cs E.M E.Q E.N i) '' {i | i ∈ l} := by
    ext d
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨⟨i, hiL, hi, rfl⟩, ht⟩
      ram_grind
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hiL, ht⟩ := (hl i).1 hi
      exact ⟨⟨i, hiL, hL' i hiL, rfl⟩, ht⟩
  have hinj : Set.InjOn (fun i => cs E.M E.Q E.N i) {i | i ∈ l} := by
    intro i hi i' hi' he
    exact cs_inj hE.hNF (hL' i ((hl i).1 hi).1) (hL' i' ((hl i').1 hi').1) he
  rw [e, hinj.ncard_image]
  rw [show {i | i ∈ l} = (l.toFinset : Set ℕ) by ext; simp]
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

/-- The exit list of a class is its list of exits. -/
theorem exl_of_list (st : St) (x : ℕ) {l : List ℕ} (hd : st.deg x = l.length)
    (he : ∀ t, t < l.length → st.ex x t = l.getD t 0) : st.exl x = l := by
  simp_all [St.exl, List.length_ofFn, List.getElem_ofFn, List.getD_eq_getElem?_getD] 

section Rm

variable (hE : E.Good) (h : Inv E st) {c : ℕ} (hc : c ∈ st.L E) {P : Set Point}
  (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P
    (st.cl E (st.s0 c)) (st.cl E (st.s1 c)))
include hE h hc hs

omit hE h hc hs in
theorem hsys_F (hE : E.Good) (_h : Inv E st) (_hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c})
    (cs E.M E.Q E.N c) P (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) : ChordSystem E.M.D (st.F E) :=
  hE.hM.sys _ (St.F_adm (st := st) hE) (St.F_finite (st := st) hE)

theorem rm_cl_in {x : ℕ} (hx : x < E.R)
    (hxc : st.cl E x = st.cl E (st.s0 c) ∨ st.cl E x = st.cl E (st.s1 c)) (μ : ℕ) :
    (st.remove c μ).cl E x = P := by
  show supR E.M ((st.remove c μ).F E) (E.reg x) = P
  rw [rm_F hE h hc]
  refine supR_eq (Chazelle.Chain.regionsIn_nonempty (hE.hRC.1 x hx)) hs.mem ?_
  refine (St.cl_spec (st := st) hE hx).2.trans ?_
  rcases hxc with e | e <;> rw [e]
  · exact hs.sub₁
  · exact hs.sub₂

omit hE h hc hs in
theorem cl_out (hE : E.Good) (_h : Inv E st) (hc : c ∈ st.L E)
    (hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c}) (cs E.M E.Q E.N c) P (st.cl E (st.s0 c))
    (st.cl E (st.s1 c))) {x : ℕ} (hx : x < E.R) (h1 : st.cl E x ≠ st.cl E (st.s0 c))
    (h2 : st.cl E x ≠ st.cl E (st.s1 c)) :
    st.cl E x ∈ E.M.regions (st.F E \ {cs E.M E.Q E.N c}) ∧ st.cl E x ≠ P := by
  rcases split_cases (St.cs_mem_F hc) hs (St.cl_spec (st := st) hE hx).1 with e | e | e
  all_goals simp_all

theorem rm_cl_out {x : ℕ} (hx : x < E.R) (h1 : st.cl E x ≠ st.cl E (st.s0 c))
    (h2 : st.cl E x ≠ st.cl E (st.s1 c)) (μ : ℕ) : (st.remove c μ).cl E x = st.cl E x := by
  show supR E.M ((st.remove c μ).F E) (E.reg x) = st.cl E x
  rw [rm_F hE h hc]
  exact supR_eq (Chazelle.Chain.regionsIn_nonempty (hE.hRC.1 x hx))
    (cl_out hE h hc hs hx h1 h2).1 (St.cl_spec (st := st) hE hx).2

section
variable {i : ℕ} (hi : i ∈ st.L E) (hic : i ≠ c)
include hi hic
/-- A chord other than `c` touches the merged region iff it touches one of the two classes. -/
theorem touch_P :
    TouchesIn E.M.D (cs E.M E.Q E.N i) P ↔ TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s0 c)) ∨
      TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s1 c)) := by
  have e := hs.exits_eq_union (hsys_F hE h hc hs) sdiff_subset (St.cs_mem_F hc)
    not_mem_sdiff_self (W := st.F E \ {cs E.M E.Q E.N c}) subset_rfl
  have hiS : cs E.M E.Q E.N i ∈ st.F E \ {cs E.M E.Q E.N c} := by
    rw [← fam_diff hE hc]; exact ⟨i, ⟨hi, by simp_all⟩, hi.1, rfl⟩
  constructor
  · intro ht
    have : cs E.M E.Q E.N i ∈ Merge.exitsIn E.M.D (st.F E \ {cs E.M E.Q E.N c}) P := ⟨hiS, ht⟩
    rw [e] at this
    rcases this with ⟨-, h'⟩ | ⟨-, h'⟩
    all_goals simp_all
  · intro ht
    have : cs E.M E.Q E.N i ∈ Merge.exitsIn E.M.D (st.F E \ {cs E.M E.Q E.N c}) P := by
      rw [e]
      rcases ht with h' | h'
      · exact Or.inl ⟨hiS, h'⟩
      · exact Or.inr ⟨hiS, h'⟩
    exact this.2

/-- No chord other than `c` touches both classes. -/
theorem not_both
    (h1 : TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s0 c)))
    (h2 : TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E (st.s1 c))) : False := by
  have hd := hs.exits_disjoint (hsys_F hE h hc hs) sdiff_subset (St.cs_mem_F hc)
    (W := st.F E \ {cs E.M E.Q E.N c}) subset_rfl
  have hiS : cs E.M E.Q E.N i ∈ st.F E \ {cs E.M E.Q E.N c} := by
    rw [← fam_diff hE hc]; exact ⟨i, ⟨hi, by simp_all⟩, hi.1, rfl⟩
  exact Set.disjoint_left.1 hd ⟨hiS, h1⟩ ⟨hiS, h2⟩


end

theorem mem_newEx (i : ℕ) :
    i ∈ st.newEx c ↔ i ∈ st.L E ∧ i ≠ c ∧ TouchesIn E.M.D (cs E.M E.Q E.N i) P := by
  unfold St.newEx
  grind [Chazelle.Core.Gran.exl_X, Chazelle.Core.Gran.exl_Y, Chazelle.Core.Gran.touch_P]

theorem newEx_nodup : (st.newEx c).Nodup := by
  unfold St.newEx
  rw [List.nodup_append]
  refine ⟨((h.cls _ ⟨c, hc, Or.inl rfl⟩).2.2.1).filter _,
    ((h.cls _ ⟨c, hc, Or.inr rfl⟩).2.2.1).filter _, fun a ha b hb hab => ?_⟩
  grind [Chazelle.Core.Gran.exl_X, Chazelle.Core.Gran.exl_Y, Chazelle.Core.Gran.not_both]

omit hE h hc hs in
theorem newEx_length (hE : E.Good) (h : Inv E st) (hc : c ∈ st.L E)
    (_hs : Merge.IsSplit E.M.D (st.F E \ {cs E.M E.Q E.N c})
    (cs E.M E.Q E.N c) P (st.cl E (st.s0 c)) (st.cl E (st.s1 c))) :
    (st.newEx c).length + 2 = st.deg (st.s0 c) + st.deg (st.s1 c) := by
  obtain ⟨-, -, -, htouch⟩ := h.sides c hc
  obtain ⟨hX, hY⟩ := h.cl_mem hE hc
  have hcX : c ∈ st.exl (st.s0 c) := (exl_X hE h hc c).2 ⟨hc, (htouch _ hX).2 (Or.inl rfl)⟩
  have hcY : c ∈ st.exl (st.s1 c) := (exl_Y hE h hc c).2 ⟨hc, (htouch _ hY).2 (Or.inr rfl)⟩
  have nX := (h.cls _ ⟨c, hc, Or.inl rfl⟩).2.2.1
  have nY := (h.cls _ ⟨c, hc, Or.inr rfl⟩).2.2.1
  unfold St.newEx
  rw [List.length_append, ← nX.erase_eq_filter, ← nY.erase_eq_filter,
    List.length_erase_of_mem hcX, List.length_erase_of_mem hcY]
  grind [St.exl, List.length_ofFn]

theorem deg_P :
    E.M.deg (st.F E \ {cs E.M E.Q E.N c}) P = (st.newEx c).length := by
  rw [← fam_diff hE hc]
  refine (deg_list hE (fun i hi => hi.1.1) (newEx_nodup hE h hc hs) fun i => ?_).symm
  rw [mem_newEx hE h hc hs]
  grind

section
variable {Z : Set Point} (hZ : Z ∈ E.M.regions (st.F E \ {cs E.M E.Q E.N c})) (hZP : Z ≠ P)
include hZ hZP
theorem other_ne : Z ∈ E.M.regions (st.F E) ∧ Z ≠ st.cl E (st.s0 c) ∧ Z ≠ st.cl E (st.s1 c) := by
  refine ⟨split_old (St.cs_mem_F hc) hs hZ hZP, fun e => hZP ?_, fun e => hZP ?_⟩
  · have hX := (h.cl_mem hE hc).1
    exact Chazelle.Chain.regionsIn_eq_of_subset hZ hs.mem
      (Chazelle.Chain.regionsIn_nonempty hX) (by rw [e]) hs.sub₁
  · have hY := (h.cl_mem hE hc).2
    exact Chazelle.Chain.regionsIn_eq_of_subset hZ hs.mem
      (Chazelle.Chain.regionsIn_nonempty hY) (by rw [e]) hs.sub₂

theorem deg_other :
    E.M.deg (st.F E \ {cs E.M E.Q E.N c}) Z = E.M.deg (st.F E) Z := by
  have e := hs.exits_other (hsys_F hE h hc hs) sdiff_subset hZ hZP
  rw [Merge.insert_sdiff_self (St.cs_mem_F hc)] at e
  show (Merge.exitsIn E.M.D _ Z).ncard = (Merge.exitsIn E.M.D _ Z).ncard
  rw [e]

theorem weight_other' :
    E.M.weight (st.F E \ {cs E.M E.Q E.N c}) Z = E.M.weight (st.F E) Z := by
  obtain ⟨hZS, h1, h2⟩ := other_ne hE h hc hs hZ hZP
  exact weight_other hE.hM (St.F_adm (st := st) hE) (St.F_finite (st := st) hE) (St.cs_mem_F hc)
    hs hZS h1 h2


end

end Rm

end

end Gran

end Chazelle.Core
