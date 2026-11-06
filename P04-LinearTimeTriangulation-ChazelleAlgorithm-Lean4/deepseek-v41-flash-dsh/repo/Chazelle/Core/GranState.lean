module

public import Chazelle.Golf

public import Chazelle.Core.GranRing

/-!
# WP-F, part 6: the abstract state of the granularity procedure and its invariant

The procedure (`GranularizeSpec`) removes chords of a valid normal form `N` by a worklist.  Its
state `St` holds, for chord records `i < K`: a live bit, the class ids `s0 i`, `s1 i` of the two
regions it separates and the ring positions `nd0 i`, `nd1 i` of its two attachment keys; for class
ids `x` (initially the region indices `< R`): the degree, the weight and the exit chords `ex x t`,
`t < deg x`; for ring positions `j < A` (the positions of the sequence table): the number `cnt j`
of live chords attached at the start key `pk j`, the ring pointers, the start edge `eg j` and the
bit `pz j` (parameter `0`); the worklist `stk` with `top` entries; the number of live chords.

`Inv E st` states that the state describes the current submap `st.F E` (the live chords):
degree and semigranularity bounds, class data of every referenced class, the ring of cut
positions, and the worklist property (live chords off the list are not removable).

* `Inv.cut_iff`: the cuts of the current submap are the start keys of the live positions;
* `gw_eq`: the integer weight `gw` of two positions is the weight of the key interval;
* `Inv.final`: with an empty worklist the current submap is γ-granular with degrees `≤ D`.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

/-! ## The environment -/

/-- The fixed data of a run. -/
structure Env where
  /-- The model. -/
  M : Model
  /-- The height polygon. -/
  Q : Polygon
  /-- The input normal form. -/
  N : NF
  /-- Its region correspondence. -/
  reg : ℕ → Set Point
  /-- The target granularity. -/
  γ : ℕ
  /-- The degree cap. -/
  D : ℕ
  /-- The model kind (`true`: chain model). -/
  ch : Bool
  /-- The number of chain edges (chain model). -/
  m : ℕ

namespace Env

variable (E : Env)

/-- Number of chords. -/
abbrev K : ℕ := E.N.nChords
/-- Number of arcs (ring positions). -/
abbrev A : ℕ := E.N.arcs.length
/-- Number of regions. -/
abbrev R : ℕ := E.N.nRegions
/-- Number of walk edges. -/
abbrev n : ℕ := E.M.W.n

/-- The hypotheses on the environment. -/
structure Good : Prop where
  hM : WalkAx E.M
  hGM : GoodModel E.M
  hNF : IsNF E.M E.Q E.N
  hRC : RegionCorr E.M E.Q E.N E.reg
  hCS : ChordSidesOK E.M E.Q E.N E.reg
  hRO : RegionsOK E.M E.Q E.N E.reg
  hne : (E.N.F E.M E.Q).Nonempty
  hcd : CountDesc E.M E.ch E.m
  hn : E.ch = true → E.n = 2 * E.m + 7

end Env

/-! ## The state -/

/-- The state of the granularity procedure. -/
structure St where
  live : ℕ → ℕ
  s0 : ℕ → ℕ
  s1 : ℕ → ℕ
  nd0 : ℕ → ℕ
  nd1 : ℕ → ℕ
  deg : ℕ → ℕ
  wt : ℕ → ℕ
  ex : ℕ → ℕ → ℕ
  cnt : ℕ → ℕ
  nxt : ℕ → ℕ
  prv : ℕ → ℕ
  eg : ℕ → ℕ
  pz : ℕ → ℕ
  stk : ℕ → ℕ
  top : ℕ
  nlive : ℕ

/-- The region of `G` containing `U` (if any). -/
noncomputable def supR (M : Model) (G : Set (Set Point)) (U : Set Point) : Set Point := by
  classical
  exact if h : ∃ Z ∈ M.regions G, U ⊆ Z then h.choose else ∅

theorem supR_spec {M : Model} {G : Set (Set Point)} {U : Set Point}
    (h : ∃ Z ∈ M.regions G, U ⊆ Z) : supR M G U ∈ M.regions G ∧ U ⊆ supR M G U := by
  unfold supR
  Ξ dite_eq_left h
  exact h.choose_spec

theorem supR_eq {M : Model} {G : Set (Set Point)} {U Z : Set Point} (hU : U.Nonempty)
    (hZ : Z ∈ M.regions G) (hUZ : U ⊆ Z) : supR M G U = Z := by
  obtain ⟨h1, h2⟩ := supR_spec ⟨Z, hZ, hUZ⟩
  exact Chazelle.Chain.regionsIn_eq_of_subset h1 hZ hU h2 hUZ

namespace St

variable (E : Env) (st : St)

/-- The live chord indices. -/
def L : Set ℕ := {i | i < E.K ∧ st.live i = 1}

/-- **The current submap.** -/
def F : Set (Set Point) := fam E.M E.Q E.N (st.L E)

/-- The region of the current submap containing the region `x` of the input (class `x`). -/
noncomputable def cl (x : ℕ) : Set Point := supR E.M (st.F E) (E.reg x)

/-- The exit chords of class `x`. -/
def exl (x : ℕ) : List ℕ := List.ofFn fun t : Fin (st.deg x) => st.ex x t

/-- Class `x` is referenced by a live chord. -/
def Ref (x : ℕ) : Prop := ∃ i ∈ st.L E, x = st.s0 i ∨ x = st.s1 i

/-- Live ring positions. -/
def Lv (j : ℕ) : Prop := 0 < st.cnt j

/-- The number of live chords attached at position `j`. -/
def cntOf (j : ℕ) : ℕ :=
  ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card +
    ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card

end St

/-- The start key of position `j`. -/
noncomputable def Env.key (E : Env) (j : ℕ) : ℝ := pk E.M E.Q E.N j

/-- The parameter of the start of position `j`. -/
noncomputable def Env.par (E : Env) (j : ℕ) : ℝ := E.M.param E.Q (E.N.arc (E.N.seq.getD j 0)).s

/-- The number of counted edges before the edge `e` (for `e` below the last walk edge). -/
def bB (ch : Bool) (e : ℕ) : ℕ := if ch then e - 6 else e

/-- **The integer weight of the key interval between two positions** from the values
`bb j = bB (edge of j)`, the bumps `xb j` (`1` iff the edge of `j` is counted and the
parameter of `j` is positive) and the number `sz` of counted edges. -/
def gwt (sz : ℕ) (bb xb : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if a = b then sz
  else if a < b then bb b + xb b - bb a
  else (sz - bb a) + min (bb b + xb b) (bb a)

/-- The start edge of position `j`. -/
def Env.edge (E : Env) (j : ℕ) : ℕ := (E.N.arc (E.N.seq.getD j 0)).s.edge

/-- The number of counted edges. -/
def Env.sz (E : Env) : ℕ := cntIn E.ch E.m 0 E.n

/-- The static data of the state are correct. -/
structure StatOK (E : Env) (st : St) : Prop where
  nd0 : ∀ i, i < E.K → st.nd0 i < E.A ∧ E.key (st.nd0 i) = E.M.key E.Q (E.N.chord i).lpos
  nd1 : ∀ i, i < E.K → st.nd1 i < E.A ∧ E.key (st.nd1 i) = E.M.key E.Q (E.N.chord i).rpos
  eg : ∀ j, j < E.A → st.eg j = bB E.ch (E.edge j)
  pz : ∀ j, j < E.A → st.pz j ≤ 1 ∧ (st.pz j = 1 ↔ (E.M.counted (E.edge j) ∧ E.par j ≠ 0))

/-- The static data only depend on the static arrays. -/
theorem StatOK.congr {E : Env} {st st' : St} (h : StatOK E st) (h0 : st'.nd0 = st.nd0)
    (h1 : st'.nd1 = st.nd1) (h2 : st'.eg = st.eg) (h3 : st'.pz = st.pz) : StatOK E st' := by
  obtain ⟨a, b, c, d⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [h0, h1, h2, h3] <;> assumption

/-- **The invariant.** -/
structure Inv (E : Env) (st : St) : Prop where
  stat : StatOK E st
  live01 : ∀ i, i < E.K → st.live i ≤ 1
  nlive : st.nlive = (st.L E).ncard
  degLe : E.M.DegLe (st.F E) E.D
  semi : E.M.Semigranular (st.F E) E.γ
  sides : ∀ i ∈ st.L E, st.s0 i < E.R ∧ st.s1 i < E.R ∧ st.cl E (st.s0 i) ≠ st.cl E (st.s1 i) ∧
    ∀ X ∈ E.M.regions (st.F E), (TouchesIn E.M.D (cs E.M E.Q E.N i) X ↔
      X = st.cl E (st.s0 i) ∨ X = st.cl E (st.s1 i))
  cls : ∀ x, st.Ref E x → st.deg x = E.M.deg (st.F E) (st.cl E x) ∧
    st.wt x = E.M.weight (st.F E) (st.cl E x) ∧ (st.exl x).Nodup ∧
    (∀ i, i ∈ st.exl x ↔ i ∈ st.L E ∧ TouchesIn E.M.D (cs E.M E.Q E.N i) (st.cl E x)) ∧
    st.deg x ≤ E.D
  refInj : ∀ x y, st.Ref E x → st.Ref E y → st.cl E x = st.cl E y → x = y
  cnt : ∀ j, j < E.A → st.cnt j = st.cntOf E j
  ring : RingOK st.Lv E.A st.nxt st.prv
  stk : ∀ t, t < st.top → st.stk t < E.K
  topLe : st.top + E.D * st.nlive ≤ E.K + E.D * E.K
  work : ∀ i ∈ st.L E, (∀ t, t < st.top → st.stk t ≠ i) →
    ¬ Merge.Removable E.M.D E.M.weight E.γ (st.F E) (cs E.M E.Q E.N i)

namespace St

variable {E : Env} {st : St}

theorem F_sub : st.F E ⊆ E.N.F E.M E.Q := fam_sub _

theorem F_adm (hE : E.Good) : st.F E ⊆ E.M.Adm := fam_adm hE.hNF _

theorem F_finite (hE : E.Good) : (st.F E).Finite := fam_finite hE.hNF _

theorem cs_mem_F {i : ℕ} (hi : i ∈ st.L E) : cs E.M E.Q E.N i ∈ st.F E := ⟨i, hi, hi.1, rfl⟩

end St

namespace Inv

variable {E : Env} {st : St}

/-- The class of `x` is a region of the current submap containing the input region `x`. -/
theorem _root_.Chazelle.Core.Gran.St.cl_spec (hE : E.Good) {x : ℕ} (hx : x < E.R) :
    st.cl E x ∈ E.M.regions (st.F E) ∧ E.reg x ⊆ st.cl E x := by
  refine supR_spec ?_
  exact Chazelle.Chain.exists_regionsIn_superset St.F_sub (hE.hRC.1 x hx)

/-- Live positions are those with a live chord attached. -/
theorem lv_iff (h : Inv E st) {j : ℕ} (hj : j < E.A) :
    st.Lv j ↔ ∃ i ∈ st.L E, st.nd0 i = j ∨ st.nd1 i = j := by
  unfold St.Lv
  Ξ h.cnt j hj
  unfold St.cntOf
  constructor
  · intro hpos
    by_cases h0 : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card
    · obtain ⟨i, hi⟩ := Finset.card_pos.1 h0
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨i, ⟨hi.1, hi.2.1⟩, Or.inl hi.2.2⟩
    · have h1 : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card := by
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.1 h1
      simp only [Finset.mem_filter, Finset.mem_range] at hi
      exact ⟨i, ⟨hi.1, hi.2.1⟩, Or.inr hi.2.2⟩
  · rintro ⟨i, ⟨hiK, hil⟩, h0 | h1⟩
    · have : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd0 i = j).card :=
        Finset.card_pos.2 ⟨i, ⊚ hiK, hil, h0⟩
      omega
    · have : 0 < ((Finset.range E.K).filter fun i => st.live i = 1 ∧ st.nd1 i = j).card :=
        Finset.card_pos.2 ⟨i, ⊚ hiK, hil, h1⟩
      omega

/-- **The cuts of the current submap are the start keys of the live positions.** -/
theorem cut_iff (hE : E.Good) (h : Inv E st) (k : ℝ) :
    E.M.IsCut (st.F E) k ↔ ∃ j, j < E.A ∧ st.Lv j ∧ E.key j = k := by
  unfold St.F
  Ξ isCut_fam_iff hE.hNF hE.hM
  constructor
  · rintro ⟨i, hiL, hi, hk | hk⟩
    · obtain ⟨h1, h2⟩ := h.stat.nd0 i hi
      exact ⟨st.nd0 i, h1, (h.lv_iff h1).2 ⟨i, hiL, Or.inl rfl⟩, Ρ h2, hk⟩
    · obtain ⟨h1, h2⟩ := h.stat.nd1 i hi
      exact ⟨st.nd1 i, h1, (h.lv_iff h1).2 ⟨i, hiL, Or.inr rfl⟩, Ρ h2, hk⟩
  · rintro ⟨j, hj, hL, rfl⟩
    obtain ⟨i, hiL, h0 | h1⟩ := (h.lv_iff hj).1 hL
    · refine ⟨i, hiL, hiL.1, Or.inl ?_⟩
      rw [← h0]; exact (h.stat.nd0 i hiL.1).2
    · refine ⟨i, hiL, hiL.1, Or.inr ?_⟩
      rw [← h1]; exact (h.stat.nd1 i hiL.1).2

end Inv

variable {E : Env} {st : St}

/-- The start keys are strictly increasing. -/
theorem key_strict (hE : E.Good) {i i' : ℕ} (hii : i < i') (hi' : i' < E.A) :
    E.key i < E.key i' := pk_strict hE.hNF hE.hne hii hi'

/-- Cyclic betweenness of positions is cyclic betweenness of their keys. -/
theorem key_cyc_iff (hE : E.Good) {a b i : ℕ} (ha : a < E.A) (hb : b < E.A) (hi : i < E.A) :
    sideInArc (E.key a) (E.key b) (E.key i) ↔ cyc a b i :=
  sideInArc_mono_iff (fun _ _ h h' => key_strict hE h h') ha hb hi

theorem key_inj (hE : E.Good) {a b : ℕ} (ha : a < E.A) (hb : b < E.A)
    (h : E.key a = E.key b) : a = b := pk_inj hE.hNF hE.hne ha hb h

/-- The start of position `j` is a proper position. -/
theorem par_mem (hE : E.Good) {j : ℕ} (hj : j < E.A) : 0 ≤ E.par j ∧ E.par j < 1 :=
  let h := (hE.hNF.2.2.2.choose_spec.2.2.2.2.2.2 _ (NFLoc.seq_lt hE.hNF hj)).1
  ⟨h.1, h.2.1⟩

/-- The start edge of a position is a walk edge. -/
theorem edge_lt (hE : E.Good) {j : ℕ} (hj : j < E.A) : E.edge j < E.n := by
  have hc := pk_cut hE.hNF hE.hne hj
  have hb := WalkAx.cut_bounds hc
  have hpar := par_mem hE hj
  have e : pk E.M E.Q E.N j = (E.edge j : ℝ) + E.par j := rfl
  rw [e] at hb
  have : (E.edge j : ℝ) < E.n := by linarith [hb.2]
  exact_mod_cast this

/-- The key of a position: its edge plus its parameter. -/
theorem key_edge (j : ℕ) : E.key j = (E.edge j : ℝ) + E.par j := rfl

/-- Increasing keys have nondecreasing edges. -/
theorem edge_mono (hE : E.Good) {a b : ℕ} (ha : a < E.A) (hb : b < E.A)
    (hlt : E.key a < E.key b) : E.edge a ≤ E.edge b := by
  have ha0 := (par_mem hE ha).1
  have hb1 := (par_mem hE hb).2
  rw [key_edge, key_edge] at hlt
  by_contra h'
  have : (E.edge b : ℝ) + 1 ≤ E.edge a := by exact_mod_cast (show E.edge b + 1 ≤ E.edge a by omega)
  linarith

/-- **The integer weight of two positions is the weight of the key interval.** -/
theorem gw_eq (hE : E.Good) (h : StatOK E st) {a b : ℕ} (ha : a < E.A) (hb : b < E.A) :
    gwt E.sz st.eg st.pz a b = E.M.arcWt (E.key a) (E.key b) := by
  have ea := edge_lt hE ha
  have eb := edge_lt hE hb
  obtain ⟨pa0, pa1⟩ := par_mem hE ha
  obtain ⟨pb0, pb1⟩ := par_mem hE hb
  Ξ key_edge, key_edge, arcWt_formula hE.hcd ea eb pa0 pa1 pb0 pb1, ← key_edge, ← key_edge
  have hcnt : E.M.counted (E.edge b) ↔ (E.ch = false ∨ (6 ≤ E.edge b ∧ E.edge b < 2 * E.m + 6)) :=
    hE.hcd.2 _ eb
  obtain ⟨hpz1, hpz⟩ := h.pz b hb
  have hn := hE.hn
  -- the bump and the stored bit
  have hbx : (E.M.counted (E.edge b) → bump (E.par b) = st.pz b) ∧
      (¬ E.M.counted (E.edge b) → st.pz b = 0) := by
    refine ⟨fun hc => ?_, fun hc => ?_⟩
    · unfold bump
      by_cases hz : E.par b = 0
      · Ξ ite_eq_right (by rw [hz]; exact lt_irrefl 0)
        by_contra h'
        have : st.pz b = 1 := ⋄
        exact (hpz.1 this).2 hz
      · Ξ ite_eq_left (lt_of_le_of_ne pb0 (Ne.symm hz))
        exact (hpz.2 ⟨hc, hz⟩).symm
    · by_contra h'
      exact hc (hpz.1 (⋄)).1
  have hb01 : bump (E.par b) ≤ 1 := by unfold bump; split_ifs <;> omega
  have hnE : E.n = E.M.W.n := rfl
  unfold gwt Env.sz
  Ξ h.eg a ha, h.eg b hb
  by_cases hab : a = b
  · subst hab; simp
  have hk : E.key a ≠ E.key b := fun e => hab (key_inj hE ha hb e)
  Ξ ite_eq_right hab, ite_eq_right hk
  by_cases hlt : a < b
  · have hkl := key_strict hE hlt hb
    have hle := edge_mono hE ha hb hkl
    Ξ ite_eq_left hlt, ite_eq_left hkl
    cases hch : E.ch with
    | false =>
      have hc : E.M.counted (E.edge b) := hcnt.2 (Or.inl hch)
      have := hbx.1 hc
      unfold cntIn bB; simp only [Bool.false_eq_true, ite_false]
      omega
    | true =>
      have hn' := hn hch
      rw [hch] at hcnt
      simp only [Bool.true_eq_false, false_or] at hcnt
      unfold cntIn bB
      ϴ ite_true
      by_cases hc : E.M.counted (E.edge b)
      · have := hcnt.1 hc
        have := hbx.1 hc
        ϴ min_def, max_def
        split_ifs <;> omega
      · have h1 := mt hcnt.2 hc
        have := hbx.2 hc
        ϴ min_def, max_def
        split_ifs <;> omega
  · have hlt' : b < a := ⋄
    have hkl := key_strict hE hlt' ha
    have hle := edge_mono hE hb ha hkl
    Ξ ite_eq_right hlt, ite_eq_right (not_lt.2 hkl.le)
    cases hch : E.ch with
    | false =>
      have hc : E.M.counted (E.edge b) := hcnt.2 (Or.inl hch)
      have := hbx.1 hc
      unfold cntIn bB; simp only [Bool.false_eq_true, ite_false]
      omega
    | true =>
      have hn' := hn hch
      rw [hch] at hcnt
      simp only [Bool.true_eq_false, false_or] at hcnt
      unfold cntIn bB
      ϴ ite_true
      by_cases hc : E.M.counted (E.edge b)
      · have := hcnt.1 hc
        have := hbx.1 hc
        ϴ min_def, max_def
        split_ifs <;> omega
      · have h1 := mt hcnt.2 hc
        have := hbx.2 hc
        ϴ min_def, max_def
        split_ifs <;> omega

/-- `size` by integer arithmetic. -/
theorem size_eq (hE : E.Good) : E.M.size = cntIn E.ch E.m 0 E.n := by
  Ξ ← ncard_counted hE.hcd le_rfl
  unfold Model.size
  congr 1
  ext p
  ϴ mem_ofPred_eq
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, Nat.zero_le _, h1⟩
  · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩

/-! ## The end of the run -/

/-- **With an empty worklist the current submap is γ-granular with degrees `≤ D`.** -/
theorem Inv.final (_hE : E.Good) (h : Inv E st) (htop : st.top = 0) :
    E.M.Granular (st.F E) E.γ ∧ E.M.DegLe (st.F E) E.D := by
  refine ⟨⟨h.semi, ?_⟩, h.degLe⟩
  have : Merge.ContractionCondIn E.M.D E.M.weight (st.F E) E.γ := by
    Ξ Merge.contractionCondIn_iff
    intro c hc
    have hcS := hc.1
    obtain ⟨i, hiL, -, rfl⟩ := hcS
    exact h.work i hiL (fun t ht => absurd ht (⋄)) hc
  exact this

end

end Gran

end Chazelle.Core
