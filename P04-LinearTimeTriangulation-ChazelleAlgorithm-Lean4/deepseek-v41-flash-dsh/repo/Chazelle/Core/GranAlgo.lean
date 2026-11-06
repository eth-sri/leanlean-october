module

public import Chazelle.Golf

public import Chazelle.Core.GranStep4

/-!
# WP-F, part 11: the abstract worklist algorithm

* `St.step`: one iteration (pop a dead chord; pop a live chord that fails the degree test or the
  weight test; otherwise remove it);
* `Inv.step`: the invariant is preserved; `measure_step`: the measure `top + (D + 1) · nlive`
  drops;
* `initSt`, `Inv.init`: the initial state built from the input normal form satisfies the
  invariant (the input submap is γ-semigranular with degrees `≤ D`).
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

namespace St

variable (E : Env) (st : St)

/-- **One iteration of the worklist.** -/
def step : St :=
  if st.live st.cur = 1 then
    if 3 ≤ st.deg (st.s0 st.cur) ∧ 3 ≤ st.deg (st.s1 st.cur) then st.pop
    else if E.γ < st.mu E st.cur then st.pop
    else st.remove st.cur (st.mu E st.cur)
  else st.pop

/-- The measure of the worklist loop. -/
def meas : ℕ := st.top + (E.D + 1) * st.nlive

end St

variable {E : Env} {st : St}

/-- **One iteration preserves the invariant.** -/
theorem Inv.step (hE : E.Good) (h : Inv E st) (htop : 0 < st.top) : Inv E (st.step E) := by
  unfold St.step
  split_ifs with hl hdeg hmu
  · -- both classes have degree `≥ 3`: not removable
    refine h.pop_keep htop fun hr => ?_
    have hc : st.cur ∈ st.L E := ⟨h.stk _ (⋄), hl⟩
    obtain ⟨P, hs⟩ := h.split hE hc
    obtain ⟨hlow, -⟩ := (h.removable_iff hE hc hs).1 hr
    omega
  · -- the merged weight exceeds `γ`: not removable
    refine h.pop_keep htop fun hr => ?_
    have hc : st.cur ∈ st.L E := ⟨h.stk _ (⋄), hl⟩
    obtain ⟨P, hs⟩ := h.split hE hc
    obtain ⟨-, hw⟩ := (h.removable_iff hE hc hs).1 hr
    rw [← h.mu_eq hE hc hs] at hw
    omega
  · -- removable
    have hc : st.cur ∈ st.L E := ⟨h.stk _ (⋄), hl⟩
    obtain ⟨P, hs⟩ := h.split hE hc
    refine h.remove hE htop hc ((h.removable_iff hE hc hs).2 ⟨?_, ?_⟩)
    · push Not at hdeg
      by_cases h3 : 3 ≤ st.deg (st.s0 st.cur)
      · exact Or.inr (hdeg h3)
      · exact Or.inl (⋄)
    · rw [← h.mu_eq hE hc hs]; omega
  · exact h.pop_dead htop hl

/-- **The measure drops by at least one per iteration.** -/
theorem measure_step (hE : E.Good) (h : Inv E st) (htop : 0 < st.top) :
    (st.step E).meas E < st.meas E := by
  unfold St.step St.meas
  split_ifs with hl hdeg hmu
  · unfold St.pop; simp only; omega
  · unfold St.pop; simp only; omega
  · have hc : st.cur ∈ st.L E := ⟨h.stk _ (⋄), hl⟩
    obtain ⟨P, hs⟩ := h.split hE hc
    have hlow : st.deg (st.s0 st.cur) < 3 ∨ st.deg (st.s1 st.cur) < 3 := by
      push Not at hdeg
      by_cases h3 : 3 ≤ st.deg (st.s0 st.cur)
      · exact Or.inr (hdeg h3)
      · exact Or.inl (⋄)
    have hlen := newEx_le hE h hc hs hlow
    have hfinL : (st.L E).Finite := (Set.finite_lt_nat E.K).subset fun i hi => hi.1
    have hnl : 1 ≤ st.nlive := by
      rw [h.nlive]; exact (Set.ncard_pos hfinL).2 ⟨_, hc⟩
    show st.top - 1 + (st.newEx st.cur).length + (E.D + 1) * (st.nlive - 1) <
      st.top + (E.D + 1) * st.nlive
    have e : (E.D + 1) * st.nlive = (E.D + 1) * (st.nlive - 1) + (E.D + 1) := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  · unfold St.pop; simp only; omega

/-! ## The initial state -/

/-- The number of chords among the first `K` whose position map sends them to `j`. -/
def cntInit (K : ℕ) (nd0 nd1 : ℕ → ℕ) (j : ℕ) : ℕ :=
  ((Finset.range K).filter fun i => nd0 i = j).card +
    ((Finset.range K).filter fun i => nd1 i = j).card

/-- **The initial state** of the worklist (static arrays given). -/
def initSt (E : Env) (nd0 nd1 eg pz : ℕ → ℕ) : St where
  live := fun _ => 1
  s0 := fun i => (E.N.chord i).up
  s1 := fun i => (E.N.chord i).dn
  nd0 := nd0
  nd1 := nd1
  deg := fun r => (E.N.region r).chords.length
  wt := fun r => (E.N.region r).wt
  ex := fun r t => (E.N.region r).chords.getD t 0
  cnt := cntInit E.K nd0 nd1
  nxt := fun j => if j + 1 < E.A then j + 1 else 0
  prv := fun j => if 0 < j then j - 1 else E.A - 1
  eg := eg
  pz := pz
  stk := fun t => t
  top := E.K
  nlive := E.K

/-- **The initial state satisfies the invariant**, if the input submap is γ-semigranular with
degrees `≤ D` and the static data are correct. -/
theorem Inv.init (hE : E.Good) {nd0 nd1 eg pz : ℕ → ℕ}
    (hstat : StatOK E (initSt E nd0 nd1 eg pz))
    (hdeg : E.M.DegLe (E.N.F E.M E.Q) E.D) (hsemi : E.M.Semigranular (E.N.F E.M E.Q) E.γ) :
    Inv E (initSt E nd0 nd1 eg pz) := by
  set st := initSt E nd0 nd1 eg pz
  have hL : st.L E = {i | i < E.K} := by
    ext i; simp [St.L, st, initSt]
  have hF : st.F E = E.N.F E.M E.Q := by
    unfold St.F; rw [hL, ← fam_univ]
    ext d; simp [fam]
  have hcl : ∀ x, x < E.R → st.cl E x = E.reg x := by
    intro x hx
    unfold St.cl
    rw [hF]
    exact supR_eq (Chazelle.Chain.regionsIn_nonempty (hE.hRC.1 x hx)) (hE.hRC.1 x hx) le_rfl
  have hside := fun {i} (hi : i < E.K) => touch_iff_side hE.hNF hE.hM hE.hRC hE.hCS hi
  have hupdn : ∀ i, i < E.K → (E.N.chord i).up < E.R ∧ (E.N.chord i).dn < E.R :=
    fun i hi => ⟨(hE.hCS i hi).1, (hE.hCS i hi).2.1⟩
  -- a referenced class is a region index
  have href : ∀ x, st.Ref E x → x < E.R := by
    rintro x ⟨i, hi, rfl | rfl⟩
    · exact (hupdn i hi.1).1
    · exact (hupdn i hi.1).2
  have hK1 : 1 ≤ E.K := by
    obtain ⟨d, hd⟩ := hE.hne
    obtain ⟨i, hi, -⟩ := mem_F_iff.1 hd
    show 1 ≤ E.N.nChords
    omega
  refine ⟨hstat, fun _ _ => le_rfl, ?_, by rw [hF]; exact hdeg, by rw [hF]; exact hsemi,
    fun i hi => ?_, fun x hx => ?_, fun x y hx hy he => ?_, fun j hj => rfl, ?_,
    fun t ht => ht, by simp [st, initSt], fun i hi hno => absurd rfl (hno i hi.1)⟩
  · show E.K = _
    rw [hL, show {i | i < E.K} = ((Finset.range E.K : Finset ℕ) : Set ℕ) by ext; simp,
      Set.ncard_coe_finset, Finset.card_range]
  · -- sides
    have hi' := hi.1
    obtain ⟨hne, htouch⟩ := hside hi'
    obtain ⟨hu, hd⟩ := hupdn i hi'
    refine ⟨hu, hd, ?_, fun X hX => ?_⟩
    · show st.cl E (E.N.chord i).up ≠ st.cl E (E.N.chord i).dn
      rw [hcl _ hu, hcl _ hd]
      exact fun e => hne (hE.hRC.2.1 _ _ hu hd e)
    · show _ ↔ X = st.cl E (E.N.chord i).up ∨ X = st.cl E (E.N.chord i).dn
      rw [hcl _ hu, hcl _ hd, hF] at *
      rw [hF] at hX
      obtain ⟨r, hr, rfl⟩ := hE.hRC.2.2 X hX
      rw [htouch r hr]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (e | e)
        · exact Or.inl (hE.hRC.2.1 _ _ hr hu e)
        · exact Or.inr (hE.hRC.2.1 _ _ hr hd e)
  · -- classes
    have hx' := href x hx
    obtain ⟨hmem, hnd, -, hwt⟩ := hE.hRO x hx'
    have hexl : st.exl x = (E.N.region x).chords :=
      exl_of_list st x rfl fun t _ => rfl
    rw [hcl x hx', hF, hexl]
    refine ⟨(deg_region hE.hNF hE.hRC hE.hRO hx').symm, hwt, hnd, fun i => ?_, ?_⟩
    · rw [hmem i, hL]; rfl
    · show (E.N.region x).chords.length ≤ E.D
      rw [← deg_region hE.hNF hE.hRC hE.hRO hx']
      exact hdeg _ (hE.hRC.1 x hx')
  · -- distinct classes
    rw [hcl x (href x hx), hcl y (href y hy)] at he
    exact hE.hRC.2.1 _ _ (href x hx) (href y hy) he
  · -- the ring: every position is live
    have hA : ∀ j, j < E.A → st.Lv j := by
      intro j hj
      have hcut := pk_cut hE.hNF hE.hne hj
      rw [← hF] at hcut
      unfold St.F at hcut
      rw [isCut_fam_iff hE.hNF hE.hM] at hcut
      obtain ⟨i, -, hi, hk⟩ := hcut
      have hpos : st.Lv j := by
        unfold St.Lv
        show 0 < cntInit E.K nd0 nd1 j
        unfold cntInit
        rcases hk with hk | hk
        · have e := (hstat.nd0 i hi).2
          rw [← hk] at e
          have : nd0 i = j := key_inj hE (hstat.nd0 i hi).1 hj e
          have : 0 < ((Finset.range E.K).filter fun i => nd0 i = j).card :=
            Finset.card_pos.2 ⟨i, by simp [hi, this]⟩
          omega
        · have e := (hstat.nd1 i hi).2
          rw [← hk] at e
          have : nd1 i = j := key_inj hE (hstat.nd1 i hi).1 hj e
          have : 0 < ((Finset.range E.K).filter fun i => nd1 i = j).card :=
            Finset.card_pos.2 ⟨i, by simp [hi, this]⟩
          omega
      exact hpos
    -- at least two positions
    have hA2 : 2 ≤ E.A := by
      obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := hE.hM.two_cuts (F_adm hE.hNF) hE.hne
      obtain ⟨j₁, hj₁, rfl⟩ := cut_pk hE.hNF hE.hGM hk₁
      obtain ⟨j₂, hj₂, rfl⟩ := cut_pk hE.hNF hE.hGM hk₂
      have : j₁ ≠ j₂ := fun e => hk (by rw [e])
      show 2 ≤ E.N.arcs.length
      omega
    exact (ringOK_full hA2).congr (fun j hj => ⟨fun _ => trivial, fun _ => hA j hj⟩)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl)

end

end Gran

end Chazelle.Core
