module

public import Chazelle.Core.SweepEvWinR2

/-!
# The sweep (WP-D), stage 3: the window of the event loop (RAM, part 3)

The body of the window computation (`bodyS`): for a nonempty family, the comparison of the key
with the end of its located arc, the step to the successor arc if the key is that end, the
comparison with the end of the arc after the key and the decision of the window end
(`BodyPost`); for the empty family, `wX = 1`.
-/

namespace Chazelle.Core

namespace SweepEv

open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep ShotList
open Chazelle.Chain (sideInArc sidePt SideAttach)

@[expose] public section

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c : Config} {J : Merge.Junction} {N₁ N₂ : NF}

theorem wr_sw {i : ℕ} (h1 : 3000 ≤ i) (h2 : i < 6000) : WR (sw i) :=
  Or.inr (Or.inr ⟨by unfold sw; omega, by unfold sw; omega⟩)

theorem ne_of_wr {r q : ℕ} (hr : ¬ WR r) (hq : WR q) : r ≠ q := by rintro rfl; exact hr hq

theorem wr_wX : WR wX := Or.inr (Or.inl ⟨by unfold wX sw; omega, by unfold wX sw; omega⟩)
theorem wr_wE : WR wE := Or.inr (Or.inl ⟨by unfold wE sw; omega, by unfold wE sw; omega⟩)
theorem wr_wH : WR wH := Or.inr (Or.inl ⟨by unfold wH sw; omega, by unfold wH sw; omega⟩)

theorem win_off_inj {n g x y : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) (hy0 : 0 ≤ y) (hyn : y < n)
    (h : off n g x = off n g y) : x = y := by
  unfold off at h; split_ifs at h <;> linarith

/-! ## The body: the arc after the key and the decision -/

def neS : Stmt := .seq cmpS (.seq eqS (.seq cmpS decS))

def bodyS : Stmt := .ifLtN K0 wCh neS (.instr (.constN wX 1))

/-- The post of the body. -/
def BodyPost (P : Polygon) (J : Merge.Junction) (N₁ : NF) (x₀ : ℝ) (u₀ : WPos) (d₀ : ℕ)
    (c c' : Config) : Prop :=
  ∃ o', o' < N₁.arcs.length ∧ ArcRegs N₁ c' o' ∧
    ((N₁.F (chainModel J.left) (Qof P)).Nonempty →
      (sideInArc (OracleQ.sk (chainModel J.left) (Qof P) N₁ o')
          (OracleQ.ek (chainModel J.left) (Qof P) N₁ o') x₀ ∨
        OracleQ.sk (chainModel J.left) (Qof P) N₁ o' = x₀) ∧
      DecOut J (U₁ P J (N₁.arc (OracleQ.sj N₁ o')).e < U₁ P J u₀) d₀
        (N₁.arc (OracleQ.sj N₁ o')).e.edge (N₁.arc (OracleQ.sj N₁ o')).e.hgt c') ∧
    (N₁.F (chainModel J.left) (Qof P) = ∅ → c'.nreg wX = 1) ∧
    (∀ r, bandOf r ∉ oracleBands → ¬ WR r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem


theorem win_F_nonempty_iff {M : Model} {Q : Polygon} {N : NF} :
    (N.F M Q).Nonempty ↔ 0 < N.chords.length := by
  constructor
  · rintro ⟨x, r, hr, -⟩
    exact List.length_pos_of_mem hr
  · intro h
    obtain ⟨r, hr⟩ := List.exists_mem_of_length_pos h
    exact ⟨_, r, hr, rfl⟩

theorem win_F_empty_iff {M : Model} {Q : Polygon} {N : NF} :
    N.F M Q = ∅ ↔ N.chords.length = 0 := by
  rw [← Set.not_nonempty_iff_eq_empty, win_F_nonempty_iff]; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **The body.** -/
theorem bodyS_irs (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) (hI : IInv W c₀ c)
    (he1 : c.nreg wE1 < (chainModel J.left).W.n)
    (hpx : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg wE1, c.nreg kH⟩)
    (h6x : c.nreg kH = 0 → 6 ≤ c.nreg wE1)
    (ho : c.nreg wO < N₁.arcs.length) (har : ArcRegs N₁ c (c.nreg wO))
    (hl1 : ¬ (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) →
      N₁.F (chainModel J.left) (Qof P) = ∅ ∨
        sideInArc (OracleQ.sk (chainModel J.left) (Qof P) N₁ (c.nreg wO))
          (OracleQ.ek (chainModel J.left) (Qof P) N₁ (c.nreg wO))
          ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩))
    (hl2 : (chainModel J.left).IsCut (N₁.F (chainModel J.left) (Qof P))
        ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) →
      OracleQ.sk (chainModel J.left) (Qof P) N₁ (c.nreg wO) =
          (chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩ ∨
        OracleQ.ek (chainModel J.left) (Qof P) N₁ (c.nreg wO) =
          (chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩)
    (hch : c.nreg wCh = N₁.chords.length) (hroom : c.nreg ALLOC + 22100 ≤ W) :
    IRS P W c₀ bodyS c 22100 (BodyPost P J N₁
      ((chainModel J.left).key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩) ⟨c.nreg wE1, c.nreg kH⟩
      (c.nreg wD) c) := by
  set M := chainModel J.left
  set x₀ := M.key (Qof P) ⟨c.nreg wE1, c.nreg kH⟩
  have hK := E.hK.fix hI
  have k0 : c.nreg K0 = 0 := hK.1
  have hP₁ : J.left.P.Simple := E.hP
  have hNF := E.hNF₁
  unfold bodyS
  by_cases hne : c.nreg K0 < c.nreg wCh
  swap
  · -- the empty family
    have hemp : N₁.F M (Qof P) = ∅ := by rw [win_F_empty_iff]; rw [k0, hch] at hne; omega
    refine (IRS.ifF hne (win_irs_const' hI wsX (by omega))).mono (by norm_num) ?_
    rintro c' ⟨v, o, m⟩
    refine ⟨c.nreg wO, ho, ?_, fun h => absurd hemp h.ne_empty, fun _ => v,
      fun r _ hr => o r (ne_of_wr hr wr_wX), m⟩
    obtain ⟨a1, a2, a3, a4⟩ := har
    exact ⟨by rw [o _ (by rne), a1], by rw [o _ (by rne), a2], by rw [o _ (by rne), a3],
      by rw [o _ (by rne), a4]⟩
  have hFne : (N₁.F M (Qof P)).Nonempty := by rw [win_F_nonempty_iff]; rw [k0, hch] at hne; omega
  refine IRS.mono (K := 22098 + 2) (IRS.ifT hne ?_) le_rfl (fun _ h => h)
  -- facts on arcs
  have hpp : ∀ j, j < N₁.arcs.length → ProperPos M (Qof P) P.n (N₁.arc j).e ∧
      (N₁.arc j).e.edge < M.W.n ∧ ((N₁.arc j).e.hgt = 0 → 6 ≤ (N₁.arc j).e.edge) := by
    intro j hj
    obtain ⟨-, ⟨hpe, hee, -⟩⟩ := arc_end_facts hP₁ hNF hj
    exact ⟨hpe, hee, end6 hP₁ hNF hFne hj⟩
  have hNT := win_nt E hI
  have hNA : NFAt c.nmem (c.nreg (sw 3)) N₁ := hNT.nfAt
  have hA0 := arcs_pos hP₁ hNF
  obtain ⟨b7, b4A, b6A⟩ := NFLoc.nfWithin_bounds hNT hNF hA0
  obtain ⟨-, -, hTB, -⟩ := win_tab E hI
  have hAc := hI.hA
  set o := c.nreg wO
  have hsj : OracleQ.sj N₁ o < N₁.arcs.length := NFLoc.seq_lt hNF ho
  obtain ⟨hr1, hr2, hr3, hr4⟩ := har
  obtain ⟨hpe, hee, he6⟩ := hpp _ hsj
  have hxr := key₁_range (Q := Qof P) he1 hpx
  -- 1. compare with the end of the located arc
  refine IRS.seq (K₂ := 11082) (cmpS_irs E hI he1 (by rwa [hr3]) hpx
    (by rwa [hr3, hr4]) h6x (by rwa [hr3, hr4]) (by omega)) ?_ |>.mono
    (by norm_num) (fun _ h => h)
  rintro c₁ hI₁ - - ⟨b1, b2, k1, m1, a1⟩
  have k1' : ∀ r, ¬ WR r → bandOf r ∉ oracleBands → c₁.nreg r = c.nreg r := fun r hr hb =>
    k1 r hb (ne_of_wr hr (wr_sw (i := 3010) (by norm_num) (by norm_num)))
      (ne_of_wr hr (wr_sw (i := 3011) (by norm_num) (by norm_num)))
  have e1 : ∀ q, q = wO ∨ q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH ∨ q = wE1 ∨ q = kH ∨ q = wD ∨
      q = sw 3 → c₁.nreg q = c.nreg q := by
    intro q hq
    have hq' : 240000 ≤ q ∧ q < 250000 ∧ q ≠ wC ∧ q ≠ sw 3011 := by
      rcases hq with h | h | h | h | h | h | h | h | h <;> subst h <;>
        simp only [sw, wO, wA, wR, wEE, wEH, wE1, kH, wD, wC] <;> omega
    exact k1 q (not_oracle_sw hq'.1 hq'.2.1) hq'.2.2.1 hq'.2.2.2
  have hEo : (⟨c.nreg wEE, c.nreg wEH⟩ : WPos) = (N₁.arc (OracleQ.sj N₁ o)).e := by
    rw [hr3, hr4]
  rw [hEo] at b1 b2
  -- 2. the successor if the key is the end
  refine IRS.seq (K₂ := 11050) (eqS_irs hI₁ E.hK hNF (by rwa [m1, e1 _ (by simp)])
    (by rw [e1 _ (by simp)]; omega) (by rw [m1, e1 _ (by simp)]; omega)
    (by rw [m1, e1 _ (by simp)]; omega) (by rwa [e1 _ (by simp)]) b1 b2
    (by rw [e1 _ (by simp)]; exact ⟨by rwa [e1 _ (by simp)],
      by rwa [e1 _ (by simp)], by rwa [e1 _ (by simp)],
      by rwa [e1 _ (by simp)]⟩)) ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₂ hI₂ - - ⟨q1, q2, har2, k2, m2⟩
  set o' := c₂.nreg wO
  have nA : ∀ q, (q = wE1 ∨ q = kH ∨ q = wD ∨ q = sw 3) → ¬ ArcW q := by
    intro q hq; rcases hq with h | h | h | h <;> subst h <;>
      simp only [ArcW, wT, wA, wR, wEE, wEH, wL, wO, wE1, kH, wD, sw] <;> omega
  have e2 : ∀ q, (q = wE1 ∨ q = kH ∨ q = wD ∨ q = sw 3) → c₂.nreg q = c.nreg q := fun q hq => by
    rw [k2 q (nA q hq), e1 q (by rcases hq with h | h | h | h <;> simp [h])]
  have eo1 : c₁.nreg wO = o := e1 _ (by simp)
  rw [eo1] at q1 q2
  have hU : ∀ y : WPos, y.edge < M.W.n → ProperPos M (Qof P) P.n y →
      U₁ P J y = U₁ P J ⟨c.nreg wE1, c.nreg kH⟩ → M.key (Qof P) y = x₀ := by
    intro y hy hpy h
    have := key₁_range (Q := Qof P) hy hpy
    exact win_off_inj this.1 this.2 hxr.1 hxr.2 h
  have hsel : o' < N₁.arcs.length ∧
      (sideInArc (OracleQ.sk M (Qof P) N₁ o') (OracleQ.ek M (Qof P) N₁ o') x₀ ∨
        OracleQ.sk M (Qof P) N₁ o' = x₀) := by
    by_cases hp : U₁ P J ⟨c.nreg wE1, c.nreg kH⟩ < U₁ P J (N₁.arc (OracleQ.sj N₁ o)).e ∨
        U₁ P J (N₁.arc (OracleQ.sj N₁ o)).e < U₁ P J ⟨c.nreg wE1, c.nreg kH⟩
    · rw [q1 hp]
      refine ⟨ho, arc_of_loc hFne hl1 hl2 fun h => ?_⟩
      have : U₁ P J (N₁.arc (OracleQ.sj N₁ o)).e = U₁ P J ⟨c.nreg wE1, c.nreg kH⟩ := by
        unfold U₁; exact congrArg _ h
      rw [this] at hp; rcases hp with h' | h' <;> exact lt_irrefl _ h'
    · push Not at hp
      rw [q2 (not_lt.2 hp.1) (not_lt.2 hp.2)]
      have heq := hU _ hee hpe (le_antisymm hp.1 hp.2)
      exact ⟨OracleQ.succP_lt ho, Or.inr (arc_of_loc' hP₁ hNF ho hFne heq)⟩
  obtain ⟨ho', hin⟩ := hsel
  obtain ⟨hr1', hr2', hr3', hr4'⟩ := har2
  have hsj' : OracleQ.sj N₁ o' < N₁.arcs.length := NFLoc.seq_lt hNF ho'
  obtain ⟨hpe', hee', he6'⟩ := hpp _ hsj'
  have a2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [k2 _ (by simp only [ArcW, wT, wA, wR, wEE, wEH, wL, wO, ALLOC, sw]; omega), a1]
  have eE1 := e2 wE1 (by simp)
  have ekH := e2 kH (by simp)
  -- 3. compare with the end of the arc after the key
  refine IRS.seq (K₂ := 32) (cmpS_irs E hI₂ (by rwa [eE1]) (by rwa [hr3'])
    (by rwa [eE1, ekH]) (by rwa [hr3', hr4']) (by rwa [eE1, ekH])
    (by rwa [hr3', hr4']) (by omega)) ?_ |>.mono (by norm_num) (fun _ h => h)
  rintro c₃ hI₃ - - ⟨b1', b2', k3, m3, a3⟩
  have hEo' : (⟨c₂.nreg wEE, c₂.nreg wEH⟩ : WPos) = (N₁.arc (OracleQ.sj N₁ o')).e := by
    rw [hr3', hr4']
  rw [hEo', eE1, ekH] at b2'
  have e3 : ∀ q, (q = wD ∨ q = wEE ∨ q = wEH ∨ q = wA ∨ q = wR) → c₃.nreg q = c₂.nreg q := by
    intro q hq
    have hq' : 240000 ≤ q ∧ q < 250000 ∧ q ≠ wC ∧ q ≠ sw 3011 := by
      rcases hq with h | h | h | h | h <;> subst h <;>
        simp only [sw, wEE, wEH, wD, wC, wA, wR] <;> omega
    exact k3 q (not_oracle_sw hq'.1 hq'.2.1) hq'.2.2.1 hq'.2.2.2
  -- 4. the decision
  refine (decS_irs hI₃ E.hK E.hM b2' (by rwa [e3 wEE (by simp), hr3']) E.hWn).mono
    (by norm_num) ?_
  rintro c₄ ⟨hdec, k4, m4⟩
  rw [e3 wD (by simp), e2 wD (by simp), e3 wEE (by simp), hr3', e3 wEH (by simp), hr4'] at hdec
  have nD : ∀ q, (q = wA ∨ q = wR ∨ q = wEE ∨ q = wEH) → ¬ DecW q := by
    intro q hq; rcases hq with h | h | h | h <;> subst h <;>
      simp only [DecW, wX, wE, wH, wDE, wPs, wA, wR, wEE, wEH, sw] <;> omega
  refine ⟨o', ho', ⟨?_, ?_, ?_, ?_⟩, fun _ => ⟨hin, hdec⟩, fun h => absurd h hFne.ne_empty,
    fun r hr hw => ?_, by rw [m4, m3, m2, m1]⟩
  · rw [k4 _ (nD _ (by simp)), e3 _ (by simp), hr1']
  · rw [k4 _ (nD _ (by simp)), e3 _ (by simp), hr2']
  · rw [k4 _ (nD _ (by simp)), e3 _ (by simp), hr3']
  · rw [k4 _ (nD _ (by simp)), e3 _ (by simp), hr4']
  · have hnD : ¬ DecW r := by
      rintro (h | h | h | h | h) <;> subst h <;> apply hw
      · exact wr_wX
      · exact wr_wE
      · exact wr_wH
      · exact wr_sw (by norm_num) (by norm_num)
      · exact wr_sw (by norm_num) (by norm_num)
    have hnA : ¬ ArcW r := by
      rintro (h | h | h | h | h | h | h) <;> subst h <;> exact hw (wr_sw (by norm_num) (by norm_num))
    rw [k4 r hnD, k3 r hr (ne_of_wr hw (wr_sw (i := 3010) (by norm_num) (by norm_num)))
      (ne_of_wr hw (wr_sw (i := 3011) (by norm_num) (by norm_num))), k2 r hnA, k1' r hw hr]


end

end SweepEv

end Chazelle.Core
