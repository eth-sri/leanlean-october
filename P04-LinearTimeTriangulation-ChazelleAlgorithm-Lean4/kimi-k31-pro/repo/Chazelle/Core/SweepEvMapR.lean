module

public import Chazelle.Core.SweepEvShot2
public import Chazelle.Core.SweepEvMap4
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-!
# The sweep (WP-D), stage 3: the map of an arrival position of `M₁` to `M` (RAM)

`mapC`: from the arrival edge `pA` (register `eA + 1`) of the walk of `C₁` and its normalised
height code (`eA + 2`), the `b₁`-offset `d = (pA + n₁ - b₁) mod n₁` (`cD`), the validity flag
`cV` (`d < E₁`, not inside the gap, not at the gap start with a positive parameter) and, when
valid, `ψ d` (`cPs`).  `mapE`: the walk edge `mEdge d = (gW + Lst + ψ d) mod n` (`cME`).

Constants (fixed registers `sw 652 … 660`, set by the initialisation): `MapK`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt)

@[expose] public section

/-! ## Registers -/

def cB1 : ℕ := sw 652
def cN1 : ℕ := sw 653
def cE1 : ℕ := sw 654
def cLL : ℕ := sw 655
def cLD : ℕ := sw 656
def cGL : ℕ := sw 657
def cNW : ℕ := sw 658
def cLE : ℕ := sw 660

def cD : ℕ := sw 2260
def cV : ℕ := sw 2261
def cPs : ℕ := sw 2262
def cME : ℕ := sw 2263

/-- The constants of the map. -/
structure MapK (J : Merge.Junction) (c : Config) : Prop where
  b1 : c.nreg cB1 = b₁ J
  n1 : c.nreg cN1 = (chainModel J.left).W.n
  e1 : c.nreg cE1 = E₁ J
  ll : c.nreg cLL = lL1 J
  ld : c.nreg cLD = lδ J
  gl : c.nreg cGL = (gW J + Lst J) % (chainModel J.whole).W.n
  nw : c.nreg cNW = (chainModel J.whole).W.n
  le : c.nreg cLE = lL1 J + lδ J

theorem MapK.fix {J : Merge.Junction} {W : ℕ} {c₀ c : Config} (h : MapK J c₀)
    (hI : IInv W c₀ c) : MapK J c := by
  have k : ∀ i, 652 ≤ i → i ≤ 660 → c.nreg (sw i) = c₀.nreg (sw i) := fun i h1 h2 =>
    hI.hin _ (by ufo IFix sw)
  obtain ⟨a, b, d, e, f, g, i, j⟩ := h
  exact ⟨(k 652 le_rfl (by norm_num)).trans a, (k 653 (by norm_num) (by norm_num)).trans b,
    (k 654 (by norm_num) (by norm_num)).trans d, (k 655 (by norm_num) (by norm_num)).trans e,
    (k 656 (by norm_num) (by norm_num)).trans f, (k 657 (by norm_num) (by norm_num)).trans g,
    (k 658 (by norm_num) (by norm_num)).trans i, (k 660 (by norm_num) (by norm_num)).trans j⟩

/-! ## The program -/

/-- The gap tests (valid branches set `cV := 1`, the branch beyond the gap `cPs := d - lδ`). -/
def mapGap : Stmt :=
  .ifLtN cLL cD (.ifLtN cD cLE .skip (block [.subN cPs cD cLD, .constN cV 1]))
    (.ifLtN cD cLL (.instr (.constN cV 1)) (.ifLtN K0 (eA + 2) .skip (.instr (.constN cV 1))))

/-- **The offset and validity of an arrival edge.** -/
def mapC : Stmt :=
  .seq (block [.addN cD (eA + 1) cN1, .subN cD cD cB1]) (.seq (condSub cD cD cN1)
    (.seq (block [.constN cV 0, .copyN cPs cD])
      (.ifLtN cD cE1 (.ifLtN K0 cLD mapGap (.instr (.constN cV 1))) .skip)))

/-- **The walk edge of `M`.** -/
def mapE : Stmt := .seq (block [.addN cME cGL cPs]) (condSub cME cME cNW)

/-- The validity of a `b₁`-offset with a height code (the arithmetic conditions of `MValid`). -/
def MVal (J : Merge.Junction) (d h : ℕ) : Prop :=
  d < E₁ J ∧ ¬ (0 < lδ J ∧ lL1 J < d ∧ d < lL1 J + lδ J) ∧ ¬ (0 < lδ J ∧ d = lL1 J ∧ h ≠ 0)

/-! ## The run -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The post of the map: the offset, the validity flag and `ψ`; only `cD, cV, cPs` change. -/
def MapPost (J : Merge.Junction) (c c' : Config) (d h : ℕ) : Prop :=
  c'.nreg cD = d ∧ c'.nreg cV ≤ 1 ∧ (c'.nreg cV = 1 ↔ MVal J d h) ∧
    (c'.nreg cV = 1 → c'.nreg cPs = ψ J d) ∧
    (∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem

/-- Setting a scratch register to a constant. -/
theorem irs_const {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r) (hv : v ≤ W) :
    IRS P W c₀ (.instr (.constN r v)) c 1 (fun c' => c'.nreg r = v ∧
      (∀ q, q ≠ r → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) :=
  (IRS.reg hI hr (Exec.constN hI.hw r v hv)).mono le_rfl (fun c' h => by
    subst h; exact ⟨by simp, fun q hq => by simp [upd_other _ _ _ hq], rfl⟩)

theorem iscr_sw' {i : ℕ} (h1 : 700 ≤ i) (h2 : i < 10000) : IScr (sw i) :=
  iscr_sw (by ufo sw) (by ufo sw)

/-- **The gap tests.** -/
theorem mapGap_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c) (hM : MapK J c)
    {d : ℕ} (hd : c.nreg cD = d) (hv0 : c.nreg cV = 0) (hps : c.nreg cPs = d)
    (hδ : 0 < lδ J) (hdE : d < E₁ J) (hW : 1 ≤ W) :
    IRS P W c₀ mapGap c 7 (fun c' => MapPost J c c' d (c.nreg (eA + 2))) := by
  have k0  := hK.1
  have hsc : IScr cV := iscr_sw' (by norm_num) (by norm_num)
  have hsp : IScr cPs := iscr_sw' (by norm_num) (by norm_num)
  have nV : cV ≠ cD := by ufo cV cD sw
  have nP : cPs ≠ cD := by ufo cPs cD sw
  have nVP : cV ≠ cPs := by ufo cV cPs sw
  unfold mapGap
  by_cases h1 : c.nreg cLL < c.nreg cD
  · rw [hM.ll, hd] at h1
    refine IRS.mono (K := 5 + 2) (IRS.ifT (by rwx [hM.ll, hd]) ?_) (by norm_num) (fun _ => id)
    by_cases h2 : c.nreg cD < c.nreg cLE
    · rw [hM.le, hd] at h2
      refine IRS.mono (K := 0 + 2) (IRS.ifT (by rwx [hM.le, hd]) (IRS.skip hI rfl))
        (by norm_num) ?_
      rintro c' rfl
      refine ⟨hd, by omega, ⟨fun h => by omega, fun h => absurd ⟨hδ, h1, h2⟩ h.2.1⟩,
        fun h => by omega, fun _ _ _ _ => rfl, rfl⟩
    · rw [hM.le, hd] at h2
      refine IRS.mono (K := 2 + 2) (IRS.ifF (by rwx [hM.le, hd]) (IRS.block _ hI
        ⟨hsp, ⟨hsc, hW⟩, trivial⟩)) (by norm_num) ?_
      rintro c' rfl
      unfold MapPost
      simp only [regB, regI]
      refine ⟨?_, ?_, ⟨fun _ => ⟨hdE, fun h => h2 h.2.2, fun h => by omega⟩, fun _ => ?_⟩, fun _ => ?_,
        fun r h1' h2' h3' => ?_, trivial⟩
      · rw [upd_other _ _ _ nV.symm, upd_other _ _ _ nP.symm, hd]
      · rw [upd_same]
      · rw [upd_same]
      · rw [upd_other _ _ _ nVP.symm, upd_same, hd, hM.ld]
        unfold ψ; rw [ite_eq_left ⟨hδ, h1⟩, ite_eq_right h2]
      · rw [upd_other _ _ _ h2', upd_other _ _ _ h3']
  · rw [hM.ll, hd] at h1
    refine IRS.mono (K := 5 + 2) (IRS.ifF (by rwx [hM.ll, hd]) ?_) (by norm_num) (fun _ => id)
    have hψ : ψ J d = d := by unfold ψ; rw [ite_eq_right (fun h => h1 h.2)]
    by_cases h3 : c.nreg cD < c.nreg cLL
    · rw [hM.ll, hd] at h3
      refine IRS.mono (K := 1 + 2) (IRS.ifT (by rwx [hM.ll, hd]) (irs_const hI hsc hW))
        (by norm_num) ?_
      rintro c' ⟨v1, v2, v3⟩
      refine ⟨by rw [v2 _ nV.symm, hd], by omega, ⟨fun _ => ⟨hdE, fun h => h1 h.2.1,
        fun h => by omega⟩, fun _ => v1⟩, fun _ => by rw [v2 _ nVP.symm, hps, hψ],
        fun r _ h2' _ => v2 r h2', v3⟩
    · rw [hM.ll, hd] at h3
      have hdl : d = lL1 J := by omega
      refine IRS.mono (K := 3 + 2) (IRS.ifF (by rwx [hM.ll, hd]) ?_) (by norm_num) (fun _ => id)
      by_cases h4 : c.nreg K0 < c.nreg (eA + 2)
      · rw [k0] at h4
        refine IRS.mono (K := 0 + 2) (IRS.ifT (by rwx [k0]) (IRS.skip hI rfl)) (by norm_num) ?_
        rintro c' rfl
        refine ⟨hd, by omega, ⟨fun h => by omega, fun h => absurd ⟨hδ, hdl, by omega⟩ h.2.2⟩,
          fun h => by omega, fun _ _ _ _ => rfl, rfl⟩
      · rw [k0] at h4
        refine IRS.mono (K := 1 + 2) (IRS.ifF (by rwx [k0]) (irs_const hI hsc hW))
          (by norm_num) ?_
        rintro c' ⟨v1, v2, v3⟩
        refine ⟨by rw [v2 _ nV.symm, hd], by omega, ⟨fun _ => ⟨hdE, fun h => h1 h.2.1,
          fun h => by omega⟩, fun _ => v1⟩, fun _ => by rw [v2 _ nVP.symm, hps, hψ],
          fun r _ h2' _ => v2 r h2', v3⟩

/-- **The offset and validity of an arrival edge.** -/
theorem mapC_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK₀ : Consts c₀) (hM₀ : MapK J c₀)
    (hpA : c.nreg (eA + 1) < (chainModel J.left).W.n)
    (hW : 2 * (chainModel J.left).W.n ≤ W) :
    IRS P W c₀ mapC c 20 (fun c' => MapPost J c c'
      ((c.nreg (eA + 1) + (chainModel J.left).W.n - b₁ J) % (chainModel J.left).W.n)
      (c.nreg (eA + 2))) := by
  have hK := hK₀.fix hI
  have hM := hM₀.fix hI
  have k0 : c.nreg K0 = 0 := hK.1
  set n₁ := (chainModel J.left).W.n with hn₁
  have hb : b₁ J < n₁ := by
    have := tpos_lt J.left J.m₁
    have hn : n₁ = 2 * J.left.m + 7 := cm_n J.left
    have hm1 : J.left.m = J.m₁ := rfl
    unfold b₁; splao
  set pA := c.nreg (eA + 1) with hpAd
  set d := (pA + n₁ - b₁ J) % n₁ with hdd
  have hsD : IScr cD := iscr_sw' (by norm_num) (by norm_num)
  have hsV : IScr cV := iscr_sw' (by norm_num) (by norm_num)
  have hsP : IScr cPs := iscr_sw' (by norm_num) (by norm_num)
  have nD : ∀ r, r = cD → r ≠ eA + 2 := by rintro r rfl; ufo cD eA sw
  -- 1. `cD := pA + n₁ - b₁`
  have hok1 : okB W c.nmem [.addN cD (eA + 1) cN1, .subN cD cD cB1] c.nreg :=
    ⟨⟨hsD, by rwo [hM.n1]⟩, hsD, trivial⟩
  refine IRS.seq (K₂ := 18) (IRS.block _ hI hok1) ?_ |>.mono (by norm_num) (fun _ => id)
  rintro c₁ hI₁ - - rfl
  simp only [regB, regI]
  set f₁ := upd (upd c.nreg cD (c.nreg (eA + 1) + c.nreg cN1)) cD
    (upd c.nreg cD (c.nreg (eA + 1) + c.nreg cN1) cD -
      upd c.nreg cD (c.nreg (eA + 1) + c.nreg cN1) cB1) with hf₁
  have v1 : f₁ cD = pA + n₁ - b₁ J := by
    rw [hf₁, upd_same, upd_same, upd_other _ _ _ (by ufo cB1 cD sw), hM.n1, hM.b1]
  have o1 : ∀ r, r ≠ cD → f₁ r = c.nreg r := fun r hr => by
    rw [hf₁, upd_other _ _ _ hr, upd_other _ _ _ hr]
  -- 2. `cD := d`
  obtain ⟨c₂, k₂, hk₂, ex₂, v₂, o₂⟩ := condSub_exec (P := P) (c := { c with nreg := f₁ })
    hI₁.hw cD cD cN1
  refine IRS.seq (K₁ := 3) (K₂ := 15) (irs_of_out hI₁ ex₂ hk₂ o₂ (by simp [hsD])) ?_ |>.mono
    (by norm_num) (fun _ => id)
  rintro c₂ hI₂ - - rfl
  obtain ⟨or₂, -, om₂, -, -⟩ := o₂
  have hn1 : f₁ cN1 = n₁ := by rw [o1 _ (by ufo cN1 cD sw), hM.n1]
  simp only at v₂
  rw [v1, hn1] at v₂
  have vd : c₂.nreg cD = d := by
    rw [v₂, hdd]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have o2 : ∀ r, r ≠ cD → c₂.nreg r = c.nreg r := fun r hr => by
    rw [or₂ r (by simp [hr])]; exact o1 r hr
  have hm2 : c₂.nmem = c.nmem := om₂
  -- 3. `cV := 0`, `cPs := d`
  have hok3 : okB W c₂.nmem [.constN cV 0, .copyN cPs cD] c₂.nreg := ⟨⟨hsV, by omega⟩, hsP, trivial⟩
  refine IRS.seq (K₂ := 13) (IRS.block _ hI₂ hok3) ?_ |>.mono (by norm_num) (fun _ => id)
  rintro c₃ hI₃ - - rfl
  simp only [regB, regI]
  have nV : cV ≠ cD := by ufo cV cD sw
  have nP : cPs ≠ cD := by ufo cPs cD sw
  have nVP : cV ≠ cPs := by ufo cV cPs sw
  set f₃ := upd (upd c₂.nreg cV 0) cPs (upd c₂.nreg cV 0 cD) with hf₃
  have d3 : f₃ cD = d := by rw [hf₃, upd_other _ _ _ nP.symm, upd_other _ _ _ nV.symm, vd]
  have v3 : f₃ cV = 0 := by rw [hf₃, upd_other _ _ _ nVP, upd_same]
  have p3 : f₃ cPs = d := by rw [hf₃, upd_same, upd_other _ _ _ nV.symm, vd]
  have o3 : ∀ r, r ≠ cD → r ≠ cV → r ≠ cPs → f₃ r = c.nreg r := fun r h1 h2 h3 => by
    rw [hf₃, upd_other _ _ _ h3, upd_other _ _ _ h2, o2 r h1]
  have e2 : f₃ (eA + 2) = c.nreg (eA + 2) :=
    o3 _ (by ufo eA cD sw) (by ufo eA cV sw) (by ufo eA cPs sw)
  have lift : ∀ c', MapPost J { c₂ with nreg := f₃ } c' d (f₃ (eA + 2)) →
      MapPost J c c' d (c.nreg (eA + 2)) := by
    rintro c' ⟨a1, a2, a3, a4, a5, a6⟩
    rw [e2] at a3
    exact ⟨a1, a2, a3, a4, fun r h1 h2 h3 => by rw [a5 r h1 h2 h3]; exact o3 r h1 h2 h3,
      by rw [a6, hm2]⟩
  -- 4. the tests
  have hI₃' := hI₃
  have hK3 : Consts { c₂ with nreg := f₃ } := hK₀.fix hI₃
  have hM3 : MapK J { c₂ with nreg := f₃ } := hM₀.fix hI₃
  by_cases hE : f₃ cD < f₃ cE1
  · have hdE : d < E₁ J := by have := hM3.e1; simp only at this; rw [d3, this] at hE; exact hE
    refine IRS.mono (K := 11 + 2) (IRS.ifT hE ?_) (by norm_num) (fun _ => id)
    have k03 : f₃ K0 = 0 := hK3.1
    by_cases hδ : f₃ K0 < f₃ cLD
    · have hδ' : 0 < lδ J := by
        have := hM3.ld; simp only at this; rw [k03, this] at hδ; exact hδ
      refine IRS.mono (K := 7 + 2) (IRS.ifT hδ ?_) (by norm_num) (fun _ => id)
      exact (mapGap_irs hI₃ hK3 hM3 d3 v3 p3 hδ' hdE (by omega)).mono le_rfl lift
    · have hδ' : lδ J = 0 := by
        have := hM3.ld; simp only at this; rwo [k03, this] at hδ
      refine IRS.mono (K := 1 + 2) (IRS.ifF hδ (irs_const hI₃ hsV (by omega))) (by norm_num) ?_
      rintro c' ⟨w1, w2, w3⟩
      refine lift c' ⟨by rw [w2 _ nV.symm, Config.nreg_mk, d3], by omega,
        ⟨fun _ => ⟨hdE, fun h => by omega, fun h => by omega⟩, fun _ => w1⟩, fun _ => ?_,
        fun r _ h2 _ => w2 r h2, w3⟩
      rw [w2 _ nVP.symm]; simp only; rw [p3]
      unfold ψ; rw [ite_eq_right (by omega)]
  · have hdE : ¬ d < E₁ J := by have := hM3.e1; simp only at this; rw [d3, this] at hE; exact hE
    refine IRS.mono (K := 0 + 2) (IRS.ifF hE (IRS.skip hI₃ rfl)) (by norm_num) ?_
    rintro c' rfl
    refine lift _ ⟨d3, by sio only,
      ⟨fun h => by sio only at h, fun h => absurd h.1 hdE⟩,
      fun h => by sio only at h, fun _ _ _ _ => rfl, rfl⟩

end

end SweepEv

end Chazelle.Core
