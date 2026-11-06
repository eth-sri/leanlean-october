module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvStopSort3

/-!
# The sweep (WP-D), stage 2: sorting the raw stop records, part 4 (the pass as a loop)

`ssBody_step`: one step of the dedupe pass keeps `SsDI` (cost between `8` and `12100`);
`while_range`: a loop with bounded body costs; `ssDedup_exec`: the whole pass.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep SweepStop SortR

@[expose] public section

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 20000 in
/-- **One step of the pass.** -/
theorem ssBody_step {P : Polygon} {W : ℕ} {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {L : List ℕ} {SBv B1 : ℕ} {d₀ d : Config} {j : ℕ}
    (hcmp : CmpOK P W ssCmp ssBc (SsCtx J d2 RB S A₀ m₀) (ssLe P J m₀ RB S) 12000)
    (hLlen : L.length = S) (hLm : ∀ x ∈ L, x < S)
    (hLs : L.Pairwise (fun x y => KLe (ssKey P J m₀ RB x) (ssKey P J m₀ RB y)))
    (hLmem : ∀ i, i < S → d₀.nmem (SBv + i) = L.getD i 0)
    (hSB : SBv + S ≤ B1) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (I : SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ j d) (hj : j < S) :
    ∃ d' k, Exec P W ssBody d d' k ∧ 8 ≤ k ∧ k ≤ 12100 ∧
      SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ (j + 1) d' := by
  obtain ⟨hw, hqj, hctx, hsb, hb1, hb2, hmem, ⟨O, hD, hC, hOj, hprev, hst, hax⟩, hregs, hrr, hrm,
    hout⟩ := I
  have hctx' := hctx
  obtain ⟨-, -, -, -, j0, j1, -, -⟩ := hctx'
  
  -- the next index
  obtain ⟨rX, rO⟩ := ssRd_val d.nmem d.nreg
  have e₁ := exec_regB (P := P) ssRd hw (by
    grind [ssRd, okW, okWI])
  set d₁ : Config := { d with nreg := regB d.nmem ssRd d.nreg } with hd₁
  set x := L.getD j 0 with hxd
  have hxL : L[j]? = some x := by
    grind
  have hxS : x < S := hLm x (List.mem_of_getElem? hxL)
  have q1X : d₁.nreg srX = x := by
    show regB _ _ _ srX = _
    rw [rX, hsb, hqj, hmem _ (by omega), hLmem j hj]
  have q1o : ∀ r, r ≠ srA → r ≠ srX → d₁.nreg r = d.nreg r := rO
  have hw₁ := e₁.wb_right
  have r1 : ∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → d₁.nreg r = d.nreg r :=
    fun r _ h => q1o r (by core_grind) (by grind [srX, sw])
  have hctx₁ : SsCtx J d2 RB S A₀ m₀ d₁ := ssCtx_keep hctx (fun r a b c' _ =>
    r1 r (not_oracle_sw a b) c') (fun _ _ => rfl)
  have K0₁ : d₁.nreg K0 = 0 := hctx₁.2.2.2.2.1
  have qJ₁ : d₁.nreg srJ = j := (q1o _ (by ssoSrt) (by ssoSrt)).trans hqj
  have sC₁ : d₁.nreg sC = O.length := (q1o _ (by ssoSrt) (by ssoSrt)).trans hC
  have sB₁ : d₁.nreg sB = B1 := (q1o _ (by ssoSrt) (by ssoSrt)).trans hb1
  have aB₁ : d₁.nreg aB = B1 + 5 * S := (q1o _ (by ssoSrt) (by ssoSrt)).trans hb2
  have hOS : O.length < S := by omega
  -- the advance, from a configuration with the item written or skipped
  have adv : ∀ (d₃ : Config) (O' : List ℕ), WordsBounded W d₃ → d₃.nreg srX = x →
      d₃.nreg srJ = j → d₃.nreg K1 = 1 → SsCtx J d2 RB S A₀ m₀ d₃ → d₃.nreg srSB = SBv →
      d₃.nreg sB = B1 → d₃.nreg aB = B1 + 5 * S →
      (∀ a, a < B1 → d₃.nmem a = d₀.nmem a) → DInv (ssKey P J m₀ RB) L (j + 1) O' →
      d₃.nreg sC = O'.length → O'.length ≤ j + 1 →
      StopRecsAt d₃.nmem B1 (O'.map (rawRec m₀ RB)) →
      AuxRecsAt d₃.nmem (B1 + 5 * S) (O'.map (rawAux m₀ RB)) →
      (∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → r ≠ sC →
        d₃.nreg r = d₀.nreg r) →
      (∀ r, bandOf r ∉ oracleBands → d₃.rreg r = d₀.rreg r) → d₃.rmem = d₀.rmem →
      d₃.output = d₀.output →
      ∃ d', Exec P W (block ssAdv) d₃ d' 2 ∧ SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ (j + 1) d' := by
    intro d₃ O' w₃ x₃ j₃ k₃ c₃ sb₃ b1₃ b2₃ m₃ D₃ C₃ l₃ st₃ ax₃ g₃ rr₃ rm₃ o₃
    obtain ⟨vP, vJ, vo⟩ := ssAdv_val d₃.nmem d₃.nreg
    have e := exec_regB (P := P) ssAdv w₃ (by
      simp only [ssAdv, okW, okWI, regI]
      refine ⟨trivial, ?_, trivial⟩
      rw [upd_other _ _ _ (by ssoSrt), upd_other _ _ _ (by ssoSrt), j₃, k₃]; omega)
    have ko : ∀ r, r ≠ srP → r ≠ srJ → regB d₃.nmem ssAdv d₃.nreg r = d₃.nreg r := vo
    refine ⟨_, e, e.wb_right, by grind, ?_, ?_, ?_, ?_, m₃,
      ⟨O', D₃, by show regB _ _ _ sC = _; rw [ko _ (by ssoSrt) (by ssoSrt)]; exact C₃, l₃,
        fun _ => ⟨x, by grind, by grind⟩, st₃, ax₃⟩,
      fun r h1 h2 h3 => ?_, rr₃, rm₃, o₃⟩
    · exact ssCtx_keep c₃ (fun r _ _ h _ => ko r (by grind [srP, sw])
        (by rintro rfl; grind [srJ, sw])) (fun _ _ => rfl)
    · show regB _ _ _ srSB = _; rw [ko _ (by ssoSrt) (by ssoSrt)]; exact sb₃
    · show regB _ _ _ sB = _; rw [ko _ (by ssoSrt) (by ssoSrt)]; exact b1₃
    · show regB _ _ _ aB = _; rw [ko _ (by ssoSrt) (by ssoSrt)]; exact b2₃
    · show regB _ _ _ r = _
      rw [ko r (by grind [srP, sw]) (by rintro rfl; grind [srJ, sw])]
      grind
  by_cases hj0 : j = 0
  · -- the first index: written
    subst hj0
    have hO0 : O = [] := hD.nil rfl
    subst hO0
    obtain ⟨d₂, k₂, e₂, hk₂, sC₂, st₂, ax₂, m₂, r₂, rr₂, rm₂, o₂⟩ := ssWr_step (P := P) (O := [])
      hw₁ hS hAB hroom hctx₁ sB₁ aB₁ (fun a ha => hmem a ha) q1X hxS sC₁ hOS hst hax
    have k₂ : ∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → r ≠ sC →
        d₂.nreg r = d.nreg r := fun r ho h hs => by
      rw [r₂ r (by rintro rfl; simp only [sr1, sw] at h; omega) (by rintro rfl; simp only [sr2, sw] at h; omega)
        (by rintro rfl; simp only [sr3, sw] at h; omega) (by rintro rfl; simp only [sr4, sw] at h; omega)
        (by rintro rfl; simp only [srS, sw] at h; omega) (by rintro rfl; simp only [srD, sw] at h; omega)
        (by rintro rfl; simp only [srE, sw] at h; omega) (by rintro rfl; simp only [srV, sw] at h; omega) hs]
      exact r1 r ho h
    have kb : ∀ q, 240000 ≤ q → q < 250000 → (q < sw 3003 ∨ sw 3016 < q) → q ≠ sC →
        d₂.nreg q = d.nreg q := fun q a b h hs => k₂ q (not_oracle_sw a b) h hs
    obtain ⟨d', ex', hI'⟩ := adv d₂ ([] ++ [x]) e₂.wb_right
      (by rw [r₂ srX (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
        (by ssoSrt)]; exact q1X)
      (by rw [r₂ srJ (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), qJ₁])
      (by rw [kb K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact j1)
      (ssCtx_keep hctx kb (fun a ha => by rw [m₂ a (by omega)]))
      (by rw [r₂ srSB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), q1o srSB (by ssoSrt) (by ssoSrt)]; exact hsb)
      (by rw [kb sB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hb1)
      (by rw [kb aB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hb2)
      (fun a ha => by rw [m₂ a ha]; exact hmem a ha)
      ((hD.step hLs hxL).1 (Or.inl rfl)) sC₂ (by simp) st₂ ax₂
      (fun r ho h hs => (k₂ r ho h hs).trans (hregs r ho h hs))
      (fun r ho => by rw [rr₂]; exact hrr r ho) (by grind) (by grind)
    have nlt : ¬ d₁.nreg K0 < d₁.nreg srJ := by omega
    exact ⟨d', _, .seq e₁ (.seq (.ifLtN_false nlt e₂) ex'), by omega, by
      simp [ssRd]; omega, hI'⟩
  · -- a later index: compared with the previous one
    have hlt : d₁.nreg K0 < d₁.nreg srJ := by omega
    obtain ⟨x', hx', hqP⟩ := hprev (by omega)
    have hx'S : x' < S := hLm x' (List.mem_of_getElem? hx')
    have hqP₁ : d₁.nreg srP = x' := (q1o _ (by ssoSrt) (by ssoSrt)).trans hqP
    -- sorted: the previous key is at most this one
    have hsort : KLe (ssKey P J m₀ RB x') (ssKey P J m₀ RB x) := by
      have := List.pairwise_iff_getElem.1 hLs (j - 1) j (by omega) (by omega) (by omega)
      rw [List.getElem?_eq_getElem (by omega)] at hx' hxL
      grind
    -- the inputs of the comparator
    obtain ⟨c0, c1, co⟩ := ssCp_val d₁.nmem d₁.nreg
    have e₂ := exec_regB (P := P) [.copyN 30000 srX, .copyN 30001 srP] hw₁ (by
      simp only [okW, okWI]; grind)
    set d₂ : Config := { d₁ with
      nreg := regB d₁.nmem [.copyN 30000 srX, .copyN 30001 srP] d₁.nreg } with hd₂
    have k₂ : ∀ r, r ≠ 30000 → r ≠ 30001 → d₂.nreg r = d₁.nreg r := co
    have hw₂ := e₂.wb_right
    have hctx₂ : SsCtx J d2 RB S A₀ m₀ d₂ := ssCtx_keep hctx₁ (fun r a _ _ _ =>
      k₂ r (by omega) (by omega)) (fun _ _ => rfl)
    obtain ⟨d₃, k₃, e₃, hk₃, hctx₃, hbit, hr₃, hrr₃, hm₃, hrm₃, ho₃⟩ := hcmp d₂ hw₂ hctx₂
    have i0 : d₂.nreg 30000 = x := by grind
    have i1 : d₂.nreg 30001 = x' := by grind
    rw [i0, i1] at hbit
    have hiff := ssLe_in (P := P) (J := J) (m := m₀) (RB := RB) hxS hx'S
    -- registers kept by the comparator
    have k₃ : ∀ r, bandOf r ∉ oracleBands → d₃.nreg r = d₂.nreg r := fun r ho =>
      hr₃ r (by rintro rfl; exact ho (by decide)) (by rintro rfl; exact ho (by decide))
        (by rintro rfl; exact ho (by decide)) (Or.inl (ssBc_sub ho))
    have k31 : ∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → d₃.nreg r = d.nreg r :=
      fun r ho h => by
        rw [k₃ r ho, k₂ r (by rintro rfl; exact ho (by decide))
          (by rintro rfl; exact ho (by decide)), r1 r ho h]
    have kb : ∀ q, 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands := fun q a b =>
      not_oracle_sw a b
    have qX₃ : d₃.nreg srX = x := by
      rw [k₃ srX (kb _ (by ssoSrt) (by ssoSrt)), k₂ srX (by ssoSrt) (by ssoSrt), q1X]
    have K0₃ : d₃.nreg K0 = 0 := hctx₃.2.2.2.2.1
    have hm₃' : ∀ a, d₃.nmem a = d.nmem a := fun a => by rw [hm₃]
    by_cases hle : KLe (ssKey P J m₀ RB x) (ssKey P J m₀ RB x')
    · -- equal keys: skipped
      have heq : ssKey P J m₀ RB x' = ssKey P J m₀ RB x := KLe.antisymm' hsort hle
      have b1 : d₃.nreg 30002 = 1 := by grind
      have t : d₃.nreg K0 < d₃.nreg 30002 := by omega
      obtain ⟨d', ex', hI'⟩ := adv d₃ O e₃.wb_right qX₃
        (by rw [k₃ srJ (kb _ (by ssoSrt) (by ssoSrt)), k₂ srJ (by ssoSrt) (by ssoSrt), qJ₁])
        hctx₃.2.2.2.2.2.1 hctx₃
        (by rw [k₃ srSB (kb _ (by ssoSrt) (by ssoSrt)), k₂ srSB (by ssoSrt) (by ssoSrt), q1o srSB (by ssoSrt) (by ssoSrt)]; exact hsb)
        (by rw [k31 sB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hb1)
        (by rw [k31 aB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hb2)
        (fun a ha => by rw [hm₃' a]; exact hmem a ha)
        ((hD.step hLs hxL).2 ⟨by omega, fun y hy => by
          grind⟩)
        (by rw [k31 sC (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hC) (by omega)
        (by grind) (by grind)
        (fun r ho h _ => (k31 r ho h).trans (hregs r ho h (by
          omega)))
        (fun r ho => by
          rw [hrr₃ r (ssBc_sub ho)]; exact hrr r ho)
        (by grind) (by grind)
      refine ⟨d', _, .seq e₁ (.seq (.ifLtN_true hlt (.seq e₂ (.seq e₃
        (.ifLtN_true t (.skip e₃.wb_right))))) ex'), by simp [ssRd]; omega, by simp [ssRd]; omega, hI'⟩
    · -- a new key: written
      have b0 : d₃.nreg 30002 = 0 := by grind
      have t : ¬ d₃.nreg K0 < d₃.nreg 30002 := by omega
      have hne : ∀ y, L[j - 1]? = some y → ssKey P J m₀ RB y ≠ ssKey P J m₀ RB x := by
        grind
      have sC₃ : d₃.nreg sC = O.length := by
        rw [k31 sC (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hC
      obtain ⟨d₄, k₄, e₄, hk₄, sC₄, st₄, ax₄, m₄, r₄, rr₄, rm₄, o₄⟩ := ssWr_step (P := P) (O := O)
        e₃.wb_right hS hAB hroom hctx₃
        (by rw [k31 sB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hb1)
        (by rw [k31 aB (kb _ (by ssoSrt) (by ssoSrt)) (by ssoSrt)]; exact hb2)
        (fun a ha => (hm₃' a).trans (hmem a ha)) qX₃ hxS sC₃ hOS
        (by grind) (by grind)
      have k₄ : ∀ r, bandOf r ∉ oracleBands → (r < sw 3003 ∨ sw 3016 < r) → r ≠ sC →
          d₄.nreg r = d.nreg r := fun r ho h hs => by
        rw [r₄ r (by rintro rfl; simp only [sr1, sw] at h; omega) (by rintro rfl; simp only [sr2, sw] at h; omega)
          (by rintro rfl; simp only [sr3, sw] at h; omega) (by rintro rfl; simp only [sr4, sw] at h; omega)
          (by rintro rfl; simp only [srS, sw] at h; omega) (by rintro rfl; simp only [srD, sw] at h; omega)
          (by rintro rfl; simp only [srE, sw] at h; omega) (by rintro rfl; simp only [srV, sw] at h; omega) hs]
        exact k31 r ho h
      have kb4 : ∀ q, 240000 ≤ q → q < 250000 → (q < sw 3003 ∨ sw 3016 < q) → q ≠ sC →
          d₄.nreg q = d.nreg q := fun q a b h hs => k₄ q (not_oracle_sw a b) h hs
      obtain ⟨d', ex', hI'⟩ := adv d₄ (O ++ [x]) e₄.wb_right
        (by rw [r₄ srX (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)
          (by ssoSrt)]; exact qX₃)
        (by rw [r₄ srJ (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), k₃ srJ (kb _ (by ssoSrt) (by ssoSrt)), k₂ srJ (by ssoSrt) (by ssoSrt), qJ₁])
        (by rw [kb4 K1 (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact j1)
        (ssCtx_keep hctx kb4 (fun a ha => by rw [m₄ a (by omega), hm₃' a]))
        (by rw [r₄ srSB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt), k₃ srSB (kb _ (by ssoSrt) (by ssoSrt)), k₂ srSB (by ssoSrt) (by ssoSrt),
          q1o srSB (by ssoSrt) (by ssoSrt)]; exact hsb)
        (by rw [kb4 sB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hb1)
        (by rw [kb4 aB (by ssoSrt) (by ssoSrt) (by ssoSrt) (by ssoSrt)]; exact hb2)
        (fun a ha => by rw [m₄ a ha, hm₃' a]; exact hmem a ha)
        ((hD.step hLs hxL).1 (Or.inr hne)) sC₄ (by simp; omega) st₄ ax₄
        (fun r ho h hs => (k₄ r ho h hs).trans (hregs r ho h hs))
        (fun r ho => by rw [rr₄, hrr₃ r (ssBc_sub ho)]; exact hrr r ho)
        (by rw [rm₄, hrm₃]; exact hrm) (by rw [o₄, ho₃]; exact hout)
      refine ⟨d', _, .seq e₁ (.seq (.ifLtN_true hlt (.seq e₂ (.seq e₃
        (.ifLtN_false t e₄)))) ex'), by simp [ssRd]; omega, by simp [ssRd]; omega, hI'⟩

section
variable {P : Polygon} {W : ℕ}
/-- **A loop with bounded body costs**: an invariant indexed by the number `j` of iterations done,
the test true exactly while `j < L`, each body cost in `[Bmin, Bmax]`. -/
theorem while_range {a b : ℕ} {body : Stmt} (I : ℕ → Config → Prop)
    (L Bmin Bmax : ℕ) (htest : ∀ j d, I j d → (d.nreg a < d.nreg b ↔ j < L))
    (hwb : ∀ j d, I j d → WordsBounded W d)
    (hbody : ∀ j d, I j d → j < L →
      ∃ d' k, Exec P W body d d' k ∧ Bmin ≤ k ∧ k ≤ Bmax ∧ I (j + 1) d') :
    ∀ j d, I j d → j ≤ L →
      ∃ d' k, Exec P W (.whileLtN a b body) d d' k ∧ (Bmin + 2) * (L - j) + 2 ≤ k ∧
        k ≤ (Bmax + 2) * (L - j) + 2 ∧ I L d' := by
  intro j d hI hj
  induction hn : L - j generalizing j d with
  | zero =>
    have hjL : j = L := by omega
    subst hjL
    exact ⟨d, 2, .whileLtN_false (fun h => absurd ((htest j d hI).1 h) (lt_irrefl _))
      (hwb j d hI), by simp, by simp, hI⟩
  | succ n ih =>
    have hlt : j < L := by omega
    obtain ⟨d₁, k₁, e₁, hk1, hk2, hI₁⟩ := hbody j d hI hlt
    obtain ⟨d', k', e', hk1', hk2', hI'⟩ := ih (j + 1) d₁ hI₁ (by omega) (by omega)
    refine ⟨d', _, Exec.whileLtN_true ((htest j d hI).2 hlt) e₁ e', ?_, ?_, hI'⟩
    all_goals grind

/-- **The dedupe pass.** -/
theorem ssDedup_exec {J : Merge.Junction} {d2 RB S A₀ : ℕ} {m₀ : ℕ → ℕ}
    {L : List ℕ} {SBv B1 : ℕ} {d₀ : Config}
    (hcmp : CmpOK P W ssCmp ssBc (SsCtx J d2 RB S A₀ m₀) (ssLe P J m₀ RB S) 12000)
    (hLlen : L.length = S) (hLm : ∀ x ∈ L, x < S)
    (hLs : L.Pairwise (fun x y => KLe (ssKey P J m₀ RB x) (ssKey P J m₀ RB y)))
    (hLmem : ∀ i, i < S → d₀.nmem (SBv + i) = L.getD i 0)
    (hSB : SBv + S ≤ B1) (hS : RB + 11 * S ≤ A₀) (hAB : A₀ ≤ B1) (hroom : B1 + 10 * S + 1 ≤ W)
    (I : SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ 0 d₀) :
    ∃ d' k, Exec P W ssDedup d₀ d' k ∧ 10 * S + 2 ≤ k ∧ k ≤ 12102 * S + 2 ∧
      SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀ S d' := by
  obtain ⟨d', k, ex, h1, h2, hI⟩ := while_range (P := P) (W := W) (a := srJ) (b := gRC)
    (body := ssBody) (SsDI P W J d2 RB S A₀ m₀ L SBv B1 d₀) S 8 12100
    (fun j d h => by rw [h.qj, h.ctx.2.2.2.1])
    (fun j d h => h.wb)
    (fun j d h hj => ssBody_step hcmp hLlen hLm hLs hLmem hSB hS hAB hroom h hj)
    0 d₀ I (Nat.zero_le _)
  exact ⟨d', k, ex, by omega, by omega, hI⟩


end

end

end SweepEv

end Chazelle.Core
