module

public import Chazelle.Core.OraclePrepArr
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics

/-!
# Lemma 3.6 (WP-H), preprocessing part 7: the inner (star) chords

The spine position `p < A` is the arc `σ p` (the arc-sequence table), of region `ρ p`.

* `fpos ρ p`: the first spine position of the region of `p`; `starOf ρ p`: the star chord
  `(fpos ρ p, p)` when it is not a spine edge; `starList ρ A`: the inner chords
  (`emitted (starOf ρ) A`), and their properties (`starList_nodup`, `mem_starList`).
* `frS`: the table `FR[r]` of the first spine position of each region, by stores in decreasing
  order of positions (`frS_exec`);
* `iS`: the allocation of the two chord arrays (capacity `3 A + 5` each) and the emission of the
  star chords into them (`iS_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-! ## The star chords -/

/-- The first spine position with the region of `p`. -/
noncomputable def fpos (ρ : ℕ → ℕ) (p : ℕ) : ℕ := by
  classical
  exact Nat.find (⟨p, rfl⟩ : ∃ q, ρ q = ρ p)

theorem fpos_spec (ρ : ℕ → ℕ) (p : ℕ) :
    ρ (fpos ρ p) = ρ p ∧ fpos ρ p ≤ p ∧ ∀ q, ρ q = ρ p → fpos ρ p ≤ q := by
  classical
  unfold fpos
  refine ⟨Nat.find_spec (⟨p, rfl⟩ : ∃ q, ρ q = ρ p), Nat.find_min' _ rfl, fun q hq => ?_⟩
  exact Nat.find_min' _ hq

open Classical in
/-- The star chord of spine position `p`. -/
noncomputable def starOf (ρ : ℕ → ℕ) (p : ℕ) : Option (ℕ × ℕ) :=
  if fpos ρ p + 2 ≤ p then some (fpos ρ p, p) else none

/-- **The inner chords.** -/
noncomputable def starList (ρ : ℕ → ℕ) (A : ℕ) : List (ℕ × ℕ) := emitted (starOf ρ) A

theorem mem_starList {ρ : ℕ → ℕ} {A : ℕ} {c : ℕ × ℕ} :
    c ∈ starList ρ A ↔ c.2 < A ∧ c.1 = fpos ρ c.2 ∧ fpos ρ c.2 + 2 ≤ c.2 := by
  unfold starList
  rw [mem_emitted]
  constructor
  · rintro ⟨j, hj, hφ⟩
    unfold starOf at hφ
    split_ifs at hφ with h
    cases hφ
    exact ⟨hj, rfl, h⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨c.2, h1, ?_⟩
    unfold starOf
    rw [ite_eq_left h3, ← h2]

/-- Emitted pairs whose second component is the index have no repetition. -/
theorem emitted_nodup {φ : ℕ → Option (ℕ × ℕ)} (h : ∀ i x, φ i = some x → x.2 = i) (n : ℕ) :
    (emitted φ n).Nodup := by
  unfold emitted
  refine List.Nodup.filterMap (fun a a' b hb hb' => ?_) List.nodup_range
  rw [← h a b hb, ← h a' b hb']

theorem starList_nodup (ρ : ℕ → ℕ) (A : ℕ) : (starList ρ A).Nodup :=
  emitted_nodup (fun i x hx => by
    unfold starOf at hx; split_ifs at hx; cases hx; rfl) A

theorem starList_length (ρ : ℕ → ℕ) (A : ℕ) : (starList ρ A).length ≤ A :=
  emitted_length_le _ A

/-- **The star chords are complete**: every spine position is its region's first, or joined to it
by a star chord or a spine edge. -/
theorem starList_complete (ρ : ℕ → ℕ) {A p : ℕ} (hp : p < A) :
    fpos ρ p = p ∨ (fpos ρ p, p) ∈ starList ρ A ∨ p = fpos ρ p + 1 := by
  have := (fpos_spec ρ p).2.1
  by_cases h : fpos ρ p + 2 ≤ p
  · exact Or.inr (Or.inl (mem_starList.2 ⟨hp, rfl, h⟩))
  · omega

/-! ## The region of a spine position -/

/-- `110065 := ρ p` for the spine position `p` in `110063`: `AB[5 SB[p]]` (scratch `110064`). -/
def rgS : Stmt :=
  block [.addN 110064 120046 110063, .loadN 110064 110064, .addN 110065 110064 110064,
    .addN 110065 110065 110065, .addN 110065 110065 110064, .addN 110065 110065 120044,
    .loadN 110065 110065]

/-- The memory facts of the arc and sequence tables. -/
structure RgMem (m : ℕ → ℕ) (AB SB A : ℕ) (σ rg : ℕ → ℕ) : Prop where
  seq : ∀ p, p < A → m (SB + p) = σ p
  σ_lt : ∀ p, p < A → σ p < A
  reg : ∀ j, j < A → m (AB + 5 * j) = rg j

theorem rgS_exec {P : Polygon} {W : ℕ} {d : Config} (hwd : WordsBounded W d) {AB SB A p : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem d.nmem AB SB A σ rg) (hAB : d.nreg 120044 = AB)
    (hSB : d.nreg 120046 = SB) (hp : d.nreg 110063 = p) (hpA : p < A) (hSW : SB + A ≤ W)
    (hAW : AB + 5 * A ≤ W) :
    ∃ d' k, Exec P W rgS d d' k ∧ k = 7 ∧
      FrameB (fun r => decide (r = 110064 ∨ r = 110065)) d d' ∧ d'.nreg 110065 = rg (σ p) := by
  have hσ := hM.σ_lt p hpA
  have hs := hM.seq p hpA
  have hr := hM.reg (σ p) hσ
  obtain ⟨d', k, e, hk, v⟩ : ∃ d' k, Exec P W rgS d d' k ∧ k = 7 ∧ d'.nreg 110065 = rg (σ p) := by
    unfold rgS
    exec_block
    · rwo [hSB, hp]
    · config_simp; rwo [hSB, hp, hs]
    · config_simp; rwo [hSB, hp, hs]
    · config_simp; rwo [hSB, hp, hs]
    · config_simp; rwo [hSB, hp, hs, hAB]
    · refine ⟨rfl, ?_⟩
      config_simp; rw [hSB, hp, hs, hAB, ← hr]; congr 1; ring
  exact ⟨d', k, e, hk, exec_frameB e (by decide), v⟩

/-! ## The first position of each region -/

/-- The body: `p := A - 1 - i`, address `FR + ρ p`, value `p`. -/
def frBody : Stmt :=
  .seq (block [.subN 110063 120030 120011, .subN 110063 110063 110069])
    (.seq rgS (block [.addN 110067 110060 110065, .copyN 110066 110063]))

/-- **The table of first positions** at the allocator (`110060`), `R` words (`R` in `110061`). -/
def frS : Stmt :=
  .seq (block [.addN 110062 120014 120048, .loadN 110061 110062, .copyN 110060 9999,
      .addN 9999 9999 110061])
    (scatS 110069 120030 120011 110067 110066 frBody)

/-- The registers written by `frS`. -/
def BFR (r : ℕ) : Bool := decide (r = 9999) || decide (110060 ≤ r ∧ r ≤ 110069)

theorem frS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {NB AB SB A R A₀ : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg) (hNB : c.nreg 120014 = NB)
    (h2 : c.nreg 120048 = 2) (hR : c.nmem (NB + 2) = R) (hAB : c.nreg 120044 = AB)
    (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hAl : c.nreg 9999 = A₀) (hNBA : NB + 2 < A₀) (hSA : SB + A ≤ A₀) (hABA : AB + 5 * A ≤ A₀)
    (hρR : ∀ p, p < A → rg (σ p) < R) (hW : A₀ + R + A ≤ W) :
    ∃ c' k, Exec P W frS c c' k ∧ k ≤ 16 * A + 8 ∧ PF BFR A₀ c c' ∧ c'.nreg 9999 = A₀ + R ∧
      c'.nreg 110060 = A₀ ∧
      ∀ p, p < A → c'.nmem (A₀ + rg (σ p)) = fpos (fun q => rg (σ q)) p := by
  set ρ : ℕ → ℕ := fun q => rg (σ q) with hρ
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 110062 120014 120048,
      .loadN 110061 110062, .copyN 110060 9999, .addN 9999 9999 110061]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg = upd (upd (upd (upd c.nreg 110062 (NB + 2)) 110061 R) 110060 A₀) 9999 (A₀ + R) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · rwo [hNB, h2]
    · config_simp; rwo [hNB, h2, hR, hAl]
    · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [hNB, h2, hR, hAl]
  have hr₁ : ∀ r, BFR r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp [BFR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp [upd]; split_ifs <;> first | omega
  have v60 : c₁.nreg 110060 = A₀ := by rw [n₁]; config_simp
  have v44 : c₁.nreg 120044 = AB := by rw [hr₁ _ (by decide), hAB]
  have v46 : c₁.nreg 120046 = SB := by rw [hr₁ _ (by decide), hSB]
  have v30 : c₁.nreg 120030 = A := by rw [hr₁ _ (by decide), hA]
  have v11 : c₁.nreg 120011 = 1 := by rw [hr₁ _ (by decide), h1]
  let K : ℕ → Bool := fun r => decide (r = 110060) || decide (r = 120044) || decide (r = 120046) ||
    decide (r = 120030) || decide (r = 120011)
  let J : Config → Prop := JK c₁ K A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, mm₂, rm₂, o₂, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 110069) (rn := 120030) (r1 := 120011) (ra := 110067) (rv := 110066) (body := frBody)
    (B := fun r => decide (110063 ≤ r ∧ r ≤ 110067)) (by decide) (by decide) (by decide)
    (by decide) (by decide) J A₀
    (fun d d' hJ hr hm => JK.stable (rs := [110069]) (fun r hr' => by
      simp [K, Bool.or_eq_true, decide_eq_true_eq] at hr'
      rcases hr' with (((rfl | rfl) | rfl) | rfl) | rfl <;> decide) hJ
      (fun r a b => hr r a (by simpa using b)) hm)
    (n := A) (κ := 12) (fun i => A₀ + ρ (A - 1 - i)) (fun i => A - 1 - i) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g60 : d.nreg 110060 = A₀ := by rw [hJ.1 _ (by decide), v60]
      have g44 : d.nreg 120044 = AB := by rw [hJ.1 _ (by decide), v44]
      have g46 : d.nreg 120046 = SB := by rw [hJ.1 _ (by decide), v46]
      have g30 : d.nreg 120030 = A := by rw [hJ.1 _ (by decide), v30]
      have g11 : d.nreg 120011 = 1 := by rw [hJ.1 _ (by decide), v11]
      have hMd : RgMem d.nmem AB SB A σ rg := ⟨fun p hp => by
          rw [hJ.2 _ (by omega), m₁]; exact hM.seq p hp, hM.σ_lt,
        fun j hj => by rw [hJ.2 _ (by omega), m₁]; exact hM.reg j hj⟩
      obtain ⟨d₁, k₁', e₁', hk₁', n₁', -⟩ : ∃ d₁ k₁', Exec P W
          (block [.subN 110063 120030 120011, .subN 110063 110063 110069]) d d₁ k₁' ∧ k₁' = 2 ∧
          d₁.nreg = upd d.nreg 110063 (A - 1 - i) ∧ True := by
        exec_block
        refine ⟨rfl, ?_, trivial⟩
        config_simp; rw [g30, g11, hri]
      have f₁' : ∀ r, r ≠ 110063 → d₁.nreg r = d.nreg r := fun r hr => by
        rw [n₁']; exact upd_other _ _ _ hr
      have hm₁' : d₁.nmem = d.nmem :=
        (exec_frameB e₁' (B := fun r => decide (r = 110063)) (by decide)).2.2.1
      obtain ⟨d₂, k₂', e₂', hk₂', f₂', v₂'⟩ := rgS_exec (P := P) e₁'.wb_right (p := A - 1 - i)
        (by rwx [hm₁']) (by rw [f₁' _ (by decide), g44])
        (by rw [f₁' _ (by decide), g46]) (by rw [n₁']; config_simp) (by omega) (by omega)
        (by omega)
      have hρl := hρR (A - 1 - i) (by omega)
      obtain ⟨d₃, k₃', e₃', hk₃', v67, v66⟩ : ∃ d₃ k₃', Exec P W
          (block [.addN 110067 110060 110065, .copyN 110066 110063]) d₂ d₃ k₃' ∧ k₃' = 2 ∧
          d₃.nreg 110067 = A₀ + ρ (A - 1 - i) ∧ d₃.nreg 110066 = A - 1 - i := by
        have a60 : d₂.nreg 110060 = A₀ := by rw [f₂'.1 _ (by decide), f₁' _ (by decide), g60]
        have a63 : d₂.nreg 110063 = A - 1 - i := by rw [f₂'.1 _ (by decide), n₁']; config_simp
        have w₂ := e₂'.wb_right
        exec_block
        · rwo [a60, v₂']
        · refine ⟨rfl, ?_, ?_⟩
          · config_simp; rw [a60, v₂']
          · config_simp; rw [a63]
      have ex : Exec P W frBody d d₃ _ := .seq e₁' (.seq e₂' e₃')
      exact ⟨d₃, _, ex, by omega, exec_frameB ex (by decide), v67, v66⟩)
    e₁.wb_right (JK.refl _ _ _) v30 v11 (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a ha => by rw [rm₂, rm₁], by rw [o₂, o₁]⟩, ?_, ?_, fun p hp => ?_⟩
  · simp [BFR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [r₂ r (by sio) (by omega)]; exact hr₁ r (by sio [BFR])
  · rw [rr₂ r (by sio only [BFR, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢),
      rr₁]
  · rw [mm₂, scat_below (fun i _ => by omega) ha, m₁]
  · rw [r₂ _ (by decide) (by decide), n₁]; config_simp
  · rw [r₂ _ (by decide) (by decide), v60]
  · -- the last store at the region of `p` is that of its first position
    obtain ⟨hf1, hf2, hf3⟩ := fpos_spec ρ p
    set q := fpos ρ p
    have hq : q < A := by omega
    have := scat_at (m := c₁.nmem) (g := fun i => A₀ + ρ (A - 1 - i)) (f := fun i => A - 1 - i)
      (n := A) (i := A - 1 - q) (by omega) (fun j hj hij e => by
        have e' : ρ (A - 1 - j) = ρ p := by
          have : ρ (A - 1 - j) = ρ (A - 1 - (A - 1 - q)) := by omega
          rw [this, show A - 1 - (A - 1 - q) = q by omega, hf1]
        have := hf3 _ e'
        omega)
    rw [show A - 1 - (A - 1 - q) = q by omega, hf1] at this
    rw [mm₂, this]

/-! ## The emission of the star chords -/

/-- The body: the region of `p`, its first position `f = FR[ρ p]`, the flag `f + 2 ≤ p`. -/
def iBody : Stmt :=
  .seq (.instr (.copyN 110063 110079))
    (.seq rgS (.seq (block [.addN 110070 110060 110065, .loadN 110076 110070, .copyN 110077 110063,
        .addN 110071 110076 120011])
      (.ifLtN 110071 110063 (.instr (.constN 110078 1)) (.instr (.constN 110078 0)))))

/-- The capacity of the chord arrays. -/
def chCap (A : ℕ) : ℕ := 3 * A + 5

/-- **The inner chords**: two chord arrays of capacity `3 A + 5` at the allocator (bases `110072`,
`110073`, capacity `110080`), and the star chords emitted into them (count `110074`). -/
def iS : Stmt :=
  .seq (block [.copyN 110072 9999, .addN 110073 120030 120030, .addN 110073 110073 120030,
      .constN 110071 5, .addN 110073 110073 110071, .copyN 110080 110073,
      .addN 110073 110073 110072, .addN 9999 110073 110080, .constN 110074 0])
    (emitS 110079 120030 120011 110078 110076 110077 110072 110073 110074 110075 iBody)

/-- The registers written by `iS`. -/
def BIS (r : ℕ) : Bool := decide (r = 9999) || decide (110063 ≤ r ∧ r ≤ 110080)

theorem iS_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) {AB SB A R FR A₀ : ℕ}
    {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg) (hAB : c.nreg 120044 = AB)
    (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A) (h1 : c.nreg 120011 = 1)
    (hFR : c.nreg 110060 = FR) (hAl : c.nreg 9999 = A₀) (hSA : SB + A ≤ A₀) (hABA : AB + 5 * A ≤ A₀)
    (hFRA : FR + R ≤ A₀) (hρR : ∀ p, p < A → rg (σ p) < R)
    (hfr : ∀ p, p < A → c.nmem (FR + rg (σ p)) = fpos (fun q => rg (σ q)) p)
    (hW : A₀ + 2 * chCap A ≤ W) :
    ∃ c' k, Exec P W iS c c' k ∧ k ≤ 30 * A + 15 ∧ PF BIS A₀ c c' ∧
      c'.nreg 9999 = A₀ + 2 * chCap A ∧ c'.nreg 110072 = A₀ ∧ c'.nreg 110073 = A₀ + chCap A ∧
      c'.nreg 110080 = chCap A ∧
      c'.nreg 110074 = (starList (fun q => rg (σ q)) A).length ∧
      PairsAt c'.nmem A₀ (A₀ + chCap A) (starList (fun q => rg (σ q)) A) := by
  set ρ : ℕ → ℕ := fun q => rg (σ q) with hρ
  obtain ⟨c₁, k₁, e₁, hk₁, n₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 110072 9999,
      .addN 110073 120030 120030, .addN 110073 110073 120030, .constN 110071 5,
      .addN 110073 110073 110071, .copyN 110080 110073, .addN 110073 110073 110072,
      .addN 9999 110073 110080, .constN 110074 0]) c c₁ k₁ ∧ k₁ = 9 ∧
      c₁.nreg = upd (upd (upd (upd (upd (upd c.nreg 110072 A₀) 110073 (A₀ + chCap A)) 110071 5)
        110080 (chCap A)) 9999 (A₀ + 2 * chCap A)) 110074 0 ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold chCap at hW ⊢
    exec_block
    · config_simp; rwo [hA]
    · config_simp; rwo [hA]
    · omega
    · config_simp; rwo [hA]
    · config_simp; rwo [hA, hAl]
    · config_simp; rwo [hA, hAl]
    · omega
    · refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
      config_simp; rw [hA, hAl]
      funext r; simp [upd]; split_ifs <;> first | omega
  have hr₁ : ∀ r, BIS r = false → c₁.nreg r = c.nreg r := fun r hr => by
    simp [BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [n₁]; simp [upd]; split_ifs <;> first | omega
  have v72 : c₁.nreg 110072 = A₀ := by rw [n₁]; config_simp
  have v73 : c₁.nreg 110073 = A₀ + chCap A := by rw [n₁]; config_simp
  have v74 : c₁.nreg 110074 = 0 := by rw [n₁]; config_simp
  have v80 : c₁.nreg 110080 = chCap A := by rw [n₁]; config_simp
  have v9 : c₁.nreg 9999 = A₀ + 2 * chCap A := by rw [n₁]; config_simp
  have v60 : c₁.nreg 110060 = FR := by rw [hr₁ _ (by decide), hFR]
  have v44 : c₁.nreg 120044 = AB := by rw [hr₁ _ (by decide), hAB]
  have v46 : c₁.nreg 120046 = SB := by rw [hr₁ _ (by decide), hSB]
  have v30 : c₁.nreg 120030 = A := by rw [hr₁ _ (by decide), hA]
  have v11 : c₁.nreg 120011 = 1 := by rw [hr₁ _ (by decide), h1]
  let K : ℕ → Bool := fun r => decide (r = 110060) || decide (r = 120044) || decide (r = 120046) ||
    decide (r = 120011)
  let J : Config → Prop := JK c₁ K A₀
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, cnt₂, pr₂, mm₂, rm₂, o₂, -⟩ := emitS_exec (P := P) (W := W)
    (ri := 110079) (rn := 120030) (r1 := 120011) (rf := 110078) (rv1 := 110076) (rv2 := 110077)
    (rR1 := 110072) (rR2 := 110073) (rc := 110074) (rt := 110075) (body := iBody)
    (B := fun r => decide (110063 ≤ r ∧ r ≤ 110071) || decide (110076 ≤ r ∧ r ≤ 110078))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (R1 := A₀) (c₀ := 0) J
    (fun d d' hJ hr hm => JK.stable (rs := [110079, 110074, 110075]) (fun r hr' => by
      simp [K, Bool.or_eq_true, decide_eq_true_eq] at hr'
      rcases hr' with ((rfl | rfl) | rfl) | rfl <;> decide) hJ
      (fun r a b => hr r a (by sio at b) (by sio at b) (by sio at b))
      (fun a ha => hm a (Or.inl (by omega))))
    (n := A) (κ := 20) (starOf ρ)
    (fun i d hi hJ hwd hri => by
      have g60 : d.nreg 110060 = FR := by rw [hJ.1 _ (by decide), v60]
      have g44 : d.nreg 120044 = AB := by rw [hJ.1 _ (by decide), v44]
      have g46 : d.nreg 120046 = SB := by rw [hJ.1 _ (by decide), v46]
      have hMd : RgMem d.nmem AB SB A σ rg := ⟨fun p hp => by
          rw [hJ.2 _ (by omega), m₁]; exact hM.seq p hp, hM.σ_lt,
        fun j hj => by rw [hJ.2 _ (by omega), m₁]; exact hM.reg j hj⟩
      have e₀ := Exec.copyN (P := P) hwd 110063 110079
      set d₀ : Config := { d with nreg := upd d.nreg 110063 (d.nreg 110079) } with hd₀
      have f₀ : ∀ r, r ≠ 110063 → d₀.nreg r = d.nreg r := fun r hr => by
        rw [hd₀]; exact upd_other _ _ _ hr
      obtain ⟨d₂, k₂', e₂', hk₂', f₂', v₂'⟩ := rgS_exec (P := P) e₀.wb_right (p := i)
        hMd (by rw [f₀ _ (by decide), g44]) (by rw [f₀ _ (by decide), g46])
        (by rw [hd₀]; config_simp; exact hri) hi (by omega) (by omega)
      have hρl : ρ i < R := hρR i hi
      have hρl' : rg (σ i) < R := hρR i hi
      have hfp : d₂.nmem (FR + ρ i) = fpos ρ i := by
        rw [f₂'.2.2.1, show d₀.nmem = d.nmem from rfl, hJ.2 _ (by omega), m₁]; exact hfr i hi
      have a60 : d₂.nreg 110060 = FR := by rw [f₂'.1 _ (by decide), f₀ _ (by decide), g60]
      have a63 : d₂.nreg 110063 = i := by rw [f₂'.1 _ (by decide), hd₀]; config_simp; exact hri
      have a11 : d₂.nreg 120011 = 1 := by
        rw [f₂'.1 _ (by decide), f₀ _ (by decide), hJ.1 _ (by decide), v11]
      have hfi := (fpos_spec ρ i).2.1
      have w₂ := e₂'.wb_right
      obtain ⟨d₃, k₃', e₃', hk₃', v76, v77, v71, v63⟩ : ∃ d₃ k₃', Exec P W
          (block [.addN 110070 110060 110065, .loadN 110076 110070, .copyN 110077 110063,
            .addN 110071 110076 120011]) d₂ d₃ k₃' ∧ k₃' = 4 ∧
          d₃.nreg 110076 = fpos ρ i ∧ d₃.nreg 110077 = i ∧ d₃.nreg 110071 = fpos ρ i + 1 ∧
          d₃.nreg 110063 = i := by
        exec_block
        · rwo [a60, v₂']
        · config_simp; rwo [a60, v₂', hfp, a11]
        · refine ⟨rfl, ?_, ?_, ?_, ?_⟩
          · config_simp; rw [a60, v₂', hfp]
          · config_simp; rw [a63]
          · config_simp; rw [a60, v₂', hfp, a11]
          · config_simp; exact a63
      have w₃ := e₃'.wb_right
      have hcase : ∃ d₄ k₄', Exec P W (.ifLtN 110071 110063 (.instr (.constN 110078 1))
          (.instr (.constN 110078 0))) d₃ d₄ k₄' ∧ k₄' ≤ 3 ∧
          d₄.nreg 110078 = (if fpos ρ i + 2 ≤ i then 1 else 0) ∧
          (∀ r, r ≠ 110078 → d₄.nreg r = d₃.nreg r) := by
        by_cases h : fpos ρ i + 2 ≤ i
        · have ht : d₃.nreg 110071 < d₃.nreg 110063 := by rwo [v71, v63]
          exact ⟨_, _, .ifLtN_true ht (Exec.constN w₃ 110078 1 (by omega)), by omega,
            by rw [ite_eq_left h]; config_simp, fun r hr => by config_simp; rw [upd_other _ _ _ hr]⟩
        · have ht : ¬ d₃.nreg 110071 < d₃.nreg 110063 := by rwo [v71, v63]
          exact ⟨_, _, .ifLtN_false ht (Exec.constN w₃ 110078 0 (Nat.zero_le _)), by omega,
            by rw [ite_eq_right h]; config_simp, fun r hr => by config_simp; rw [upd_other _ _ _ hr]⟩
      obtain ⟨d₄, k₄', e₄', hk₄', v78, r₄⟩ := hcase
      have ex : Exec P W iBody d d₄ _ := .seq e₀ (.seq e₂' (.seq e₃' e₄'))
      refine ⟨d₄, _, ex, by omega, exec_frameB ex (by decide), fun hn => ?_, fun x hx => ?_⟩
      · unfold starOf at hn
        split_ifs at hn with h
        rw [v78, ite_eq_right h]
      · unfold starOf at hx
        split_ifs at hx with h
        cases hx
        exact ⟨by rw [v78, ite_eq_left h], by rw [r₄ _ (by decide), v76],
          by rw [r₄ _ (by decide), v77]⟩)
    e₁.wb_right (JK.refl _ _ _) v30 v11 v72 v73 v74
    (by ufo chCap) (by ufo chCap at hW ⊢)
  rw [Nat.zero_add] at cnt₂
  simp [Nat.add_zero] at pr₂
  refine ⟨c₂, _, .seq e₁ e₂, by nlinarith, ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_,
    fun a ha => by rw [rm₂, rm₁], by rw [o₂, o₁]⟩, ?_, ?_, ?_, ?_, cnt₂, pr₂⟩
  · simp [BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
    rw [r₂ r (by sio) (by omega) (by omega) (by omega)]; exact hr₁ r (by sio [BIS])
  · rw [rr₂ r (by sio only [BIS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢),
      rr₁]
  · rw [mm₂ a (Or.inl (by omega)), m₁]
  · rw [r₂ _ (by decide) (by decide) (by decide) (by decide), v9]
  · rw [r₂ _ (by decide) (by decide) (by decide) (by decide), v72]
  · rw [r₂ _ (by decide) (by decide) (by decide) (by decide), v73]
  · rw [r₂ _ (by decide) (by decide) (by decide) (by decide), v80]

end

end OracleR

end Chazelle.Core
