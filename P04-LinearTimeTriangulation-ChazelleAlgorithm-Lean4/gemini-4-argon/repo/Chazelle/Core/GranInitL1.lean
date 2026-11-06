module

public import Chazelle.Core.GranInitHdr

/-!
# WP-F, init part 7: the chord arrays and the worklist

* `chLoop`: for every chord record `i < K`: `live i := 1`, `s0 i := up`, `s1 i := dn`
  (`chLoop_exec`);
* `stkLoop`: `stk t := t` for `t < K + D K` (`stkLoop_exec`).
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- One chord record (`r70 = i`, `r71 = CB + 5 i`, `r76 = 5`). -/
def chBody : Stmt := block [.addN 90072 90030 90070, .constN 90073 1, .storeN 90072 90073,
  .addN 90074 90071 90020, .loadN 90075 90074, .addN 90072 90031 90070, .storeN 90072 90075,
  .addN 90074 90074 90019, .loadN 90075 90074, .addN 90072 90032 90070, .storeN 90072 90075,
  .addN 90071 90071 90076, .addN 90070 90070 90019]

/-- The chord loop. -/
def chLoop : Stmt := .seq (block [.constN 90070 0, .copyN 90071 90013, .constN 90076 5])
  (.whileLtN 90070 90010 chBody)

/-- Registers written by the init loops. -/
def Binit (r : ℕ) : Bool := decide (90070 ≤ r ∧ r < 90100)

theorem wrS_chLoop : wrS Binit chLoop = true := by decide

/-- The chord-loop invariant. -/
structure ChI (W K CB : ℕ) (d : Dm) (chords : ℕ → CRec) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  i_le : c.nreg 90070 ≤ K
  ptr : c.nreg 90071 = CB + 5 * c.nreg 90070
  c76 : c.nreg 90076 = 5
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  live : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + u) = 1
  s0 : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oS0 + u) = (chords u).up
  s1 : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oS1 + u) = (chords u).dn
  mem : ∀ a, (a < d.b0 ∨ d.b0 + d.oNd0 ≤ a) → c.nmem a = c₀.nmem a

set_option maxHeartbeats 1000000 in
theorem chBody_exec {P : Polygon} {W K CB : ℕ} {d : Dm} {chords : ℕ → CRec} {c₀ c : Config}
    (hI : ChI W K CB d chords c₀ c) (hB : Bases c₀ d) (hK : d.K = K)
    (h10 : c₀.nreg 90010 = K) (h19 : c₀.nreg 90019 = 1) (h20 : c₀.nreg 90020 = 3)
    (hrec : ∀ i, i < K → c₀.nmem (CB + 5 * i + 3) = (chords i).up ∧
      c₀.nmem (CB + 5 * i + 4) = (chords i).dn)
    (hCB : CB + 5 * K ≤ d.b0) (hW : d.b0 + d.oEnd ≤ W) (ht : c.nreg 90070 < K) :
    ∃ c' k, Exec P W chBody c c' k ∧ ChI W K CB d chords c₀ c' ∧ k ≤ 13 ∧
      c'.nreg 90070 = c.nreg 90070 + 1 := by
  obtain ⟨hw, hi, hp, h76, hr, hl, hs0, hs1, hm⟩ := hI
  obtain ⟨y1, y2, y3, y4, y5, y6, -⟩ := d.lay
  have yN : d.oNd0 = 3 * d.K := rfl
  have b30 : c.nreg 90030 = d.b0 := by rw [hr _ (by decide), hB.bLive]
  have b31 : c.nreg 90031 = d.b0 + d.oS0 := by rw [hr _ (by decide), hB.bS0]
  have b32 : c.nreg 90032 = d.b0 + d.oS1 := by rw [hr _ (by decide), hB.bS1]
  have c19 : c.nreg 90019 = 1 := by rw [hr _ (by decide), h19]
  have c20 : c.nreg 90020 = 3 := by rw [hr _ (by decide), h20]
  obtain ⟨rup, rdn⟩ := hrec _ ht
  have mup : c.nmem (CB + 5 * c.nreg 90070 + 3) = (chords (c.nreg 90070)).up := by
    rw [hm _ (by left; omega), rup]
  have mdn : c.nmem (CB + 5 * c.nreg 90070 + 4) = (chords (c.nreg 90070)).dn := by
    rw [hm _ (by left; omega), rdn]
  have hEnd : d.oNd0 ≤ d.oEnd := by dm_simp; omega
  have v1 : upd c.nmem (d.b0 + c.nreg 90070) 1 (CB + 5 * c.nreg 90070 + 3) =
      (chords (c.nreg 90070)).up := by
    rw [Machine.upd_other _ _ _ (by omega), mup]
  have v2 : upd (upd c.nmem (d.b0 + c.nreg 90070) 1) (d.b0 + d.oS0 + c.nreg 90070)
      (chords (c.nreg 90070)).up (CB + 5 * c.nreg 90070 + 3 + 1) = (chords (c.nreg 90070)).dn := by
    rwa [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
  unfold chBody
  exec_block
  all_goals try (have : d.oNd0 ≤ d.oEnd := hEnd; omega)
  all_goals try (config_simp; simp only [b30, b31, b32, c19, c20, hp, h76]; omega)
  refine ⟨⟨by assumption, ?_, ?_, ?_, fun r hr' => ?_, fun u hu => ?_, fun u hu => ?_,
    fun u hu => ?_, fun a ha => ?_⟩, by omega, ?_⟩ <;>
    config_simp <;> simp only [b30, b31, b32, c19, c20, hp, h76, v1] <;>
    (try simp only [v2])
  · omega
  · omega
  · have := hr r hr'
    simp only [Binit, decide_eq_false_iff_not] at hr'
    simp only [upd]
    split_ifs <;> first | omega
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · subst hui
      rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega)]
      simp [upd]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hl u (by omega)
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · subst hui
      rw [Machine.upd_other _ _ _ (by omega)]
      simp [upd]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hs0 u (by omega)
  · config_simp at hu; simp only [c19] at hu
    by_cases hui : u = c.nreg 90070
    · subst hui
      simp [upd]
    · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
        Machine.upd_other _ _ _ (by omega)]
      exact hs1 u (by omega)
  · rw [Machine.upd_other _ _ _ (by omega), Machine.upd_other _ _ _ (by omega),
      Machine.upd_other _ _ _ (by omega)]
    exact hm a ha

theorem chLoop_exec {P : Polygon} {W K CB : ℕ} {d : Dm} {chords : ℕ → CRec} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (hK : d.K = K)
    (h10 : c₀.nreg 90010 = K) (h13 : c₀.nreg 90013 = CB) (h19 : c₀.nreg 90019 = 1)
    (h20 : c₀.nreg 90020 = 3)
    (hrec : ∀ i, i < K → c₀.nmem (CB + 5 * i + 3) = (chords i).up ∧
      c₀.nmem (CB + 5 * i + 4) = (chords i).dn)
    (hCB : CB + 5 * K ≤ d.b0) (hW : d.b0 + d.oEnd ≤ W) (hW5 : 5 ≤ W) :
    ∃ c' k, Exec P W chLoop c₀ c' k ∧ k ≤ 15 * K + 5 ∧
      (∀ u, u < K → c'.nmem (d.b0 + u) = 1 ∧ c'.nmem (d.b0 + d.oS0 + u) = (chords u).up ∧
        c'.nmem (d.b0 + d.oS1 + u) = (chords u).dn) ∧
      (∀ a, (a < d.b0 ∨ d.b0 + d.oNd0 ≤ a) → c'.nmem a = c₀.nmem a) ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W chLoop c₀ c' k ∧ k ≤ 15 * K + 5 ∧
      (∀ u, u < K → c'.nmem (d.b0 + u) = 1 ∧ c'.nmem (d.b0 + d.oS0 + u) = (chords u).up ∧
        c'.nmem (d.b0 + d.oS1 + u) = (chords u).dn) ∧
      (∀ a, (a < d.b0 ∨ d.b0 + d.oNd0 ≤ a) → c'.nmem a = c₀.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_chLoop⟩
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0, .copyN 90071 90013,
      .constN 90076 5]) c₀ c₁ k₁ ∧ k₁ = 3 ∧ ChI W K CB d chords c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun u hu => ?_,
        fun u hu => ?_, fun a _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp; rw [h13]; omega
      · config_simp
      · simp only [Binit, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · simp [upd] at hu
      · simp [upd] at hu
      · simp [upd] at hu
      · config_simp
  obtain ⟨q, q0⟩ := q
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90010)
    (body := chBody) (ChI W K CB d chords c₀) (fun c => K - c.nreg 90070) 13 (fun _ h => h.wb)
    (fun c I ht => by
      have t : c.nreg 90070 < K := by rwa [I.regs 90010 (by decide), h10] at ht
      obtain ⟨c', k, e, I', hk, hi⟩ := chBody_exec (P := P) I hB hK h10 h19 h20 hrec hCB hW t
      exact ⟨c', k, e, I', hk, by omega⟩) q
  have hK' : c'.nreg 90070 = K := by
    rw [I'.regs 90010 (by decide), h10] at hx; have := I'.i_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => ⟨I'.live u (by omega), I'.s0 u (by omega),
    I'.s1 u (by omega)⟩, I'.mem⟩
  rw [q0] at hk
  omega

/-! ## The worklist -/

/-- One stack entry (`r70 = t`). -/
def stkBody : Stmt := block [.addN 90072 90043 90070, .storeN 90072 90070, .addN 90070 90070 90019]

/-- `stk t := t` for `t < K + D K` (`r77`). -/
def stkLoop : Stmt := .seq (block [.constN 90070 0, .addN 90077 90010 90026])
  (.whileLtN 90070 90077 stkBody)

theorem wrS_stkLoop : wrS Binit stkLoop = true := by decide

/-- The stack-loop invariant. -/
structure StkI (W : ℕ) (d : Dm) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  t_le : c.nreg 90070 ≤ d.cap
  cap : c.nreg 90077 = d.cap
  regs : ∀ r, Binit r = false → c.nreg r = c₀.nreg r
  stk : ∀ u, u < c.nreg 90070 → c.nmem (d.b0 + d.oStk + u) = u
  mem : ∀ a, (a < d.b0 + d.oStk ∨ d.b0 + d.oTmp ≤ a) → c.nmem a = c₀.nmem a

theorem stkLoop_exec {P : Polygon} {W : ℕ} {d : Dm} {c₀ : Config}
    (hw : WordsBounded W c₀) (hB : Bases c₀ d) (h10 : c₀.nreg 90010 = d.K)
    (h26 : c₀.nreg 90026 = d.D * d.K) (h19 : c₀.nreg 90019 = 1) (hW : d.b0 + d.oEnd ≤ W) :
    ∃ c' k, Exec P W stkLoop c₀ c' k ∧ k ≤ 5 * d.cap + 4 ∧
      (∀ u, u < d.cap → c'.nmem (d.b0 + d.oStk + u) = u) ∧
      (∀ a, (a < d.b0 + d.oStk ∨ d.b0 + d.oTmp ≤ a) → c'.nmem a = c₀.nmem a) ∧
      FrameS Binit c₀ c' := by
  suffices hh : ∃ c' k, Exec P W stkLoop c₀ c' k ∧ k ≤ 5 * d.cap + 4 ∧
      (∀ u, u < d.cap → c'.nmem (d.b0 + d.oStk + u) = u) ∧
      (∀ a, (a < d.b0 + d.oStk ∨ d.b0 + d.oTmp ≤ a) → c'.nmem a = c₀.nmem a) by
    obtain ⟨c', k, e, h1, h2, h3⟩ := hh
    exact ⟨c', k, e, h1, h2, h3, exec_frameS e wrS_stkLoop⟩
  obtain ⟨y1, y2, y3, y4, -⟩ := d.lay
  have hcap : d.cap = d.K + d.D * d.K := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, q, q0⟩ : ∃ c₁ k₁, Exec P W (block [.constN 90070 0,
      .addN 90077 90010 90026]) c₀ c₁ k₁ ∧ k₁ = 2 ∧ StkI W d c₀ c₁ ∧ c₁.nreg 90070 = 0 := by
    exec_block
    · omega
    · config_simp; rw [h10, h26]; omega
    · refine ⟨rfl, ⟨by assumption, ?_, ?_, fun r hr => ?_, fun u hu => ?_, fun a _ => rfl⟩, ?_⟩
      · config_simp; omega
      · config_simp; rw [h10, h26, hcap]
      · simp only [Binit, decide_eq_false_iff_not] at hr
        config_simp; simp only [upd]; split_ifs <;> first | rfl | omega
      · simp [upd] at hu
      · config_simp
  obtain ⟨c', k, e, I', hx, hk⟩ := Exec.whileLtN_bounded (P := P) (a := 90070) (b := 90077)
    (body := stkBody) (StkI W d c₀) (fun c => d.cap - c.nreg 90070) 3 (fun _ h => h.wb)
    (fun c I ht => by
      obtain ⟨hwc, hle, hc77, hr, hs, hm⟩ := I
      rw [hc77] at ht
      have b43 : c.nreg 90043 = d.b0 + d.oStk := by rw [hr _ (by decide), hB.bStk]
      have c19 : c.nreg 90019 = 1 := by rw [hr _ (by decide), h19]
      unfold stkBody
      exec_block
      · rw [b43]; omega
      · config_simp; rw [c19]; omega
      · refine ⟨⟨by assumption, ?_, ?_, fun r hr' => ?_, fun u hu => ?_, fun a ha => ?_⟩, by omega,
          ?_⟩
        · config_simp; rw [c19]; omega
        · config_simp; exact hc77
        · simp only [Binit, decide_eq_false_iff_not] at hr'
          config_simp; simp only [upd]; split_ifs <;> first | omega | exact hr r (by simp [Binit]; omega)
        · config_simp at hu; rw [c19] at hu
          config_simp; rw [b43]
          by_cases hut : u = c.nreg 90070
          · rw [hut]; simp
          · rw [Machine.upd_other _ _ _ (by omega)]; exact hs u (by omega)
        · config_simp; rw [b43, Machine.upd_other _ _ _ (by omega)]; exact hm a ha
        · config_simp; rw [c19]; omega) q
  have hfull : c'.nreg 90070 = d.cap := by rw [I'.cap] at hx; have := I'.t_le; omega
  refine ⟨c', _, .seq e₁ e, ?_, fun u hu => I'.stk u (by omega), I'.mem⟩
  rw [q0] at hk
  omega

end

end Gran

end Chazelle.Core
