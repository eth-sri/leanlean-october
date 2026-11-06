module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRSplF
public import Chazelle.Core.DownPhaseDrvRPad

/-!
# Down-phase driver (RAM side): the splice, tail

The program **`splS sB`** and **`splT_exec`**: from the configuration after the sorted buckets,
the merge with `E` (`splC`), the padding from `B'` (`padS 210026`, so that the step count covers
everything allocated since `B'`), the sorted build `sB` (`SortedMeets`) and the outputs.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK
open BuildNF (codeLe)

@[expose] public section

/-- The tail of the splice: merge, padding, sorted build, outputs. -/
def splT (sB : Stmt) : Stmt := .seq splC (.seq (padS 210026) (.seq spl7 (.seq sB spl8)))

/-- **The splice** with the sorted build `sB`. -/
def splS (sB : Stmt) : Stmt :=
  .seq (.seq spl0 (.seq cpS (.seq spl1 cpS)))
    (.seq (.seq spl2 (.seq DownNF.phaseAS spl3))
      (.seq (.seq bktS (.seq (.instr (.constN 210050 0)) bsLoop)) (splT sB)))

theorem wrM_spl7 : wrM (fun r => decide (40000 ≤ r ∧ r ≤ 40004)) spl7 = true := by decide
theorem wrM2_spl7 : wrM2 (fun r => decide (40000 ≤ r ∧ r ≤ 40004)) (fun _ => false) spl7 = true := by
  decide
theorem wrM_spl8 : wrM (fun r => decide (210002 ≤ r ∧ r ≤ 210005)) spl8 = true := by decide
theorem wrM2_spl8 :
    wrM2 (fun r => decide (210002 ≤ r ∧ r ≤ 210005)) (fun _ => false) spl8 = true := by decide

/-- Registers of `bDownDrv` are outside the bands of the sorted build. -/
theorem band21_notin {r : ℕ} (h1 : 210000 ≤ r) (h2 : r < 220000) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) := by
  core_grind

/-- The cost of the tail (`A₀` the start of `L'`, `A` the allocation pointer on entry). -/
def splTCost (κB K K₂ A₀ A : ℕ) : ℕ :=
  splCCost K K₂ + 3 * (A - A₀ + 4 * (K + K₂)) + 12 + κB * (K + K₂ + 1)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The tail of the splice.** -/
theorem splT_exec {sB : Stmt} {κB : ℕ} (hB : SortedMeets sB κB) (hG : GoodEnv P)
    (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {D T SE Rb A₀ : ℕ} {M : Model} {L L₂ : List (ℕ × ℕ × ℕ)} {E E₂ : List ℕ}
    (h01 : c.nreg 210001 = D) (h25 : c.nreg 210025 = L.length + L₂.length)
    (h26 : c.nreg 210026 = A₀) (h27 : c.nreg 210027 = 2 * L.length)
    (h28 : c.nreg 210028 = 2 * L₂.length) (h29 : c.nreg 210029 = 2 * (L.length + L₂.length))
    (h04 : c.nreg 210004 = SE) (h48 : c.nreg 210048 = Rb) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T)
    (h42' : c.nreg 42001 = 2 * (L.length + L₂.length))
    (hA₀ : A₀ + 3 * (L.length + L₂.length) ≤ c.nreg ALLOC)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hgood : GoodModel M) (hok : ChordTriplesOK M (Qof P) (L ++ L₂))
    (hCL : ChordListAt c.nmem A₀ (L ++ L₂)) (hrec : RecsAt c.nmem T (L ++ L₂))
    (hT : T + 8 * (L.length + L₂.length) ≤ c.nreg ALLOC)
    (hE : seg c.nmem SE (2 * L.length) = E) (hSE : SE + 2 * L.length ≤ c.nreg ALLOC)
    (hE₂ : seg c.nmem Rb (2 * L₂.length) = E₂) (hRb : Rb + 2 * L₂.length ≤ c.nreg ALLOC)
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M (Qof P) L))
    (hperm₂ : E₂.Perm ((List.range (2 * L₂.length)).map (2 * L.length + ·)))
    (hsort₂ : E₂.Pairwise (codeLe M (Qof P) (L ++ L₂)))
    (hroom : c.nreg ALLOC + 8 * (L.length + L₂.length) + splCCost L.length L₂.length +
      κB * (L.length + L₂.length + 1) + 1 ≤ W) :
    ∃ c' k, Exec P W (splT sB) c c' k ∧
      k ≤ splTCost κB L.length L₂.length A₀ (c.nreg ALLOC) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A₀ + k ∧
      c'.nreg 210002 = A₀ ∧ c'.nreg 210003 = L.length + L₂.length ∧
      c.nreg ALLOC ≤ c'.nreg 210004 ∧
      c'.nreg 210004 + 2 * (L.length + L₂.length) ≤ c'.nreg ALLOC ∧
      seg c'.nmem (c'.nreg 210004) (2 * (L.length + L₂.length)) =
        DownDrv.splice M (Qof P) (L ++ L₂) E E₂ ∧
      c.nreg ALLOC ≤ c'.nreg 210005 ∧
      NFWithin c'.nmem (c'.nreg 210005) (c'.nreg ALLOC)
        (BuildNF.buildNF M (Qof P) (L ++ L₂) (DownDrv.splice M (Qof P) (L ++ L₂) E E₂)) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bs56 r = false → Bcp r = false →
        (r < 210002 ∨ 210005 < r) → r ≠ 210068 → r ≠ 210069 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output := by
  set K := L.length with hKd
  set K₂ := L₂.length with hK₂d
  set A₃ := c.nreg ALLOC with hA₃
  have hlen : (L ++ L₂).length = K + K₂ := List.length_append
  obtain ⟨hP, hS⟩ := DownDrv.splice_ok hperm hsort hperm₂ hsort₂
  set E' := DownDrv.splice M (Qof P) (L ++ L₂) E E₂ with hE'd
  have hcodes : ∀ x ∈ E ++ E₂, x < 2 * (L ++ L₂).length := by
    intro x hx
    rw [hlen]
    rcases List.mem_append.1 hx with h | h
    · grind
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (hperm₂.mem_iff.1 h)
      simp_all +arith
  -- the merge
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, m71, mA, mseg, mlow, mfr, mrr, mrm, mout⟩ :=
    splC_exec (P := P) (W := W) hG hWn c hw (D := D) (T := T) (SE := SE) (Rb := Rb) (K := K)
      (K₂ := K₂) (M := M) (L' := L ++ L₂) (E := E) (E₂ := E₂) h27 h28 h29 h04 h48 h34 h40 h42
      (by omega) hlen hwf hM hok hrec (by omega) hE hSE hE₂ hRb hcodes
      (by omega)
  rw [← hA₃] at m71 mA mlow
  have hmseg : seg c₄.nmem (c₄.nreg 210071) (2 * (K + K₂)) = E' := mseg
  have k4 : ∀ r, 210000 ≤ r → r < 220000 → Bs56 r = false → Bcp r = false →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    mfr r (band21_notin h1 h2) h3 h4 (by omega_nf)
  have b26 : c₄.nreg 210026 = A₀ := by ram_simp
  -- the padding
  obtain ⟨c₅, e₅, pfr, prr, pnm, prm, pout, w₅⟩ :=
    padS_exec (P := P) (src := 210026) w₄ (by grind [ALLOC])
      (by omega)
  have hp9 : c₄.nreg 9999 = A₃ + 4 * (K + K₂) := by ram_grind
  have q01 : c₅.nreg 210001 = D := by
    ram_simp
  have q25 : c₅.nreg 210025 = K + K₂ := by
    ram_simp
  have q26 : c₅.nreg 210026 = A₀ := by ram_grind
  have q71 : c₅.nreg 210071 = A₃ + 2 * (K + K₂) := by ram_grind
  have q9 : c₅.nreg 9999 = A₃ + 4 * (K + K₂) := by ram_grind
  -- the arguments of the sorted build
  obtain ⟨c₆, k₆, e₆, hk₆, v0, v1, v2, v4, hm₆⟩ : ∃ c₆ k₆, Exec P W spl7 c₅ c₆ k₆ ∧ k₆ = 4 ∧
      c₆.nreg 40000 = D ∧ c₆.nreg 40001 = A₀ ∧ c₆.nreg 40002 = K + K₂ ∧
      c₆.nreg 40004 = A₃ + 2 * (K + K₂) ∧ c₆.nmem = c₅.nmem := by
    unfold spl7
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> omega
  have f₆ := exec_frameM e₆ wrM_spl7
  have w₆ := e₆.wb_right
  have a6 : c₆.nreg ALLOC = A₃ + 4 * (K + K₂) := by
    rw [f₆.1 _ (by decide)]; exact q9
  have hm6 : ∀ a, a < A₃ → c₆.nmem a = c.nmem a := fun a ha => by ram_grind
  obtain ⟨hM₆, hwf₆⟩ := desc_agree hwf hM (m' := c₆.nmem) hm6
  have hwf₆' : ModelDescWF P (c₆.nreg ALLOC) c₆.nmem D := hwf₆.mono (by ram_grind)
  have hCL₆ : ChordListAt c₆.nmem A₀ (L ++ L₂) := fun i hi => by
    obtain ⟨x1, x2, x3⟩ := hCL i hi
    rw [hlen] at hi
    exact ⟨by grind, by grind,
      by grind⟩
  have hseg₆ : seg c₆.nmem (A₃ + 2 * (K + K₂)) (2 * (K + K₂)) = E' := by
    ram_grind
  -- the sorted build
  have H7 := hB P W c₆ w₆
    (by
      simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd]
      refine ⟨hG, hWn, by ram_grind, M, L ++ L₂, E', by ram_grind, hgood,
        by omega, by ram_grind, by ram_grind, hok,
        by ram_grind, by rw [v4, hlen]; exact hseg₆, hP, hS⟩)
    (by
      simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd]
      ram_grind)
  obtain ⟨c₇, k₇, e₇, hk₇, post₇, fr₇⟩ := H7
  simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd] at hk₇ post₇
  rw [v2] at hk₇
  obtain ⟨o1, o2, -, -, -⟩ := post₇ M (L ++ L₂) (by ram_grind) (by omega)
    (by ram_grind)
  rw [v4, hlen, hseg₆] at o2
  rw [a6] at o1
  obtain ⟨fr7, rr7, nm7, rm7, out7, al7, au7⟩ := fr₇
  rw [a6] at al7 au7 nm7 rm7
  have k7 : ∀ r, 210000 ≤ r → r < 220000 → c₇.nreg r = c₆.nreg r := fun r h1 h2 =>
    fr7 r (by simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild]; omega)
      (by omega_nf)
  have r26 : c₇.nreg 210026 = A₀ := by
    rw [k7 _ (by norm_num) (by norm_num), f₆.1 _ (by decide), q26]
  have r25 : c₇.nreg 210025 = K + K₂ := by
    rw [k7 _ (by norm_num) (by norm_num), f₆.1 _ (by decide), q25]
  have r71 : c₇.nreg 210071 = A₃ + 2 * (K + K₂) := by
    rw [k7 _ (by norm_num) (by norm_num), f₆.1 _ (by decide), q71]
  -- the outputs
  have w₇ := e₇.wb_right
  obtain ⟨c₈, k₈, e₈, hk₈, u2, u3, u4, u5, hm₈⟩ : ∃ c₈ k₈, Exec P W spl8 c₇ c₈ k₈ ∧ k₈ = 4 ∧
      c₈.nreg 210002 = A₀ ∧ c₈.nreg 210003 = K + K₂ ∧ c₈.nreg 210004 = A₃ + 2 * (K + K₂) ∧
      c₈.nreg 210005 = c₇.nreg 40003 ∧ c₈.nmem = c₇.nmem := by
    unfold spl8
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> omega
  have f₈ := exec_frameM e₈ wrM_spl8
  have a8 : c₈.nreg ALLOC = c₇.nreg ALLOC := f₈.1 _ (by decide)
  have hm8 : ∀ a, a < A₃ + 4 * (K + K₂) → c₈.nmem a = c₆.nmem a := fun a ha => by
    rw [hm₈, nm7 a ha]
  refine ⟨c₈, k₄ + (3 * (c₄.nreg 9999 - c₄.nreg 210026) + 4 + (k₆ + (k₇ + k₈))),
    .seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))), ?_, ?_, ?_, u2, u3, ?_, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr h56 hcp hro h68 h69 hra => ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
  · unfold splTCost
    rw [hp9, b26, hk₆, hk₈]
    omega
  · rw [a8]; omega
  · rw [a8, hp9, b26]; omega
  · rw [u4]; omega
  · rw [u4, a8]; omega
  · rw [u4, seg_congr (m' := c₆.nmem) fun i hi => hm8 _ (by omega), hseg₆]
  · rw [u5]; omega
  · rw [u5, hm₈, a8]; exact o2
  · rw [hm8 a (by omega), hm6 a ha]
  · rw [f₈.1 r (by omega_nf)]
    rw [fr7 r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto) hra]
    rw [f₆.1 r (by
      simp only [Finset.mem_insert, Finset.mem_singleton, bandOf, bSort, bSign, bBuild] at hr
      simp only [decide_eq_false_iff_not]; omega)]
    rw [pfr r h68 h69, mfr r hr h56 hcp hra]
  · rw [exec_frameM2 e₈ wrM2_spl8 r rfl, rr7 r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto),
      exec_frameM2 e₆ wrM2_spl7 r rfl, prr, mrr r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto)]
  · rw [f₈.2.2.1, rm7 a (by omega), f₆.2.2.1, prm, mrm]
  · rw [f₈.2.2.2, out7, f₆.2.2.2, pout, mout]

end exec

end

end DrvR

end Chazelle.Core
