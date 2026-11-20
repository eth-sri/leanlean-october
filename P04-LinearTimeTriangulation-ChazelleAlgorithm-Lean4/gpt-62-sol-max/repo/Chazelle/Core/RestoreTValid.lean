module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.RestoreTRun

/-!
# WP-E, the candidate test on the RAM, part 10: the arc scan

The first half of the validity check scans the arcs of the region `r` (register `83002`): for
each arc it reads the two ends, compares their keys with the key of the candidate `x`, and
accumulates three flags: `83042` (the key of `x` is strictly inside the arc), `83043` (an arc
begins at `x`), `83044` (an arc ends at `x`).

Scratch registers: `83030` the place in the arc list, `83031` its length, `83032` the arc, `83033
… 83036` its ends, `83037 … 83041` the comparison bits (`s < x`, `x < s`, `x < e`, `e < x`,
`s < e`).

* `Agr c c' S`: the registers of band `bRestore` outside `S` agree.
* `arcRead_rs`: reading the ends of the `t`-th arc.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- The registers of band `bRestore` outside `S` agree. -/
def Agr (c c' : Config) (S : List ℕ) : Prop :=
  ∀ q, 80000 ≤ q → q < 90000 → q ∉ S → c'.nreg q = c.nreg q

theorem Agr.refl (c : Config) (S : List ℕ) : Agr c c S := fun _ _ _ _ => rfl

theorem Agr.trans {c c₁ c₂ : Config} {S₁ S₂ : List ℕ} (h₁ : Agr c c₁ S₁) (h₂ : Agr c₁ c₂ S₂) :
    Agr c c₂ (S₁ ++ S₂) := fun q h1 h2 hq => by
  simp only [List.mem_append, not_or] at hq
  rw [h₂ q h1 h2 hq.2, h₁ q h1 h2 hq.1]

theorem Agr.mono {c c' : Config} {S S' : List ℕ} (h : Agr c c' S) (hS : ∀ q ∈ S, q ∈ S') :
    Agr c c' S' := fun q h1 h2 hq => h q h1 h2 (fun h' => hq (hS q h'))

theorem Agr.of_upd {c c' : Config} {r v : ℕ} (h : c'.nreg = upd c.nreg r v) : Agr c c' [r] :=
  fun q _ _ hq => by
    simp_all

theorem Agr.of_band {c c' : Config} (h : ∀ q, 80000 ≤ q → q < 90000 → c'.nreg q = c.nreg q)
    (S : List ℕ) : Agr c c' S := fun q h1 h2 _ => h q h1 h2


variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- The arc at place `t` of the region. -/
def arcAt (N : NF) (r t : ℕ) : ℕ := (N.region r).arcs.getD t 0

/-- A field read of the arc in `83032` and a copy into `d`. -/
def arcF (f d : ℕ) : Stmt := .seq (tArcF f 83032) (.instr (.copyN d 50210))

/-- **Reading the ends of the arc at place `83030`.** -/
def arcRead : Stmt :=
  .seq (tRegItem 1 83030) (.seq (.instr (.copyN 83032 50210))
    (.seq (arcF 1 83033) (.seq (arcF 2 83034) (.seq (arcF 3 83035) (arcF 4 83036)))))

/-- Read a field with a model operation, then copy it to restoration scratch. -/
private theorem copyField_rs {s : Stmt} {d value : ℕ} (hd : Scr d)
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ 13 ∧
      c'.nreg 50210 = value ∧ TStep W c₀ c c' k) :
    RS P W c₀ (.seq s (.instr (.copyN d 50210))) c 14
      (fun c' => c'.nreg d = value ∧ Agr c c' [d]) :=
  RS.seq (RS.op h) fun _ hI _ ⟨v, hb⟩ =>
    RS.mono (RS.copy hI hd) le_rfl fun _ e =>
      ⟨by rw [e, upd_eq, v], (Agr.of_band hb []).trans (Agr.of_upd e)⟩

/-- A field read of the arc in `83032` followed by a copy into a scratch register. -/
theorem arcF_rs {f d : ℕ} (hf : f < 5) (hd : Scr d) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hj : c.nreg 83032 < N.arcs.length) (hroom : c.nreg ALLOC + 11 ≤ W) :
    RS P W c₀ (arcF f d) c 14
      (fun c' => c'.nreg d = arFld (N.arc (c.nreg 83032)) f ∧ Agr c c' [d]) :=
  copyField_rs hd (tArcF_exec hf (by reg_omega) hE hI hj hroom)

/-- The arc at place `t` of the region is an arc record. -/
theorem arcAt_lt (hE : TGood P W M N c₀) {t : ℕ}
    (ht : t < (N.region (c₀.nreg 83002)).arcs.length) :
    arcAt N (c₀.nreg 83002) t < N.arcs.length ∧
      arcAt N (c₀.nreg 83002) t ∈ (N.region (c₀.nreg 83002)).arcs := by
  have hr := hE.hr
  obtain ⟨-, -, -, reg, -, -, harcs, -⟩ := hE.hNF
  have hmem : arcAt N (c₀.nreg 83002) t ∈ (N.region (c₀.nreg 83002)).arcs := by
    unfold arcAt
    simp_all
  exact ⟨((harcs.2.2.2 _ hr _).1 hmem).1, hmem⟩

/-- **The ends of the arc at place `t`.** -/
theorem arcRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region (c₀.nreg 83002)).arcs.length)
    (hroom : c.nreg ALLOC + 80 ≤ W) :
    RS P W c₀ arcRead c 80 (fun c' =>
      c'.nreg 83033 = (N.arc (arcAt N (c₀.nreg 83002) (c.nreg 83030))).s.edge ∧
      c'.nreg 83034 = (N.arc (arcAt N (c₀.nreg 83002) (c.nreg 83030))).s.hgt ∧
      c'.nreg 83035 = (N.arc (arcAt N (c₀.nreg 83002) (c.nreg 83030))).e.edge ∧
      c'.nreg 83036 = (N.arc (arcAt N (c₀.nreg 83002) (c.nreg 83030))).e.hgt ∧
      Agr c c' [83032, 83033, 83034, 83035, 83036]) := by
  have hjl := (arcAt_lt hE ht).1
  set j := arcAt N (c₀.nreg 83002) (c.nreg 83030) with hjdef
  have h1 := tRegItem_exec (f := 1) (tr := 83030) (Or.inl rfl) (by unfold InR; omega) hE hI
    (by assumption) (by omega)
  rw [ite_eq_left rfl] at h1
  refine RS.mono (K := 20 + (1 + (14 + (14 + (14 + 14))))) ?_ (by norm_num) (fun _ h => h)
  refine RS.seq (RS.op h1) fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) (by unfold Scr; omega))
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = j := by rw [hc₂, upd_eq, v₁]; rfl
  have a2 := (Agr.of_band h8₁ []).trans (Agr.of_upd hc₂)
  refine RS.seq (arcF_rs (f := 1) (d := 83033) (by norm_num) (by unfold Scr; omega) hE hI₂
    (by rwa [q2]) (by omega)) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = j := by ram_rw [a₃, q2]
  refine RS.seq (arcF_rs (f := 2) (d := 83034) (by norm_num) (by unfold Scr; omega) hE hI₃
    (by rwa [q3]) (by omega)) fun c₄ hI₄ hA₄ ⟨v₄, a₄⟩ => ?_
  have q4 : c₄.nreg 83032 = j := by ram_rw [a₄, q3]
  refine RS.seq (arcF_rs (f := 3) (d := 83035) (by norm_num) (by unfold Scr; omega) hE hI₄
    (by rwa [q4]) (by omega)) fun c₅ hI₅ hA₅ ⟨v₅, a₅⟩ => ?_
  have q5 : c₅.nreg 83032 = j := by ram_rw [a₅, q4]
  refine (arcF_rs (f := 4) (d := 83036) (by norm_num) (by unfold Scr; omega) hE hI₅
    (by rwa [q5]) (by omega)).mono le_rfl fun c₆ ⟨v₆, a₆⟩ => ?_
  have a26 := (((a2.trans a₃).trans a₄).trans a₅).trans a₆
  refine ⟨?_, ?_, ?_, ?_, a26.mono (by simp)⟩
  · ram_rw [a₆, a₅,
      a₄, v₃, q2]; rfl
  · ram_rw [a₆, a₅,
      v₄, q3]; rfl
  · ram_rw [a₆, v₅, q4]; rfl
  · rw [v₆, q5]; rfl


/-! ## Comparisons -/

/-- Copy the two comparison bits into `u`, `v`. -/
def cp2 (u v : ℕ) : Stmt := .seq (.instr (.copyN u 50210)) (.instr (.copyN v 50211))

theorem cp2_rs {u v : ℕ} (hu : Scr u) (hv : Scr v) (huv : u ≠ v) (hI : TInv W c₀ c) :
    RS P W c₀ (cp2 u v) c 2 (fun c' => c'.nreg u = c.nreg 50210 ∧ c'.nreg v = c.nreg 50211 ∧
      Agr c c' [u, v]) := by
  unfold Scr at hu hv
  refine RS.seq (RS.copy hI (r := u) (a := 50210) hu) fun c₁ hI₁ _ h₁ =>
    (RS.copy hI₁ (r := v) (a := 50211) hv).mono le_rfl fun c₂ h₂ => ⟨?_, ?_, ?_⟩
  · simp_all
  · ram_finish
  · exact ((Agr.of_upd h₁).trans (Agr.of_upd h₂)).mono (by simp)

section

variable {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)

include hK in
/-- **A key comparison with its bits saved** in `u`, `v`. -/
theorem kcmp_rs {a b d e u v : ℕ}
    (ha : InR a) (hb : InR b) (hd : InR d) (he : InR e) (hu : Scr u) (hv : Scr v) (huv : u ≠ v)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hx : PosG M (Qof P) P.n ⟨c.nreg a, c.nreg b⟩) (hy : PosG M (Qof P) P.n ⟨c.nreg d, c.nreg e⟩)
    (hroom : c.nreg ALLOC + Kk ≤ W) :
    RS P W c₀ (.seq (kc a b d e) (cp2 u v)) c (Kk + 2) (fun c' =>
      BitIs c' u (M.key (Qof P) ⟨c.nreg a, c.nreg b⟩ < M.key (Qof P) ⟨c.nreg d, c.nreg e⟩) ∧
      BitIs c' v (M.key (Qof P) ⟨c.nreg d, c.nreg e⟩ < M.key (Qof P) ⟨c.nreg a, c.nreg b⟩) ∧
      Agr c c' [u, v]) := by
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b2, hst⟩ := hK a b d e ha hb hd he P W M N c₀ c hE hI hx hy hroom
  refine RS.seq (RS.op (Q := fun c₁ => BitIs c₁ 50210 _ ∧ BitIs c₁ 50211 _)
    ⟨c₁, k₁, e₁, hk₁, ⟨b1, b2⟩, hst⟩)
    fun c₁ hI₁ _ ⟨⟨b1, b2⟩, h8⟩ => (cp2_rs hu hv huv hI₁).mono le_rfl fun c₂ ⟨q1, q2, a2⟩ =>
      ⟨b1.of_eq q1, b2.of_eq q2, ((Agr.of_band h8 []).trans a2).mono (by simp)⟩

/-- **The three comparisons of an arc** with the candidate. -/
def cmpArc (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq (kc 83033 83034 83005 83006) (cp2 83037 83038))
    (.seq (.seq (kc 83005 83006 83035 83036) (cp2 83039 83040))
      (.seq (kc 83033 83034 83035 83036) (cp2 83041 83051)))

/-- The key of the position held in the registers `a`, `b`. -/
noncomputable def keyAt (M : Model) (P : Polygon) (c : Config) (a b : ℕ) : ℝ :=
  M.key (Qof P) ⟨c.nreg a, c.nreg b⟩

include hK in
theorem cmpArc_rs
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hs : PosG M (Qof P) P.n ⟨c.nreg 83033, c.nreg 83034⟩)
    (he : PosG M (Qof P) P.n ⟨c.nreg 83035, c.nreg 83036⟩)
    (hroom : c.nreg ALLOC + 3 * (Kk + 2) ≤ W) :
    RS P W c₀ (cmpArc kc) c (3 * (Kk + 2)) (fun c' =>
      BitIs c' 83037 (keyAt M P c 83033 83034 < keyAt M P c₀ 83005 83006) ∧
      BitIs c' 83038 (keyAt M P c₀ 83005 83006 < keyAt M P c 83033 83034) ∧
      BitIs c' 83039 (keyAt M P c₀ 83005 83006 < keyAt M P c 83035 83036) ∧
      BitIs c' 83040 (keyAt M P c 83035 83036 < keyAt M P c₀ 83005 83006) ∧
      BitIs c' 83041 (keyAt M P c 83033 83034 < keyAt M P c 83035 83036) ∧
      Agr c c' [83037, 83038, 83039, 83040, 83041, 83051]) := by
  have i5 := hI.hin 83005 (by norm_num) (by norm_num)
  have i6 := hI.hin 83006 (by norm_num) (by norm_num)
  have hx : PosG M (Qof P) P.n ⟨c.nreg 83005, c.nreg 83006⟩ := by
    rw [i5, i6]; exact hE.xPosG
  have kx : keyAt M P c₀ 83005 83006 = keyAt M P c 83005 83006 := by
    unfold keyAt; rw [i5, i6]
  rw [kx]
  unfold cmpArc
  refine RS.mono (K := (Kk + 2) + ((Kk + 2) + (Kk + 2))) ?_ (by omega) (fun _ h => h)
  refine RS.seq (kcmp_rs hK (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (by omega) hE hI hs hx
    (by omega)) fun c₁ hI₁ hA₁ ⟨b37, b38, a₁⟩ => ?_
  have g : ∀ q, q ∈ [83033, 83034, 83035, 83036, 83005, 83006] → c₁.nreg q = c.nreg q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₁ q (by omega) (by omega) (by simp; omega)
  refine RS.seq (kcmp_rs hK (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (by omega) hE hI₁
    (by simp_all)
    (by simp_all) (by omega))
    fun c₂ hI₂ hA₂ ⟨b39, b40, a₂⟩ => ?_
  have g2 : ∀ q, q ∈ [83033, 83034, 83035, 83036, 83005, 83006] → c₂.nreg q = c.nreg q := by
    intro q hq
    rw [← g q hq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₂ q (by omega) (by omega) (by simp; omega)
  refine (kcmp_rs hK (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (by omega) hE hI₂
    (by ram_simp [g2] <;> reg_omega)
    (by ram_simp [g2] <;> reg_omega) (by omega)).mono le_rfl
    fun c₃ ⟨b41, _, a₃⟩ => ?_
  unfold keyAt at *
  ram_rw [g 83005, g 83006, g 83035, g 83036] at b39 b40
  ram_rw [g2 83033, g2 83034, g2 83035, g2 83036] at b41
  have a12 := (a₁.trans a₂).trans a₃
  refine ⟨?_, ?_, ?_, ?_, b41, a12.mono (by simp)⟩
  · exact b37.of_eq (by ram_rw [a₃,
      a₂])
  · exact b38.of_eq (by ram_rw [a₃,
      a₂])
  · exact b39.of_eq (by ram_rw [a₃])
  · exact b40.of_eq (by ram_rw [a₃])


/-! ## Flags -/

/-- The effect of a conditional flag update: the flag `r` becomes `1` if `cond`, else stays. -/
def FlagUpd (c c' : Config) (r : ℕ) (cond : Prop) : Prop :=
  (c'.nreg r = 1 ↔ c.nreg r = 1 ∨ cond) ∧ (c.nreg r ≤ 1 → c'.nreg r ≤ 1) ∧ Agr c c' [r]

/-- Set a flag. -/
def setF (r : ℕ) : Stmt := .instr (.constN r 1)

theorem leaf_set {r K : ℕ} {cond : Prop} (hI : TInv W c₀ c) (hr : Scr r) (hK : 1 ≤ K)
    (hc : cond) : RS P W c₀ (setF r) c K (fun c' => FlagUpd c c' r cond) :=
  (RS.const hI hr (by have := hI.hw.1 83023; rwa [hI.h23] at this)).mono hK
    fun c' h => ⟨by simp_all, by rw [h, upd_eq]; omega, Agr.of_upd h⟩

theorem leaf_skip {r K : ℕ} {cond : Prop} (hI : TInv W c₀ c) (hc : ¬ cond) :
    RS P W c₀ .skip c K (fun c' => FlagUpd c c' r cond) :=
  RS.skip hI ⟨by simp [hc], id, Agr.refl c _⟩

/-- **Update of the inside flag** `83042`: set if the candidate's key is strictly inside the arc
(`83041`: `s < e`, `83037`: `s < x`, `83039`: `x < e`). -/
def updIn : Stmt :=
  .ifLtN 83041 83023
    (.ifLtN 83037 83023 (.ifLtN 83039 83023 .skip (setF 83042)) (setF 83042))
    (.ifLtN 83037 83023 .skip (.ifLtN 83039 83023 .skip (setF 83042)))


theorem updIn_rs {pse psx pxe : Prop} (hI : TInv W c₀ c) (h41 : BitIs c 83041 pse)
    (h37 : BitIs c 83037 psx) (h39 : BitIs c 83039 pxe) :
    RS P W c₀ updIn c 7 (fun c' => FlagUpd c c' 83042
      ((pse ∧ psx ∧ pxe) ∨ (¬ pse ∧ (psx ∨ pxe)))) := by
  have h1 := hI.h23
  have hs : Scr 83042 := by reg_omega
  unfold updIn
  rcases bit01 h41 with ⟨q41, n41⟩ | ⟨q41, n41⟩ <;>
  rcases bit01 h37 with ⟨q37, n37⟩ | ⟨q37, n37⟩ <;>
  rcases bit01 h39 with ⟨q39, n39⟩ | ⟨q39, n39⟩
  · refine RS.ifT (by omega) (RS.ifT (by omega) (RS.ifT (by omega) (leaf_skip hI ?_)))
    simp [n41, n37, n39]
  · refine RS.ifT (by omega) (RS.ifT (by omega) (RS.ifF (by omega) (leaf_set hI hs le_rfl ?_)))
    simp [n41, n39]
  · refine RS.ifT (by omega) (RS.ifF (by omega) (leaf_set hI hs (by norm_num) ?_))
    simp [n41, n37]
  · refine RS.ifT (by omega) (RS.ifF (by omega) (leaf_set hI hs (by norm_num) ?_))
    simp [n41, n37]
  · refine RS.ifF (by omega) (RS.ifT (by omega) (leaf_skip hI ?_))
    simp [n41, n37]
  · refine RS.ifF (by omega) (RS.ifT (by omega) (leaf_skip hI ?_))
    simp [n41, n37]
  · refine RS.ifF (by omega) (RS.ifF (by omega) (RS.ifT (by omega) (leaf_skip hI ?_)))
    simp [n41, n39]
  · refine RS.ifF (by omega) (RS.ifF (by omega) (RS.ifF (by omega) (leaf_set hI hs le_rfl ?_)))
    simp [n41, n37, n39]

/-- **Update of an equality flag** `f`: set if both bits `u` (`a < b`) and `v` (`b < a`) are
`0`. -/
def updEq (u v f : ℕ) : Stmt := .ifLtN u 83023 (.ifLtN v 83023 (setF f) .skip) .skip

theorem updEq_rs {u v f : ℕ} {a b : ℝ} (hf : Scr f) (hI : TInv W c₀ c) (hu : BitIs c u (a < b))
    (hv : BitIs c v (b < a)) :
    RS P W c₀ (updEq u v f) c 5 (fun c' => FlagUpd c c' f (a = b)) := by
  have h1 := hI.h23
  unfold updEq
  rcases bit01 hu with ⟨qu, nu⟩ | ⟨qu, nu⟩ <;>
  rcases bit01 hv with ⟨qv, nv⟩ | ⟨qv, nv⟩
  · refine RS.ifT ?_ (RS.ifT ?_ (leaf_set hI hf le_rfl
      (le_antisymm (not_lt.1 nv) (not_lt.1 nu)))) <;> omega
  · refine RS.ifT ?_ (RS.ifF ?_
      (leaf_skip hI (fun h => by simp_all))) <;> omega
  · exact RS.ifF (by omega) (leaf_skip hI (fun h => by simp_all))
  · exact RS.ifF (by omega) (leaf_skip hI (fun h => by simp_all))


/-! ## The arc loop -/

/-- The body of the arc loop. -/
def arcBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq arcRead (.seq (cmpArc kc) (.seq updIn (.seq (updEq 83037 83038 83043)
    (.seq (updEq 83039 83040 83044) (.instr (.addN 83030 83030 83023))))))

/-- The cost bound of the body of the arc loop. -/
def arcKB (Kk : ℕ) : ℕ := 80 + (3 * (Kk + 2) + (7 + (5 + (5 + 1))))

/-- The start key of the arc at place `t`. -/
noncomputable def ksAt (M : Model) (P : Polygon) (N : NF) (r t : ℕ) : ℝ :=
  M.key (Qof P) (N.arc (arcAt N r t)).s

/-- The end key of the arc at place `t`. -/
noncomputable def keAt (M : Model) (P : Polygon) (N : NF) (r t : ℕ) : ℝ :=
  M.key (Qof P) (N.arc (arcAt N r t)).e

/-- **The invariant of the arc loop** (started in `cS`). -/
def ArcI (M : Model) (P : Polygon) (N : NF) (c₀ cS c : Config) : Prop :=
  c.nreg 83031 = (N.region (c₀.nreg 83002)).arcs.length ∧
    c.nreg 83030 ≤ c.nreg 83031 ∧
    c.nreg 83042 ≤ 1 ∧ c.nreg 83043 ≤ 1 ∧ c.nreg 83044 ≤ 1 ∧
    (c.nreg 83042 = 1 ↔ ∃ t < c.nreg 83030, Chazelle.Chain.sideInArc (ksAt M P N (c₀.nreg 83002) t)
      (keAt M P N (c₀.nreg 83002) t) (M.key (Qof P) (xOf c₀))) ∧
    (c.nreg 83043 = 1 ↔ ∃ t < c.nreg 83030,
      ksAt M P N (c₀.nreg 83002) t = M.key (Qof P) (xOf c₀)) ∧
    (c.nreg 83044 = 1 ↔ ∃ t < c.nreg 83030,
      M.key (Qof P) (xOf c₀) = keAt M P N (c₀.nreg 83002) t) ∧
    Agr cS c [83030, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040, 83041,
      83042, 83043, 83044, 83051]

theorem sideInArc_bits {a b x : ℝ} :
    ((a < b ∧ a < x ∧ x < b) ∨ (¬ a < b ∧ (a < x ∨ x < b))) ↔
      Chazelle.Chain.sideInArc a b x := by
  unfold Chazelle.Chain.sideInArc
  split_ifs with h <;> tauto

theorem lt_succ_exists {p : ℕ → Prop} {t : ℕ} :
    (∃ t' < t + 1, p t') ↔ (∃ t' < t, p t') ∨ p t := by
  constructor
  · rintro ⟨t', h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | rfl
    · exact Or.inl ⟨t', h, h2⟩
    · exact Or.inr h2
  · rintro (⟨t', h1, h2⟩ | h)
    · exact ⟨t', by omega, h2⟩
    · tauto

include hK in
/-- **One iteration of the arc loop.** -/
theorem arcBody_rs
    (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) {cS : Config}
    (hI : TInv W c₀ c) (hA : ArcI M P N c₀ cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + arcKB Kk ≤ W) :
    RS P W c₀ (arcBody kc) c (arcKB Kk) (fun c' => ArcI M P N c₀ cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, f1, f2, f3, i1, i2, i3, aS⟩ := hA
  set r := c₀.nreg 83002
  set t := c.nreg 83030 with htdef
  have ht' : t < (N.region r).arcs.length := by rwa [← hL]
  obtain ⟨hjl, -⟩ := arcAt_lt hE ht'
  have hpos := hE.arcPosG hne hjl
  unfold arcBody arcKB
  refine RS.seq (arcRead_rs hE hI ht' (by unfold arcKB at hroom; omega))
    fun c₁ hI₁ hA₁ ⟨s1, s2, s3, s4, a₁⟩ => ?_
  have hs : PosG M (Qof P) P.n ⟨c₁.nreg 83033, c₁.nreg 83034⟩ := by rw [s1, s2]; exact hpos.1
  have he : PosG M (Qof P) P.n ⟨c₁.nreg 83035, c₁.nreg 83036⟩ := by rw [s3, s4]; exact hpos.2
  refine RS.seq (cmpArc_rs hK hE hI₁ hs he (by unfold arcKB at hroom; omega))
    fun c₂ hI₂ hA₂ ⟨b37, b38, b39, b40, b41, a₂⟩ => ?_
  have ks : keyAt M P c₁ 83033 83034 = ksAt M P N r t := by
    unfold keyAt ksAt; rw [s1, s2]
  have ke : keyAt M P c₁ 83035 83036 = keAt M P N r t := by
    unfold keyAt keAt; rw [s3, s4]
  have kx : keyAt M P c₀ 83005 83006 = M.key (Qof P) (xOf c₀) := rfl
  rw [ks, kx] at b37 b38
  rw [kx, ke] at b39 b40
  rw [ks, ke] at b41
  refine RS.seq (updIn_rs hI₂ b41 b37 b39) fun c₃ hI₃ hA₃ ⟨u1, u2, a₃⟩ => ?_
  have b37' := b37.of_eq (a₃ 83037 (by norm_num) (by norm_num) (by simp))
  have b38' := b38.of_eq (a₃ 83038 (by norm_num) (by norm_num) (by simp))
  refine RS.seq (updEq_rs (by unfold Scr; omega) hI₃ b37' b38')
    fun c₄ hI₄ hA₄ ⟨v1, v2, a₄⟩ => ?_
  have b39' := (b39.of_eq (a₃ 83039 (by norm_num) (by norm_num) (by simp))).of_eq
    (a₄ 83039 (by norm_num) (by norm_num) (by simp))
  have b40' := (b40.of_eq (a₃ 83040 (by norm_num) (by norm_num) (by simp))).of_eq
    (a₄ 83040 (by norm_num) (by norm_num) (by simp))
  refine RS.seq (updEq_rs (by unfold Scr; omega) hI₄ b39' b40')
    fun c₅ hI₅ hA₅ ⟨w1, w2, a₅⟩ => ?_
  have e30 : c₅.nreg 83030 = t := by
    ram_rw [a₅, a₄,
      a₃, a₂,
      a₁]
  have e23 := hI₅.h23
  refine (RS.add hI₅ (r := 83030) (a := 83030) (b := 83023) (by unfold Scr; omega)
    (by rw [e30, e23]; have := hI.hw.1 83031; omega)).mono le_rfl fun c₆ h₆ => ?_
  have a₆ := Agr.of_upd h₆
  have e6 : c₆.nreg 83030 = t + 1 := by rw [h₆, upd_eq, e30, e23]
  -- the chain of agreements
  have a16 := ((((a₁.trans a₂).trans a₃).trans a₄).trans a₅).trans a₆
  have g : ∀ q, 80000 ≤ q → q < 90000 → q ∉ [83030, 83032, 83033, 83034, 83035, 83036, 83037,
      83038, 83039, 83040, 83041, 83042, 83043, 83044, 83051] → c₆.nreg q = c.nreg q :=
    fun q h1 h2 hq => a16 q h1 h2 (fun h => hq (by simp at h ⊢; omega))
  -- the flags at `c₆`
  have fl42 : c₆.nreg 83042 = c₃.nreg 83042 := by
    ram_rw [h₆, upd_ne, a₅,
      a₄]
  have fl43 : c₆.nreg 83043 = c₄.nreg 83043 := by
    ram_rw [h₆, upd_ne, a₅]
  have fl44 : c₆.nreg 83044 = c₅.nreg 83044 := by simp [h₆]
  have o42 : c₂.nreg 83042 = c.nreg 83042 := by
    ram_rw [a₂, a₁]
  have o43 : c₃.nreg 83043 = c.nreg 83043 := by
    ram_rw [a₃, a₂,
      a₁]
  have o44 : c₄.nreg 83044 = c.nreg 83044 := by
    ram_rw [a₄, a₃,
      a₂, a₁]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e6⟩
  · ram_rw assumption [g 83031]
  · ram_simp [e6, g] <;> omega
  · rw [fl42]; exact u2 (by rwa [o42])
  · rw [fl43]; exact v2 (by rwa [o43])
  · rw [fl44]; exact w2 (by rwa [o44])
  · rw [fl42, u1, o42, i1, e6, lt_succ_exists, sideInArc_bits]
  · rw [fl43, v1, o43, i2, e6, lt_succ_exists]
  · rw [fl44, w1, o44, i3, e6, lt_succ_exists]
  · intro q h1 h2 hq
    by_cases hq' : q ∈ [83030, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040,
      83041, 83042, 83043, 83044, 83051]
    · exact absurd hq' hq
    · rw [g q h1 h2 hq', aS q h1 h2 hq]


/-- **The arc scan.** -/
def arcScan (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.instr (.constN 83042 0)) (.seq (.instr (.constN 83043 0))
    (.seq (.instr (.constN 83044 0)) (.seq (tRegLen 0) (.seq (.instr (.copyN 83031 50210))
      (.seq (.instr (.constN 83030 0)) (.whileLtN 83030 83031 (arcBody kc)))))))

/-- The cost bound of the arc scan for a region with `A` arcs. -/
def arcScanK (Kk A : ℕ) : ℕ := 1 + (1 + (1 + (13 + (1 + (1 + ((arcKB Kk + 2) * A + 2))))))

private theorem exists_place {xs : List ℕ} {p : ℕ → Prop} :
    (∃ t < xs.length, p (xs.getD t 0)) ↔ ∃ j ∈ xs, p j := by
  rw [List.exists_mem_iff_exists_getElem]
  constructor <;> rintro ⟨i, hi, h⟩ <;> exact ⟨i, hi, by simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using h⟩

/-- Run an incrementing scan to its fixed limit while carrying its invariant. -/
private theorem scan_rs {I : Config → Prop} {s : Stmt} {K A : ℕ}
    (range : ∀ d, I d → d.nreg 83031 = A ∧ d.nreg 83030 ≤ d.nreg 83031)
    (step : ∀ d, TInv W c₀ d → I d → d.nreg 83030 < d.nreg 83031 → d.nreg ALLOC + K ≤ W →
      RS P W c₀ s d K (fun e => I e ∧ e.nreg 83030 = d.nreg 83030 + 1))
    (hI : TInv W c₀ c) (hc : I c) (hz : c.nreg 83030 = 0)
    (room : c.nreg ALLOC + (K + 2) * A ≤ W) :
    RS P W c₀ (.whileLtN 83030 83031 s) c ((K + 2) * A + 2)
      (fun d => I d ∧ d.nreg 83030 = A) := by
  have hm : c.nreg 83031 - c.nreg 83030 = A := by rw [(range c hc).1, hz, Nat.sub_zero]
  refine (RS.while I (fun d => d.nreg 83031 - d.nreg 83030) K (fun _ _ ht => by omega)
    (fun d hd hi ht hr => (step d hd hi ht hr).mono le_rfl fun e ⟨hei, h⟩ => ?_)
    hI hc (by rwa [hm])).mono (by rw [hm]) ?_
  · have h₁ := (range d hi).1
    have h₂ := (range e hei).1
    exact ⟨hei, by omega⟩
  · rintro d ⟨hd, h⟩
    obtain ⟨h₁, h₂⟩ := range d hd
    exact ⟨hd, by omega⟩

include hK in
/-- **Contract of the arc scan**: the three flags. -/
theorem arcScan_rs
    (hE : TGood P W M N c₀) (hne : (N.F M (Qof P)).Nonempty) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + arcScanK Kk (N.region (c₀.nreg 83002)).arcs.length ≤ W) :
    RS P W c₀ (arcScan kc) c (arcScanK Kk (N.region (c₀.nreg 83002)).arcs.length) (fun c' =>
      c'.nreg 83042 ≤ 1 ∧ c'.nreg 83043 ≤ 1 ∧ c'.nreg 83044 ≤ 1 ∧
      (c'.nreg 83042 = 1 ↔ FIn M P N (c₀.nreg 83002) (xOf c₀)) ∧
      (c'.nreg 83043 = 1 ↔ FS M P N (c₀.nreg 83002) (xOf c₀)) ∧
      (c'.nreg 83044 = 1 ↔ FE M P N (c₀.nreg 83002) (xOf c₀)) ∧
      Agr c c' [83030, 83031, 83032, 83033, 83034, 83035, 83036, 83037, 83038, 83039, 83040,
        83041, 83042, 83043, 83044, 83051]) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rwa [hI.h23] at this
  unfold arcScan arcScanK
  refine RS.seq ((ram_app% (RS.const hI (r := 83042) (v := 0) ?_ ?_)))
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq ((ram_app% (RS.const hI₁ (r := 83043) (v := 0) ?_ ?_)))
    fun c₂ hI₂ hA₂ h₂ => ?_
  refine RS.seq (RS.const hI₂ (r := 83044) (v := 0) (by unfold Scr; omega) (by omega))
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 0) (Or.inl rfl) hE hI₃ (by unfold arcScanK at hroom; omega)))
    fun c₄ hI₄ hA₄ ⟨v₄, h8₄⟩ => ?_
  refine RS.seq (RS.copy hI₄ (r := 83031) (a := 50210) (by unfold Scr; omega))
    fun c₅ hI₅ hA₅ h₅ => ?_
  refine RS.seq (RS.const hI₅ (r := 83030) (v := 0) (by unfold Scr; omega) (by omega))
    fun c₆ hI₆ hA₆ h₆ => ?_
  have a₆ : Agr c c₆ [83042, 83043, 83044, 83031, 83030] :=
    (((((Agr.of_upd h₁).trans (Agr.of_upd h₂)).trans (Agr.of_upd h₃)).trans
      (Agr.of_band h8₄ [])).trans (Agr.of_upd h₅)).trans (Agr.of_upd h₆) |>.mono (by simp)
  have e31 : c₆.nreg 83031 = (N.region (c₀.nreg 83002)).arcs.length := by
    ram_finish
  have e30 : c₆.nreg 83030 = 0 := by rw [h₆, upd_eq]
  have e42 : c₆.nreg 83042 = 0 := by
    ram_finish [h₆, h₅, h8₄, h₃, h₂, h₁]
  have e43 : c₆.nreg 83043 = 0 := by
    ram_finish
  have e44 : c₆.nreg 83044 = 0 := by
    ram_finish
  have hI0 : ArcI M P N c₀ c₆ c₆ := by
    refine ⟨e31, by omega, by omega, by omega, by omega, ?_, ?_, ?_, Agr.refl _ _⟩ <;>
    simp only [e30, Nat.not_lt_zero, false_and, exists_false, iff_false] <;> omega
  refine (scan_rs (I := ArcI M P N c₀ c₆) (fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ => arcBody_rs hK hE hne) hI₆ hI0 e30 (by unfold arcScanK at hroom; omega)).mono
    le_rfl ?_
  rintro c' ⟨⟨hL, htL, f1, f2, f3, i1, i2, i3, aS⟩, hT⟩
  rw [hT] at i1 i2 i3
  refine ⟨f1, f2, f3, i1.trans (exists_place (p := fun j => Chazelle.Chain.sideInArc
      (M.key (Qof P) (N.arc j).s) (M.key (Qof P) (N.arc j).e) (M.key (Qof P) (xOf c₀)))),
    i2.trans (exists_place (p := fun j => M.key (Qof P) (N.arc j).s = M.key (Qof P) (xOf c₀))),
    i3.trans (exists_place (p := fun j => M.key (Qof P) (xOf c₀) = M.key (Qof P) (N.arc j).e)) |>.trans ?_, ?_⟩
  · simp only [FE, eq_comm]
  · exact (a₆.trans aS).mono (by simp)

end


/-! ## The exit scan -/

/-- The exit chord at place `t` of the region. -/
def chordAt (N : NF) (r t : ℕ) : ℕ := (N.region r).chords.getD t 0

/-- The end of a chord record the ray from the candidate would run along: the left end for
`σ = 1`, the right end otherwise. -/
def endPos (σb : ℕ) (cr : CRec) : WPos := if σb = 1 then cr.lpos else cr.rpos

/-- A field read of the chord in `83032` and a copy into `d`. -/
def chF (f d : ℕ) : Stmt := .seq (tChordF f 83032) (.instr (.copyN d 50210))

theorem chF_rs {f d : ℕ} (hf : f < 5) (hd : Scr d) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hi : c.nreg 83032 < N.nChords) (hroom : c.nreg ALLOC + 11 ≤ W) :
    RS P W c₀ (chF f d) c 14
      (fun c' => c'.nreg d = crFld (N.chord (c.nreg 83032)) f ∧ Agr c c' [d]) :=
  copyField_rs hd (tChordF_exec hf (by reg_omega) hE hI hi hroom)

/-- The chord at place `t` of the region is a chord record. -/
theorem chordAt_lt (hE : TGood P W M N c₀) {t : ℕ}
    (ht : t < (N.region (c₀.nreg 83002)).chords.length) :
    chordAt N (c₀.nreg 83002) t < N.nChords ∧
      chordAt N (c₀.nreg 83002) t ∈ (N.region (c₀.nreg 83002)).chords := by
  have hr := hE.hr
  obtain ⟨-, -, -, reg, -, -, -, hregs, -⟩ := hE.hNF
  have hmem : chordAt N (c₀.nreg 83002) t ∈ (N.region (c₀.nreg 83002)).chords := by
    unfold chordAt
    simp_all
  exact ⟨(((hregs _ hr).1 _).1 hmem).1, hmem⟩

/-- **Reading the relevant end of the chord at place `83030`** into `83048`, `83047`. -/
def endRead : Stmt :=
  .seq (tRegItem 3 83030) (.seq (.instr (.copyN 83032 50210))
    (.seq (chF 0 83047) (.seq (.instr (.addN 83047 83047 83023))
      (.ifLtN 83008 83023 (chF 2 83048) (chF 1 83048)))))

theorem endRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region (c₀.nreg 83002)).chords.length)
    (hroom : c.nreg ALLOC + 60 ≤ W) :
    RS P W c₀ endRead c 60 (fun c' =>
      c'.nreg 83048 = (endPos (c₀.nreg 83008) (N.chord (chordAt N (c₀.nreg 83002)
        (c.nreg 83030)))).edge ∧
      c'.nreg 83047 = (endPos (c₀.nreg 83008) (N.chord (chordAt N (c₀.nreg 83002)
        (c.nreg 83030)))).hgt ∧
      Agr c c' [83032, 83047, 83048]) := by
  have hil := (chordAt_lt hE ht).1
  have h1 := tRegItem_exec (f := 3) (tr := 83030) (Or.inr rfl) (by unfold InR; omega) hE hI
    (by assumption) (by omega)
  ram_rw [ite_eq_right] at h1
  refine RS.mono (K := 20 + (1 + (14 + (1 + (14 + 2))))) ?_ (by norm_num) (fun _ h => h)
  refine RS.seq (RS.op h1) fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) (by unfold Scr; omega))
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = chordAt N (c₀.nreg 83002) (c.nreg 83030) := by
    rw [hc₂, upd_eq, v₁]; rfl
  have a2 := (Agr.of_band h8₁ []).trans (Agr.of_upd hc₂)
  refine RS.seq (chF_rs (f := 0) (d := 83047) (by norm_num) (by unfold Scr; omega) hE hI₂
    (by rwa [q2]) (by omega)) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = chordAt N (c₀.nreg 83002) (c.nreg 83030) := by
    ram_rw [a₃, q2]
  have e23 := hI₃.h23
  have hh : (N.chord (chordAt N (c₀.nreg 83002) (c.nreg 83030))).h < P.n := by
    obtain ⟨-, -, -, reg, -, -, -, -, -, hh, -⟩ := hE.hNF
    have := hh _ hil
    rwa [show (Qof P).n = P.n from shear_n _ _] at this
  refine RS.seq (RS.add hI₃ (r := 83047) (a := 83047) (b := 83023) (by unfold Scr; omega)
    (by rw [v₃, e23, q2]; have := hE.hW; ram_simp [hostWords, crFld] <;> reg_omega))
    fun c₄ hI₄ hA₄ h₄ => ?_
  have q4 : c₄.nreg 83032 = chordAt N (c₀.nreg 83002) (c.nreg 83030) := by
    ram_finish
  have v4 : c₄.nreg 83047 = (N.chord (chordAt N (c₀.nreg 83002) (c.nreg 83030))).h + 1 := by
    ram_finish
  have a4 : Agr c c₄ [83032, 83047] :=
    ((a2.trans a₃).trans (Agr.of_upd h₄)).mono (by simp)
  have i8 := ram_app% (hI₄.hin 83008 ?_ ?_)
  have e23' := hI₄.h23
  have fin : ∀ f, f < 5 → (f = 1 ↔ c₀.nreg 83008 = 1) → (f = 2 ↔ c₀.nreg 83008 ≠ 1) →
      RS P W c₀ (chF f 83048) c₄ 14 (fun c' =>
      c'.nreg 83048 = (endPos (c₀.nreg 83008) (N.chord (chordAt N (c₀.nreg 83002)
        (c.nreg 83030)))).edge ∧
      c'.nreg 83047 = (endPos (c₀.nreg 83008) (N.chord (chordAt N (c₀.nreg 83002)
        (c.nreg 83030)))).hgt ∧
      Agr c c' [83032, 83047, 83048]) := fun f hf h1 h2 =>
    (chF_rs (f := f) (d := 83048) hf (by unfold Scr; omega) hE hI₄ (by rwa [q4])
      (by omega)).mono le_rfl fun c₅ ⟨v₅, a₅⟩ => by
      refine ⟨?_, ?_, (a4.trans a₅).mono (by simp)⟩
      · rw [v₅, q4]
        unfold endPos
        by_cases hσ : c₀.nreg 83008 = 1
        · rw [ite_eq_left hσ, h1.2 hσ]; rfl
        · rw [ite_eq_right hσ, h2.2 hσ]; rfl
      · ram_rw [a₅, v4]
        unfold endPos
        split_ifs <;> rfl
  have hσ1 := hE.hσ
  by_cases hσ : c₄.nreg 83008 < c₄.nreg 83023
  · refine RS.ifT hσ ((ram_app% (fin 2 ?_ ?_ ?_)))
  · refine RS.ifF hσ ((ram_app% (fin 1 ?_ ?_ ?_)))


/-- The body of the exit loop. -/
def exitBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq endRead (.seq (.seq (kc 83048 83047 83005 83006) (cp2 83037 83038))
    (.seq (updEq 83037 83038 83046) (.instr (.addN 83030 83030 83023))))

/-- The cost bound of the body of the exit loop. -/
def exitKB (Kk : ℕ) : ℕ := 60 + ((Kk + 2) + (5 + 1))

/-- The key of the relevant end of the exit chord at place `t`. -/
noncomputable def kendAt (M : Model) (P : Polygon) (N : NF) (r σb t : ℕ) : ℝ :=
  M.key (Qof P) (endPos σb (N.chord (chordAt N r t)))

/-- **The invariant of the exit loop** (started in `cS`). -/
def ExitI (M : Model) (P : Polygon) (N : NF) (c₀ cS c : Config) : Prop :=
  c.nreg 83031 = (N.region (c₀.nreg 83002)).chords.length ∧
    c.nreg 83030 ≤ c.nreg 83031 ∧ c.nreg 83046 ≤ 1 ∧
    (c.nreg 83046 = 1 ↔ ∃ t < c.nreg 83030,
      kendAt M P N (c₀.nreg 83002) (c₀.nreg 83008) t = M.key (Qof P) (xOf c₀)) ∧
    Agr cS c [83030, 83032, 83037, 83038, 83046, 83047, 83048]

theorem endPos_posG (hE : TGood P W M N c₀) {i : ℕ} (hi : i < N.nChords) (σb : ℕ) :
    PosG M (Qof P) P.n (endPos σb (N.chord i)) := by
  unfold endPos
  split_ifs
  · exact (hE.chordPosG hi).1
  · exact (hE.chordPosG hi).2

/-- **One iteration of the exit loop.** -/
theorem exitBody_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {cS : Config}
    (hI : TInv W c₀ c) (hA : ExitI M P N c₀ cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + exitKB Kk ≤ W) :
    RS P W c₀ (exitBody kc) c (exitKB Kk) (fun c' => ExitI M P N c₀ cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, f1, i1, aS⟩ := hA
  have ht' : c.nreg 83030 < (N.region (c₀.nreg 83002)).chords.length := by rwa [← hL]
  obtain ⟨hil, -⟩ := chordAt_lt hE ht'
  have hpos := endPos_posG hE hil (c₀.nreg 83008)
  unfold exitBody exitKB
  refine RS.seq (endRead_rs hE hI ht' (by unfold exitKB at hroom; omega))
    fun c₁ hI₁ hA₁ ⟨s1, s2, a₁⟩ => ?_
  have hy : PosG M (Qof P) P.n ⟨c₁.nreg 83048, c₁.nreg 83047⟩ := by rwa [s1, s2]
  have i5 := ram_app% (hI₁.hin 83005 ?_ ?_)
  have i6 := ram_app% (hI₁.hin 83006 ?_ ?_)
  have hx : PosG M (Qof P) P.n ⟨c₁.nreg 83005, c₁.nreg 83006⟩ := by
    rw [i5, i6]; exact hE.xPosG
  refine RS.seq (kcmp_rs hK (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (by omega) hE hI₁ hy hx
    (by unfold exitKB at hroom; omega)) fun c₂ hI₂ hA₂ ⟨b37, b38, a₂⟩ => ?_
  refine RS.seq (updEq_rs (by unfold Scr; omega) hI₂ b37 b38) fun c₃ hI₃ hA₃ ⟨v1, v2, a₃⟩ => ?_
  have e30 : c₃.nreg 83030 = c.nreg 83030 := by
    ram_rw [a₃, a₂,
      a₁]
  have e23 := hI₃.h23
  refine (RS.add hI₃ (r := 83030) (a := 83030) (b := 83023) (by unfold Scr; omega)
    (by rw [e30, e23]; have := hI.hw.1 83031; omega)).mono le_rfl fun c₄ h₄ => ?_
  have e4 : c₄.nreg 83030 = c.nreg 83030 + 1 := by rw [h₄, upd_eq, e30, e23]
  have a14 := ((a₁.trans a₂).trans a₃).trans (Agr.of_upd h₄)
  have g : ∀ q, 80000 ≤ q → q < 90000 →
      q ∉ [83030, 83032, 83037, 83038, 83046, 83047, 83048] → c₄.nreg q = c.nreg q :=
    fun q h1 h2 hq => a14 q h1 h2 (fun h => hq (by simp at h ⊢; omega))
  have fl : c₄.nreg 83046 = c₃.nreg 83046 := by simp [h₄]
  have o46 : c₂.nreg 83046 = c.nreg 83046 := by
    ram_rw [a₂, a₁]
  have kx : M.key (Qof P) ⟨c₁.nreg 83005, c₁.nreg 83006⟩ = M.key (Qof P) (xOf c₀) := by
    rw [i5, i6]; rfl
  have ky : M.key (Qof P) ⟨c₁.nreg 83048, c₁.nreg 83047⟩ =
      kendAt M P N (c₀.nreg 83002) (c₀.nreg 83008) (c.nreg 83030) := by
    rw [s1, s2]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, e4⟩
  · ram_rw assumption [g 83031]
  · ram_simp [e4, g] <;> omega
  · rw [fl]; exact v2 (by rwa [o46])
  · rw [fl, v1, o46, i1, e4, lt_succ_exists, ky, kx]
  · intro q h1 h2 hq
    rw [g q h1 h2 hq, aS q h1 h2 hq]

/-- **The exit scan.** -/
def exitScan (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.instr (.constN 83046 0)) (.seq (tRegLen 2) (.seq (.instr (.copyN 83031 50210))
    (.seq (.instr (.constN 83030 0)) (.whileLtN 83030 83031 (exitBody kc)))))

/-- The cost bound of the exit scan for a region with `D` exit chords. -/
def exitScanK (Kk D : ℕ) : ℕ := 1 + (13 + (1 + (1 + ((exitKB Kk + 2) * D + 2))))

theorem not_clear_iff {M : Model} {P : Polygon} {N : NF} {r : ℕ} {x : WPos} {σb : ℕ} :
    ¬ Clear M P N r x σb ↔ ∃ i ∈ (N.region r).chords,
      M.key (Qof P) (endPos σb (N.chord i)) = M.key (Qof P) x := by
  by_cases hσ : σb = 1 <;> simp [Clear, endPos, hσ]

/-- **Contract of the exit scan**: the flag `83046` is `1` iff some exit chord of the region
leaves the candidate in the direction. -/
theorem exitScan_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + exitScanK Kk (N.region (c₀.nreg 83002)).chords.length ≤ W) :
    RS P W c₀ (exitScan kc) c (exitScanK Kk (N.region (c₀.nreg 83002)).chords.length) (fun c' =>
      c'.nreg 83046 ≤ 1 ∧
      (c'.nreg 83046 = 1 ↔ ¬ Clear M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
      Agr c c' [83030, 83031, 83032, 83037, 83038, 83046, 83047, 83048]) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rwa [hI.h23] at this
  unfold exitScan exitScanK
  refine RS.seq ((ram_app% (RS.const hI (r := 83046) (v := 0) ?_ ?_)))
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) (Or.inr rfl) hE hI₁
    (by unfold exitScanK at hroom; omega))) fun c₂ hI₂ hA₂ ⟨v₂, h8₂⟩ => ?_
  refine RS.seq (RS.copy hI₂ (r := 83031) (a := 50210) (by unfold Scr; omega))
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq ((ram_app% (RS.const hI₃ (r := 83030) (v := 0) ?_ ?_)))
    fun c₄ hI₄ hA₄ h₄ => ?_
  have a₄ : Agr c c₄ [83046, 83031, 83030] :=
    ((((Agr.of_upd h₁).trans (Agr.of_band h8₂ [])).trans (Agr.of_upd h₃)).trans
      (Agr.of_upd h₄)).mono (by simp)
  have e31 : c₄.nreg 83031 = (N.region (c₀.nreg 83002)).chords.length := by
    ram_finish
  have e30 : c₄.nreg 83030 = 0 := by rw [h₄, upd_eq]
  have e46 : c₄.nreg 83046 = 0 := by
    ram_finish
  have hI0 : ExitI M P N c₀ c₄ c₄ := by
    refine ⟨e31, by omega, by omega, ?_, Agr.refl _ _⟩
    simp_all 
  refine (scan_rs (I := ExitI M P N c₀ c₄) (fun _ h => ⟨h.1, h.2.1⟩)
    (fun _ => exitBody_rs hK hE) hI₄ hI0 e30 (by unfold exitScanK at hroom; omega)).mono
    le_rfl ?_
  rintro c' ⟨⟨hL, htL, f1, i1, aS⟩, hT⟩
  rw [hT] at i1
  exact ⟨f1, i1.trans ((exists_place (p := fun j => M.key (Qof P) (endPos (c₀.nreg 83008)
    (N.chord j)) = M.key (Qof P) (xOf c₀))).trans not_clear_iff.symm), (a₄.trans aS).mono (by simp)⟩

end

end Restore

end Chazelle.Core
