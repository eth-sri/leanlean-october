module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRBkt
public import Chazelle.Core.NFBuildEvCmp

/-!
# Down-phase driver (RAM side): sorting a segment of event codes in place

`sortBack` sorts the `len` event codes at `X` (registers `210055`, `210054` of `bDownDrv`) by the
event comparator `evCmp` of `BuildNF` (the order `codeLe` of the chord list whose records are at
`T`, register `42000`): `SortR.sortStmt evCmp` writes a sorted copy above the allocator, which is
copied back to `X` (`sortBack_exec`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- Copy the sorted codes back. -/
def copyBack : Stmt :=
  .whileLtN 210056 210054
    (block [.addN 210058 30005 210056, .loadN 210059 210058, .addN 210058 210055 210056,
      .storeN 210058 210059, .addN 210056 210056 210034])

/-- **Sort the segment at `X = r210055` of length `r210054` in place.** -/
def sortBack : Stmt :=
  .seq (block [.copyN 30003 210055, .copyN 30004 210054])
    (.seq (SortR.sortStmt evCmp) (.seq (.instr (.constN 210056 0)) copyBack))

/-- The registers of band `bDownDrv` the copy-back loop writes. -/
def Bcb (r : ℕ) : Bool := decide (210056 ≤ r ∧ r ≤ 210059)

theorem wrM_cb : wrM Bcb
    (block [.addN 210058 30005 210056, .loadN 210059 210058, .addN 210058 210055 210056,
      .storeN 210058 210059, .addN 210056 210056 210034]) = true := ⌖

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 1000000 in
theorem cbBody_exec (d : Config) (hw : WordsBounded W d) {i X src : ℕ}
    (h56 : d.nreg 210056 = i) (h55 : d.nreg 210055 = X) (h05 : d.nreg 30005 = src)
    (h34 : d.nreg 210034 = 1) (hW1 : src + i ≤ W) (hW2 : X + i ≤ W) (hW3 : i + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210058 30005 210056, .loadN 210059 210058,
      .addN 210058 210055 210056, .storeN 210058 210059, .addN 210056 210056 210034]) d d' k ∧
      k = 5 ∧ d'.nreg 210056 = i + 1 ∧ d'.nmem = upd d.nmem (X + i) (d.nmem (src + i)) ∧
      FrameM Bcb d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210058 30005 210056,
      .loadN 210059 210058, .addN 210058 210055 210056, .storeN 210058 210059,
      .addN 210056 210056 210034]) d d' k ∧ k = 5 ∧ d'.nreg 210056 = i + 1 ∧
      d'.nmem = upd d.nmem (X + i) (d.nmem (src + i)) := by
    exec_block
    all_goals try (config_simp; (try simp only [h56, h55, h05, h34]); omega)
    refine ⟨rfl, ?_, ?_⟩ <;> config_simp <;> Θ h56, h55, h05, h34
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_cb⟩

/-- **The copy-back loop.** -/
theorem copyBack_exec {d : Config} (hw : WordsBounded W d) {X src len : ℕ}
    (h56 : d.nreg 210056 = 0) (h54 : d.nreg 210054 = len) (h55 : d.nreg 210055 = X)
    (h05 : d.nreg 30005 = src) (h34 : d.nreg 210034 = 1) (hsep : X + len ≤ src)
    (hW : src + len + 1 ≤ W) :
    ∃ d' k, Exec P W copyBack d d' k ∧ k ≤ 7 * len + 2 ∧ WordsBounded W d' ∧
      seg d'.nmem X len = seg d.nmem src len ∧
      (∀ a, (a < X ∨ X + len ≤ a) → d'.nmem a = d.nmem a) ∧ FrameM Bcb d d' := by
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 210056 = i ∧
    e.nreg 210054 = len ∧ e.nreg 210055 = X ∧ e.nreg 30005 = src ∧ e.nreg 210034 = 1 ∧
    FrameM Bcb d e ∧
    ∀ a, e.nmem a = if X ≤ a ∧ a < X + i then d.nmem (src + (a - X)) else d.nmem a
  obtain ⟨d', k, ex, ⟨w', _, _, _, _, _, hf', hm'⟩, hk⟩ := forLoop (P := P) (W := W)
    (ir := 210056) (nr := 210054) Inv 5 len
    (fun i e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun i e hi ⟨hw, h1, h2, h3, h4, h5, hf, hm⟩ => by
      obtain ⟨e', k, ex, hk, h1', hm', hf'⟩ := cbBody_exec (P := P) e hw h1 h3 h4 h5
        (⋄) (⋄) (⋄)
      have g : ∀ r, Bcb r = false → e'.nreg r = e.nreg r := hf'.1
      refine ⟨e', k, ex, ⟨ex.wb_right, h1', (g _ (⌖)).trans h2, (g _ (⌖)).trans h3,
        (g _ (⌖)).trans h4, (g _ (⌖)).trans h5, hf.trans hf', fun a => ?_⟩,
        ⋄⟩
      Ξ hm', Machine.upd_apply
      by_cases ha : a = X + i
      · rw [ite_eq_left ha, hm (src + i), ite_eq_right (⋄), ite_eq_left (⋄),
          show a - X = i by omega]
      · rw [ite_eq_right ha, hm a]; split_ifs <;> first | rfl | omega)
    (j := 0) ⟨hw, h56, h54, h55, h05, h34, FrameM.refl _ _, fun a => Ρ ite_eq_right (⋄)⟩
    (Nat.zero_le _)
  refine ⟨d', k, ex, ⋄, w', ?_, fun a ha => ?_, hf'⟩
  · unfold seg; apply List.map_congr_left; intro i hi
    Ξ' List.mem_range at hi
    Ξ hm', ite_eq_left (⋄), show X + i - X = i by omega
  · Ξ hm', ite_eq_right (⋄)

set_option maxHeartbeats 2000000 in
/-- **Sorting a segment of event codes in place.** -/
theorem sortBack_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {X len D T : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)}
    (h55 : c.nreg 210055 = X) (h54 : c.nreg 210054 = len) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L.length)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hL : ChordTriplesOK M (Qof P) L) (hR : RecsAt c.nmem T L)
    (hTA : T + 8 * L.length ≤ c.nreg ALLOC) (hX : X + len ≤ c.nreg ALLOC)
    (hcodes : ∀ x ∈ seg c.nmem X len, x < 2 * L.length)
    (hroom : c.nreg ALLOC + SortR.sortCost 11010 len + 1 ≤ W) :
    ∃ c' k, Exec P W sortBack c c' k ∧ k ≤ SortR.sortCost 11010 len + 7 * len + 5 ∧
      WordsBounded W c' ∧
      (seg c'.nmem X len).Perm (seg c.nmem X len) ∧
      (seg c'.nmem X len).Pairwise (BuildNF.codeLe M (Qof P) L) ∧
      (∀ a, a < c.nreg ALLOC → (a < X ∨ X + len ≤ a) → c'.nmem a = c.nmem a) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + SortR.sortCost 11010 len ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bcb r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bcb r = false →
        c'.rreg r = c.rreg r) ∧
      (∀ a, a < c.nreg ALLOC → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L.length ∧
      (∀ r, 43000 ≤ r → r < 44000 → c'.nreg r = c.nreg r) := by
  have hW1 : 1 ≤ W := by unfold hostWords at hWn; omega
  -- the sort's inputs
  obtain ⟨c₁, k₁, e₁, hk₁, v3, v4, g₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 30003 210055, .copyN 30004 210054]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 30003 = X ∧ c₁.nreg 30004 = len ∧
      (∀ r, r ≠ 30003 → r ≠ 30004 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
    · exact h55
    · exact h54
    · Θ h1, h2
  have w₁ := e₁.wb_right
  have hA₁ : c₁.nreg ALLOC = c.nreg ALLOC := g₁ _ (⌖) (by decide)
  -- the sort
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (m₀ := c₁.nmem) (A₀ := c₁.nreg ALLOC)
    (D := D) (T := T) (M := M) (L := L) (⋄) (by rw [hA₁, m₁]; exact hwf)
    (by rw [m₁]; exact hM) hL (by rw [m₁]; exact hR) (⋄) c₁.nreg
  have hJ₁ : EvJ c₁.nmem (c₁.nreg ALLOC) D T (2 * L.length) c₁.nreg c₁ :=
    ⟨by rw [g₁ _ (⌖) (by decide), h40], by rw [g₁ _ (by decide) (by decide), h42],
      by rw [g₁ _ (⌖) (by decide), h42'], fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hseg : seg c₁.nmem (c₁.nreg 30003) (seg c.nmem X len).length = seg c.nmem X len := by
    Ξ v3, seg_length, m₁
  obtain ⟨c₂, k₂, e₂, hk₂, J₂, F₂, s₁, s₂, Ls, hLs, hperm, hsort⟩ := SortR.sortStmt_exec
    (P := P) (W := W) hcmp (⌖)
    (fun a b d h1 h2 => evLeB_trans M (Qof P) L _ a b d h1 h2)
    (fun a b => evLeB_total M (Qof P) L _ a b) w₁ hJ₁ (evJ_stable _ _ _ _ _ _)
    (seg c.nmem X len) hseg (Ρ v4, seg_length) (by rw [v3, seg_length, hA₁]; exact hX)
    (by rw [seg_length, hA₁]; omega)
  rw [seg_length] at hk₂ s₂ hLs
  obtain ⟨j1, j2, j3, j4, j5⟩ := J₂
  have w₂ := e₂.wb_right
  -- the counter and the copy back
  have e₃ := Exec.constN (P := P) w₂ 210056 0 (Nat.zero_le _)
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 210056 0 } with hc₃
  have g₃ : ∀ r, r ≠ 210056 → c₃.nreg r = c₂.nreg r := fun r hr => by rw [hc₃]; simp [hr]
  have hb2 : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := fun r hr hra => F₂.1 r (by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hr) hra
  have b21 : ∀ r, 210000 ≤ r → r < 220000 → bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) :=
    fun r h1 h2 => by simp [bandOf, bSort, bSign, bBuild]; omega
  have b3 : ∀ r, 30000 ≤ r → r < 40000 → bandOf r = bSort := fun r h1 h2 => by
    simp [bandOf, bSort]; omega
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, hf₄⟩ := copyBack_exec (P := P) e₃.wb_right
    (X := X) (src := c₂.nreg 30005) (len := len) (by rw [hc₃]; simp)
    (by rw [g₃ _ (⌖), hb2 _ (b21 _ (by norm_num) (by norm_num)) (by decide),
      g₁ _ (⌖) (by decide), h54])
    (by rw [g₃ _ (⌖), hb2 _ (b21 _ (by norm_num) (by norm_num)) (by decide),
      g₁ _ (⌖) (by decide), h55])
    (g₃ _ (⌖))
    (by rw [g₃ _ (⌖), hb2 _ (b21 _ (by norm_num) (by norm_num)) (by decide),
      g₁ _ (⌖) (by decide), h34])
    (by rw [hA₁] at s₁; omega) (by have := F₂.2.2.2.2.2.2; rw [hA₁] at this; omega)
  have g₄ : ∀ r, Bcb r = false → c₄.nreg r = c₃.nreg r := hf₄.1
  have hA₂ := F₂.2.2.2.2.2.1
  have hA₂' := F₂.2.2.2.2.2.2
  rw [hA₁] at hA₂ hA₂'
  refine ⟨c₄, k₁ + (k₂ + (1 + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ⋄, w₄, ?_, ?_,
    fun a ha hX' => ?_, ?_, ?_, fun r hr hcb hra => ?_, fun r hr hcb => ?_, fun a ha => ?_, ?_,
    ?_, ?_, ?_, fun r h1 h2 => ?_⟩
  · rw [hs₄, show c₃.nmem = c₂.nmem from rfl, hLs]; exact hperm
  · Ξ hs₄, show c₃.nmem = c₂.nmem from rfl, hLs
    refine hsort.imp_of_mem fun {a b} ha hb hab => ?_
    have ha' := hcodes a (hperm.mem_iff.1 ha)
    have hb' := hcodes b (hperm.mem_iff.1 hb)
    unfold evLeB at hab; rw [ite_eq_left ha', ite_eq_left hb'] at hab
    simpa using hab
  · Ξ hm₄ a hX', show c₃.nmem = c₂.nmem from rfl, F₂.2.2.1 a (by rw [hA₁]; exact ha), m₁
  · rw [g₄ _ (⌖), g₃ _ (by decide)]; omega
  · rw [g₄ _ (⌖), g₃ _ (by decide)]; omega
  · have h56 : r ≠ 210056 := fun h => by subst h; simp [Bcb] at hcb
    Ξ g₄ r hcb, g₃ r h56, hb2 r hr hra
    exact g₁ r (fun h => by subst h; exact hr (⊚ bandOf, bSort)) (fun h => by
      subst h; exact hr (⊚ bandOf, bSort))
  · rw [hf₄.2.1 r hcb, show c₃.rreg = c₂.rreg from rfl,
      F₂.2.1 r (by simpa [Finset.mem_insert, Finset.mem_singleton] using hr), rr₁]
  · Ξ hf₄.2.2.1, show c₃.rmem = c₂.rmem from rfl, F₂.2.2.2.1 a (by rw [hA₁]; exact ha), rm₁
  · Ξ hf₄.2.2.2, show c₃.output = c₂.output from rfl, F₂.2.2.2.2.1, o₁
  · rw [g₄ _ (⌖), g₃ _ (by decide), j1]
  · rw [g₄ _ (⌖), g₃ _ (by decide), j2]
  · rw [g₄ _ (⌖), g₃ _ (by decide), j3]
  · rw [g₄ _ (by simp only [Bcb, decide_eq_false_iff_not]; omega), g₃ _ (⋄),
      j5 r h1 h2, g₁ _ (⋄) (by omega)]

end exec

end

end DrvR

end Chazelle.Core
