module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvTFiltS

/-!
# Down-phase transition (D2), RAM part 6: the normal form with its event list

`buildT` is the procedure of `BuildNFSpec` (`BuildRam.buildStmt`: phase A sorts the `2K` event
codes by `codeLe`, phase B builds the normal form of that ordering) with one instruction added
between the phases: it saves phase A's event pointer (register `30005`) in register `190020`.
So the sorted event list `E` stays available below the allocator next to the normal form
`buildNF M Q L E` (`buildT_exec`) — what the level invariant `Inv(λ)` needs (finding F-D5).
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs SignK NFLoc SortL BuildRam
open BuildNF (codeLe)

@[expose] public section

/-- **The build with the event pointer.** -/
def buildT : Stmt :=
  .seq (block [.constN 190020 0, .constN 43250 0])
    (.ifLtN 43250 40002 (.seq phaseA (.seq (.instr (.copyN 190020 30005)) phaseB)) zeroCase)

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The build with the event pointer**: the event list `E` at register `190020` and the normal
form `buildNF M Q L E` at register `40003`, both below the allocator. -/
theorem buildT_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List (ℕ × ℕ × ℕ)} {D B : ℕ}
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hgood : GoodModel M) (hok : ChordTriplesOK M (Qof P) L) (hCL : ChordListAt c.nmem B L)
    (hBL : B + 3 * L.length ≤ c.nreg ALLOC) (h0 : c.nreg 40000 = D) (h1 : c.nreg 40001 = B)
    (h2 : c.nreg 40002 = L.length)
    (hcost : c.nreg ALLOC + κBuild * (L.length * (Nat.clog 2 L.length + 1) + 1) + 4 ≤ W) :
    ∃ c' k, Exec P W buildT c c' k ∧
      k ≤ κBuild * (L.length * (Nat.clog 2 L.length + 1) + 1) + 4 ∧
      (∃ E : List ℕ, E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M (Qof P) L) ∧
        c'.nreg 190020 + 2 * L.length ≤ c'.nreg ALLOC ∧
        seg c'.nmem (c'.nreg 190020) (2 * L.length) = E ∧
        c.nreg ALLOC ≤ c'.nreg 40003 ∧
        NFWithin c'.nmem (c'.nreg 40003) (c'.nreg ALLOC) (BuildNF.buildNF M (Qof P) L E)) ∧
      (∀ r, bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) → r ≠ ALLOC → r ≠ 190020 →
        c'.nreg r = c.nreg r) ∧
      Frame {bBuild, bSort, bSign, bTrans} c c' k := by
  set K := L.length with hKdef
  set A₀ := c.nreg ALLOC with hA₀
  have hA : c.nreg 9999 = A₀ := rfl
  have hX : 1 ≤ K * (Nat.clog 2 K + 1) + 1 := by omega
  
  have hsc := sortCost_le K
  have hcost' := hcost
  unfold κBuild at hcost'
  -- the first two instructions
  obtain ⟨c₀, k₀, x₀, hk₀, q20, q50, g₀, m₀⟩ : ∃ c₀ k₀, Exec P W
      (block [.constN 190020 0, .constN 43250 0]) c c₀ k₀ ∧ k₀ = 2 ∧ c₀.nreg 190020 = 0 ∧
      c₀.nreg 43250 = 0 ∧ (∀ r, r ≠ 190020 → r ≠ 43250 → c₀.nreg r = c.nreg r) ∧
      c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧ c₀.rmem = c.rmem ∧ c₀.output = c.output := by
    exec_block
    · omega
    · omega
    ram_simp
  obtain ⟨m₀, rr₀, rm₀, o₀⟩ := m₀
  have w₀ := x₀.wb_right
  have hc0A : c₀.nreg ALLOC = A₀ := g₀ 9999 (by norm_num) (by norm_num)
  by_cases hK : 0 < K
  · -- phase A
    have t₀ : c₀.nreg 43250 < c₀.nreg 40002 := by
      ram_grind
    obtain ⟨c₁, k₁, x₁, hk₁, w₁, F₁, d1, d2, d3, d4, d5, d6, d7, hrec, e1, e2, E, hE, hperm,
      hsort⟩ := phaseA_exec (P := P) hG hWn c₀ w₀ (M := M) (L := L) (D := D) (B := B)
        (by ram_grind) (by ram_grind) hok (by ram_grind)
        (by omega) (by ram_grind)
        (by ram_grind)
        (by ram_grind)
        (by ram_grind)
    rw [hc0A] at d2 hrec e1
    -- the event pointer
    set SE := c₁.nreg 30005 with hSEdef
    set H := c₁.nreg 9999 with hHdef
    have e2' : SE + 2 * K ≤ H := e2
    have xc := Exec.copyN (P := P) w₁ 190020 30005
    set c₁' : Config := { c₁ with nreg := upd c₁.nreg 190020 (c₁.nreg 30005) } with hc₁'
    have w₁' := xc.wb_right
    have gc : ∀ r, r ≠ 190020 → c₁'.nreg r = c₁.nreg r := fun r hr => by ram_simp
    have v20 : c₁'.nreg 190020 = SE := by ram_simp
    have hElen : E.length = 2 * K := by rw [hperm.length_eq, List.length_range]
    have hlow₁ : ∀ a, a < A₀ → c₁.nmem a = c.nmem a := fun a ha => by
      rw [F₁.2.2.1 a (by omega), m₀]
    have hAH : A₀ ≤ H := by omega
    have hHk : H ≤ A₀ + k₁ := by have := F₁.2.2.2.2.2.2; rw [hc0A] at this; exact this
    obtain ⟨hM₁, hwf₁⟩ := desc_agree hwf hM hlow₁
    have hI : BuildNF.Input M (Qof P) L E :=
      ⟨walkAx_of_goodModel hgood, hok, hperm,
        BuildNF.sorted_of_codeLe (walkAx_of_goodModel hgood) hok hperm hsort⟩
    have hCL₁ : ChordListAt c₁.nmem B L := fun i hi => by
      obtain ⟨a1, a2, a3⟩ := hCL i hi
      grind
    -- phase B
    obtain ⟨c₂, k₂, x₂, hk₂, hk₂', w₂, F₂, h40003, h9999, hlow, hNF⟩ := phaseB_exec (P := P) hG
      hWn c₁' w₁' (M := M) (L := L) (E := E) (D := D) (T := A₀) (SE := SE)
      (B := B) (H := H) hI hK (by ram_grind) (by ram_grind)
      (by ram_grind) (by ram_grind)
      (by ram_grind) (by ram_grind)
      (by ram_grind) (by ram_grind)
      (by ram_grind)
      (modelDescWF_mono hwf₁ hAH) hM₁ hrec (by omega) hCL₁ (by omega)
      (fun j hj => seg_getD hE (by omega)) (by omega)
      (by grind [sizeB, costA])
    have X : Exec P W buildT c c₂ (k₀ + (k₁ + (1 + k₂) + 1)) :=
      .seq x₀ (.ifLtN_true t₀ (.seq x₁ (.seq xc x₂)))
    have h20 : c₂.nreg 190020 = SE := by rw [F₂.1 _ (by simp [BphaseB]), v20]
    refine ⟨c₂, _, X, ?_, ⟨E, hperm, hsort, ?_, ?_, ?_, ?_⟩, fun r hr' hra h19 => ?_, ?_⟩
    · unfold costA at hk₁; unfold κBuild
      grind
    · omega_nf
    · rw [h20]
      rw [← hE]
      unfold seg
      apply List.map_congr_left
      grind
    · omega
    · ram_grind
    · have h43 : r ≠ 43250 := by
        grind [bandOf, bBuild]
      rw [F₂.1 r (BphaseB_false hr' hra), gc r h19, F₁.1 r hr' hra, g₀ r h19 h43]
    · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
      · have hr' : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := fun h => hr (by
          grind)
        have h19 : r ≠ 190020 := by
          grind [bandOf, bTrans]
        have h43 : r ≠ 43250 := by
          grind [bandOf, bBuild]
        rw [F₂.1 r (BphaseB_false hr' hra), gc r h19, F₁.1 r hr' hra, g₀ r h19 h43]
      · have hr' : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := fun h => hr (by
          grind)
        rw [exec_frameM2 x₂ wrM2_phaseB r (BRb_false hr'), show c₁'.rreg = c₁.rreg from rfl,
          F₁.2.1 r hr', rr₀]
      · ram_simp
      · rw [F₂.2.2.1, show c₁'.rmem = c₁.rmem from rfl,
          F₁.2.2.2.1 a (by omega), rm₀]
      · rw [F₂.2.2.2, show c₁'.output = c₁.output from rfl, F₁.2.2.2.2.1, o₀]
      · omega_nf
      · omega_nf
  · -- `K = 0`
    have hK0 : K = 0 := by omega
    have t₀ : ¬ c₀.nreg 43250 < c₀.nreg 40002 := by
      ram_grind
    obtain ⟨c', k, x, hk, hk', w', F', h40003, h9999, hlow, hNF⟩ := zeroCase_exec (P := P) hWn c₀
      w₀ (M := M) (L := L) (E := []) (D := D) (H := A₀) hK0
      (by ram_grind) hc0A (by ram_grind)
      (by ram_grind) (by nlinarith)
    have X : Exec P W buildT c c' (k₀ + (k + 2)) := .seq x₀ (.ifLtN_false t₀ x)
    have h20 : c'.nreg 190020 = 0 := by ram_grind
    refine ⟨c', _, X, by omega_nf, ⟨[], by grind,
      List.Pairwise.nil, ?_, ?_, ?_, ?_⟩, fun r hr' hra h19 => ?_, ?_⟩
    · omega
    · ram_simp
    · rw [h40003]
    · ram_grind
    · have h43 : r ≠ 43250 := by
        grind [bandOf, bBuild]
      rw [F'.1 r (BphaseB_false hr' hra), g₀ r h19 h43]
    · have R' : ∀ r, BRb r = false → c'.rreg r = c.rreg r := fun r hr =>
        (exec_frameM2 x wrM2_zeroCase r hr).trans (by rw [rr₀])
      refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_⟩
      · have hr' : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := fun h => hr (by
          grind)
        have h19 : r ≠ 190020 := by
          grind [bandOf, bTrans]
        have h43 : r ≠ 43250 := by
          grind [bandOf, bBuild]
        rw [F'.1 r (BphaseB_false hr' hra), g₀ r h19 h43]
      · have hr' : bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := fun h => hr (by
          grind)
        exact R' r (BRb_false hr')
      · ram_grind
      · ram_grind
      · ram_grind
      · omega_nf
      ram_grind

end exec

end

end DrvT

end Chazelle.Core
