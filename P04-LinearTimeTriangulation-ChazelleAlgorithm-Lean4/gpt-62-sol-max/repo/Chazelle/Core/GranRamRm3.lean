module

public import Chazelle.Core.GranRamRm2

/-!
# WP-F, RAM part 8: the removal on the RAM

`rmStmt = gather; relabel; write back; tail; ring` executes `St.remove c μ` (`rm_exec`): from a
machine state `MS` of `st` with the chord `c` on top of the worklist, its classes, degrees,
positions, death bits and merged weight in registers, it reaches a machine state of
`st.remove c μ`.
-/

namespace Chazelle.Core

namespace Gran

open Machine Machine.Stmt Programs SignK

@[expose] public section

/-- **The removal.** -/
def rmStmt : Stmt := .seq gatherStmt (.seq relStmt (.seq wbStmt (.seq tailStmt ringStmt)))

/-- The registers the removal writes. -/
def Brm2 (r : ℕ) : Bool := Brm r || decide (r = 90050) || decide (r = 90051)

theorem wrS_rm : wrS Brm2 rmStmt = true := by decide

theorem optUnl_eq (S : St) (b : Bool) (j : ℕ) : S.optUnl b j =
    { S with nxt := if b then (St.unl (S.nxt, S.prv) j).1 else S.nxt,
             prv := if b then (St.unl (S.nxt, S.prv) j).2 else S.prv } := by
  cases b <;> rfl

theorem rm_exec {P : Polygon} {W : ℕ} {E : Env} {d : Dm} {A₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    {st : St} (hE : E.Good) (hM : MS W E d A₀ m₀ c st) (hI : Inv E st) (hD : DimOK E d W)
    (hA : A₀ ≤ d.b0) {cc μ : ℕ} (hc : cc ∈ st.L E) (_htop : 0 < st.top)
    (hlow : st.deg (st.s0 cc) < 3 ∨ st.deg (st.s1 cc) < 3) (hI' : Inv E (st.remove cc μ))
    (h62 : c.nreg 90062 = cc) (h64 : c.nreg 90064 = st.s0 cc) (h65 : c.nreg 90065 = st.s1 cc)
    (h66 : c.nreg 90066 = st.deg (st.s0 cc)) (h67 : c.nreg 90067 = st.deg (st.s1 cc))
    (h68 : c.nreg 90068 = st.nd0 cc) (h69 : c.nreg 90069 = st.nd1 cc)
    (h72 : c.nreg 90072 = bit (decide (st.cnt (st.nd0 cc) = 1)))
    (h73 : c.nreg 90073 = bit (decide (st.cnt (st.nd1 cc) = 1)))
    (h78 : c.nreg 90078 = μ) :
    ∃ c' k, Exec P W rmStmt c c' k ∧ k ≤ 60 * E.D + 65 ∧ MS W E d A₀ m₀ c' (st.remove cc μ) ∧
      FrameS Brm2 c c' := by
  suffices hh : ∃ c' k, Exec P W rmStmt c c' k ∧ k ≤ 60 * E.D + 65 ∧
      (WordsBounded W c' → FrameS Brm2 c c' → MS W E d A₀ m₀ c' (st.remove cc μ)) by
    obtain ⟨c', k, e, h1, h2⟩ := hh
    have F := exec_frameS e wrS_rm
    exact ⟨c', k, e, h1, h2 e.wb_right F, F⟩
  have hw := hM.wb
  have hC := hM.cst
  have henc := hM.enc
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩ := d.lay
  have yN : d.oNd0 = 3 * d.K := rfl
  obtain ⟨P', hs⟩ := hI.split hE hc
  obtain ⟨hX, hY, -, htouch⟩ := hI.sides cc hc
  obtain ⟨hXr, hYr⟩ := hI.cl_mem hE hc
  
  have hcY := (exl_Y hE hI hc cc).2 ⟨hc, (htouch _ hYr).2 (Or.inr rfl)⟩
  have clX := hI.cls _ ⟨cc, hc, Or.inl rfl⟩
  have clY := hI.cls _ ⟨cc, hc, Or.inr rfl⟩
  have hlen := newEx_le hE hI hc hs hlow
  
  have hfY : ((st.exl (st.s1 cc)).filter (· != cc)).length + 1 = st.deg (st.s1 cc) := by
    rw [← clY.2.2.1.erase_eq_filter, List.length_erase_of_mem hcY, exl_length]
    have := List.length_pos_of_mem hcY
    rw [exl_length] at this
    omega
  have hroom : ((st.exl (st.s0 cc)).filter (· != cc)).length + st.deg (st.s1 cc) ≤ E.D + 1 := by
    have : (st.newEx cc).length = ((st.exl (st.s0 cc)).filter (· != cc)).length +
        ((st.exl (st.s1 cc)).filter (· != cc)).length := by
      unfold St.newEx; rw [List.length_append]
    omega
  have hcap : st.top - 1 + (st.newEx cc).length ≤ d.cap := by
    have := hI'.topLe
    simp only [St.remove] at this
    have e : d.cap = E.K + E.D * E.K := by unfold Dm.cap; rw [hD.K, hD.D]
    omega
  -- gather
  obtain ⟨c₁, k₁, e₁, hk₁, g100, g103, g104, gtmp, gmem, gF⟩ := gather_exec (P := P) hw hC henc hD
    hX hY clX.2.2.2.2 clY.2.2.2.2 hroom h62 h64 h65 h66 h67
  have g₁ := gF.1
  have hw₁ := e₁.wb_right
  have hC₁ := hC.frame fun r hr h' => g₁ r (by simp [Brm]; omega)
  have henc₁ := henc.mem_congr fun a _ ha => gmem a (Or.inl ha)
  -- relabel
  obtain ⟨c₂, k₂, e₂, hk₂, E₂, r₂, m₂, F₂⟩ := relStmt_exec (P := P) hw₁ hC₁ henc₁ hD hY
    clY.2.2.2.2 clY.2.2.1 (fun i hi => ((clY.2.2.2.1 i).1 hi).1.1)
    (by ram_rw [g₁, h62]) (by ram_rw [g₁, h64])
    (by ram_rw [g₁, h65]) (by ram_rw [g₁, h67]) g104
  have hw₂ := e₂.wb_right
  have hC₂ : Cst c₂ E d := hC₁.frame fun r hr h' => r₂ r (by omega) (by omega) (by omega)
    (by omega)
  -- write back
  obtain ⟨c₃, k₃, e₃, hk₃, E₃, w108, r₃, m₃, F₃⟩ := wbStmt_exec (P := P) (top := st.top)
    (L := st.newEx cc) hw₂ hC₂ E₂ hD hX hlen hcap
    (by ram_rw [r₂, g100]; rfl)
    (by ram_simp [r₂, g103] )
    (by ram_simp [r₂, g₁, hM.top] )
    (fun i hi => by
      rw [m₂ _ (by right; omega)]
      exact gtmp i (by rwa [g100]))
  have hw₃ := e₃.wb_right
  have hC₃ : Cst c₃ E d := hC₂.frame fun r hr h' => r₃ r (by omega) (by omega) (by omega)
    (by omega)
  have R₃ : ∀ r, r < 90100 → c₃.nreg r = c.nreg r := fun r hr => by
    ram_rw [r₃ r,
      r₂ r, g₁ r (by simp [Brm]; omega)]
  -- tail
  obtain ⟨c₄, k₄, e₄, hk₄, E₄, t50, t51, r₄, m₄⟩ := tailStmt_exec (P := P) (len := (st.newEx cc).length)
    (μ := μ) hw₃ hC₃ E₃ hD hX hc.1 hcap (by ram_rw [R₃, h62])
    (by ram_rw [R₃, h64])
    (by ram_rw [r₃,
      r₂, g100]; rfl)
    (by ram_rw [R₃, h78]) w108
  have hw₄ := e₄.wb_right
  have hC₄ : Cst c₄ E d := hC₃.frame fun r hr h' => r₄ r (by omega) (by omega) (by omega)
    (by omega)
  have R₄ : ∀ r, r < 90100 → r ≠ 90050 → r ≠ 90051 → c₄.nreg r = c.nreg r := fun r hr a1 a2 => by
    ram_rw [r₄ r a1 a2, R₃ r hr]
  -- ring
  have hn0 := (hI.stat.nd0 cc hc.1).1
  have hn1 := (hI.stat.nd1 cc hc.1).1
  have hL0 := (hI.lv_iff hn0).2 ⟨cc, hc, Or.inl rfl⟩
  have hL1 := (hI.lv_iff hn1).2 ⟨cc, hc, Or.inr rfl⟩
  obtain ⟨⟨a0, -, -, -⟩, ⟨b0', -, -, -⟩⟩ := hI.ring _ hn0 hL0
  obtain ⟨⟨a1, -, -, -⟩, ⟨b1', -, -, -⟩⟩ := hI.ring _ hn1 hL1
  rw [← hD.A] at hn0 hn1 a0 b0' a1 b1'
  obtain ⟨c₅, k₅, e₅, hk₅, E₅, r₅, m₅⟩ := ringStmt_exec (P := P) (n1 := st.nd0 cc)
    (n2 := st.nd1 cc) hw₄ hC₄ E₄ hD (by ram_simp [R₄, h68] )
    (by ram_simp [R₄, h69] )
    (by ram_rw [R₄, h72]; rfl)
    (by ram_rw [R₄, h73]; rfl) hn0 hn1 (hI.nd_ne hE hc)
    ⟨a0, b0'⟩ ⟨a1, b1'⟩
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, fun hw₅ F => ?_⟩
  · rw [← hD.D] at hlen ⊢; rw [← hD.D] at hk₁ hk₂ hk₃; omega
  refine ⟨hw₅, hC₄.frame fun r hr _ => r₅ r (by omega) (by omega) (by omega), ?_, ?_, ?_, ?_⟩
  · -- the encoding of the removed state
    refine E₅.st_congr (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_) (fun i _ => ?_)
      (fun i _ => ?_) (fun x _ => ?_) (fun x _ => ?_) (fun x t _ _ => ?_) (fun j _ => ?_)
      (fun j _ => ?_) (fun j _ => ?_) (fun j _ => ?_) (fun j _ => ?_) (fun t _ => ?_) <;>
      simp only [St.remove, St.rg, St.tl, St.wb, St.rel, optUnl_eq, St.newEx, St.ring2]
    · by_cases h1 : st.cnt (st.nd0 cc) = 1 <;> by_cases h2 : st.cnt (st.nd1 cc) = 1 <;>
        simp [h1, h2]
    · by_cases h1 : st.cnt (st.nd0 cc) = 1 <;> by_cases h2 : st.cnt (st.nd1 cc) = 1 <;>
        simp [h1, h2]
  · ram_rw [r₅, t50]; rfl
  · ram_rw [r₅, t51, R₃, hM.nlive]; rfl
  · intro a ha
    have hab : a < d.b0 := by omega
    ram_rw [m₅ a, m₄ a, m₃ a, m₂ a,
      gmem a, hM.low a ha]

end

end Gran

end Chazelle.Core
