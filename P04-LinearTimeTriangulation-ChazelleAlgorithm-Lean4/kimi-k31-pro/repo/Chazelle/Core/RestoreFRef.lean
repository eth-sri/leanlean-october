module

public import Chazelle.Core.RestoreFChord

/-!
# WP-E, the search on the RAM (`FindOK`), part 17: the reference arc and the children

* `refLoad`: the start `(81108, 81109)` of the first arc of the region `dn` (`81156`) of the
  piece's normal form (handle `81134`);
* `kidLoad`: the children `lo` (`81118`) and `hi` (`81119`) of the node `k` (`81121`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs NFLoc

/-- The decomposition nodes lie below the bound of a protected normal form. -/
theorem dec_bound {m : ℕ → ℕ} {B E : ℕ} {N : NF} (h : NFWithin m B E N) {k : ℕ}
    (hk : k < N.dec.length) : m (B + 8) + 3 * k + 2 < E := by
  have := robust_addr2 (b := B + 8) (o := 3 * k + 2) (v := (N.dnode k).hi)
    (fun m' hm' => by
      have := ((h m' hm').2.2.2.2.2.2.2.2.2.1 k hk).2.2
      simpa only [Nat.add_assoc] using this)
  omega

/-- The reads of the reference arc: the arc-list offset of region `dn`. -/
def refL1 : List Instr :=
  [.addN 81116 81134 81015, .loadN 81116 81116, .addN 81116 81116 81156,
    .addN 81116 81116 81156, .addN 81116 81116 81156, .addN 81116 81116 81156,
    .addN 81116 81116 81156, .addN 81116 81116 81012, .loadN 81116 81116]

/-- The first arc of region `dn`. -/
def refL2 : List Instr :=
  [.addN 81117 81134 81016, .loadN 81117 81117, .addN 81116 81117 81116, .loadN 81116 81116]

/-- The start of that arc. -/
def refL3 : List Instr :=
  [.addN 81117 81134 81014, .addN 81117 81117 81012, .loadN 81117 81117,
    .addN 81117 81117 81116, .addN 81117 81117 81116, .addN 81117 81117 81116,
    .addN 81117 81117 81116, .addN 81117 81117 81116, .addN 81117 81117 81012,
    .loadN 81108 81117, .addN 81117 81117 81012, .loadN 81109 81117]

/-- **The reference arc.** -/
def refLoad : Stmt := .seq (Stmt.block refL1) (.seq (Stmt.block refL2) (Stmt.block refL3))

/-- The reads of the children. -/
def kidL : List Instr :=
  [.addN 81115 81134 81016, .addN 81115 81115 81012, .loadN 81115 81115,
    .addN 81115 81115 81121, .addN 81115 81115 81121, .addN 81115 81115 81121,
    .addN 81115 81115 81012, .loadN 81118 81115, .addN 81115 81115 81012, .loadN 81119 81115]

/-- **The children of the node.** -/
def kidLoad : Stmt := Stmt.block kidL

variable {E : FEnv} {c₀ c : Config}

theorem refLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N)
    (hdn : c.nreg 81156 < N.nRegions) (har : 0 < (N.region (c.nreg 81156)).arcs.length)
    (hj : (N.region (c.nreg 81156)).arcs.getD 0 0 < N.arcs.length) :
    FRS B E.P E.W c₀ refLoad c 25 (fun c' =>
      c'.nreg 81108 = (N.arc ((N.region (c.nreg 81156)).arcs.getD 0 0)).s.edge ∧
      c'.nreg 81109 = (N.arc ((N.region (c.nreg 81156)).arcs.getD 0 0)).s.hgt ∧
      ∀ q, q ≠ 81108 → q ≠ 81109 → q ≠ 81116 → q ≠ 81117 → c'.nreg q = c.nreg q) := by
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  obtain ⟨hB7, -, hab, hrb, hlb, -⟩ := nf_bounds hN'
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hrl : c.nreg 81156 < N.regions.length := hdn
  obtain ⟨-, -, -, hl, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  have rj := hl 0 har
  rw [Nat.add_zero] at rj
  obtain ⟨-, s1, s2, -, -⟩ := hNA.2.2.2.2.2.2.1 _ hj
  have b1 := hrb _ hdn
  have b2 := hlb _ hdn 0 har
  rw [Nat.add_zero] at b2
  have b3 := hab _ hj
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81015 = 5 ∧ c'.nreg 81016 = 7 ∧ c'.nreg 81014 = 3 ∧
      c'.nreg 81012 = 1 := fun c' h =>
    ⟨by rw [h.hin _ (by unfold FFix; omega), hE.k5], by rw [h.hin _ (by unfold FFix; omega), hE.k7],
      by rw [h.hin _ (by unfold FFix; omega), hE.k3], by rw [h.hin _ (by unfold FFix; omega), hE.k1]⟩
  obtain ⟨k5, k7, k3, k1⟩ := fx c hI
  -- stage 1
  have ok1 : okB E.W c.nmem refL1 c.nreg := by
    simp only [refL1, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k1]
    norm_num
    (repeat' apply And.intro) <;> omega
  refine FRS.seq (K₂ := 16) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem refL1 c.nreg q := fun q => by rw [h₁]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have v16 : c₁.nreg 81116 = c.nmem (c.nmem (c.nreg 81134 + 5) + 5 * c.nreg 81156 + 1) := by
    rw [e₁]; simp [refL1, regB, regI, upd, k5, k1]; congr 1; ring
  have f₁ : ∀ q, q ≠ 81116 → c₁.nreg q = c.nreg q := fun q hq => by
    rw [e₁]; refine regB_other _ _ _ (fun i hi => ?_)
    simp only [refL1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
  obtain ⟨-, k7₁, -, -⟩ := fx c₁ hI₁
  have w34 := f₁ 81134 (by norm_num)
  -- stage 2
  have ok2 : okB E.W c₁.nmem refL2 c₁.nreg := by
    simp only [refL2, okB, okI, regI, upd]
    simp only [FScr, FOut, k7₁, w34, v16, m₁]
    norm_num
    (repeat' apply And.intro) <;> omega
  refine FRS.seq (K₂ := 12) (FRS.block hB _ hI₁ ok2) (fun c₂ hI₂ hA₂ h₂ => ?_)
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem refL2 c₁.nreg q := fun q => by rw [h₂]
  have m₂ : c₂.nmem = c.nmem := by rw [h₂, m₁]
  have v16' : c₂.nreg 81116 = (N.region (c.nreg 81156)).arcs.getD 0 0 := by
    rw [e₂]; simp [refL2, regB, regI, upd, k7₁, w34, v16, m₁]; exact rj
  have f₂ : ∀ q, q ≠ 81116 → q ≠ 81117 → c₂.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₂, regB_other _ _ _ (fun i hi => ?_), f₁ q h1]
    simp only [refL2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
  obtain ⟨-, -, k3₂, k1₂⟩ := fx c₂ hI₂
  have x34 := f₂ 81134 (by norm_num) (by norm_num)
  have e4 : c.nreg 81134 + 3 + 1 = c.nreg 81134 + 4 := by ring
  generalize hjdef : (N.region (c.nreg 81156)).arcs.getD 0 0 = j at v16' b3 s1 s2 ⊢
  -- stage 3
  have ok3 : okB E.W c₂.nmem refL3 c₂.nreg := by
    simp only [refL3, okB, okI, regI, upd]
    simp only [FScr, FOut, k3₂, k1₂, x34, v16', m₂]
    norm_num
    rw [e4]
    (repeat' apply And.intro) <;> omega
  refine (FRS.block hB _ hI₂ ok3).mono (by simp [refL3]) (fun c₃ h₃ => ?_)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem refL3 c₂.nreg q := fun q => by rw [h₃]
  have ea : c.nmem (c.nreg 81134 + 4) + j + j + j + j + j + 1 =
      c.nmem (c.nreg 81134 + 4) + 5 * j + 1 := by ring
  refine ⟨?_, ?_, fun q h1 h2 h3 h4 => ?_⟩
  · rw [e₃]; simp [refL3, regB, regI, upd, k3₂, k1₂, x34, v16', m₂, e4]; rw [ea, s1]
  · rw [e₃]; simp [refL3, regB, regI, upd, k3₂, k1₂, x34, v16', m₂, e4]
    rw [ea, show c.nmem (c.nreg 81134 + 4) + 5 * j + 1 + 1 = c.nmem (c.nreg 81134 + 4) + 5 * j + 2
      by ring, s2]
  · rw [e₃, regB_other _ _ _ (fun i hi => ?_), f₂ q h3 h4]
    simp only [refL3, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> omega

theorem kidLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N)
    (hk : c.nreg 81121 < N.dec.length) :
    FRS B E.P E.W c₀ kidLoad c 10 (fun c' =>
      c'.nreg 81118 = (N.dnode (c.nreg 81121)).lo ∧ c'.nreg 81119 = (N.dnode (c.nreg 81121)).hi ∧
      ∀ q, q ≠ 81115 → q ≠ 81118 → q ≠ 81119 → c'.nreg q = c.nreg q) := by
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  have hdb := dec_bound hN' hk
  have hB8 : c.nreg 81134 + 11 < c₀.nreg ALLOC := by
    have := robust_addr (v := N.dec.length) fun m' hm' => (hN' m' hm').2.2.2.2.1
    omega
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  obtain ⟨-, r1, r2⟩ := hNA.2.2.2.2.2.2.2.2.2.1 _ hk
  have k7 : c.nreg 81016 = 7 := by rw [hI.hin _ (by unfold FFix; omega), hE.k7]
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by unfold FFix; omega), hE.k1]
  set k := c.nreg 81121
  set B8 := c.nmem (c.nreg 81134 + 8)
  have e8 : c.nreg 81134 + 7 + 1 = c.nreg 81134 + 8 := by ring
  have ok : okB E.W c.nmem kidL c.nreg := by
    simp only [kidL, okB, okI, regI, upd]
    simp only [FScr, FOut, k7, k1]
    norm_num
    rw [e8]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  refine (FRS.block hB _ hI ok).mono (by simp [kidL]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem kidL c.nreg q := fun q => by rw [h']
  have ea : B8 + k + k + k + 1 = B8 + 3 * k + 1 := by ring
  refine ⟨?_, ?_, fun q h1 h2 h3 => ?_⟩
  · rw [e']; simp [kidL, regB, regI, upd, k7, k1, e8]; rw [ea, r1]
  · rw [e']; simp [kidL, regB, regI, upd, k7, k1, e8]; rw [ea, show B8 + 3 * k + 1 + 1 = B8 + 3 * k + 2
      by ring, r2]
  · rw [e']
    refine regB_other _ _ _ (fun i hi => ?_)
    simp only [kidL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;>
      omega

end

end Restore

end Chazelle.Core
