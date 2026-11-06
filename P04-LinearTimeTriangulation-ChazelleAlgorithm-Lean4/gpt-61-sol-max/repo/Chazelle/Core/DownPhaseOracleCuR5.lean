module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleCuR4

/-!
# WP-M (E7-B, RAM part 19): the assembly of the answer, executed

`asmC_exec`: from the recorded slots (valid below the allocator `O`, flags bits), the assembly
writes at `O` the number of pieces and from `O + 1` the translated pieces of the slots, oldest
first (`ps = (slotsOf c 4).flatMap (slotPcs m n)`), sets the answer register `150010 := O` and
the allocator past the list, within `42 |ps| + 60` steps, in the frame of the interior oracles.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-- The registers the assembly writes in band `17`. -/
def Basm' (r : ℕ) : Bool := Basm r || decide (r = 170221)

theorem basm_io {r : ℕ} (h : Basm' r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band' (Or.inl (by ram_grind))

section exec

variable {P : Polygon} {W : ℕ}

set_option maxRecDepth 20000 in
theorem asm_cost {k₂ k₃ k₄ k₅ L1 L2 L3 L4 : ℕ} (h2 : k₂ + 42 * 0 ≤ 42 * L1 + 12)
    (h3 : k₃ + 42 * L1 ≤ 42 * L2 + 12) (h4 : k₄ + 42 * L2 ≤ 42 * L3 + 12)
    (h5 : k₅ + 42 * L3 ≤ 42 * L4 + 12) : 3 + (k₂ + (k₃ + (k₄ + (k₅ + 3)))) ≤ 42 * L4 + 60 := by
  omega

theorem asm_low {k₂ k₃ k₄ k₅ L1 L2 L3 L4 : ℕ} (h2 : 7 * L1 ≤ 7 * 0 + k₂)
    (h3 : 7 * L2 ≤ 7 * L1 + k₃) (h4 : 7 * L3 ≤ 7 * L2 + k₄) (h5 : 7 * L4 ≤ 7 * L3 + k₅) :
    1 + 7 * L4 ≤ 3 + (k₂ + (k₃ + (k₄ + (k₅ + 3)))) := by
  omega

/-- **The assembly of the answer.** -/
theorem asmC_exec (c : Config) (hw : WordsBounded W c) {n Hγ e₁ : ℕ} {V0 V : ℝ}
    (h10 : c.nreg 170010 = n) (h11 : c.nreg 170011 = 1) (hn : n = (Qof P).n) (hnW : 2 * n ≤ W)
    (hok : SlotsOK P c.nmem (c.nreg ALLOC) Hγ e₁ V0 (slotsOf c 4) V)
    (hbit : ∀ j, j < 4 → c.nreg (170200 + 5 * j) ≤ 1)
    (hroom : c.nreg ALLOC + 42 * ((slotsOf c 4).flatMap (slotPcs c.nmem n)).length + 60 ≤ W) :
    ∃ c' k, Exec P W asmC c c' k ∧
      k ≤ 42 * ((slotsOf c 4).flatMap (slotPcs c.nmem n)).length + 60 ∧
      c'.nreg 150010 = c.nreg ALLOC ∧
      c'.nmem (c.nreg ALLOC) = ((slotsOf c 4).flatMap (slotPcs c.nmem n)).length ∧
      (∀ j (hj : j < ((slotsOf c 4).flatMap (slotPcs c.nmem n)).length) f, f < 7 →
        c'.nmem (c.nreg ALLOC + 1 + 7 * j + f) =
          pcW (((slotsOf c 4).flatMap (slotPcs c.nmem n))[j]'hj) f) ∧
      c'.nreg ALLOC = c.nreg ALLOC + 1 + 7 * ((slotsOf c 4).flatMap (slotPcs c.nmem n)).length ∧
      Frame ioBands c c' k := by
  set O := c.nreg ALLOC with hO
  set Lf : ℕ → ℕ := fun j => ((slotsOf c j).flatMap (slotPcs c.nmem n)).length with hLf
  have hL0 : Lf 0 = 0 := by grind [slotsOf]
  have hLle : ∀ j, j ≤ 4 → Lf j ≤ Lf 4 := fun j hj => flat_le hj
  -- the start
  have hA9 : c.nreg 9999 = O := rfl
  obtain ⟨c₁, k₁, x₁, hk₁, a21, a22, a23, ar, am⟩ : ∃ c₁ k₁, Exec P W asmInit c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 170221 = O ∧ c₁.nreg 170222 = O + 1 ∧ c₁.nreg 170223 = 0 ∧
      (∀ r, r ≠ 170221 → r ≠ 170222 → r ≠ 170223 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    unfold asmInit
    exec_block
    all_goals (grind [upd])
  have F₁ : BuildRam.FrameM Basm' c c₁ := BuildRam.exec_frameM x₁ (by decide)
  have A₁ : AsmSt c.nmem n O (slotsOf c 0) c₁ :=
    ⟨a21, by ram_grind, by ram_grind, fun a _ => by rw [am],
      fun j hj => by ram_grind⟩
  -- one slot
  have step : ∀ k, k < 4 → ∀ d : Config, WordsBounded W d → AsmSt c.nmem n O (slotsOf c k) d →
      BuildRam.FrameM Basm' c d →
      ∃ d' k', Exec P W (asmK k) d d' k' ∧ k' + 42 * Lf k ≤ 42 * Lf (k + 1) + 12 ∧
        7 * Lf (k + 1) ≤ 7 * Lf k + k' ∧ AsmSt c.nmem n O (slotsOf c (k + 1)) d' ∧
        BuildRam.FrameM Basm' c d' := fun k hk d wd hA hF => by
    have hsl : ∀ r, 170200 ≤ r → r < 170220 → d.nreg r = c.nreg r := by
      intro r r1 r2
      apply hF.1 r
      core_grind
    obtain ⟨d', k', e', h1, h2, hA', F'⟩ := asmK_exec (P := P) k hk d wd (c₀ := c) (Hγ := Hγ)
      (e₁ := e₁) hA hsl
      ((hF.1 _ (by decide)).trans h10) ((hF.1 _ (by decide)).trans h11) (hbit k hk)
      (fun hf => SlotsOK.mem hok _ (mem_slotsOf_of hf (by omega))) hn hnW
      (by ram_grind)
    exact ⟨d', k', e', h1, h2, hA', hF.trans (frameM_mono F' (fun r hr => by
      simp only [Basm', hr, Bool.true_or]))⟩
  obtain ⟨c₂, k₂, e₂, p2, q2, A₂, F₂⟩ := step 0 (by norm_num) c₁ x₁.wb_right A₁ F₁
  obtain ⟨c₃, k₃, e₃, p3, q3, A₃, F₃⟩ := step 1 (by norm_num) c₂ e₂.wb_right A₂ F₂
  obtain ⟨c₄, k₄, e₄, p4, q4, A₄, F₄⟩ := step 2 (by norm_num) c₃ e₃.wb_right A₃ F₃
  obtain ⟨c₅, k₅, e₅, p5, q5, A₅, F₅⟩ := step 3 (by norm_num) c₄ e₄.wb_right A₄ F₄
  rw [hL0] at p2 q2
  have w₅ := e₅.wb_right
  -- the end
  obtain ⟨c₆, k₆, e₆, hk₆, b10, bA, bm, br, brr, brm, bo⟩ : ∃ c₆ k₆, Exec P W finC c₅ c₆ k₆ ∧
      k₆ = 3 ∧ c₆.nreg 150010 = O ∧ c₆.nreg ALLOC = O + 1 + 7 * Lf 4 ∧
      c₆.nmem = upd c₅.nmem O (Lf 4) ∧ (∀ r, r ≠ 150010 → r ≠ ALLOC → c₆.nreg r = c₅.nreg r) ∧
      c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have g21 := A₅.r21
    have g22 := A₅.r22
    have g23 := A₅.r23
    unfold finC
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
    · config_simp; exact g21
    · omega_nf
    · ram_simp <;> omega_nf
    · config_simp; unfold ALLOC at h2; ram_simp <;> omega_nf
  have ex : Exec P W asmC c c₆ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆))))) :=
    .seq x₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆))))
  have hk := asm_cost p2 p3 p4 p5
  have hl := asm_low q2 q3 q4 q5
  simp only [Nat.reduceAdd] at hl hk
  refine ⟨c₆, _, ex, by ram_grind, b10, by ram_simp <;> omega_nf, fun j hj f hf => ?_,
    bA, ⟨fun r hr ha => ?_, fun r hr => ?_, fun a ha => ?_, fun a _ => ?_, by rw [bo, F₅.2.2.2],
      by omega, by omega⟩⟩
  · rw [bm, upd_other _ _ _ (by omega)]
    exact A₅.out j hj f hf
  · have hb : Basm' r = false := by
      cases hB : Basm' r
      · rfl
      · exact absurd (basm_io hB).1 hr
    rw [br r (fun h => hr (by rw [h]; unfold bandOf ioBands oracleBands; decide)) ha]
    exact F₅.1 r hb
  · have hb : Basm' r = false := by
      cases hB : Basm' r
      · rfl
      · exact absurd (basm_io hB).1 hr
    rw [brr]; exact F₅.2.1 r hb
  · rw [bm, upd_other _ _ _ (by omega)]
    exact A₅.lo a (by omega)
  · rw [brm, F₅.2.2.1]

end exec

end

end IOrc

end Chazelle.Core
