module

public import Chazelle.Core.NFBuildPhaseB2

/-!
# WP-C (BuildNF), RAM part 24: phase B writes `buildNF`

`phaseB_exec`: from the state after the sort (`K > 0`), `phaseB = phaseB1; regPhase` writes the
normal form `buildNF M Q L E` at `H = ALLOC` (`NFWithin` below the new allocator
`H + sizeB K`), with the handle in `r40003`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK NFLoc
open BuildNF (cf af chordRec arcRec gapStarts keyA wA upC dnC stk gapsB cw)

@[expose] public section

/-- **Phase B** (`K > 0`). -/
def phaseB : Stmt := .seq phaseB1 regPhase

/-- The registers phase B writes: bands `bSign`, `bBuild` and the allocator. -/
def BphaseB (r : ℕ) : Bool :=
  decide (r = 9999 ∨ (10000 ≤ r ∧ r < 20000) ∨ (40000 ≤ r ∧ r < 50000))

theorem wr_phaseB : wrM BphaseB phaseB = true := by
  have h1 : wrM BphaseB setupB = true := wrM_of_wr (wr_mono (fun r hr => by
    simp only [BsetupB, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [BphaseB, decide_eq_true_eq]; omega) wr_setupB)
  have h2 : wrM BphaseB lohiS = true := wrM_of_wr (wr_mono (fun r hr => by
    simp only [decide_eq_true_eq] at hr
    simp only [BphaseB, decide_eq_true_eq]; omega) wr_lohiS)
  have h3 : wrM BphaseB passLoop = true := by
    have := wrM_mono (B' := BphaseB) (fun r hr => ?_) wr_passBody
    · simp only [passLoop, wrM]; exact this
    · cases hb : Bpass r
      · rw [hb] at hr; exact absurd hr (by simp)
      · by_contra hc
        simp only [BphaseB, decide_eq_true_eq, not_or, not_and, not_lt] at hc
        have : Bpass r = false := Bpass_false (by omega)
        rw [this] at hb; exact absurd hb (by simp)
  have h4 : wrM BphaseB regPhase = true := wrM_mono (fun r hr => by
    simp only [BregPhase, Bool.or_eq_true, decide_eq_true_eq] at hr
    simp only [BphaseB, decide_eq_true_eq]; omega) wr_regPhase
  simp only [phaseB, phaseB1, wrM, h1, h2, h3, h4, Bool.and_self]

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Phase B writes the normal form.** -/
theorem phaseB_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {M : Model} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {D T SE B H : ℕ}
    (hI : BuildNF.Input M (Qof P) L E) (hK : 0 < L.length)
    (hD : c.nreg 40000 = D) (hT : c.nreg 42000 = T) (hN : c.nreg 42001 = 2 * L.length)
    (hB : c.nreg 43001 = B) (hKr : c.nreg 43002 = L.length) (h0 : c.nreg 43010 = 0)
    (h1 : c.nreg 43011 = 1) (hSEr : c.nreg 30005 = SE) (hH : c.nreg 9999 = H)
    (hwf : ModelDescWF P H c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hR : RecsAt c.nmem T L) (hTH : T + 8 * L.length ≤ H) (hCL : ChordListAt c.nmem B L)
    (hBH : B + 3 * L.length ≤ H) (hSE : ∀ j, j < E.length → c.nmem (SE + j) = E.getD j 0)
    (hSEH : SE + E.length ≤ H) (hroom : H + sizeB L.length ≤ W) :
    ∃ c' k, Exec P W phaseB c c' k ∧ k ≤ 23604 * L.length + 200 ∧
      sizeB L.length ≤ k ∧ FrameM BphaseB c c' ∧
      c'.nreg 40003 = H ∧ c'.nreg 9999 = H + sizeB L.length ∧
      (∀ a, a < H → c'.nmem a = c.nmem a) ∧
      NFWithin c'.nmem H (c'.nreg 9999) (BuildNF.buildNF M (Qof P) L E) := by
  set K := L.length with hKdef
  have hlen : E.length = 2 * K := hI.length_E
  obtain ⟨c₃, k₃, x₃, hk₃, hk₃', w₃, C₃, F, c₂, I⟩ := phaseB1_exec (P := P) hG hWn c hw hI hlen
    hD hT hN hB hKr h0 h1 hSEr hH hwf hM hR hTH hCL hBH hSE hSEH hroom
  have hgs : gapsB M (Qof P) L E E.length = gapStarts M (Qof P) L E := BuildNF.gapsB_full _ _ _ _
  set A := (gapStarts M (Qof P) L E).length with hAdef
  have hAle : A ≤ 2 * K := by
    rw [hAdef, ← hgs]; have := BuildNF.gapsB_length_le M (Qof P) L E E.length; omega
  have htake : (cw E).take E.length = cw E := by
    rw [List.take_of_length_le (by simp [cw])]
  -- the tables of the pass
  have hkey : ∀ j, j < A → c₃.nmem (H + 12 + 5 * K + 5 * j) = keyA M (Qof P) L E j := fun j hj => by
    have := (I.arcs j (by rwa [hgs])).1 0 (by norm_num)
    rw [Nat.add_zero, hgs] at this
    rw [this]; rfl
  have hkR : ∀ j, j < A → keyA M (Qof P) L E j < K + 1 := fun j _ => by
    unfold keyA; rw [BuildNF.arcRec_eq]; have := BuildNF.topR_le hI ((gapStarts M (Qof P) L E).getD j 0 + 1)
    simp only; omega
  have hwt : ∀ j, j < A → c₃.nmem (H + 17 + 28 * K + j) = wA M (Qof P) L E j := fun j hj => by
    have := (I.arcs j (by rwa [hgs])).2
    rw [hgs] at this
    rw [this]; rfl
  have hch : ∀ i, i < K → ∀ f, f < 5 → c₃.nmem (H + 12 + 5 * i + f) = cf (chordRec M (Qof P) L E i) f :=
    fun i hi f hf => I.chords i hi (by rw [htake]; exact BuildNF.mem_cw hI hi) f hf
  have hu : ∀ i, i < K → c₃.nmem (H + 12 + 5 * i + 3) = upC M (Qof P) L E i := fun i hi => by
    rw [hch i hi 3 (by norm_num)]; rfl
  have hv : ∀ i, i < K → c₃.nmem (H + 12 + 5 * i + 4) = dnC M (Qof P) L E i := fun i hi => by
    rw [hch i hi 4 (by norm_num)]; rfl
  have huR : ∀ i, i < K → upC M (Qof P) L E i < K + 1 := fun i hi => by
    have := (BuildNF.chordRec_up_le hI hi).1; unfold upC; omega
  have hvR : ∀ i, i < K → dnC M (Qof P) L E i < K + 1 := fun i hi => by
    have := (BuildNF.chordRec_up_le hI hi).2; unfold dnC; omega
  have hA₃ : c₃.nreg 43102 = A := by rw [I.r102, hgs]
  -- the region phase
  obtain ⟨c', k, x, hk, hk', f', h40003, T1, T2, T3, T4, T5, T6⟩ := regPhase_exec (P := P) c₃ w₃
    C₃ hA₃ hAle hkey hkR hwt hu hv huR hvR hroom
  have C' := C₃.frame f' (by decide)
  have X : Exec P W phaseB c c' (k₃ + k) := .seq x₃ x
  refine ⟨c', _, X, by omega, by unfold sizeB; omega, exec_frameM X wr_phaseB, h40003, C'.rA,
    fun a ha => by rw [T2 a (Or.inl ha), I.low a ha], ?_⟩
  -- the normal form
  intro m' hm'
  rw [C'.rA] at hm'
  have hoff : offF (cntF (keyA M (Qof P) L E) A) (cnt2F (upC M (Qof P) L E) (dnC M (Qof P) L E) K)
      (K + 1) ≤ A + 2 * K := offF_R_le _ _ _ hkR
  have hK0 : K ≠ 0 := by omega
  refine BuildNF.nfAt_of_tables hI hK0 (H := H) (CT := H + 12) (AT := H + 12 + 5 * K)
    (RT := H + 12 + 15 * K) (QT := H + 17 + 20 * K) (LT := H + 17 + 22 * K)
    (fun f hf => by rw [hm' _ (by unfold sizeB; omega), T1 f hf])
    (fun i hi f hf => by
      rw [hm' _ (by unfold sizeB; omega), T2 _ (Or.inr (by omega)), hch i hi f hf])
    (fun j hj f hf => by
      rw [hm' _ (by unfold sizeB; omega), T2 _ (Or.inr (by omega))]
      have := (I.arcs j (by rwa [hgs])).1 f hf
      rw [hgs] at this
      rw [show H + 12 + 5 * K + 5 * j + f = H + 12 + 5 * K + 5 * j + f from rfl, this])
    (fun r hr f hf => by rw [hm' _ (by unfold sizeB; omega), T3 r hr f hf])
    (fun r hr t ht => by
      simp only [← hAdef, ← hKdef] at ht hr ⊢
      have := offF_succ (cntF (keyA M (Qof P) L E) A)
        (cnt2F (upC M (Qof P) L E) (dnC M (Qof P) L E) K) r
      have := offF_mono (cntF (keyA M (Qof P) L E) A)
        (cnt2F (upC M (Qof P) L E) (dnC M (Qof P) L E) K) (show r + 1 ≤ K + 1 by omega)
      rw [hm' _ (by unfold sizeB; omega), T4 r hr t ht])
    (fun r hr t ht => by
      simp only [← hAdef, ← hKdef] at ht hr ⊢
      have := offF_succ (cntF (keyA M (Qof P) L E) A)
        (cnt2F (upC M (Qof P) L E) (dnC M (Qof P) L E) K) r
      have := offF_mono (cntF (keyA M (Qof P) L E) A)
        (cnt2F (upC M (Qof P) L E) (dnC M (Qof P) L E) K) (show r + 1 ≤ K + 1 by omega)
      rw [hm' _ (by unfold sizeB; omega), T5 r hr t ht])
    (fun j hj => by rw [hm' _ (by unfold sizeB; omega), T6 j hj])

end exec

end

end BuildRam

end Chazelle.Core
