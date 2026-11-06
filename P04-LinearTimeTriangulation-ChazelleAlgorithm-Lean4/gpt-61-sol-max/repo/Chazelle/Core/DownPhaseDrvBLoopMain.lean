module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvBLoop

/-!
# Down-phase base (D9): the region loop meets its contract

`regLoopSpec_of (hS : RegStepSpec s κR) : RegLoopSpec` with the program `regLoopS s` and the cost
constant `κR + 60`.
-/

namespace Chazelle.Core

namespace DrvB

open Machine Machine.Stmt Programs BuildRam SignK
open BuildNF (codeLe)

@[expose] public section


theorem room_aux {κR K X r : ℕ} (hr : r + 1 ≤ K + 1) :
    (r + 1) * (κR * X) ≤ (κR + 60) * (K + 1) * X := by
  have h1 : (r + 1) * (κR * X) ≤ (K + 1) * (κR * X) := Nat.mul_le_mul_right _ hr
  grind

set_option maxHeartbeats 8000000 in
/-- **The region loop of the base case.** -/
theorem regLoopSpec_of {s : Stmt} {κR : ℕ} (hS : RegStepSpec s κR) : RegLoopSpec := by
  refine ⟨regLoopS s, κR + 60, ?_⟩
  intro P W c L E S₀ Cm hw hpre hroom
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hpre.hG.1
  obtain ⟨-, -, -, reg, g1, g2, g3, g4, -⟩ := DownMath.isNF_build hQ hpre.hok hpre.hperm hpre.hsort
  set Ev : BEnv := ⟨P, W, L, E, reg, c.nmem, c.nreg 210001, c.nreg 210005, c.nreg 212019, S₀, Cm⟩
    with hEv
  -- sizes
  set X := (S₀ + 1) * (Cm + 1) with hXdef
  
  have hT : (κR + 60) * (L.length + 1) * (S₀ + 1) * (Cm + 1) = (κR + 60) * (L.length + 1) * X := by
    grind
  have hper : κR * (S₀ + 1) * (Cm + 1) = κR * X := by grind
  rw [hT] at hroom ⊢
  have hKX : L.length + 1 ≤ (κR + 60) * (L.length + 1) * X := by
    grind
  
  have hBW : c.nreg 212019 + 10 * P.n ≤ W := by have := hpre.hroom; omega
  -- the facts of the data
  have hE : BGood Ev := by
    refine ⟨hpre.hG, hpre.hWh, hpre.hok, hpre.hperm, hpre.hsort, hpre.hdeg, ⟨g1, g2, g3, g4⟩,
      hpre.hNF, hpre.hMD, hpre.hMDW, hBW, hpre.hS₀, ?_⟩
    intro r hr t ht
    show (if L.length = 0 then P.n else _) ≤ Cm
    by_cases hK : L.length = 0
    · rw [ite_eq_left hK]; exact hpre.hCm0 hK
    · rw [ite_eq_right hK]
      have ht' : t < ((BuildNF.buildNF (interiorModel (Qof P)) (Qof P) L E).region r).arcs.length := by
        simp_all [BEnv.nRg] 
      apply hpre.hCm r hr
      simp_all
  -- bounds of the initialisation
  have hNw := hpre.hNF
  obtain ⟨nb1, -, -, nb4, -, -⟩ := Restore.nf_bounds hNw
  have hR0 := nb4 0 (by rw [hE.nRegions]; omega)
  have hn : P.n ≤ W := by omega
  -- initialisation
  obtain ⟨d1, k1, e1, hk1, a00, a01, a02, a10, a11, a12, b02, b03, b05, b06, b14, b16, b17, b31,
      a13, a14, a18, b20, b21, b22, f1⟩ := regInit_exec (P := P) c hw rfl hpre.hK rfl rfl hn
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by have := hpre.hMDW; omega)
  have hw1 := e1.wb_right
  have q1 : ∀ r, Binit r = false → d1.nreg r = c.nreg r := f1.1
  have hfix : ∀ q, (210000 ≤ q ∧ q < 210030) ∨ q = 212019 → Binit q = false := fun q hq => by
    grind [Binit, decide_eq_false_iff_not]
  have hregs : BRegs Ev d1 := by
    refine ⟨a00, a01, a02, a10, ?_, a12, b02, b03, b05, b14, b16, ?_,
      by grind, by grind⟩
    · rw [a11]; show _ = if decide (c.nmem (c.nreg 210001 + 1) = 1) = true then 1 else 0
      ram_grind
    · rw [b17]; exact hNw.nfAt.2.1
  have hmem1 : d1.nmem = c.nmem := f1.2.2.1
  have hal1 : d1.nreg ALLOC = c.nreg ALLOC := f1.1 9999 (by decide)
  have hrst0 : RSt Ev 0 d1 := by
    refine ⟨hw1, hregs, b06, a14, by ram_simp <;> omega_nf,
      fun r hr => absurd hr (Nat.not_lt_zero _), by omega, ?_,
      by have := hpre.hroom; ram_grind⟩
    refine ⟨by rw [b20]; rfl, by rw [b21]; rfl, by rw [b22]; rfl, ?_, ?_, ?_, ?_⟩
    · intro i hi; simp [BEnv.TL] at hi
    · intro _; exact ⟨fun q hq => by grind [BEnv.TL], fun q hq => by grind [BEnv.TL]⟩
    · intro _ q hq; simp [BEnv.TL] at hq
    ram_grind
  have hRF1 : Restore.RF DrvR.drvBands (c.nreg 212019) c d1 k1 := by
    have hB : ∀ r, bandOf r ∉ DrvR.drvBands → Binit r = false := fun r hr => by
      simp only [Binit, decide_eq_false_iff_not]
      have : r / 10000 ≠ 21 := fun h => hr (by
        show r / 10000 ∈ DrvR.drvBands
        rw [h]; decide)
      omega
    refine ⟨fun r hr _ => f1.1 r (hB r hr), fun r hr => f1.2.1 r (hB r hr),
      fun a _ => by rw [hmem1], fun a _ => by rw [f1.2.2.2.1], f1.2.2.2.2, ?_, ?_⟩ <;>
      rw [hal1]; omega
  -- the loop
  set A := c.nreg ALLOC with hAdef
  let I : Config → Prop := fun d => ∃ r, r ≤ L.length + 1 ∧ RSt Ev r d ∧
    d.nreg 212013 = L.length + 1 ∧ d.nreg ALLOC ≤ A + r * (κR * X) ∧
    ∀ q, (FixB q ∨ q = 212013 ∨ q = 216006) → d.nreg q = d1.nreg q
  have hI1 : I d1 := ⟨0, by omega, hrst0, a13, by omega,
    fun _ _ => rfl⟩
  obtain ⟨d', k', e', ⟨r', hr', rst', h13', hal', keep'⟩, hnot, rf', hk'⟩ :=
    Restore.whileLtN_frame (P := P) (W := W) (a := 212014) (b := 212013) (body := s)
      (B := DrvR.drvBands) (A₀ := c.nreg 212019) I (fun d => L.length + 1 - d.nreg 212014) (κR * X)
      (fun d ⟨_, _, h, _⟩ => h.wb)
      (fun d ⟨r, hr, rst, h13, hal, keep⟩ hlt => by
        have hr1 : r < L.length + 1 := by rw [rst.r14, h13] at hlt; exact hlt
        have hroomr : d.nreg ALLOC + κR * (Ev.S₀ + 1) * (Ev.Cm + 1) ≤ Ev.W := by
          show d.nreg ALLOC + κR * (S₀ + 1) * (Cm + 1) ≤ W
          rw [hper]
          have := room_aux (κR := κR) (X := X) (r := r) (K := L.length) (by omega)
          ram_grind
        obtain ⟨d'', k, ex, hk, rst'', rf, kp⟩ := hS Ev hE r d hr1 rst hroomr
        have hk' : k ≤ κR * X := by grind
        refine ⟨d'', k, ex, ⟨r + 1, by omega, rst'', by grind,
          ?_, fun q hq => (kp q hq).trans (keep q hq)⟩, rf, hk', ?_⟩
        · have := rf.2.2.2.2.2.2
          ram_grind
        · rw [rst''.r14, rst.r14]; omega)
      hI1
  have hr'K : r' = L.length + 1 := by
    rw [rst'.r14, h13'] at hnot; omega
  subst hr'K
  -- the cost
  have hk : k1 + k' ≤ (κR + 60) * (L.length + 1) * X := by
    have hμ : L.length + 1 - d1.nreg 212014 = L.length + 1 := by omega
    rw [hμ] at hk'
    grind
  refine ⟨d', k1 + k', .seq e1 e', hk, ?_, hRF1.trans rf'⟩
  -- the postcondition
  have hout := rst'.out
  
  obtain ⟨m1, m2, m3, m4⟩ := bktMath Ev hE (fun q => d'.nmem (Ev.BK + q)) (d'.nreg 212018)
    hout.bk hout.bk0 rst'.mx
  have hnl : (newLB (liBit c.nmem (c.nreg 210001)) (Qof P) L E).length =
      (Ev.TL (L.length + 1)).length := by
    show ((tagLB Ev.li Ev.Q Ev.L Ev.E).map Prod.snd).length = _
    rw [List.length_map]; rfl
  refine ⟨fun q hq1 hq2 => ?_, ?_, ?_, m1, hout.list, fun q hq => m2 q hq,
    fun q q' hq hq' h => m3 q q' hq hq' h, m4, rst'.mxS⟩
  · rw [keep' q (Or.inl (Or.inl ⟨hq1, hq2⟩)), q1 q (hfix q (Or.inl ⟨hq1, hq2⟩))]
  · rw [keep' 212019 (Or.inl (Or.inr (Or.inr (Or.inl rfl)))), q1 _ (hfix _ (Or.inr rfl))]
  · rw [hout.cnt, hnl]

end

end DrvB

end Chazelle.Core
