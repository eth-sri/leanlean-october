module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepEvInit5

/-!
# The sweep (WP-D), stages 2–3: the assembly (task Z)

**`asmTask : AsmTask`**: from an initialisation (`InitTask`) and the run steps (`RunTask`), the
program `init ; run sh ; fin` meets `SweepEvSpec`, with `κ D = κI + κR D + 5`.

* the junction and the normal form `N₂` quantified in `Post` are those of the environment: the
  junction by `junction_unique`; a normal form readable at the handle of `N₂` and valid has the
  same chord, arc, region and sequence records (`nf_recs_eq`), and the outputs `Out` depend on
  nothing else (`out_congr`);
* the frame: the initialisation's frame, the run steps' relative frame with the invariant `IInv`
  (`frame_of_irs`) and the register frame of `fin`.

-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-! ## The normal form of the post -/

/-- Lists with the same length and entries are equal. -/
theorem list_ext_getD' {α : Type} {l l' : List α} (x : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i x = l'.getD i x) : l = l' :=
  List.ext_getElem hl fun i h1 h2 => by
    simp_all

/-- **The layout and validity determine the records**: two valid normal forms readable at the
same handle have the same chord, arc, region and sequence records. -/
theorem nf_recs_eq {m : ℕ → ℕ} {B : ℕ} {M M' : Model} {Q Q' : Polygon} {N N' : NF}
    (h : NFAt m B N) (h' : NFAt m B N') (hN : IsNF M Q N) (hN' : IsNF M' Q' N') :
    N.chords = N'.chords ∧ N.arcs = N'.arcs ∧ N.regions = N'.regions ∧ N.seq = N'.seq := by
  obtain ⟨c0, a0, r0, -, -, hc, ha, hr, hs, -⟩ := h
  obtain ⟨c0', a0', r0', -, -, hc', ha', hr', hs', -⟩ := h'
  have hA : N.arcs = N'.arcs := list_ext_getD' ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ (by omega) fun j hj => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := ha j hj
    obtain ⟨b1, b2, b3, b4, b5⟩ := ha' j (by omega)
    change N.arc j = N'.arc j
    rcases hx : N.arc j with ⟨x1, ⟨x2, x3⟩, ⟨x4, x5⟩⟩
    rcases hy : N'.arc j with ⟨y1, ⟨y2, y3⟩, ⟨y4, y5⟩⟩
    rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
    simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    simp only [ARec.mk.injEq, WPos.mk.injEq]; omega
  obtain ⟨-, -, -, reg, -, -, -, -, hS, -⟩ := hN
  obtain ⟨-, -, -, reg', -, -, -, -, hS', -⟩ := hN'
  have hl : N.seq.length = N.arcs.length := by rw [hS.1.length_eq, List.length_range]
  have hl' : N'.seq.length = N'.arcs.length := by rw [hS'.1.length_eq, List.length_range]
  refine ⟨list_ext_getD' ⟨0, 0, 0, 0, 0⟩ (by omega) fun i hi => ?_, hA,
    list_ext_getD' ⟨[], [], 0⟩ (by omega) fun q hq => ?_,
    list_ext_getD' 0 (by omega) fun t ht => by
      rw [← hs t ht, ← hs' t (by omega)]⟩
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hc i hi
    obtain ⟨b1, b2, b3, b4, b5⟩ := hc' i (by omega)
    change N.chord i = N'.chord i
    rcases hx : N.chord i with ⟨x1, x2, x3, x4, x5⟩
    rcases hy : N'.chord i with ⟨y1, y2, y3, y4, y5⟩
    rw [hx] at a1 a2 a3 a4 a5; rw [hy] at b1 b2 b3 b4 b5
    simp only at a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    simp only [CRec.mk.injEq]; omega
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hr q hq
    obtain ⟨b1, b2, b3, b4, b5⟩ := hr' q (by omega)
    change N.region q = N'.region q
    have harcs : (N.region q).arcs = (N'.region q).arcs :=
      list_ext_getD' 0 (by omega) fun t ht => by rw [← a4 t ht, ← b4 t (by omega)]
    have hchs : (N.region q).chords = (N'.region q).chords :=
      list_ext_getD' 0 (by omega) fun t ht => by rw [← a5 t ht, ← b5 t (by omega)]
    rcases hx : N.region q with ⟨x1, x2, x3⟩
    rcases hy : N'.region q with ⟨y1, y2, y3⟩
    rw [hx, hy] at harcs hchs; rw [hx] at a3; rw [hy] at b3
    simp only at harcs hchs a3 b3
    simp only [RRec.mk.injEq]; exact ⟨harcs, hchs, by omega⟩

/-- **The outputs depend only on the chord, arc, region and sequence records** of the normal
form (the decomposition fields are not read). -/
theorem out_congr {P : Polygon} {J : Merge.Junction} {N N' : NF} {c : Config}
    (hc : N.chords = N'.chords) (ha : N.arcs = N'.arcs) (hr : N.regions = N'.regions)
    (hs : N.seq = N'.seq) : Out P J N c → Out P J N' c := by
  obtain ⟨c1, a, r, s, d, ro, l⟩ := N
  aesop

/-! ## The finalisation -/

set_option maxRecDepth 20000 in
theorem finCfg_val (c : Config) :
    (finCfg c).nreg (sw 200) = c.nreg sB ∧ (finCfg c).nreg (sw 201) = c.nreg sC ∧
      (finCfg c).nreg (sw 300) = c.nreg lB ∧ (finCfg c).nreg (sw 301) = c.nreg lC ∧
      (finCfg c).nreg (sw 302) = c.nreg cTB ∧
      ∀ r, r ≠ sw 200 → r ≠ sw 201 → r ≠ sw 300 → r ≠ sw 301 → r ≠ sw 302 →
        (finCfg c).nreg r = c.nreg r := by
  simp_all [finCfg, finL, regB, regI, Config.nreg_mk, sB, sC, lB, lC, cTB, sw, Nat.reduceAdd, upd_same, ne_eq, upd_other, Nat.reduceEqDiff, not_false_eq_true] 

theorem fin_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c) :
    Exec P W fin c (finCfg c) 5 :=
  exec_regB finL hw (by simp_all [finL, okW, okWI] )

theorem fin_frame (c : Config) : Frame ioBands c (finCfg c) 5 := by
  obtain ⟨-, -, -, -, -, ho⟩ := finCfg_val c
  refine frame_regs 5 (fun r hr => ho r ?_ ?_ ?_ ?_ ?_) rfl rfl rfl rfl <;> rintro rfl <;>
    exact hr (sw_io (by omega_nf) (by omega_nf))

/-! ## Task Z -/

set_option maxRecDepth 20000 in
/-- **Task Z: the assembly.** -/
theorem asmTask : AsmTask := by
  rintro ⟨init, κI', hI⟩ ⟨run, κR, hR⟩
  refine ⟨fun sh => .seq init (.seq (run sh) fin), fun D => κI' + κR D + 5,
    fun sh Bs F X Ok hXl hBs hsh => ?_⟩
  intro P W c hw hpre hroom
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, H₀, J₀, N₁₀, N₂₀, hpa₀⟩ := hpre'
  have hpa : PreAt X Ok P c H₀ J₀ N₁₀ N₂₀ := hpa₀
  set K := c.nmem (rd c bSweep 3) + c.nmem (rd c bSweep 4) + 1 with hKd
  set M := F (rd c bSweep 5) + Nat.clog 2 K + 1 with hMd
  set D := rd c bSweep 6 with hDd
  have hM1 : 1 ≤ M := by omega
  have hcost : cost (fun D => κI' + κR D + 5) F P c = (κI' + κR D + 5) * K * M := rfl
  rw [hcost] at hroom ⊢
  have hIK : κI' * K ≤ κI' * K * M := Nat.le_mul_of_pos_right _ hM1
  have hRK : (κI' + κR D + 5) * K * M = κI' * K * M + κR D * K * M + 5 * K * M := by ring
  have hKM : 1 ≤ K * M := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hKM5 : 5 ≤ 5 * K * M := by grind
  obtain ⟨c₀, k₀, e₀, hk₀, fr₀, hw₀, hkeep, hEnv⟩ :=
    hI sh Bs F X Ok hXl hBs hsh P W c hw hpre (show c.nreg ALLOC + κI' * K ≤ W by omega)
  have hk₀' : k₀ ≤ κI' * K := hk₀
  have E := hEnv H₀ J₀ N₁₀ N₂₀ hpa
  have nN1 := hpa.2.2.2.2.1.nfAt
  have nN2 := hpa.2.2.2.2.2.1.nfAt
  have hK1 : N₁₀.nChords = c.nmem (rd c bSweep 3) := nN1.1.symm
  have hK2 : N₂₀.nChords = c.nmem (rd c bSweep 4) := nN2.1.symm
  have e5 : c₀.nreg (sw 5) = rd c bSweep 5 := hkeep 5 (by norm_num)
  have e6 : c₀.nreg (sw 6) = rd c bSweep 6 := hkeep 6 (by norm_num)
  have hA₀ : c₀.nreg ALLOC ≤ c.nreg ALLOC + k₀ := fr₀.2.2.2.2.2.2
  have hA₀' : c.nreg ALLOC ≤ c₀.nreg ALLOC := fr₀.2.2.2.2.2.1
  obtain ⟨c', k₁, e₁, hk₁, hII, hIFr, hout⟩ := hR sh Bs F X Ok P W c₀ J₀ N₁₀ N₂₀ E hw₀ (by
    ram_grind)
  rw [e5, e6, hK1, hK2] at hk₁
  have hk₁' : k₁ ≤ κR D * K * M := hk₁
  obtain ⟨hOut, s1, s2, l1, l2, t1, z1, z2⟩ := hout
  rw [hK1, hK2] at z1 z2
  rw [hK2] at t1
  obtain ⟨f200, f201, f300, f301, f302, fo⟩ := finCfg_val c'
  have hw' := e₁.wb_right
  have eTB : c'.nreg cTB = c₀.nreg cTB := hII.hin _ (by omega_nf)
  refine ⟨finCfg c', k₀ + (k₁ + 5), .seq e₀ (.seq e₁ (fin_exec hw')), by omega,
    ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun H J N₂ hJ hN₂ hNF₂ => ?_⟩, ?_⟩
  · rw [fo _ (by omega_nf) (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf), hII.hin _ (by omega_nf)]
    grind
  · show c.nreg ALLOC ≤ (finCfg c').nreg (sw 200)
    omega
  · show (finCfg c').nreg (sw 200) + 5 * (finCfg c').nreg (sw 201) ≤ (finCfg c').nreg ALLOC
    rw [f200, f201, fo _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf) (by omega_nf)]
    exact s2
  · show c.nreg ALLOC ≤ (finCfg c').nreg (sw 300)
    omega
  · show (finCfg c').nreg (sw 300) + 7 * (finCfg c').nreg (sw 301) ≤ (finCfg c').nreg ALLOC
    rw [f300, f301, fo _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf) (by omega_nf)]
    exact l2
  · show c.nreg ALLOC ≤ (finCfg c').nreg (sw 302)
    rw [f302, eTB]; have := E.hT; omega
  · show (finCfg c').nreg (sw 302) + 3 * (2 * c.nmem (rd c bSweep 4)) ≤ (finCfg c').nreg ALLOC
    rw [f302, fo _ (by omega_nf) (by omega_nf)
      (by omega_nf) (by omega_nf) (by omega_nf)]
    exact t1
  · show (finCfg c').nreg (sw 201) ≤ _
    omega
  · show (finCfg c').nreg (sw 301) ≤ _
    omega
  · have hJJ : J₀ = J := junction_unique hpa.1 hJ
    subst hJJ
    obtain ⟨hc, ha, hr, hs⟩ := nf_recs_eq nN2 hN₂ hpa.2.2.2.2.2.2.2.1 hNF₂
    exact out_congr hc ha hr hs hOut
  · have f₁ : Frame ioBands c₀ c' k₁ := frame_of_irs hII hIFr
    exact frame_ioB ((fr₀ : Frame ioBands c c₀ k₀).trans (frame_ioB (f₁.trans (fin_frame c'))))

end

end SweepEv

end Chazelle.Core
