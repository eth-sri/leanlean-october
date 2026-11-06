module

public import Chazelle.Golf

public import Chazelle.Core.SweepEvStepL9

/-!
# The sweep (WP-D), stage 3: Task L1 (one iteration of the event loop)

**`stepTask : StepTask`**: an iteration that does not finish keeps `LoopInv` (stops, layout,
next key and its labels, gap regions, stop pointer, log, measure, table) and lowers the number of
keys left.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

set_option maxHeartbeats 2000000 in
/-- **Task L1: one iteration that does not finish.** -/
theorem stepTask : StepTask := by
  intro sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' E L hI hd
  obtain ⟨-, -, A, hBA⟩ := hI.2.2.2.1
  obtain ⟨rs, ax, hD⟩ := L.stops
  have S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax :=
    ⟨E, L, hI, hd, hBA, hBA.val, hD⟩
  obtain ⟨hlt, hpw, -⟩ := stp_next_key E L hI hd
  obtain ⟨hmlt, hmeas, -, -⟩ := stp_meas_step E L hI hd
  obtain ⟨hstops, hso⟩ := stp_stops_c' E L hI hd
  obtain ⟨esB, eaB, esC, -, -⟩ := stp_arrays_c' E L hI hd
  obtain ⟨-, hptr, hptrL, -⟩ := stp_ptr_c' E L hI hd
  obtain ⟨hlabR, hinv⟩ := S.labels
  have hsome := stp_key_some hI hd
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, -⟩ := hI.2.2.2.2.2.2.2 hsome
  have eTB : c'.nreg cTB = c.nreg cTB := stp_iter_keep hI (k := 661) (⋄)
  have elB : c'.nreg lB = c.nreg lB := stp_iter_keep hI (k := 2430) (⋄)
  have egN : c'.nreg gN = c.nreg gN := stp_iter_keep hI (k := 2440) (⋄)
  have egR : ∀ u, u < 2 → c'.nreg (gR + u) = c.nreg (gR + u) := fun u hu => by
    have := stp_iter_keep hI (k := 2441 + u) (⋄)
    rwa [show sw (2441 + u) = gR + u by unfold gR sw; omega] at this
  have hAl := stp_alloc_mono hI
  have hgN := L.gapN
  refine ⟨{
    stops := hstops
    sorted := fun i i' hii hi' => by
      rw [esC] at hi'
      rw [(hso i (⋄)).2.2, (hso i' hi').2.2]
      exact L.sorted i i' hii hi'
    two := fun i hi => by
      rw [esC] at hi
      rw [(hso i (⋄)).2.2, (hso (i + 2) hi).2.2]
      exact L.two i hi
    tab0 := by rw [eTB]; exact L.tab0
    lay1 := by rw [eTB, elB]; exact L.lay1
    lay2 := by rw [elB, esB]; exact L.lay2
    lay3 := by rw [elB, eaB]; exact L.lay3
    lay4 := by rw [esB, esC]; have := L.lay4; omega
    lay5 := by rw [eaB, esC]; have := L.lay5; omega
    key := hpw
    keyL := le_trans L.keyL hlt.le
    labN := hkN4
    labR := hlabR
    inv := hinv
    gapN := by rw [egN]; exact L.gapN
    gapR := fun i hi => by
      rw [egN] at hi
      rw [egR i (⋄)]
      exact L.gapR i hi
    gap := fun V hV => by
      obtain ⟨i, hi, hiV⟩ := L.gap V hV
      exact ⟨i, by rw [egN]; exact hi, by rw [egR i (⋄)]; exact hiV⟩
    ptr := hptr
    ptrL := hptrL
    log := S.log'
    meas := hmeas
    tab := S.tab'
    done0 := hd }, hmlt⟩

end

end SweepEv

end Chazelle.Core
