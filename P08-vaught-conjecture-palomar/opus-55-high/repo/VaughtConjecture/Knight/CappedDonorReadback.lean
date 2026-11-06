/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorRetarget
public import VaughtConjecture.Knight.CappedDonorRelease

/-! # The HIGH/LOW readback consumer from explicit chart receipts (newapproach2 §7 of new4)

The **semantic half** of the probe readback of the reviewer's new4 §7: what an admissible
two-threshold state reads back once the physical charts have supplied their receipts.  Nothing
here constructs a state or a physical probe; the receipts are explicit hypotheses.

* **The high chart** (`LowRef.high_readback`, new4 §7.1): at a cutoff where the cap is present,
  with a positive gate and the **actual cap and reference values** (the receipts of a bounded
  grade-`N` chart), HIGH pins the stored cutoff to the actual cut (`cut_actual_lt_cap`: the actual
  cut lies strictly below the actual cap by the endpoint margin, so `b ∧ H = B` cancels), the
  receiving relation reads every donor non-top request field back literally (`nonTop_readback`),
  hence the non-top maximum is strictly below the stored cutoff as soon as the actual cut is
  positive (the block-zero comparison reference of audit18 §5 supplies that), and the stored
  cutoff is strictly below the cap field.  That is exactly LOW's antecedent, obtained from
  numerical receipts — not from the donor's non-top tags.
* **The low chart makes LOW exact** (`LowRef.readback`, new4 §7.2): with, in addition, the low
  frontier **top** (`LowRef.eC_top`: the owner and the low source read top, the receipt of a
  grade-`K` controller with value top), LOW forces every donor-top request field to be top.
  Together, the current request section **is** the donor labelling (`readback_eq`).

**The probe contract** (`LowRef.readback_of_actualFace`): every receipt except the rendered
state's admissibility and the gate is the value of the **actual private labelling at an actual
occurrence**, so a probe section that retains the actual private face literally supplies them
all at once.  Receipt by receipt:

* `hcap` (the cap value): supplied by the full-scope grade-`N` controller `F.cell` of the
  reference context (`Ref.cap`, `cap_cell`); its chart is the cap's own row `E_cap` on `Low`
  through the exact bounded witness `Ref.exists_witness` — the grade-`N` chart, clipped at `H`.
* `href i` (the reference values): supplied by the block representatives `C.repBase i`
  (`Ref.ref`, `vact_ref`), block `0` included; read through the same grade-`N` chart
  (`read_ref_rep`).
* `hcut` (the positive actual cut): supplied by the block-zero comparison representative
  (audit18 §5, `exists_ref_zero`); no chart, an order fact (`cut_actual`).
* `hc`, `hr` (the owner and the low source top): supplied by the surviving full-scope grade-`K`
  owner `c` and the lost top `r` of the protected-flexibility alternative — both **actual tops**
  (`LowRef.exists_of_protectedFlex_top`); their chart is the owner's own row `E_c` through the
  exact bounded witness `LowRef.exists_witness` — the grade-`K` chart, uncapped since
  `vact c = ⊤`.
* `hg` (the positive gate): a grade-one node of the probe kept non-bottom by bottom-pattern
  realization (new4 §8); no chart.
* `hS` (`TAdmissible` at `j ≥ N`): the rendered two-threshold state of the probe section; built
  from the guarded source rows of the probe (new4 §§3–6), HIGH through the cap's row and LOW
  through `c`'s row.
The last two items are the physical obligations proper: rendering an arbitrary lawful probe
section as an admissible two-threshold state (with its charts the witnesses of the two installed
rows above), and bottom-pattern realization keeping the gate node positive.  Nothing here asserts
either; `readback_of_actualFace` states exactly what they must deliver. -/

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd AmalgamationPlan

namespace CappedDonor

namespace Ref

variable {I : Type*} [Fintype I] {nP N J : ℕ} {P : SemScheme (nP + 1)} {C : SemScheme J}
  {R : Ref I nP N J P C}

/-- The actual cut lies strictly below the actual cap (the endpoint margin). -/
theorem cut_actual_lt_cap : R.cut R.vactL < R.vact R.cap := by
  rw [R.cut_actual]
  exact (Finset.sup_lt_iff R.cap_pos).mpr fun i _ => R.margin i

end Ref

end CappedDonor

end VaughtConjecture.Knight
