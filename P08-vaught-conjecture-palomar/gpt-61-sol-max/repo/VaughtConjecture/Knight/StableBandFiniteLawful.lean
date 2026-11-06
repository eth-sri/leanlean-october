/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.DirectedFiniteJump
import VaughtConjecture.Knight.StableBandVector

/-! # Stable lawfulness from one finite observation and a jump

The stable band vector is a jump of one provisional vector above any requested
base cover. The jump cutoff can be fixed before choosing that base: choose it
beyond the finitely many finite stable offsets. Monotonicity and directedness
then synchronize finite attainments and infinite escape. This is finite
synchronization, not its elimination, and it uses no topology.

The decoded stable labels are therefore lawful by finite provisional lawfulness
and jump preservation. Only source consistency and covering are required;
receiving and successor modelhood remain separate. Face coherence is unchanged.
-/

namespace VaughtConjecture.Knight


universe w

namespace KnightRealization

variable {α : LimitStage} {M : Type w} {R : KnightRealization α M}

namespace RootedCover

variable {x : R.LabelledExt}

/-- Jump-invariance above the maximum grade passes finite lawfulness to the
completed-band supremum. The general finite-vector lemma carries the entire
synchronization argument; no closed-set theorem or occurrence scheduler is used. -/
theorem stableBand_mem_lawfulBand_of_finiteJump (hc : R.IsExactParentConsistent)
    (hv : R.IsInitialSegmentCovering) : stableBand x ∈ x.type.LawfulBand := by
  
  have := isDirectedOrder hc hv x
  exact DirectedFiniteJump.predicate_iSup_of_jump
    (fun d : x.type.TopCell => offset d.2) (fun d => offset_mono d.1 d.2)
    (Finset.univ.sup fun d => x.type.scheme.scheme.grade d)
    (fun r => r ∈ x.type.LawfulBand)
    (fun K hK _ hr => x.type.jump_mem_lawfulBand α.2 K (fun d =>
      (Finset.le_sup 
        (Finset.mem_univ d)).trans hK) hr)
    provisionalBand_mem_lawfulBand

end RootedCover

/-- Stable lawfulness by finite-vector synchronization and one jump. The
statement matches the structural core's existing lawfulness interface. -/
theorem stableLiftRespects_of_finiteJump (hc : R.IsExactParentConsistent)
    (hv : R.IsInitialSegmentCovering) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hp : R.eval t = some p) :
    RespectsSemantics p.scheme.rows (fun d => R.stableValue t p d) := by
  let x : R.LabelledExt := ⟨n, t, p, hp⟩
  have h := RootedCover.stableBand_mem_lawfulBand_of_finiteJump (x := x) hc hv
  change RespectsSemantics _ _ at h
  rwa [RootedCover.bandLabel_stableBand hc hv] at h


