/- Continuous signed local frame sections from the inverse function theorem on
twenty selected triple-trace rows. The row map is injective on the chart;
reversal supplies the second section on a common open neighborhood. -/
module

public import Glennie.Compact.Sections.Reversal
public import Glennie.Compact.NativeFlatRank20
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.NativeDictionary Glennie.Compact.FlowFamily
  Glennie.Compact.ChartTransfer Glennie.Compact.FlatBase Glennie.Compact.Rank20
  Glennie.Compact.Rank20Certificate

noncomputable section

/-! ## Continuity of the moved atoms -/

/-- Decode the continuous coordinate family through the native linear equivalence. -/
theorem continuous_movedTriple_atom (T : Triple) (a i : Fin 3) :
    Continuous fun s : Fin 20 → ℝ => movedTriple T s a i  :=
  continuous_movedFrame contextDirection contextDirection_isJordanDerivation
    contextDirection_traceFree T a i

/-! ## The inverse function theorem on `cRow (ledger54 (movedTriple T s))` -/

/-! ## The flat base -/

/-- The flat base triple of FlatBase, in slot order. -/
def flatBase : Triple := ![flatFrameP, flatFrameQ, flatFrameR]

theorem flatBase_frames : ∀ a : Fin 3, Frame (flatBase a) := by
  intro a
  fin_cases a
  · exact flatFrameP_frame
  · exact flatFrameQ_frame
  · exact flatFrameR_frame

theorem phiOf_flatBase : phiOf flatBase = -4 / 27 := flat_phi


















/-- The reversed flat triple has the SAME complete 54-entry ledger as the flat triple: all 27
triple traces 1/9 and all 27 pair overlaps 1/3. This is why one invertibility witness suffices
for both sections. -/
theorem ledger54_revTriple_flatBase :
    ledger54 (revTriple flatBase) = ledger54 flatBase := by
  rw [ledger54_revTriple]
  have h := uniform_pair_blocks flatFrameP flatFrameQ flatFrameR flatFrameP_frame
    flatFrameQ_frame flatFrameR_frame flat_uniform
  have hc : ∀ i j k, ledger flatFrameP flatFrameQ flatFrameR i j k = 1 / 9 := flat_uniform
  ext <;> simp [revLedger, ledger54, flatBase, hc, h]

/-- Hence the chart involution fixes the flat chart point. -/
theorem tau_flatChart :
    tau (encode20 (ledger54 flatBase)) = encode20 (ledger54 flatBase) := by
  rw [tau_encode20 flatBase flatBase_frames,
    ← ledger54_revTriple, ledger54_revTriple_flatBase]

/-! The common chart domain is intersected with its reversal preimage. Reversal
preserves frames and reverses Phi. The chart identity below is used only for
frames, where its affine-domain hypothesis holds. -/
structure SignedSections where
  V : Set (Fin 20 → ℝ)
  openV : IsOpen V
  base : encode20 (ledger54 flatBase) ∈ V
  pos : (Fin 20 → ℝ) → Triple
  neg : (Fin 20 → ℝ) → Triple
  contPos : ContinuousOn pos V
  contNeg : ContinuousOn neg V
  framePos : ∀ b ∈ V, ∀ a, Frame (pos b a)
  frameNeg : ∀ b ∈ V, ∀ a, Frame (neg b a)
  chartPos : ∀ b ∈ V, encode20 (ledger54 (pos b)) = b
  chartNeg : ∀ b ∈ V, encode20 (ledger54 (neg b)) = b
  phiPos : ∀ b ∈ V, 0 < phiOf (pos b)
  phiNeg : ∀ b ∈ V, phiOf (neg b) < 0

theorem flat_two_sections : Nonempty SignedSections := by
  obtain ⟨e, he⟩ := Glennie.Compact.Rank20.rank20_of_bridge
    flatBase Glennie.Compact.NativeFlatRank20.jacobianEntry_flatBase_all
  have hd := hasStrictFDerivAt_rowLedger flatBase
  rw [← he] at hd
  let Psi := hd.toOpenPartialHomeomorph (rowLedger flatBase)
  have hleft : Psi.symm (rowLedger flatBase 0) = 0 :=
    Psi.left_inv hd.mem_toOpenPartialHomeomorph_source
  have hright (b) (hb : b ∈ Psi.target) : rowLedger flatBase (Psi.symm b) = b :=
    Psi.right_inv hb
  let U := rowsOf ⁻¹' Psi.target
  let sec : (Fin 20 → ℝ) → Triple := fun b => movedTriple flatBase (Psi.symm (rowsOf b))
  have hc : ContinuousOn sec U := by
    refine continuousOn_pi' fun a => continuousOn_pi' fun i => ?_
    exact (continuous_movedTriple_atom flatBase a i).comp_continuousOn'
      (Psi.continuousOn_symm.comp' continuous_rowsOf.continuousOn (fun b hb => hb))
  let W := U ∩ (fun b => phiOf (sec b)) ⁻¹' Set.Iio 0
  have hWopen : IsOpen W :=
    (continuous_phiOf.comp_continuousOn' hc).isOpen_inter_preimage
      (Psi.open_target.preimage continuous_rowsOf) isOpen_Iio
  have hcont : ContinuousOn sec W := hc.mono Set.inter_subset_left
  have hb0 := rowsOf_encode20_movedTriple flatBase flatBase_frames 0
  rw [movedTriple_zero] at hb0
  have hmem : encode20 (ledger54 flatBase) ∈ W := by
    constructor
    · change rowsOf (encode20 (ledger54 flatBase)) ∈ Psi.target
      rw [hb0]
      exact hd.image_mem_toOpenPartialHomeomorph_target
    · change phiOf (movedTriple flatBase (Psi.symm (rowsOf (encode20 (ledger54 flatBase))))) < 0
      rw [hb0, hleft, movedTriple_zero, phiOf_flatBase]
      norm_num
  have hframes (b) : ∀ a, Frame (sec b a) :=
    movedTriple_frame flatBase flatBase_frames _
  have hledger (b) (hb : b ∈ W) : encode20 (ledger54 (sec b)) = b := by
    apply rowsOf_injective
    rw [rowsOf_encode20_movedTriple flatBase flatBase_frames, hright (rowsOf b) hb.1]
  refine ⟨⟨W ∩ tau ⁻¹' W, hWopen.inter (hWopen.preimage continuous_tau),
    ⟨hmem, by simpa only [Set.mem_preimage, tau_flatChart] using hmem⟩,
    (fun b => revTriple (sec (tau b))), sec,
    continuous_revTriple.comp_continuousOn'
      (hcont.comp' continuous_tau.continuousOn (fun b hb => hb.2)),
    hcont.mono (fun b hb => hb.1), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b _
    exact frame_revTriple _ (hframes (tau b))
  · intro b _
    exact hframes b
  · intro b hb
    show encode20 (ledger54 (revTriple (sec (tau b)))) = b
    rw [ledger54_revTriple, ← tau_encode20 (sec (tau b)) (hframes (tau b)),
      hledger (tau b) hb.2, tau_tau]
  · intro b hb
    exact hledger b hb.1
  · intro b hb
    rw [phiOf_revTriple]
    exact neg_pos.mpr hb.2.2
  · intro b hb
    exact hb.1.2


theorem SignedSections.ledgerPos (d : SignedSections) (b) (hb : b ∈ d.V) :
    ledger54 (d.pos b) = decode20 b := by
  simpa only [d.chartPos b hb] using (decode_encode_frames _ (d.framePos b hb)).symm
theorem SignedSections.ledgerNeg (d : SignedSections) (b) (hb : b ∈ d.V) :
    ledger54 (d.neg b) = decode20 b := by
  simpa only [d.chartNeg b hb] using (decode_encode_frames _ (d.frameNeg b hb)).symm

end
end Glennie.Compact.Sections
