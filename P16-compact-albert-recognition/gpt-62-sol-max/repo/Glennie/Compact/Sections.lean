module

public import Glennie.Compact.Sections.Reversal
public import Glennie.Compact.Rank20Reduction
public import Glennie.Compact.FlatBase
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.NormNum
@[expose] public section

namespace Glennie.Compact.NearbyOrbitsClosed
open Affine20 FlatBase Glennie.SubmissionR03

abbrev ChartPoint := Fin 20 → ℝ

/-- The two analytic sections, on a chart where their signs have a strict margin. -/
structure LocalData where
  V : Set ChartPoint
  openV : IsOpen V
  base : encode20 (ledger54 flatBase) ∈ V
  pos : ChartPoint → Triple
  neg : ChartPoint → Triple
  contPos : ContinuousOn pos V
  contNeg : ContinuousOn neg V
  framePos : ∀ b ∈ V, IsFrameTriple (pos b)
  frameNeg : ∀ b ∈ V, IsFrameTriple (neg b)
  chartPos : ∀ b ∈ V, encode20 (ledger54 (pos b)) = b
  chartNeg : ∀ b ∈ V, encode20 (ledger54 (neg b)) = b
  marginPos : ∀ b ∈ V, 1 / 27 < phiOf (pos b)
  marginNeg : ∀ b ∈ V, phiOf (neg b) < -(1 / 27)

end Glennie.Compact.NearbyOrbitsClosed

namespace Glennie.Compact.Sections

open Glennie.Compact.Affine20 Glennie.Compact.NativeDictionary Glennie.Compact.FlowFamily
  Glennie.Compact.ChartTransfer Glennie.Compact.FlatBase Glennie.Compact.Rank20 NearbyOrbitsClosed

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ledger54_revTriple_flatBase : ledger54 (revTriple flatBase) = ledger54 flatBase := by
  have hp := uniform_pair_blocks _ _ _ flatFrameP_frame flatFrameQ_frame flatFrameR_frame flat_uniform
  have hL : ledger54 flatBase = (fun _ _ _ => 1/9, fun _ _ => 1/3, fun _ _ => 1/3, fun _ _ => 1/3) :=
    Prod.ext (funext fun i => funext fun j => funext (flat_uniform i j))
      (Prod.ext (by funext i j; exact (hp i j).1)
        (Prod.ext (by funext j k; exact (hp j k).2.1) (by funext k i; exact (hp k i).2.2)))
  rw [ledger54_revTriple, hL]
  rfl

/-- Hence the chart involution fixes the flat chart point. -/
theorem tau_flatChart :
    tau (encode20 (ledger54 flatBase)) = encode20 (ledger54 flatBase) := by
  rw [tau_encode20 (ledger54 flatBase) (ledger54_inDomain flatBase flatBase_frames),
    ← ledger54_revTriple, ledger54_revTriple_flatBase]

theorem flat_two_sections (e : ChartPoint ≃L[ℝ] ChartPoint)
    (he : (e : ChartPoint →L[ℝ] ChartPoint) = rowLedgerDeriv flatBase) : Nonempty LocalData := by
  have hd : HasStrictFDerivAt (rowLedger flatBase) (e : ChartPoint →L[ℝ] ChartPoint) 0 :=
    he.symm ▸ hasStrictFDerivAt_rowLedger flatBase
  obtain ⟨Psi, hcoe, hsrc⟩ : ∃ Psi : OpenPartialHomeomorph ChartPoint ChartPoint,
      (Psi : ChartPoint → ChartPoint) = rowLedger flatBase ∧ 0 ∈ Psi.source :=
    ⟨hd.toOpenPartialHomeomorph _, hd.toOpenPartialHomeomorph_coe,
      hd.mem_toOpenPartialHomeomorph_source⟩
  let W₀ := rowsOf ⁻¹' Psi.target
  let sec (b : ChartPoint) := movedTriple flatBase (Psi.symm (rowsOf b))
  have hcont₀ : ContinuousOn sec W₀ := continuousOn_pi' fun a => continuousOn_pi' fun i =>
    (continuous_movedFrame contextDirection flatBase a i).comp_continuousOn'
      (Psi.continuousOn_symm.comp' continuous_rowsOf.continuousOn (fun _ h => h))
  let W := W₀ ∩ (phiOf ∘ sec) ⁻¹' Set.Iio (-(1/27))
  have hWopen : IsOpen W := (continuous_phiOf.comp_continuousOn hcont₀).isOpen_inter_preimage
    (Psi.open_target.preimage continuous_rowsOf) isOpen_Iio
  have hb : rowsOf (encode20 (ledger54 flatBase)) = Psi 0 := by
    rw [show Psi 0 = rowLedger flatBase 0 from congrFun hcoe 0]
    simpa only [movedTriple_zero] using rowsOf_encode20_movedTriple flatBase flatBase_frames 0
  have hmem : encode20 (ledger54 flatBase) ∈ W := by
    refine ⟨?_, ?_⟩
    · change _ ∈ Psi.target
      rw [hb]
      exact Psi.mapsTo hsrc
    · change phiOf (sec (encode20 (ledger54 flatBase))) < -(1/27)
      dsimp only [sec]
      rw [hb, Psi.left_inv hsrc, movedTriple_zero]
      change phi (encoder flatFrameP) (encoder flatFrameQ) (encoder flatFrameR) < _
      rw [flat_phi]
      norm_num
  have hledger (b : ChartPoint) (hb : b ∈ W) : encode20 (ledger54 (sec b)) = b :=
    rowsOf_injective ((rowsOf_encode20_movedTriple flatBase flatBase_frames _).trans
      (hcoe ▸ Psi.right_inv hb.1))
  have hcont : ContinuousOn sec W := hcont₀.mono Set.inter_subset_left
  have hframes (b : ChartPoint) : IsFrameTriple (sec b) := movedTriple_frame flatBase flatBase_frames _
  refine ⟨⟨W ∩ tau ⁻¹' W, hWopen.inter (hWopen.preimage continuous_tau),
    ⟨hmem, by rwa [Set.mem_preimage, tau_flatChart]⟩,
    fun b => revTriple (sec (tau b)), sec,
    continuous_revTriple.comp_continuousOn' (hcont.comp continuous_tau.continuousOn (fun _ h => h.2)),
    hcont.mono Set.inter_subset_left,
    fun b hb => frame_revTriple _ (hframes (tau b)), fun b _ => hframes b,
    ?_, fun b hb => hledger b hb.1, ?_, fun _ hb => hb.1.2⟩⟩
  · intro b hb
    rw [ledger54_revTriple, ← tau_encode20 _ (ledger54_inDomain _ (hframes (tau b))),
      hledger (tau b) hb.2, tau_tau]
  · intro b hb
    rw [phiOf_revTriple]
    exact lt_neg.mpr hb.2.2

end
end Glennie.Compact.Sections
