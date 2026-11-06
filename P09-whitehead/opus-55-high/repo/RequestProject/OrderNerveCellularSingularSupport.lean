import RequestProject.OrderNerveCellularSingularChains
import RequestProject.OrderNerveSingularCarrierExactness
import RequestProject.OrderNerveDecoding
import RequestProject.Tac



namespace FiniteChains.Comb
open TopologicalSingular

theorem orderCellSingularDecode1List_supported {P} [PartialOrder P]
    (A : Set P) (l : List P) (hl : l.IsChain (· ≤ ·)) (hv : ∀ p ∈ l, p ∈ A) :
    orderCellSingularChain1 (decodeOrdEdgeList l) ∈
      subChains (orderNerveRealizationSubcomplex P A) 1 := by
  classical
  cases l with
  | nil => simp [decodeOrdEdgeList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdEdgeList]
    | cons b l =>
      cases l with
      | cons c l => simp [decodeOrdEdgeList]
      | nil =>
        have hab : a ≤ b := by simp_all
        rwd [decodeOrdEdgeList, dif_pos hab, orderCellSingularChain1_single]
        apply single_mem_subChains
        intro z
        apply orderNerveSingularSimplex_supported
        intro i
        fin_cases i
        · tauto
        tauto

/-- Realizing an increasing one-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode1_supported {P} [PartialOrder P]
    (A : Set P) {c} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain1 (decodeOrdNerve1 c) ∈
      subChains (orderNerveRealizationSubcomplex P A) 1 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rwd [decodeOrdNerve1_of]
    exact orderCellSingularDecode1List_supported A l hl.1 hl.2
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all

theorem orderCellSingularDecode2List_supported {P} [PartialOrder P]
    (A : Set P) (l : List P) (hl : l.IsChain (· ≤ ·)) (hv : ∀ p ∈ l, p ∈ A) :
    orderCellSingularChain2 (decodeOrdTriList l) ∈
      subChains (orderNerveRealizationSubcomplex P A) 2 := by
  classical
  cases l with
  | nil => simp [decodeOrdTriList]
  | cons a l =>
    cases l with
    | nil => simp [decodeOrdTriList]
    | cons b l =>
      cases l with
      | nil => simp [decodeOrdTriList]
      | cons c l =>
        cases l with
        | cons d l => simp [decodeOrdTriList]
        | nil =>
          have habc : a ≤ b ∧ b ≤ c := by simp_all
          rwd [decodeOrdTriList, dif_pos habc, orderCellSingularChain2_single]
          apply single_mem_subChains
          intro z
          apply orderNerveSingularSimplex_supported
          intro i
          fin_cases i
          · tauto
          · tauto
          tauto

/-- Realizing an increasing two-chain preserves every vertex carrier. -/
theorem orderCellSingularDecode2_supported {P} [PartialOrder P]
    (A : Set P) {c} (hc : c ∈ Nerve.IncOn A) :
    orderCellSingularChain2 (decodeOrdNerve2 c) ∈
      subChains (orderNerveRealizationSubcomplex P A) 2 := by
  induction hc using AddSubgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, hl, rfl⟩
    rwd [decodeOrdNerve2_of]
    exact orderCellSingularDecode2List_supported A l hl.1 hl.2
  | zero => simp
  | add x y _ _ hx hy => aesop
  | neg x _ hx => simp_all
