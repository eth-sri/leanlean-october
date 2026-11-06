module

public import CountAdapter
public import FinalDensitySurface.Pieces
import WeylPort.Analytic.RealLaplace

/-!
# Proved solution surface

No import of Challenge. The count definitions are supplied by CountCore with
the same fixed bodies as Challenge. CountAdapter proves their exact equality
to the existing natural-valued count; no analytic/finiteness hypothesis is
assumed. Every advertised proof is an exact count transfer from the frozen
statement surface, preserving endpoints and the constant's quantifier order.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
public section
namespace LewkoDensityPalomar

section
variable {σ ε : ℝ}
include σ ε
theorem provider_P1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P1 hlo hhi hε)

theorem provider_P2 (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ < (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P2 hlo hhi hε)

theorem provider_P3 (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P3 hlo hhi hε)

theorem provider_P4 (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P4 hlo hhi hε)

theorem provider_P5 (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ < (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P5 hlo hhi hε)

theorem provider_P6 (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P6 hlo hhi hε)

theorem provider_P7 (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ < (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P7 hlo hhi hε)

theorem provider_P8 (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (1867/2347 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P8 hlo hhi hε)

theorem provider_P9 (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P9 hlo hhi hε)

theorem provider_P10 (hlo : (7/10 : ℝ) < σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P10 hlo hhi hε)

theorem provider_P11 (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P11 hlo hhi hε)

theorem provider_P12 (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P12 hlo hhi hε)

theorem provider_P13 (hlo : (3/4 : ℝ) < σ)
    (hhi : σ < (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P13 hlo hhi hε)

theorem provider_P14 (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P14 hlo hhi hε)

theorem provider_P15 (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P15 hlo hhi hε)

theorem provider_P16 (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P16 hlo hhi hε)

theorem provider_P17 (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P17 hlo hhi hε)

theorem provider_P18 (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P18 hlo hhi hε)

theorem provider_P19 (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P19 hlo hhi hε)

theorem provider_P20 (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P20 hlo hhi hε)

theorem provider_P21 (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P21 hlo hhi hε)

theorem provider_P22 (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P22 hlo hhi hε)

theorem provider_P23 (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P23 hlo hhi hε)

theorem provider_P24 (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P24 hlo hhi hε)

theorem provider_P25 (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P25 hlo hhi hε)

theorem provider_P26 (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P26 hlo hhi hε)

theorem provider_P27 (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P27 hlo hhi hε)

theorem provider_P28 (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P28 hlo hhi hε)

theorem provider_P29 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P29 hlo hhi hε)

theorem provider_P30 (hlo : (19/22 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P30 hlo hhi hε)

theorem provider_P31 (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.provider_P31 hlo hhi hε)

theorem piece_G1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/10 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G1 hlo hhi hε)

theorem piece_G2 (hlo : (7/10 : ℝ) ≤ σ)
    (hhi : σ ≤ (19/25 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G2 hlo hhi hε)

theorem piece_G3 (hlo : (19/25 : ℝ) ≤ σ)
    (hhi : σ < (127/167 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(8*σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G3 hlo hhi hε)

theorem piece_G4 (hlo : (127/167 : ℝ) ≤ σ)
    (hhi : σ < (13/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(13*σ - 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G4 hlo hhi hε)

theorem piece_G5 (hlo : (13/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/22 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(5*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G5 hlo hhi hε)

theorem piece_G6 (hlo : (17/22 : ℝ) ≤ σ)
    (hhi : σ < (41/53 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2/(9*σ - 6))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G6 hlo hhi hε)

theorem piece_G7 (hlo : (41/53 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(7*σ - 1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G7 hlo hhi hε)

theorem piece_G8 (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ < (23/29 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/(16*σ - 8))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G8 hlo hhi hε)

theorem piece_G9 (hlo : (23/29 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G9 hlo hhi hε)

theorem piece_G10 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_G10 hlo hhi hε)

theorem piece_B1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B1 hlo hhi hε)

theorem piece_B2 (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B2 hlo hhi hε)

theorem piece_B3 (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (11/15 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((9/4)*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B3 hlo hhi hε)

theorem piece_B4 (hlo : (11/15 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((15/(5*σ + 3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B4 hlo hhi hε)

theorem piece_B5 (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B5 hlo hhi hε)

theorem piece_B6 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_B6 hlo hhi hε)

theorem piece_O1 (hlo : (1/2 : ℝ) ≤ σ)
    (hhi : σ ≤ (9/13 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((-3/(σ - 2))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O1 hlo hhi hε)

theorem piece_O2 (hlo : (9/13 : ℝ) ≤ σ)
    (hhi : σ ≤ (12/17 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((18/(7*σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O2 hlo hhi hε)

theorem piece_O3 (hlo : (12/17 : ℝ) ≤ σ)
    (hhi : σ ≤ (5/7 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(8*σ-3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O3 hlo hhi hε)

theorem piece_O4 (hlo : (5/7 : ℝ) ≤ σ)
    (hhi : σ ≤ (113/153 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((12/(9*σ-1))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O4 hlo hhi hε)

theorem piece_O5 (hlo : (113/153 : ℝ) ≤ σ)
    (hhi : σ ≤ (3/4 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((255/(153*σ+7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O5 hlo hhi hε)

theorem piece_O6 (hlo : (3/4 : ℝ) < σ)
    (hhi : σ ≤ (7/9 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(2*σ))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O6 hlo hhi hε)

theorem piece_O7 (hlo : (7/9 : ℝ) ≤ σ)
    (hhi : σ ≤ (29359/37574 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(11*σ-7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O7 hlo hhi hε)

theorem piece_O8 (hlo : (29359/37574 : ℝ) ≤ σ)
    (hhi : σ ≤ (1015/1294 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((4744/(4870*σ-1283))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O8 hlo hhi hε)

theorem piece_O9 (hlo : (1015/1294 : ℝ) ≤ σ)
    (hhi : σ ≤ (353/447 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6154/(6354*σ-1693))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O9 hlo hhi hε)

theorem piece_O10 (hlo : (353/447 : ℝ) ≤ σ)
    (hhi : σ ≤ (467/586 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3782/(3936*σ-1065))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O10 hlo hhi hε)

theorem piece_O11 (hlo : (467/586 : ℝ) ≤ σ)
    (hhi : σ ≤ (289/358 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2168/(2282*σ-631))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O11 hlo hhi hε)

theorem piece_O12 (hlo : (289/358 : ℝ) ≤ σ)
    (hhi : σ ≤ (163/198 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((566/(606*σ-173))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O12 hlo hhi hε)

theorem piece_O13 (hlo : (163/198 : ℝ) ≤ σ)
    (hhi : σ ≤ (7873/9370 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((31544/(35670*σ-11203))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O13 hlo hhi hε)

theorem piece_O14 (hlo : (7873/9370 : ℝ) ≤ σ)
    (hhi : σ ≤ (2018/2375 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((1261710/(1447460*σ-465509))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O14 hlo hhi hε)

theorem piece_O15 (hlo : (2018/2375 : ℝ) ≤ σ)
    (hhi : σ ≤ (1959705/2298302 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3066/(3616*σ-1215))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O15 hlo hhi hε)

theorem piece_O16 (hlo : (1959705/2298302 : ℝ) ≤ σ)
    (hhi : σ ≤ (6482825/7570038 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((597962/(729216*σ-257415))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O16 hlo hhi hε)

theorem piece_O17 (hlo : (6482825/7570038 : ℝ) ≤ σ)
    (hhi : σ ≤ (2905/3354 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((16504356/(20732766*σ-7623595))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O17 hlo hhi hε)

theorem piece_O18 (hlo : (2905/3354 : ℝ) ≤ σ)
    (hhi : σ ≤ (7/8 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((2172/(2742*σ-1015))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O18 hlo hhi hε)

theorem piece_O19 (hlo : (7/8 : ℝ) ≤ σ)
    (hhi : σ ≤ (24139/27578 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O19 hlo hhi hε)

theorem piece_O20 (hlo : (24139/27578 : ℝ) ≤ σ)
    (hhi : σ ≤ (23/26 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O20 hlo hhi hε)

theorem piece_O21 (hlo : (23/26 : ℝ) ≤ σ)
    (hhi : σ ≤ (17/19 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O21 hlo hhi hε)

theorem piece_O22 (hlo : (17/19 : ℝ) ≤ σ)
    (hhi : σ ≤ (1 : ℝ)) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((3/(10*σ - 7))*(1-σ)) + ε)) := by
  exact bound_of_literal (FinalDensitySurface.piece_O22 hlo hhi hε)
end

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
theorem global39over17 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) := by pm_2725 FinalDensitySurface.global39over17

theorem uniform_P29 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) := by pm_2725 FinalDensitySurface.uniform_P29
end

section
variable {ε : ℝ} (hε : 0 < ε)
include ε hε
theorem uniform_P30 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) := by pm_2725 FinalDensitySurface.uniform_P30

theorem uniform_P31 :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) := by pm_2725 FinalDensitySurface.uniform_P31
end

end LewkoDensityPalomar
