module

public import CountAdapter
public import FinalDensitySurface.Pieces

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal
public section
namespace LewkoDensityPalomar

density_decl provider_P1 FinalDensitySurface.provider_P1 σ ((1/2 : ℝ) ≤ σ) (σ ≤ (7/10 : ℝ)) ((-3/(σ - 2))*(1-σ))
density_decl provider_P2 FinalDensitySurface.provider_P2 σ ((7/10 : ℝ) ≤ σ) (σ < (19/25 : ℝ)) ((15/(5*σ + 3))*(1-σ))
density_decl provider_P3 FinalDensitySurface.provider_P3 σ ((19/25 : ℝ) ≤ σ) (σ < (127/167 : ℝ)) ((9/(8*σ - 2))*(1-σ))
density_decl provider_P4 FinalDensitySurface.provider_P4 σ ((127/167 : ℝ) ≤ σ) (σ < (13/17 : ℝ)) ((15/(13*σ - 3))*(1-σ))
density_decl provider_P5 FinalDensitySurface.provider_P5 σ ((13/17 : ℝ) ≤ σ) (σ < (17/22 : ℝ)) ((6/(5*σ - 1))*(1-σ))
density_decl provider_P6 FinalDensitySurface.provider_P6 σ ((17/22 : ℝ) ≤ σ) (σ < (41/53 : ℝ)) ((2/(9*σ - 6))*(1-σ))
density_decl provider_P7 FinalDensitySurface.provider_P7 σ ((41/53 : ℝ) ≤ σ) (σ < (7/9 : ℝ)) ((9/(7*σ - 1))*(1-σ))
density_decl provider_P8 FinalDensitySurface.provider_P8 σ ((7/9 : ℝ) ≤ σ) (σ < (1867/2347 : ℝ)) ((9/(16*σ - 8))*(1-σ))
density_decl provider_P9 FinalDensitySurface.provider_P9 σ ((23/29 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) ((3/(2*σ))*(1-σ))
density_decl provider_P10 FinalDensitySurface.provider_P10 σ ((7/10 : ℝ) < σ) (σ ≤ (1 : ℝ)) ((3/(10*σ - 7))*(1-σ))
density_decl provider_P11 FinalDensitySurface.provider_P11 σ ((9/13 : ℝ) ≤ σ) (σ ≤ (5/7 : ℝ)) ((18/(7*σ+3))*(1-σ))
density_decl provider_P12 FinalDensitySurface.provider_P12 σ ((5/7 : ℝ) ≤ σ) (σ ≤ (3/4 : ℝ)) ((9/4)*(1-σ))
density_decl provider_P13 FinalDensitySurface.provider_P13 σ ((3/4 : ℝ) < σ) (σ < (1 : ℝ)) ((3/(2*σ))*(1-σ))
density_decl provider_P14 FinalDensitySurface.provider_P14 σ ((7/10 : ℝ) ≤ σ) (σ ≤ (5/7 : ℝ)) ((6/(8*σ-3))*(1-σ))
density_decl provider_P15 FinalDensitySurface.provider_P15 σ ((5/7 : ℝ) ≤ σ) (σ ≤ (113/153 : ℝ)) ((12/(9*σ-1))*(1-σ))
density_decl provider_P16 FinalDensitySurface.provider_P16 σ ((113/153 : ℝ) ≤ σ) (σ ≤ (3/4 : ℝ)) ((255/(153*σ+7))*(1-σ))
density_decl provider_P17 FinalDensitySurface.provider_P17 σ ((7/9 : ℝ) ≤ σ) (σ ≤ (29359/37574 : ℝ)) ((3/(11*σ-7))*(1-σ))
density_decl provider_P18 FinalDensitySurface.provider_P18 σ ((29359/37574 : ℝ) ≤ σ) (σ ≤ (1015/1294 : ℝ)) ((4744/(4870*σ-1283))*(1-σ))
density_decl provider_P19 FinalDensitySurface.provider_P19 σ ((1015/1294 : ℝ) ≤ σ) (σ ≤ (353/447 : ℝ)) ((6154/(6354*σ-1693))*(1-σ))
density_decl provider_P20 FinalDensitySurface.provider_P20 σ ((353/447 : ℝ) ≤ σ) (σ ≤ (467/586 : ℝ)) ((3782/(3936*σ-1065))*(1-σ))
density_decl provider_P21 FinalDensitySurface.provider_P21 σ ((467/586 : ℝ) ≤ σ) (σ ≤ (289/358 : ℝ)) ((2168/(2282*σ-631))*(1-σ))
density_decl provider_P22 FinalDensitySurface.provider_P22 σ ((289/358 : ℝ) ≤ σ) (σ ≤ (163/198 : ℝ)) ((566/(606*σ-173))*(1-σ))
density_decl provider_P23 FinalDensitySurface.provider_P23 σ ((163/198 : ℝ) ≤ σ) (σ ≤ (7873/9370 : ℝ)) ((31544/(35670*σ-11203))*(1-σ))
density_decl provider_P24 FinalDensitySurface.provider_P24 σ ((7873/9370 : ℝ) ≤ σ) (σ ≤ (2018/2375 : ℝ)) ((1261710/(1447460*σ-465509))*(1-σ))
density_decl provider_P25 FinalDensitySurface.provider_P25 σ ((2018/2375 : ℝ) ≤ σ) (σ ≤ (1959705/2298302 : ℝ)) ((3066/(3616*σ-1215))*(1-σ))
density_decl provider_P26 FinalDensitySurface.provider_P26 σ ((1959705/2298302 : ℝ) ≤ σ) (σ ≤ (6482825/7570038 : ℝ)) ((597962/(729216*σ-257415))*(1-σ))
density_decl provider_P27 FinalDensitySurface.provider_P27 σ ((6482825/7570038 : ℝ) ≤ σ) (σ ≤ (2905/3354 : ℝ)) ((16504356/(20732766*σ-7623595))*(1-σ))
density_decl provider_P28 FinalDensitySurface.provider_P28 σ ((2905/3354 : ℝ) ≤ σ) (σ ≤ (7/8 : ℝ)) ((2172/(2742*σ-1015))*(1-σ))
density_decl provider_P29 FinalDensitySurface.provider_P29 σ ((7/8 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) (1086/5537)
density_decl provider_P30 FinalDensitySurface.provider_P30 σ ((19/22 : ℝ) ≤ σ) (σ ≤ (23/26 : ℝ)) ((24/(30*σ-11))*(1-σ))
density_decl provider_P31 FinalDensitySurface.provider_P31 σ ((23/26 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) ((6/(σ+3))*(1-σ))

density_decl piece_G1 FinalDensitySurface.piece_G1 σ ((1/2 : ℝ) ≤ σ) (σ ≤ (7/10 : ℝ)) ((-3/(σ - 2))*(1-σ))
density_decl piece_G2 FinalDensitySurface.piece_G2 σ ((7/10 : ℝ) ≤ σ) (σ ≤ (19/25 : ℝ)) ((15/(5*σ + 3))*(1-σ))
density_decl piece_G3 FinalDensitySurface.piece_G3 σ ((19/25 : ℝ) ≤ σ) (σ < (127/167 : ℝ)) ((9/(8*σ - 2))*(1-σ))
density_decl piece_G4 FinalDensitySurface.piece_G4 σ ((127/167 : ℝ) ≤ σ) (σ < (13/17 : ℝ)) ((15/(13*σ - 3))*(1-σ))
density_decl piece_G5 FinalDensitySurface.piece_G5 σ ((13/17 : ℝ) ≤ σ) (σ ≤ (17/22 : ℝ)) ((6/(5*σ - 1))*(1-σ))
density_decl piece_G6 FinalDensitySurface.piece_G6 σ ((17/22 : ℝ) ≤ σ) (σ < (41/53 : ℝ)) ((2/(9*σ - 6))*(1-σ))
density_decl piece_G7 FinalDensitySurface.piece_G7 σ ((41/53 : ℝ) ≤ σ) (σ ≤ (7/9 : ℝ)) ((9/(7*σ - 1))*(1-σ))
density_decl piece_G8 FinalDensitySurface.piece_G8 σ ((7/9 : ℝ) ≤ σ) (σ < (23/29 : ℝ)) ((9/(16*σ - 8))*(1-σ))
density_decl piece_G9 FinalDensitySurface.piece_G9 σ ((23/29 : ℝ) ≤ σ) (σ ≤ (7/8 : ℝ)) ((3/(2*σ))*(1-σ))
density_decl piece_G10 FinalDensitySurface.piece_G10 σ ((7/8 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) ((3/(10*σ - 7))*(1-σ))

density_decl piece_B1 FinalDensitySurface.piece_B1 σ ((1/2 : ℝ) ≤ σ) (σ ≤ (9/13 : ℝ)) ((-3/(σ - 2))*(1-σ))
density_decl piece_B2 FinalDensitySurface.piece_B2 σ ((9/13 : ℝ) ≤ σ) (σ ≤ (5/7 : ℝ)) ((18/(7*σ+3))*(1-σ))
density_decl piece_B3 FinalDensitySurface.piece_B3 σ ((5/7 : ℝ) ≤ σ) (σ ≤ (11/15 : ℝ)) ((9/4)*(1-σ))
density_decl piece_B4 FinalDensitySurface.piece_B4 σ ((11/15 : ℝ) ≤ σ) (σ ≤ (3/4 : ℝ)) ((15/(5*σ + 3))*(1-σ))
density_decl piece_B5 FinalDensitySurface.piece_B5 σ ((3/4 : ℝ) < σ) (σ ≤ (7/8 : ℝ)) ((3/(2*σ))*(1-σ))
density_decl piece_B6 FinalDensitySurface.piece_B6 σ ((7/8 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) ((3/(10*σ - 7))*(1-σ))

density_decl piece_O1 FinalDensitySurface.piece_O1 σ ((1/2 : ℝ) ≤ σ) (σ ≤ (9/13 : ℝ)) ((-3/(σ - 2))*(1-σ))
density_decl piece_O2 FinalDensitySurface.piece_O2 σ ((9/13 : ℝ) ≤ σ) (σ ≤ (12/17 : ℝ)) ((18/(7*σ+3))*(1-σ))
density_decl piece_O3 FinalDensitySurface.piece_O3 σ ((12/17 : ℝ) ≤ σ) (σ ≤ (5/7 : ℝ)) ((6/(8*σ-3))*(1-σ))
density_decl piece_O4 FinalDensitySurface.piece_O4 σ ((5/7 : ℝ) ≤ σ) (σ ≤ (113/153 : ℝ)) ((12/(9*σ-1))*(1-σ))
density_decl piece_O5 FinalDensitySurface.piece_O5 σ ((113/153 : ℝ) ≤ σ) (σ ≤ (3/4 : ℝ)) ((255/(153*σ+7))*(1-σ))
density_decl piece_O6 FinalDensitySurface.piece_O6 σ ((3/4 : ℝ) < σ) (σ ≤ (7/9 : ℝ)) ((3/(2*σ))*(1-σ))
density_decl piece_O7 FinalDensitySurface.piece_O7 σ ((7/9 : ℝ) ≤ σ) (σ ≤ (29359/37574 : ℝ)) ((3/(11*σ-7))*(1-σ))
density_decl piece_O8 FinalDensitySurface.piece_O8 σ ((29359/37574 : ℝ) ≤ σ) (σ ≤ (1015/1294 : ℝ)) ((4744/(4870*σ-1283))*(1-σ))
density_decl piece_O9 FinalDensitySurface.piece_O9 σ ((1015/1294 : ℝ) ≤ σ) (σ ≤ (353/447 : ℝ)) ((6154/(6354*σ-1693))*(1-σ))
density_decl piece_O10 FinalDensitySurface.piece_O10 σ ((353/447 : ℝ) ≤ σ) (σ ≤ (467/586 : ℝ)) ((3782/(3936*σ-1065))*(1-σ))
density_decl piece_O11 FinalDensitySurface.piece_O11 σ ((467/586 : ℝ) ≤ σ) (σ ≤ (289/358 : ℝ)) ((2168/(2282*σ-631))*(1-σ))
density_decl piece_O12 FinalDensitySurface.piece_O12 σ ((289/358 : ℝ) ≤ σ) (σ ≤ (163/198 : ℝ)) ((566/(606*σ-173))*(1-σ))
density_decl piece_O13 FinalDensitySurface.piece_O13 σ ((163/198 : ℝ) ≤ σ) (σ ≤ (7873/9370 : ℝ)) ((31544/(35670*σ-11203))*(1-σ))
density_decl piece_O14 FinalDensitySurface.piece_O14 σ ((7873/9370 : ℝ) ≤ σ) (σ ≤ (2018/2375 : ℝ)) ((1261710/(1447460*σ-465509))*(1-σ))
density_decl piece_O15 FinalDensitySurface.piece_O15 σ ((2018/2375 : ℝ) ≤ σ) (σ ≤ (1959705/2298302 : ℝ)) ((3066/(3616*σ-1215))*(1-σ))
density_decl piece_O16 FinalDensitySurface.piece_O16 σ ((1959705/2298302 : ℝ) ≤ σ) (σ ≤ (6482825/7570038 : ℝ)) ((597962/(729216*σ-257415))*(1-σ))
density_decl piece_O17 FinalDensitySurface.piece_O17 σ ((6482825/7570038 : ℝ) ≤ σ) (σ ≤ (2905/3354 : ℝ)) ((16504356/(20732766*σ-7623595))*(1-σ))
density_decl piece_O18 FinalDensitySurface.piece_O18 σ ((2905/3354 : ℝ) ≤ σ) (σ ≤ (7/8 : ℝ)) ((2172/(2742*σ-1015))*(1-σ))
density_decl piece_O19 FinalDensitySurface.piece_O19 σ ((7/8 : ℝ) ≤ σ) (σ ≤ (24139/27578 : ℝ)) (1086/5537)
density_decl piece_O20 FinalDensitySurface.piece_O20 σ ((24139/27578 : ℝ) ≤ σ) (σ ≤ (23/26 : ℝ)) ((24/(30*σ-11))*(1-σ))
density_decl piece_O21 FinalDensitySurface.piece_O21 σ ((23/26 : ℝ) ≤ σ) (σ ≤ (17/19 : ℝ)) ((6/(σ+3))*(1-σ))
density_decl piece_O22 FinalDensitySurface.piece_O22 σ ((17/19 : ℝ) ≤ σ) (σ ≤ (1 : ℝ)) ((3/(10*σ - 7))*(1-σ))

theorem global39over17 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (1/2 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((39/17 : ℝ)*(1-σ)) + ε)) :=
  bound_of_uniform_literal (FinalDensitySurface.global39over17 hε)

theorem uniform_P29 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (7/8 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ ((1086/5537) + ε)) :=
  bound_of_uniform_literal (FinalDensitySurface.uniform_P29 hε)

theorem uniform_P30 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (19/22 : ℝ) ≤ σ →
      σ ≤ (23/26 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((24/(30*σ-11))*(1-σ)) + ε)) :=
  bound_of_uniform_literal (FinalDensitySurface.uniform_P30 hε)

theorem uniform_P31 {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, (23/26 : ℝ) ≤ σ →
      σ ≤ (1 : ℝ) → 2 ≤ T →
      zeroCount σ T ≤ ENNReal.ofReal (C * T ^ (((6/(σ+3))*(1-σ)) + ε)) :=
  bound_of_uniform_literal (FinalDensitySurface.uniform_P31 hε)

end LewkoDensityPalomar
