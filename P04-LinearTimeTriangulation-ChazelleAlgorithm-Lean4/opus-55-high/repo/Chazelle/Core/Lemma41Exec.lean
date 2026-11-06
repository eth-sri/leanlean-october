module

public import Chazelle.MacT
public import Chazelle.Core.Lemma41Node
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.ShootCutGrade
public import Chazelle.Core.BruteRam3
public import Chazelle.Chain.Submap
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.GranInitL3

namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs Chazelle Chazelle.Merge
@[expose] public section
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **Lemma 4.1 on the RAM.** -/
theorem l41_exec {O : OracleIface} (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} (hMM : MergeMeets sM κ F G H ztsy OkModel)
    (hF : Monotone F) (hGm : Monotone G) (hH : Monotone H)
    {c : Config} (hw : WordsBounded W c) {A h a L lam : ℕ}
    (hA : c.nreg ALLOC = A) (r0 : c.nreg 160000 = h) (r1 : c.nreg 160001 = a)
    (r2 : c.nreg 160002 = L) (r3 : c.nreg 160003 = lam)
    (hX : (gradeCtx O).holds P c.nmem h A) (hlΛ : lam ≤ c.nmem h) (h7 : 7 ≤ lam)
    (han : a + L + 1 ≤ P.n) (hL1 : 2 ^ ztma < L) (hL2 : L ≤ 2 ^ lam)
    (hbud : A + l41Big κ F G H lam a L ≤ W) :
    ∃ c' k, Exec P W (l41S sM) c c' k ∧ k ≤ l41Big κ F G H lam a L ∧
      (∃ C N, C.P = Qof P ∧ C.s = a ∧ C.m = L ∧
        Robust ztdo c'.nmem (fun m => NFAt m (c'.nreg 160004) N) ∧
        IsCanonicalNF ztc zta N ztcad 4) ∧
      Frame l41Bands c c' k := by
  zuk
  zuku
  have hR : Robust A c.nmem (fun m' => GradeRaw O P m' h A) := hX
  have hBig0 : 40 * lam ^ 2 + 169 * lam + 84 + 11 * (cover lam ztqy a).length ≤
      l41Big κ F G H lam a L := by unfold l41Big; omega
  have hsqpos : lam ≤ lam ^ 2 := by_nlinarith
  -- the prologue
  obtain ⟨c5, k5, e5, hk5, hk5', hw5, h5A, hhost, m5c, rr5, rm5, o5, fr5, s00, s10, s11, s14, s15, s20,
      s21, s22, s24, s26, s27, s32, s33, s80, s81, s82, s83, s84, s87⟩ :=
    l41A_exec hG hWh hw hA r0 r1 r2 r3 hR hlΛ h7 han hL1 hL2 by_omega
  -- the leaves
  obtain ⟨c8, k8, e8, hk8, hw8, h8A, h8Ak, hLev, m8c, s8_14, s8_66, fr8, rr8, rm8, o8⟩ :=
    l41B_exec hG hWh hw5 hR hlΛ h7 han hL1 hL2 m5c hhost h5A s10 s11 s14 s15 s20 s21 s22 s24
      s26 s27 s81 s82 s87 by_omega
  zuhyu
  have hj2 : 2 ≤ (cover lam ztqy a).length := two_le_cover by_omega by_omega
  obtain ⟨j, hj⟩ : ∃ j, (cover lam (a + L) a).length = j := zths
  rw [hj] at hk8 h8A hLev s8_14 s8_66 hj2l hj2 hBig0
  have c85 : ∀ r, 160000 ≤ r → r < 160090 → ¬ CovRG r → ¬ L0RG r → r ≠ 160066 →
      c8.nreg r = c5.nreg r := fun r a1 a2 a3 a4 a5 => fr8 r a3 a4 a5 by_omega
  have s8 : ∀ r, (r = 160000 ∨ r = 160024 ∨ r = 160032 ∨ r = 160033 ∨ r = 160080 ∨
      r = 160081 ∨ r = 160083 ∨ r = 160084) → c8.nreg r = c5.nreg r := fun r hr =>
    c85 r by_omega by_omega ztiit ztbsj by_omega
  -- the merge tree
  have hlen0 : (leafShp lam ztqy a).length = j := by rw [leafShp_length, hj]
  have hgran0 := leafShp_gran (lam := lam) (b := a + L) (a := a)
  have hstep := gradeGran_step ztma
  rw [show lam - 1 + 1 = lam by omega] at hstep
  have hcj : Nat.clog 2 j ≤ Nat.clog 2 lam + 1 := clog_le_of_le_two_mul hj2l
  zudom
  zucvv
  have hG0cl : gradeGran ztma + Nat.clog 2 j ≤ gradeGran lam := by
    grind
  have hXs : (gradeCtx O).holds P c8.nmem h ztvkp := by
    rw [h8A]
    exact (gradeCtx O).mono _ _ _ _ _ by_omega
      ((gradeCtx O).local_ _ _ _ _ _ (fun x hx => (m8c x hx).symm) hX)
  have hst0 : TreeSt P W ztsy c8 ztvkp A h ztcad a L
      ztwyd ztwsz c8 := by
    refine ⟨hw8, by_omega, by rw [s8 _ by_decide]; omega,
      ⟨A + 7 + 6 * j, s8_66, by_omega, by_grind⟩,
      leafShp_consec _ _ _, by_omega, leafShp_first (lam := lam) (b := a + L) (a := a) by_omega,
      by zuoyo; omega, fun k hk => (hgran0 k hk).1,
      fun k hk => (hgran0 k hk).2, fun h1 => by_omega, by_grind, le_rfl,
      fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl, hXs, rfl⟩
  have hPI : PInv ztwsz ztcad j L ztdow
      ztwyd ztwsz := by
    refine ⟨by_omega, by_omega, by zuoyo; omega, by_grind,
      le_rfl, le_rfl, fun x hx hxl => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    have := (hgran0 k hk).1
    unfold nd at this
    rw [List.getD_eq_getElem _ _ hk] at this
    unfold leafP at hxl
    grind
  have hTC := totCost_le κ F G H hF hGm hH (Gl := gradeGran lam) (G0 := gradeGran ztma)
    (J := j) (L := L)
    (LS0 := leafKb lam a L) j ztwyd ztwsz by_omega hPI
  rw [hlen0] at hTC
  have hBig2 : 40 * lam ^ 2 + 169 * lam + 84 + 11 * j +
      Nat.clog 2 j * (lvBound κ F G H ztcad ztwsz j L ztdow + 2) =
      l41Big κ F G H lam a L := by unfold l41Big; rw [hj]
  have hGcapX : gradeGran lam ≤ (gradeCtx O).cap P c8.nmem h := by
    show gradeGran lam ≤ 2 ^ (c8.nmem h - 1)
    have hh : ztpox := le_lt hR (x := h) (v := topGrade P.n + 1) fun m' _ hm' => hm'.1
    rw [m8c h hh]
    zucvv
    have : 2 ^ ztma ≤ 2 ^ (c.nmem h - 1) :=
      Nat.pow_le_pow_right by_norm_num by_omega
    omega
  obtain ⟨c9, k9, ns', γ', e9, hk9, h9A, hlen', hst9⟩ :=
    tree_exec hG hWh hWn hMM ztgjv (fun C hC => okModel_chain hG C hC)
      ztbmi ztbmi
      ztbmi ztbmi
      ztbmi ztbmi
      ztbmi hGcapX by_omega j ztwyd
      ztwsz c8 by_omega hst0
      by_grind
  obtain ⟨hw9, -, -, ⟨B9, h9_66, hB9, hLev9⟩, -, -, hfirst, hsum, -, -, hone, -, hAs9, hm98,
    hrm98, ho98, fr98, frr98, -, -⟩ := hst9
  -- the single node
  obtain ⟨C, hCs, hCm, hN⟩ := hLev9 0 by_omega
  have hγ1 := hone hlen'
  have hCm' : C.m = L := by
    rw [hCm]
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen'
    zultk
    simpa [nd] using hsum
  have hCs' : C.s = a := by_omega
  have nLv : ∀ r, zteuy → ¬ LvRG r := fun r hr => by
    unfold LvRG PairRG DescRG RbRG; omega
  have s9_24 : c9.nreg 160024 = 1 := by
    rw [fr98 _ (bandOK_l41 by_decide by_decide) (by unfold LvRG PairRG DescRG RbRG; decide)
      by_omega, s8 _ by_decide]; omega
  have hB9W : B9 + 1 ≤ W := by_grind
  obtain ⟨c10, k10, e10, hk10, hw10, t04, fr10, hm10, hrr10, hrm10, ho10⟩ :=
    epiB_exec (P := P) hw9 h9_66 s9_24 hB9W
  have c10A : c10.nreg ALLOC = c9.nreg ALLOC :=
    fr10 _ by_omega by_omega
  obtain ⟨-, hCP, -, -, -, -, N, hNW, hc⟩ := hN
  simp only [Nat.mul_zero, Nat.add_zero] at hNW
  rw [hγ1] at hc
  refine ⟨c10, k5 + (k8 + (k9 + k10)), .seq e5 (.seq e8 (.seq e9 e10)), ?_,
    ⟨C, N, hCP, hCs', hCm', ?_, hc⟩, ?_⟩
  · omega
  · rw [c10A, hm10, t04]; exact hNW
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
    · zuhhv
      rw [fr10 r by_omega by_omega, fr98 r hr2 zttty hra,
        fr8 r ztiit ztbsj by_omega hra]
      exact fr5 r hr1 hra
    · zuhhv
      rw [hrr10, frr98 r hr2 zttty, rr8, rr5]
    · zvmze at hx; rw [hm10, hm98 x by_omega, m8c x hx]
    · zvmze at hx; rw [hrm10, hrm98 x by_omega, rm8, rm5]
    · grind
    · omega
    omega
end proofs
open Chazelle.Cost Finset
noncomputable def scF (κ : ℕ) (γ : ℕ) : ℕ :=
  κ * ztxd * rpowCeil ztwku ztby + κ

/-- The cutter's piece count of `ShootCutSpec`. -/
def scG (κ : ℕ) (γ : ℕ) : ℕ := κ * ztxd
theorem cutGran_mono : Monotone cutGran := fun _ _ h =>
  gradeGran_mono zttas
theorem rpowCeil_mono {x y : ℕ} (a : ℝ) (ha : 0 ≤ a) (h : x ≤ y) : rpowCeil x a ≤ rpowCeil y a :=
  Nat.ceil_mono (Real.rpow_le_rpow ztdlc by_simp_all ha)
variable (κ : ℕ) (g : ℕ)
theorem scF_mono : Monotone ztbon := by
  intro x y h
  unfold scF
  have h1 := Nat.clog_mono_right 2 h
  have h2 : cutGran x * zthf ^ 2 ≤ cutGran y * zthlg ^ 2 :=
    Nat.mul_le_mul (cutGran_mono h) zttbd
  have h3 := rpowCeil_mono ztby by_norm_num h2
  gcongr
theorem scG_mono : Monotone ztboo := fun x y h => by
  have := Nat.clog_mono_right 2 h
  unfold scG; gcongr

/-! ## Powers of `E = 2^(λ/75)` -/

/-- `E^k = 2^(kλ/75)`. -/
theorem E_pow (lam k : ℕ) : ztht ^ k = (2 : ℝ) ^ ((k : ℝ) * lam / 75) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul by_norm_num]; grind
theorem two_pow_le_E {n lam k : ℕ} {b : ℝ} (h : (n : ℝ) ≤ (k : ℝ) * lam / 75 + b) :
    (2 : ℝ) ^ n ≤ (2 : ℝ) ^ b * ztht ^ k := by
  rw [E_pow, ← Real.rpow_natCast, two_rpow_mul_two_rpow]
  apply two_rpow_le_two_rpow; linarith
theorem ceilBeta_le_real : (ceilBeta g : ℝ) ≤ (g : ℝ) / 5 + 1 := by
  have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ beta * g by rw [beta_eq]; positivity)
  unfold ceilBeta; rw [beta_eq] at this ⊢; linarith
theorem le_ceilBeta_real : (g : ℝ) / 5 ≤ (ceilBeta g : ℝ) := by
  have := beta_mul_le_ceilBeta g; rw [beta_eq] at this; linarith
section bounds
variable {lam : ℕ}

/-- `2^⌈βλ⌉ ≤ 2 E^15`. -/
theorem two_pow_ceilBeta_le (lam : ℕ) :
    (2 : ℝ) ^ ceilBeta lam ≤ 2 * ztht ^ 15 := by
  have := two_pow_le_E (n := ceilBeta lam) (lam := lam) (k := 15) (b := 1)
    (by have := ceilBeta_le_real lam; grind)
  simp_all

/-- `γ'_λ ≤ 2402 E^15`. -/
theorem gradeGran_le_E (lam : ℕ) :
    (gradeGran lam : ℝ) ≤ 2402 * ztht ^ 15 := by
  have h1 := gradeGran_le_real lam
  have h2 := two_pow_ceilBeta_le lam
  linarith

/-- `⌈log₂ γ'_λ⌉ + 1 ≤ 3λ` for `λ ≥ 6`. -/
theorem clog_gradeGran_add_one_le (h6 : 6 ≤ lam) : Nat.clog 2 ztcad + 1 ≤ 3 * lam := by
  have h1 := clog_gradeGran_le lam
  have h2 : Nat.clog 2 ztcad ≤ Nat.clog 2 zthxo :=
    Nat.clog_mono_right 2 by_omega
  have h3 := ceilBeta_le lam
  omega

/-- `H(γ'_λ) = γ'_{⌈log₂ γ'_λ⌉} ≤ 19216 E^3`. -/
theorem cutGran_le_E (lam : ℕ) :
    (cutGran ztcad : ℝ) ≤ 19216 * ztht ^ 3 := by
  unfold cutGran
  set CL := Nat.clog 2 _ with hCL
  have h1 := gradeGran_le_real CL
  have hcl : (CL : ℝ) ≤ (lam : ℝ) / 5 + 12 := by
    have a1 := clog_gradeGran_le lam
    have a2 : CL ≤ Nat.clog 2 zthxo := Nat.clog_mono_right 2 by_omega
    have a3 := ceilBeta_le_real lam
    have : (CL : ℝ) ≤ (ceilBeta lam : ℝ) + 11 := by exact_mod_cast by_omega
    linarith
  have h2 : (2 : ℝ) ^ ceilBeta CL ≤ (2 : ℝ) ^ (4 : ℝ) * ztht ^ 3 :=
    two_pow_le_E (by have := ceilBeta_le_real CL; grind)
  linarith

/-- `λ ≤ 150 E`. -/
theorem lam_le_E (lam : ℕ) : (lam : ℝ) ≤ 150 * (2 : ℝ) ^ ztbxl := by
  have := nat_le_two_rpow 75 by_norm_num lam
  grind
theorem one_le_E (lam : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ ztbxl :=
  Real.one_le_rpow by_norm_num by_positivity

/-- `⌈(H (Gλ + 1)²)^{1/3}⌉ ≤ 4901 E^11`. -/
theorem rpowCeil_le_E (lam : ℕ) :
    (rpowCeil (cutGran ztcad * zthxo ^ 2) ztby : ℝ) ≤
      4901 * ztht ^ 11 := by
  zuid

  zulhx
  have hG := gradeGran_le_E lam
  rw [← hE] at hH hG
  have hG1 : ((gradeGran lam : ℕ) : ℝ) + 1 ≤ 2403 * E ^ 15 := by
    have : (1 : ℝ) ≤ E ^ 15 := one_le_pow₀ hE1
    linarith
  set X := cutGran _ * zthxo ^ 2 with hX
  have hXR : (X : ℝ) ≤ ztjft ^ 3 := by
    rw [hX]; push_cast
    have h0 : (0 : ℝ) ≤ (gradeGran lam : ℝ) + 1 := by_positivity
    calc (cutGran _ : ℝ) * ((gradeGran lam : ℝ) + 1) ^ 2
        ≤ (19216 * E ^ 3) * (2403 * E ^ 15) ^ 2 := by
          apply mul_le_mul hH (pow_le_pow_left₀ h0 hG1 2) by_positivity by_positivity
      _ ≤ ztjft ^ 3 := by
          have : (0 : ℝ) ≤ E ^ 33 := by_positivity
          grind
  have hroot : (X : ℝ) ^ ztby ≤ 4900 * E ^ 11 := by
    have h0 : (0 : ℝ) ≤ 4900 * E ^ 11 := by_positivity
    calc (X : ℝ) ^ ztby ≤ (ztjft ^ 3) ^ ztby :=
          Real.rpow_le_rpow ztdlc hXR by_norm_num
      _ = 4900 * E ^ 11 := by
          zucqh
  zujqv

  have : (1 : ℝ) ≤ E ^ 11 := one_le_pow₀ hE1
  linarith

/-- **The cost factor of one merge**: `φ ≤ K₁ λ² E^14`. -/
theorem phiL_le (κM κ : ℕ) {L : ℕ} (h7 : 7 ≤ lam) (hL : L ≤ 2 ^ lam) :
    (phiL ztbdd ztbon ztboo cutGran ztcad L : ℝ) ≤
      (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) * (lam : ℝ) ^ 2 *
        ztht ^ 14 := by
  zuid

  zuhfe
  have hl7 : (7 : ℝ) ≤ lam := by_simp_all
  have hCL : ((Nat.clog 2 ztcad + 1 : ℕ) : ℝ) ≤ 3 * lam := by
    exact_mod_cast clog_gradeGran_add_one_le by_omega
  have hR := rpowCeil_le_E lam
  zulhx
  rw [← hE] at hR hH
  have hLc : Nat.clog 2 ztgt ≤ lam + 1 := by
    zudwq
    grind
  have hLcR : (Nat.clog 2 ztgt : ℝ) ≤ lam + 1 := by exact_mod_cast hLc
  unfold phiL scF scG
  push_cast
  push_cast at hCL
  have hκ : (0 : ℝ) ≤ κ := Nat.cast_nonneg _
  have hκM : (0 : ℝ) ≤ κM := Nat.cast_nonneg _
  set c := (Nat.clog 2 _ : ℝ) + 1 with hc
  set r := (rpowCeil _ ztby : ℝ)
    with hr
  have hc0 : 0 ≤ c := by_positivity
  have hr0 : 0 ≤ r := by_positivity
  have hE11 : 1 ≤ E ^ 11 := one_le_pow₀ hE1
  have hE3 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
  have hEE : E ≤ E ^ 3 := by
    calc E = E ^ 1 := by_simp_all
      _ ≤ E ^ 3 := pow_le_pow_right₀ hE1 by_norm_num
  -- the three factors
  have hFb : (κ : ℝ) * c * r + κ ≤ κ * 14704 * lam * E ^ 11 := by
    have  :=
      mul_le_mul hCL hR hr0 by_positivity
    have h1 : (1 : ℝ) ≤ lam * E ^ 11 := by_nlinarith
    nlinarith
  have hGb := mul_le_mul_of_nonneg_left hCL hκ
  have hHb : (cutGran ztcad : ℝ) + (Nat.clog 2 ztgt : ℝ) + 1 ≤ 19368 * E ^ 3 := by
    nlinarith
  have hF0 : 0 ≤ (κ : ℝ) * c * r + κ := by_positivity
  have hG0 : 0 ≤ (κ : ℝ) * c := by_positivity
  calc (κM : ℝ) * ((κ : ℝ) * c * r + κ) * ((κ : ℝ) * c) *
        ((cutGran _ : ℝ) + (Nat.clog 2 _ : ℝ) + 1)
      ≤ (κM : ℝ) * (κ * 14704 * lam * E ^ 11) * (κ * (3 * lam)) * (19368 * E ^ 3) := by
        gcongr
    _ = (κM * κ ^ 2 * 14704 * 3 * 19368 : ℝ) * (lam : ℝ) ^ 2 * E ^ 14 := by_ring
end bounds
section rest
variable {lam : ℕ}

/-- The chord bound of a leaf of grade `g`. -/
noncomputable def leafW (g : ℕ) : ℕ := 60 * ztgyd / gradeGran g
theorem leafW_le (g : ℕ) : leafW g ≤ 540 * 2 ^ ztczo := by
  unfold leafW
  have hcb := ceilBeta_le g
  have h1 : 60 * ztgyd ≤ 540 * 2 ^ g := by
    grind
  have h2 := two_pow_ceilBeta_le_gradeGran g
  have h3 : 2 ^ g = 2 ^ ceilBeta g * 2 ^ ztczo := by
    zunvh; simp_all
  calc 60 * ztgyd / gradeGran g ≤ 540 * 2 ^ g / 2 ^ ceilBeta g :=
        Nat.div_le_div h1 h2 by_positivity
    _ = 540 * 2 ^ ztczo := by
        rw [h3, show 540 * (2 ^ ceilBeta g * 2 ^ ztczo) =
          2 ^ ceilBeta g * (540 * 2 ^ ztczo) by ring,
          Nat.mul_div_cancel_left _ by_positivity]

/-- **The chords of the leaves**: `≤ 10800 E^60`. -/
theorem leafKb_le {a L : ℕ} (h1 : 1 ≤ lam) (hL : L ≤ 2 ^ lam) :
    (leafKb lam a L : ℝ) ≤ 10800 * ztht ^ 60 := by
  have hsub : leafKb lam a L ≤ ((leafShp lam _ a).map kb).sum :=
    sublist_sum_le ((List.filter_sublist).map kb)
  have hmap : (leafShp lam ztqy a).map kb = (cover lam ztqy a).map fun q => leafW q.1 := by
    unfold leafShp; rw [List.map_map]; rfl
  have hw := cover_weight_le (b := a + L) (x := a) leafW h1 by_omega
  rw [← hmap] at hw
  have hsum : ∑ g ∈ range lam, leafW g ≤ ∑ g ∈ range lam, 540 * 2 ^ ztczo :=
    Finset.sum_le_sum fun g _ => leafW_le g
  have hR : ((∑ g ∈ range lam, 540 * 2 ^ ztczo : ℕ) : ℝ) ≤
      5400 * ztht ^ 60 := by
    push_cast
    zulqt
    have := resetCost_le lam
    have e : (2 : ℝ) ^ ztein = ztht ^ 60 := by
      rw [E_pow, beta_eq]; grind
    grind
  have : (leafKb lam a L : ℝ) ≤ 2 * ((∑ g ∈ range lam, 540 * 2 ^ ztczo : ℕ) : ℝ) := by
    exact_mod_cast by_omega
  linarith

/-- **The chords of the merged nodes**: `(120 L + 420 J) / (γ'_{λ-1} + 1) ≤ 252240 E^60`. -/
theorem mergedKb_le {L J : ℕ} (h1 : 1 ≤ lam) (hL : L ≤ 2 ^ lam) (hJ : J ≤ 2 * lam) :
    ((ztckq / ztzmb : ℕ) : ℝ) ≤
      252240 * ztht ^ 60 := by
  zuid

  zuhfe
  refine le_trans (Nat.cast_div_le) ?_
  have hG0 : E ^ 15 ≤ 2 * ((gradeGran ztma : ℝ) + 1) := by
    have a1 : ((2 ^ ceilBeta ztma : ℕ) : ℝ) ≤ gradeGran ztma := by
      exact_mod_cast two_pow_ceilBeta_le_gradeGran _
    have a2 : E ^ 15 ≤ (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ ((ceilBeta ztma : ℕ) : ℝ) := by
      rw [hE, E_pow, two_rpow_mul_two_rpow]
      zujrx
      have := le_ceilBeta_real ztma
      have e : ((lam - 1 : ℕ) : ℝ) = (lam : ℝ) - 1 := by_simp_all
      grind
    rw [Real.rpow_natCast, Real.rpow_one] at a2
    grind
  have hpos : (0 : ℝ) < (gradeGran ztma : ℝ) + 1 := by_positivity
  push_cast
  zuhla
  have hLR : (L : ℝ) ≤ E ^ 75 := by
    have : ((L : ℕ) : ℝ) ≤ ((2 ^ lam : ℕ) : ℝ) := by exact_mod_cast hL
    rw [hE, E_pow]; simp_all
  have hJR : (J : ℝ) ≤ 300 * E := by
    zuiuk
    linarith
  have hE60 : ztrzt := by_positivity
  have hEE : E ≤ E ^ 75 := by
    calc E = E ^ 1 := by_simp_all
      _ ≤ E ^ 75 := pow_le_pow_right₀ hE1 by_norm_num
  have e75 : E ^ 75 = E ^ 60 * E ^ 15 := by_ring
  nlinarith

/-- The constant of one level. -/
def lvK (κM κ : ℕ) : ℕ := κM * κ ^ 2 * 14704 * 3 * 19368 * 263340 + 728
variable (κM κ : ℕ)
/-- **One level**: `lvBound ≤ K₂ λ² E^74`. -/
theorem lvBound_le {a L J : ℕ} (h7 : 7 ≤ lam) (hL : L ≤ 2 ^ lam) (hJ : J ≤ 2 * lam) :
    (lvBound ztbdd ztbon ztboo cutGran ztcad ztwsz J L
      ztdow : ℝ) ≤
      (lvK κM κ : ℝ) * (lam : ℝ) ^ 2 * ztht ^ 74 := by
  unfold lvK
  zuid

  zuhfe
  zuhza
  have hφ := phiL_le κM κ h7 hL
  have hLS := leafKb_le (a := a) by_omega hL
  have hM := mergedKb_le by_omega hL hJ
  rw [← hE] at hφ hLS hM
  have hJR : (J : ℝ) ≤ 300 * E ^ 60 := by
    zuiuk
    have : E ≤ E ^ 60 := by
      calc E = E ^ 1 := by_simp_all
        _ ≤ E ^ 60 := pow_le_pow_right₀ hE1 by_norm_num
    linarith
  set R := (leafKb lam a L : ℝ) + ((ztckq / ztzmb : ℕ) : ℝ) +
    (J : ℝ) with hR
  have hRb : R ≤ 263340 * E ^ 60 := by_linarith
  have hR0 : 0 ≤ R := by_positivity
  zuckg
  have hK1 : 0 ≤ K1 := by_positivity
  have hφ0 : (0 : ℝ) ≤ phiL ztbdd ztbon ztboo cutGran ztcad L :=
    Nat.cast_nonneg _
  have hprod : (phiL ztbdd _ _ cutGran _ L : ℝ) * R ≤
      K1 * (lam : ℝ) ^ 2 * E ^ 14 * (263340 * E ^ 60) :=
    mul_le_mul hφ hRb hR0 by_positivity
  zuivu
  zukft
  have hJ2 : ztgtj := by exact_mod_cast hJ
  unfold lvBound
  push_cast
  rw [← hR] at *
  have hl2E : (lam : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 * E ^ 74 := by_nlinarith
  grind

/-- **Lemma 4.1's step bound is `O(lemma41Nat λ)`.** -/
theorem l41Big_le {a L : ℕ} (h7 : 7 ≤ lam) (_hL1 : 2 ^ ztma < L)
    (hL : L ≤ 2 ^ lam) :
    l41Big ztbdd ztbon ztboo cutGran lam a L ≤
      (lvK κM κ + 400) * ztrta := by
  obtain ⟨K2, hK2⟩ : ∃ K2, lvK κM κ = K2 := by_simp_all
  rw [hK2]
  zufpg
  have hj2 : j ≤ 2 * lam := cover_length_le by_omega by_omega
  have hcj := clog_le_of_le_two_mul hj2
  have hlv := lvBound_le κM κ (a := a) h7 hL hj2
  rw [hK2] at hlv
  zuid

  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = (lam : ℝ) ^ 2 * ((Nat.clog 2 lam : ℝ) + 1) * E ^ 74 :=
    by_simp_all
  have hN : V ≤ lemma41Nat lam := by
    unfold lemma41Nat
    have e : E ^ 74 = (2 : ℝ) ^ ((74 : ℝ) / 75 * lam) := by
      zuecz
    rw [hV, e]; exact Nat.le_ceil _
  zuhza
  zuivu
  have hcl0 : (0 : ℝ) ≤ Nat.clog 2 lam := Nat.cast_nonneg _
  zukft
  have hV1 : (lam : ℝ) ^ 2 ≤ V := by
    have h1 : (1 : ℝ) ≤ ztbfr * E ^ 74 := by_nlinarith
    calc (lam : ℝ) ^ 2 = (lam : ℝ) ^ 2 * 1 := by_ring
      _ ≤ (lam : ℝ) ^ 2 * (ztbfr * E ^ 74) :=
          mul_le_mul_of_nonneg_left h1 ztqwr
      _ = V := by_grind
  have hV2 : ztbfr ≤ V := by
    have h1 : (1 : ℝ) ≤ (lam : ℝ) ^ 2 * E ^ 74 := by_nlinarith
    calc ztbfr = ztbfr * 1 := by_ring
      _ ≤ ztbfr * ((lam : ℝ) ^ 2 * E ^ 74) :=
          mul_le_mul_of_nonneg_left h1 by_positivity
      _ = V := by_grind
  have hcjR : (Nat.clog 2 j : ℝ) ≤ (Nat.clog 2 lam : ℝ) + 1 := by exact_mod_cast hcj
  have hjR : (j : ℝ) ≤ 2 * lam := by exact_mod_cast hj2
  have hlvR : (lvBound ztbdd ztbon ztboo cutGran ztcad ztwsz
      j L ztdow : ℝ) + 2 ≤ (K2 : ℝ) * (lam : ℝ) ^ 2 * E ^ 74 + 2 := by_linarith
  have hK2 : (0 : ℝ) ≤ K2 := Nat.cast_nonneg _
  have hmain : (Nat.clog 2 j : ℝ) * ((lvBound ztbdd ztbon ztboo cutGran
      ztcad ztwsz j L ztdow : ℝ) + 2) ≤
      (K2 : ℝ) * V + 2 * V := by
    have h0 : (0 : ℝ) ≤ (lvBound ztbdd ztbon ztboo cutGran ztcad
      ztwsz j L ztdow : ℝ) + 2 := by_positivity
    calc (Nat.clog 2 j : ℝ) * ((lvBound ztbdd _ _ cutGran
          _ _ j L _ : ℝ) + 2)
        ≤ ztbfr * ((K2 : ℝ) * (lam : ℝ) ^ 2 * E ^ 74 + 2) :=
          mul_le_mul hcjR hlvR h0 by_positivity
      _ = (K2 : ℝ) * V + 2 * ztbfr := by_grind
      _ ≤ (K2 : ℝ) * V + 2 * V := by_linarith
  have hbig : (l41Big ztbdd ztbon ztboo cutGran lam a L : ℝ) ≤
      ((K2 + 400 : ℕ) : ℝ) * V := by
    unfold l41Big
    grind
  have hfin : ((K2 + 400 : ℕ) : ℝ) * V ≤ ((K2 + 400 : ℕ) : ℝ) * ((lemma41Nat lam : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left by_linarith ztdlc
  have : (l41Big ztbdd ztbon ztboo cutGran lam a L : ℝ) ≤
      (((K2 + 400) * ztrta : ℕ) : ℝ) := by
    grind
  zufc
end rest
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Chazelle
@[expose] public section
theorem lemma41_of (O : OracleIface) (hM : MergeSpec) (hSC : ShootCutSpec O) :
    Lemma41Spec O := by
  zuejl
  obtain ⟨mk, κM, hmk⟩ := mergeMeets_of hM
  have hMM : MergeMeets ztdvk κM ztmnn ztmno cutGran ztsy OkModel :=
    hmk sh cu oracleBands oracleBands ztmnn ztmno cutGran ztsy OkModel
      ztgjv ztqcs ztijh ztwdd ztwde cutGran_mono
      subset_rfl subset_rfl hsh hcu
  refine ⟨l41S ztdvk, lvK ztwih κs + 400, ?_⟩
  intro P W c hw ⟨hG, hWh, hX, hΛ, h7, han, hL1, hL2⟩ hbud
  have h7' : 7 ≤ rd c bL41 3 := h7
  have e : l41Big κM ztmnn ztmno cutGran ztrvk ztrvi ztrvj =
      l41Big (fun _ => κM 4) ztmnn ztmno cutGran ztrvk ztrvi
        ztrvj := rfl
  have hB := l41Big_le ztwih κs (a := rd c bL41 1) h7' hL1 hL2
  zvmyr at hB
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ :=
    l41_exec hG hWh hMM ztwdd ztwde cutGran_mono hw rfl rfl rfl rfl rfl hX hΛ h7'
      han hL1 hL2 (le_trans (Nat.add_le_add_left hB _) hbud)
  exact ⟨c', k, ex, le_trans hk hB, hpost, hfr⟩
end
end Chazelle.Core.L41
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def halfBody : Stmt := block [.addN 170043 170003 170040, .storeN 170043 170041,
  .addN 170043 170043 170020, .storeN 170043 170041, .addN 170040 170040 170021,
  .addN 170041 170041 170020, .addN 9999 9999 170021]

/-- **The halving table.** -/
def halfS : Stmt := .seq (block [.copyN 170003 9999, .constN 170040 0, .constN 170041 0,
  .addN 170042 170001 170020]) (.whileLtN 170040 170042 halfBody)

/-- The registers written by `halfS` (besides the allocator). -/
def HalfRG (r : ℕ) : Prop := r = 170003 ∨ (170040 ≤ r ∧ r ≤ 170043)

/-- The registers written by `halfBody` (besides the allocator). -/
def HalfBRG (r : ℕ) : Prop := r = 170040 ∨ r = 170041 ∨ r = 170043
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem halfBody_exec (hw : WordsBounded W c) {D t y Al : ℕ}
    (h03 : c.nreg 170003 = D) (h40 : c.nreg 170040 = t) (h41 : c.nreg 170041 = y)
    (hA : c.nreg ALLOC = Al) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (hW : D + t + 2 ≤ W) (hWy : y + 1 ≤ W) (hWA : Al + 2 ≤ W) :
    ∃ c' k, Exec P W halfBody c c' k ∧ k = 7 ∧ WordsBounded W c' ∧
      c'.nreg 170040 = t + 2 ∧ c'.nreg 170041 = y + 1 ∧ c'.nreg ALLOC = Al + 2 ∧
      c'.nmem (D + t) = y ∧ c'.nmem (D + t + 1) = y ∧
      (∀ a, a ≠ D + t → a ≠ D + t + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ HalfBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold halfBody
  exec_block
  all_goals try (config_simp; (try simp only [h03, h40, h41, hA, h20, h21]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · unfold HalfBRG at h1
    simp_all
set_option maxHeartbeats 16000000 in
/-- **The halving table on the RAM.** -/
theorem halfS_exec (hw : WordsBounded W c) {n D : ℕ}
    (hA : c.nreg ALLOC = D) (h01 : c.nreg 170001 = n) (h20 : c.nreg 170020 = 1)
    (h21 : c.nreg 170021 = 2) (hW : D + n + 4 ≤ W) :
    ∃ c' k, Exec P W halfS c c' k ∧ k ≤ 9 * n + 24 ∧ WordsBounded W c' ∧
      c'.nreg 170003 = D ∧ D + n + 1 ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ D + n + 3 ∧
      c'.nreg ALLOC ≤ D + k ∧
      (∀ x, x ≤ n → c'.nmem ztswk = x / 2) ∧
      ztiuj ∧
      ztgss ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i03, i40, i41, i42, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 170003 9999, .constN 170040 0, .constN 170041 0, .addN 170042 170001 170020])
      c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 170003 = D ∧ c1.nreg 170040 = 0 ∧
      c1.nreg 170041 = 0 ∧ c1.nreg 170042 = n + 1 ∧ (∀ r, ¬ HalfRG r → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h01, h20]); omega)
    refine ⟨rfl, ‹_›, by_simp_all, by config_simp, by config_simp,
      by simp_all, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    unfold HalfRG at hr
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have r1 : ∀ r, ¬ HalfRG r → c1.nreg r = c.nreg r := fr1
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ ∃ k, 2 * k ≤ n + 2 ∧
    c'.nreg 170040 = 2 * k ∧ c'.nreg 170041 = k ∧ c'.nreg 170042 = n + 1 ∧
    c'.nreg 170003 = D ∧ c'.nreg ALLOC = D + 2 * k ∧
    (∀ x, x < 2 * k → c'.nmem ztswk = x / 2) ∧ ztiuj ∧
    ztgss ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, e, ⟨hw', t, ht, h40', h41', h42', h03', hA', hent, hlow, fr', hrr', hrm', ho'⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170040) (b := 170042) (body := halfBody) I
      (fun c' => 9 * (n + 2 - c'.nreg 170040)) ztcht ztbms
      (fun c2 ⟨hw2, t, ht, h40, h41, h42, h03, hA2, hent, hlow, fr2, hrr2, hrm2, ho2⟩ htest => by
        rw [h40, h42] at htest
        have g : ∀ r, ¬ HalfRG r → r ≠ ALLOC → c2.nreg r = c.nreg r := fr2
        obtain ⟨c3, k3, e3, hk3, hw3, q40, q41, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          halfBody_exec (P := P) hw2 h03 h40 h41 hA2
            ztyar
            ztyar
            by_omega by_omega by_omega
        refine ⟨c3, k3, e3, ⟨hw3, t + 1, by_omega, by_omega, q41,
          by rw [fr3 170042 ztqfy by_omega]; omega,
          by rw [fr3 170003 ztqfy by_omega]; omega,
          by omega, fun x hx => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by simp_all, by_simp_all, by_simp_all⟩, ?_, ?_⟩
        · grind
        · grind
        · rw [fr3 r (by unfold HalfBRG; unfold HalfRG at h1; omega) h2]; simp_all
        · omega
        omega)
      ⟨hw1, 0, by_omega, i40, i41, i42, i03,
        by rw [r1 _ ztlj, hA]; ring,
        fun x hx => by_omega, fun a _ => by zvmxz, fun r h1 _ => r1 r h1, hrr1, hrm1, ho1⟩
  rw [h40', h42'] at htest
  have hk' : k ≤ 9 * ztttu + 2 := by
    omega
  zufwy
  have hA1 : c1.nreg ALLOC = D := by rw [r1 _ ztlj]; exact hA
  refine ⟨c', k1 + k, .seq e1 e, ?_, hw', h03', by_omega, by_omega, by_omega,
    fun x hx => hent x by_omega, hlow, fr', hrr', hrm', ho'⟩
  grind
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey
  Chazelle.Core.Brute
@[expose] public section
theorem topIdx_one {C : Chain} (h1 : C.m = 1) :
    C.topIdx = if (C.vertex 0).2 < (C.vertex 1).2 then 1 else 0 := by
  have ht := C.topIdx_le
  have hspec := C.topIdx_spec.2
  zus
  · grind
  · have := C.topIdx_min (j := 0) by_omega (fun i hi => by
      grind)
    omega

/-- The points of the height test. -/
def d0PtsB : Stmt := block [.constN 170050 0, .copyN 170051 170016, .constN 170053 0,
  .addN 170054 170016 170020, .constN 170056 0, .constN 170057 0]

/-- The registers of `bitS`. -/
def d0BitB : Stmt := block [.copyN 180000 170016, .copyN 180010 170001, .constN 180011 1,
  .copyN 180013 170059, .constN 180028 0]

/-- The descriptor words. -/
def d0StoreB : Stmt := block [.copyN 170060 9999, .addN 9999 9999 170023,
  .storeN 170060 170004, .addN 170058 170060 170020, .storeN 170058 170016,
  .addN 170058 170058 170020, .storeN 170058 170020, .addN 170058 170058 170020,
  .storeN 170058 170059, .addN 170058 170058 170020, .storeN 170058 180014]

/-- **The descriptor of a grade-0 chain.** -/
def desc0S : Stmt := .seq d0PtsB (.seq (kbit 170050 170053 170056 1 170059)
  (.seq d0BitB (.seq bitS d0StoreB)))

/-- The registers of band `bUp` written by `desc0S`. -/
def D0RG (r : ℕ) : Prop := 170050 ≤ r ∧ r ≤ 170060
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 8000000 in
theorem d0PtsB_exec (hw : WordsBounded W c) {s : ℕ}
    (h16 : c.nreg 170016 = s) (h20 : c.nreg 170020 = 1) (hW : s + 1 ≤ W) :
    ∃ c' k, Exec P W d0PtsB c c' k ∧ k = 6 ∧ WordsBounded W c' ∧
      SymPtIn c' 170050 (.vtx s) ∧ SymPtIn c' 170053 (.vtx ztbk) ∧
      SymPtIn c' 170056 ztga ∧
      (∀ r, ¬ D0RG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold d0PtsB
  exec_block
  all_goals try (config_simp; (try simp only [h16, h20]); omega)
  refine ⟨rfl, ‹_›, ⟨by config_simp, by_simp_all⟩,
    ⟨by config_simp, by_simp_all⟩, ⟨by config_simp, by config_simp⟩,
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  unfold D0RG at hr
  zubi
  repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 8000000 in
theorem d0BitB_exec (hw : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W d0BitB c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 180000 = c.nreg 170016 ∧ c'.nreg 180010 = c.nreg 170001 ∧ c'.nreg 180011 = 1 ∧
      c'.nreg 180013 = c.nreg 170059 ∧ c'.nreg 180028 = 0 ∧
      (∀ r, r ≠ 180000 → r ≠ 180010 → r ≠ 180011 → r ≠ 180013 → r ≠ 180028 →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold d0BitB
  exec_block
  all_goals try (config_simp; omega)
  simp_all
set_option maxHeartbeats 8000000 in
theorem d0StoreB_exec (hw : WordsBounded W c) {TD hp s t b : ℕ}
    (hA : c.nreg ALLOC = TD) (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = s)
    (h59 : c.nreg 170059 = t) (h14 : c.nreg 180014 = b) (h20 : c.nreg 170020 = 1)
    (h23 : c.nreg 170023 = 5) (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W d0StoreB c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170060 = TD ∧
      c'.nmem TD = hp ∧ c'.nmem ztjni = s ∧ c'.nmem ztnpx = 1 ∧ c'.nmem zthcw = t ∧
      c'.nmem zthcx = b ∧ ztzu ∧
      (∀ r, ¬ D0RG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold d0StoreB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h20, h23]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h04, h20, Machine.upd_apply]; grind
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h20, Machine.upd_apply]; grind
  · zumqr
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 16000000 in
/-- **The descriptor of a grade-0 chain on the RAM.** -/
theorem desc0S_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp s : ℕ} (hA : c.nreg ALLOC = TD) (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = s)
    (h01 : c.nreg 170001 = P.n) (h20 : c.nreg 170020 = 1) (h23 : c.nreg 170023 = 5)
    (hs : s + 2 ≤ P.n) (hW : TD + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W desc0S c c' k ∧ k ≤ 1900 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170060 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = s → C.m = 1 → HostAt c'.nmem hp ztqg →
        ChainDescAt c'.nmem TD zta ztqg C) ∧
      ztzu ∧
      (∀ r, ¬ D0RG r → bandOf r ≠ bBrute → Bk r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztexd ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zuc
  zudos
  -- the points
  obtain ⟨c1, k1, e1, hk1, hw1, p1, p2, p3, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    d0PtsB_exec (P := P) hw h16 h20 by_omega
  -- the height test
  obtain ⟨c2, k2, e2, hk2, fb2, hf2, hiff2⟩ := kbit_exec (P := P) hG hWn c1 hw1
    (a := 170050) (b := 170053) (d := 170056) (op := 1) (dst := 170059) by_omega by_omega
    by_omega by_omega by_omega (sa := .vtx s) (sb := .vtx ztbk) (sd := .vtx 0)
    (show s < P.n by omega) (show s + 1 < P.n by omega) ztdwe p1 p2 p3
  zueik
  zump
  have k2r : ∀ r, Bk r = false → r ≠ 170059 → c2.nreg r = c1.nreg r := fun r h1 h2 =>
    fr2 r ztljl
  zudmv
  -- the bit registers
  obtain ⟨c3, k3, e3, hk3, hw3, b00, b10, b11, b13, b28, fr3, hm3, hrr3, hrm3, ho3⟩ :=
    d0BitB_exec (P := P) hw2 by_omega
  -- the bit
  set t := c2.nreg 170059 with ht
  have hsn : ∀ C : Chain, C.P = Qof P → C.s = s → C.m = 1 → C.topIdx = t := by
    intro C hCP hCs hCm
    rw [topIdx_one hCm]
    have e0 : C.vertex 0 = (Qof P).vtx s := by
      unfold Chain.vertex Chain.edgeIdx; rw [hCP, hQn, hCs, Nat.add_zero,
        Nat.mod_eq_of_lt by_omega]
    have e1 : C.vertex 1 = (Qof P).vtx ztbk := by
      unfold Chain.vertex Chain.edgeIdx; rw [hCP, hQn, hCs, Nat.mod_eq_of_lt by_omega]
    zucpp
    have hiff : t = 1 ↔ ((Qof P).vtx s).2 < ((Qof P).vtx ztbk).2 := by
      rw [ht, hiff2]; rfl
    grind
  have c3_00 : c3.nreg 180000 = s := by
    rw [b00, k2r _ zttgv by_omega, fr1 _ ztdmi]; omega
  have c3_10 : c3.nreg 180010 = P.n := by
    rw [b10, k2r _ zttgv by_omega, fr1 _ ztdmi]; omega
  have c3_13 : c3.nreg 180013 = t := by rw [b13]
  obtain ⟨C0, hC0P, hC0s, hC0m⟩ : ∃ C0 : Chain, C0.P = Qof P ∧ C0.s = s ∧ C0.m = 1 :=
    ⟨⟨Qof P, s, 1, le_rfl, by_omega⟩, rfl, rfl, rfl⟩
  obtain ⟨c4, k4, e4, hk4, fb4, hb4, hiff4⟩ := bitS_exec hG hWn hW8 (C := C0) hC0P
    by_omega c3 hw3 by_omega c3_10 b11
    by_grind b28
  obtain ⟨fr4, frr4, hm4, hrm4, ho4⟩ := fb4
  zubgi
  have k4r : ∀ r, Bbit r = false → c4.nreg r = c3.nreg r := fr4
  have bb : ∀ r, 160000 ≤ r → r < 170061 → Bbit r = false := fun r a b => by
    simp [Bbit, Bk]; omega
  -- the stores
  have c4r : ∀ r, 160000 ≤ r → r < 170050 → c4.nreg r = c.nreg r := fun r a b => by
    rw [k4r r (bb r a by_omega), fr3 r by_omega by_omega by_omega by_omega by_omega,
      k2r r (bk r a) by_omega, fr1 r ztdmi]
  have c4A : c4.nreg ALLOC = TD := by
    rw [k4r _ by_rfl, fr3 _ by_omega by_omega
      by_omega by_omega by_omega,
      k2r _ by_rfl by_omega, fr1 _ ztdmi]
    exact hA
  obtain ⟨c5, k5, e5, hk5, hw5, h5A, h560, w0, w1, w2, w3, w4, hm5, fr5, hrr5, hrm5, ho5⟩ :=
    d0StoreB_exec (P := P) hw4 (TD := TD) (hp := hp) (s := s) (t := t)
      (b := c4.nreg 180014)
      c4A
      by_grind by_grind
      by_grind
      rfl by_grind
      by_grind hW
  have hm5c : ∀ a, ztlfu → c5.nmem a = c.nmem a := fun a ha => by
    grind
  refine ⟨c5, k1 + ztvs, .seq e1 ztbxo,
    by omega, hw5, h5A, h560, w0, fun C hCP hCs hCm hH => ?_, hm5c,
    fun r h1 h2 h3 h4 => ?_, fun r h1 h2 h3 => ?_, by_grind,
    by grind⟩
  · have hC : C = C0 := chain_eq by_grind by_omega by_omega
    subst hC
    refine ⟨by_grind, ?_, by_omega, by_omega,
      by grind, by zunsh; omega⟩
    zuody; have := L41.poly_whole zta by_omega; grind
  · have hb' : ztumw := h2
    unfold bandOf at hb'
    zumqr
    rw [fr5 r ztdmi h4, k4r r (by simp [Bbit, h3]; omega),
      fr3 r by_omega by_omega by_omega by_omega by_omega,
      k2r r h3 by_omega, fr1 r ztdmi]
  · have hb : bandOf r ≠ 17 := h2
    have hb' : ztumw := h3
    unfold bandOf at hb hb'
    rw [hrr5, frr4 r (by simp [Bbit, h1]; omega), hrr3, frr2 r (by simp [Bkb, h1]; omega), hrr1]
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey
@[expose] public section
def unionB : Stmt := block [.copyN 160037 9999, .addN 9999 9999 170023, .constN 160024 1]

/-- **The descriptor of the union of two consecutive chains.** -/
def unionS : Stmt := .seq unionB descS
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
theorem unionB_exec {c : Config} (hw : WordsBounded W c) {TD : ℕ} (hA : c.nreg ALLOC = TD)
    (h23 : c.nreg 170023 = 5) (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W unionB c c' k ∧ k = 3 ∧ WordsBounded W c' ∧
      c'.nreg 160037 = TD ∧ c'.nreg ALLOC = TD + 5 ∧ c'.nreg 160024 = 1 ∧
      (∀ r, r ≠ 160037 → r ≠ 160024 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold unionB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h23]); omega)
  simp_all
set_option maxHeartbeats 16000000 in
/-- **The descriptor of the union on the RAM** (whole host). -/
theorem unionS_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {pl pr TD hp : ℕ} {C₁ C₂ : Chain} (hA : c.nreg ALLOC = TD)
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h23 : c.nreg 170023 = 5)
    (hd1 : ChainDescAt c.nmem pl zta ztqg C₁)
    (hd2 : ChainDescAt c.nmem pr zta ztqg C₂)
    (hh1 : c.nmem pl = hp) (hh2 : c.nmem pr = hp) (hhp : hp + 7 ≤ TD)
    (hP1 : C₁.P = Qof P) (hP2 : C₂.P = Qof P) (hs : C₂.s = C₁.s + C₁.m)
    (hn : C₁.s + C₁.m + C₂.m + 1 ≤ P.n) (hlo : pl + 5 ≤ TD) (hlo' : pr + 5 ≤ TD)
    (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W unionS c c' k ∧ k ≤ 303 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 160037 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = C₁.s → C.m = C₁.m + C₂.m →
        ChainDescAt c'.nmem TD zta ztqg C) ∧
      ztzu ∧
      (∀ r, ¬ DescRG r → Bk r = false → r ≠ 160037 → r ≠ 160024 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztcxk ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, u37, uA, u24, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    unionB_exec (P := P) hw hA h23 hW
  have hd1' : ChainDescAt c1.nmem pl zta ztqg C₁ := by_simp_all
  have hd2' : ChainDescAt c1.nmem pr zta ztqg C₂ := by_simp_all
  obtain ⟨c2, k2, e2, hk2, hw2, -, t0, t1, t2, t3, t4, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descS_exec hG hWn hw1 by_simp_all
      by_simp_all u37 u24 hd1' hd2' hP1 hP2 hs
      hn hlo hlo' hW
  have hlen : C₁.m + C₂.m + 1 ≤ C₁.P.n := by
    rw [hP1, show (Qof P).n = P.n from shear_n _ _]; omega
  have mem2 : ∀ a, a < TD → c2.nmem a = c1.nmem a := fun a ha => hm2 a ztbbu
  have g1 := chainDescAt_agree hd1' hlo by_grind hhp mem2
  have g2 := chainDescAt_agree hd2' hlo' by_grind hhp mem2
  have hTD : ChainDescAt c2.nmem TD zta ztqg (jOf C₁ C₂ hlen).whole := by
    refine descWhole hlen by_grind hs g1 g2 ?_ t1 t2 t3 ?_
    · grind
    grind
  refine ⟨c2, k1 + k2, .seq e1 e2, by_omega, hw2,
    by zuofi; exact uA,
    by zuofj; omega,
    by grind, fun C hCP hCs hCm => ?_,
    fun a ha => by_grind, fun r h1 h2 h3 h4 h5 => by
      grind,
    fun r h1 h2 => by_grind, by_grind, by_grind⟩
  have hC : C = (jOf C₁ C₂ hlen).whole :=
    chain_eq (by rw [hCP, jOf_whole_P, hP1]) (by rw [hCs, jOf_whole_s])
      (by rw [hCm, jOf_whole_m])
  grind
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def bruteCall (sB : Stmt) : Stmt :=
  .seq zthsx
    (.seq sB ztoyu)

/-- Lemma 4.1: `(h, s, len, g) ↦ NF` in `170031`. -/
def l41Call (sL : Stmt) : Stmt :=
  .seq (block [.copyN 160000 170005, .copyN 160001 170016, .copyN 160002 170017,
    .copyN 160003 170007]) (.seq sL (block [.copyN 170031 160004]))

/-- The oracle preprocessing: `(desc, NF, γ) ↦` structure in `170032`. -/
def prepCall (sP : Stmt) : Stmt :=
  .seq zthsp
    (.seq sP ztoyv)
section proofs
variable {P : Polygon} {W : ℕ}
variable {r : ℕ}
theorem band_brute (h1 : 180000 ≤ r) (h2 : r < 190000) : bandOf r = bBrute := by
  unfold bandOf bBrute; omega
theorem band_l41' (h1 : 160000 ≤ r) (h2 : r < 170000) : bandOf r = bL41 := by
  zulud
theorem band_prep (h1 : 110000 ≤ r) (h2 : r < 120000) : bandOf r = bOPrep := by
  unfold bandOf bOPrep; omega
set_option maxHeartbeats 16000000 in
/-- **Brute force, called from the up phase.** -/
theorem bruteCall_exec {sB : Stmt} {κB : ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        ztuu)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust ztdo c'.nmem ztwq ∧
        IsCanonicalNF ztc zta N ztczy 4)
      ztyp)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {s len γ : ℕ} (h16 : c.nreg 170016 = s) (h17 : c.nreg 170017 = len)
    (h11 : c.nreg 170011 = γ) (hl : 1 ≤ len) (hsl : s + len + 1 ≤ P.n) (hγ : 1 ≤ γ)
    (hlγ : len = 1 ∨ 2 ≤ γ) (hbud : c.nreg ALLOC + κB * ztkaf ^ 3 ≤ W) :
    ∃ c' k, Exec P W zthti c c' k ∧ k ≤ κB * ztkaf ^ 3 + 4 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem ztggx ztdo N ∧
        IsCanonicalNF ztc zta N γ 4) ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ bruteBands → r ≠ 170031 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ bruteBands → c'.rreg r = c.rreg r) := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      zthsx c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 180000 = s ∧ c1.nreg 180001 = len ∧
      c1.nreg 180002 = γ ∧ (∀ r, r ≠ 180000 → r ≠ 180001 → r ≠ 180002 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    simp_all
  have hA1 : ztmus := fr1 _ by_omega by_omega
    by_omega
  obtain ⟨c2, k2, e2, hk2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, fr2⟩ :=
    hB P W c1 hw1 ⟨hG, hWh, by show 1 ≤ c1.nreg 180001; omega,
      by show c1.nreg 180000 + c1.nreg 180001 + 1 ≤ P.n; omega,
      by show 1 ≤ c1.nreg 180002; omega,
      by show c1.nreg 180001 = 1 ∨ 2 ≤ c1.nreg 180002; omega⟩
      (by show c1.nreg ALLOC + κB * ztrmq ^ 3 ≤ W; grind)
  replace hk2 : k2 ≤ κB * ztrmq ^ 3 := hk2
  rw [i1] at hk2
  zubbu
  zump
  obtain ⟨c3, k3, e3, hk3, hw3, o31, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      ztoyu c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170031 = c2.nreg 180003 ∧ ztive ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  zudyd
  have hbb : ∀ r, bandOf r ∉ bruteBands → r < 180000 ∨ 190000 ≤ r := by
    zuz
    zukr
    exact hr (by rw [band_brute by_omega by_omega]; decide)
  refine ⟨c3, k1 + ztdve, .seq e1 ztbpc, by_omega, hw3, by_omega,
    by omega, ⟨C, N, hCP, by rw [hCs]; exact i0, by rw [hCm]; exact i1,
      by zuocd; exact hNW, by rw [← i2]; exact hc⟩,
    fun a ha => by_grind,
    fun a ha => by_grind,
    by grind, fun r h1 h2 h3 => ?_, fun r h1 => by_grind⟩
  grind
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
/-- **Lemma 4.1, called from the up phase.** -/
theorem l41Call_exec {O : OracleIface} {sL : Stmt} {κL : ℕ}
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem ztbdk ztm ∧
        rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust ztdo c'.nmem ztwr ∧
        IsCanonicalNF ztc zta N ztbqg 4)
      ztxk)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {h s len g : ℕ} (h05 : c.nreg 170005 = h) (h16 : c.nreg 170016 = s)
    (h17 : c.nreg 170017 = len) (h07 : c.nreg 170007 = g)
    (hX : (gradeCtx O).holds P c.nmem h ztm) (hgΛ : g ≤ c.nmem h) (h7 : 7 ≤ g)
    (hsl : s + len + 1 ≤ P.n) (hl1 : 2 ^ ztfe < len) (hl2 : len ≤ 2 ^ g)
    (hbud : c.nreg ALLOC + κL * ztcnv ≤ W) :
    ∃ c' k, Exec P W zthyo c c' k ∧ k ≤ κL * ztcnv + 5 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem ztggx ztdo N ∧
        IsCanonicalNF ztc zta N ztcvr 4) ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ l41Bands → r ≠ 170031 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ l41Bands → c'.rreg r = c.rreg r) := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, i3, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 160000 170005, .copyN 160001 170016, .copyN 160002 170017,
        .copyN 160003 170007]) c c1 k1 ∧
      k1 = 4 ∧ WordsBounded W c1 ∧ c1.nreg 160000 = h ∧ c1.nreg 160001 = s ∧
      c1.nreg 160002 = len ∧ c1.nreg 160003 = g ∧
      (∀ r, r ≠ 160000 → r ≠ 160001 → r ≠ 160002 → r ≠ 160003 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    simp_all
  have hA1 : ztmus := fr1 _ by_omega by_omega
    by_omega by_omega
  have hX1 : (gradeCtx O).holds P c1.nmem (rd c1 bL41 0) zterf := by
    show (gradeCtx O).holds P c1.nmem ztvkj _
    grind
  obtain ⟨c2, k2, e2, hk2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, fr2⟩ :=
    hL P W c1 hw1 ⟨hG, hWh, hX1,
      by show c1.nreg 160003 ≤ c1.nmem ztvkj; grind,
      by show lemma41Start ≤ c1.nreg 160003; rw [i3]; exact h7,
      by show c1.nreg 160001 + c1.nreg 160002 + 1 ≤ P.n; omega,
      by show 2 ^ (c1.nreg 160003 - 1) < c1.nreg 160002; grind,
      by show c1.nreg 160002 ≤ 2 ^ c1.nreg 160003; grind⟩
      (by show c1.nreg ALLOC + κL * ztocw ≤ W
          grind)
  replace hk2 : k2 ≤ κL * ztocw := hk2
  rw [i3] at hk2
  zubbu
  zump
  obtain ⟨c3, k3, e3, hk3, hw3, o31, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      (block [.copyN 170031 160004]) c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170031 = c2.nreg 160004 ∧ ztive ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  zudyd
  have hbb : ∀ r, bandOf r ∉ l41Bands → r < 160000 ∨ 170000 ≤ r := by
    zuz
    zukr
    exact hr (by rw [band_l41' by_omega by_omega]; decide)
  refine ⟨c3, k1 + ztdve, .seq e1 ztbpc, by_omega, hw3, by_omega,
    by omega, ⟨C, N, hCP, by rw [hCs]; exact i1, by rw [hCm]; exact i2,
      by zuocd; exact hNW, by rw [← i3]; exact hc⟩,
    fun a ha => by_grind,
    fun a ha => by_grind,
    by grind, fun r h1 h2 h3 => ?_, fun r h1 => by_grind⟩
  grind
set_option maxHeartbeats 16000000 in
/-- **The oracle preprocessing, called from the up phase.** -/
theorem prepCall_exec {O : OracleIface} (hV : O.Valid) (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c) {B F γ : ℕ} {H : Host}
    {C : Chain} {N : NF} (h30 : c.nreg 170030 = B) (h31 : c.nreg 170031 = F)
    (h11 : c.nreg 170011 = γ) (hwf : ChainWF P ztm c.nmem B)
    (hd : ChainDescAt c.nmem B zta H C) (hCP : C.P = Qof P)
    (hNW : NFWithin c.nmem F ztm N) (hc : IsCanonicalNF ztc zta N γ 4)
    (hbud : c.nreg ALLOC + O.κ * ztxkq ≤ W) :
    ∃ c' k, Exec P W (prepCall O.prep) c c' k ∧
      k ≤ O.κ * ztxkq + 4 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      c.nreg ALLOC ≤ c'.nreg 170032 ∧ c'.nreg 170032 + 3 ≤ c'.nreg ALLOC ∧
      c'.nmem ztvgg = B ∧ c'.nmem (c'.nreg 170032 + 1) = F ∧
      c'.nmem (c'.nreg 170032 + 2) = γ ∧
      (∀ m', ztdwr → O.At P m' ztvgg) ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → r ≠ 170032 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → c'.rreg r = c.rreg r) := by
  zuk
  obtain ⟨hVb, hVp, -⟩ := hV
  obtain ⟨c1, k1, e1, hk1, hw1, i0, i1, i2, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      zthsp c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 110000 = B ∧ c1.nreg 110001 = F ∧
      c1.nreg 110002 = γ ∧ (∀ r, r ≠ 110000 → r ≠ 110001 → r ≠ 110002 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    refine ⟨rfl, ‹_›, by_tauto, by_tauto,
      by tauto, fun r a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have hA1 : ztmus := fr1 _ by_omega by_omega
    by_omega
  have hwf1 : ChainWF P zterf c1.nmem ztrvx := by
    show ChainWF P zterf c1.nmem ztvke
    grind
  have hd1 : ChainDescAt c1.nmem ztrvx zta H C := by
    show ChainDescAt c1.nmem ztvke zta H C
    grind
  have hN1 : NFWithin c1.nmem (rd c1 bOPrep 1) zterf N := by
    show NFWithin c1.nmem ztqji zterf N
    grind
  have hc1 : IsCanonicalNF ztc zta N (rd c1 bOPrep 2) 4 := by
    show IsCanonicalNF ztc zta N (c1.nreg 110002) 4
    grind
  obtain ⟨c2, k2, e2, hk2, ⟨q0, q0', q1, q2, q3, q4⟩, fr2⟩ :=
    hVp P W c1 hw1 ⟨hG, hWh, hwf1, H, C, N, hd1, hCP, hN1, hc1⟩
      (by show c1.nreg ALLOC + O.κ * (c1.nmem ztqji *
            ztihk + 1) ≤ W
          grind)
  replace hk2 : k2 ≤ O.κ * (c1.nmem ztqji *
    ztihk + 1) := hk2
  rw [i0, i1, hm1] at hk2
  zubbu
  zump
  obtain ⟨c3, k3, e3, hk3, hw3, o32, fr3, hm3, hrr3, hrm3, ho3⟩ : ∃ c3 k3, Exec P W
      ztoyv c2 c3 k3 ∧ k3 = 1 ∧ WordsBounded W c3 ∧
      c3.nreg 170032 = c2.nreg 110003 ∧ (∀ r, r ≠ 170032 → c3.nreg r = c2.nreg r) ∧
      c3.nmem = c2.nmem ∧ c3.rreg = c2.rreg ∧ c3.rmem = c2.rmem ∧ c3.output = c2.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  zudyd
  have hbb : ∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → r < 110000 ∨ 120000 ≤ r := by
    zuz
    zukr
    exact hr (by rw [band_prep by_omega by_omega]; decide)
  have hsub : ∀ r, bandOf r ∉ oracleBands ∪ {bOPrep} → bandOf r ∉ O.bands := fun r hr h' =>
    hr (hVb h')
  refine ⟨c3, k1 + ztdve, .seq e1 ztbpc, by_omega, hw3, by_omega,
    by omega, by rw [o32, ← hA1]; exact q0, by rw [o32, hA3]; exact q0',
    by zunqy; exact q1.trans i0, by zunqy; exact q2.trans i1,
    by zunqy; exact q3.trans i2,
    fun m' hm' => by rw [o32]; exact q4 m' by_grind,
    fun a ha => by_grind,
    fun a ha => by_grind,
    by grind, fun r h1 h2 h3 => ?_,
    fun r h1 => by_grind⟩
  have := hbb r h1
  rw [fr3 r h2, fr2r r (hsub r h1) h3, fr1 r by_omega by_omega by_omega]
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def mdB : Stmt := block [.copyN 170070 9999, .addN 9999 9999 170026, .storeN 170070 170029,
  .copyN 170072 170030, .addN 170073 170070 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074,
  .addN 170072 170072 170020, .addN 170073 170073 170020,
  .loadN 170074 170072, .storeN 170073 170074]

/-- **Coarsening.** -/
def granCall (sG : Stmt) : Stmt :=
  .seq mdB (.seq (block [.copyN 90000 170070, .copyN 90001 170031, .copyN 90002 170025,
    .copyN 90003 170011]) (.seq sG (block [.copyN 170031 90004])))

/-- The registers written by `mdB`. -/
def MdRG (r : ℕ) : Prop := 170070 ≤ r ∧ r ≤ 170074
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 16000000 in
theorem mdB_exec {c : Config} (hw : WordsBounded W c) {MD B : ℕ} (hA : c.nreg ALLOC = MD)
    (h30 : c.nreg 170030 = B) (h20 : c.nreg 170020 = 1) (h26 : c.nreg 170026 = 6)
    (h29 : c.nreg 170029 = 0) (hB : B + 5 ≤ MD) (hW : MD + 6 ≤ W) :
    ∃ c' k, Exec P W mdB c c' k ∧ k = 23 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = MD + 6 ∧ c'.nreg 170070 = MD ∧ c'.nmem MD = 0 ∧
      (∀ j, j < 5 → c'.nmem ztqae = c.nmem ztelw) ∧
      (∀ a, (a < MD ∨ MD + 6 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ MdRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold mdB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h30, h20, h26, h29]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, fun j hj => ?_, fun a ha => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; omega
  · tauto
  · config_simp; zunlk; grind
  · config_simp
    zunlk
    grind
  · config_simp; simp only [hA, h30, h20, Machine.upd_apply]; grind
  · unfold MdRG at h1
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
set_option maxHeartbeats 16000000 in
/-- **Coarsening, called from the up phase.** -/
theorem granCall_exec {sG : Stmt} {κG : ℕ → ℕ}
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P ztm c.nmem ztqa ∧
        ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
          NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztqb ∧
          M.Semigranular ztwiv ztbdj)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
        NFAt c.nmem ztbdi N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
          N'.F M zta ⊆ N.F M zta ∧
          IsCanonicalNF M zta N' ztbdj ztqb)
      (fun _ c => κG ztqb *
        ztin))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {MD B F γ γ0 hp : ℕ} {C : Chain} {N : NF}
    (hA : c.nreg ALLOC = MD) (h30 : c.nreg 170030 = B) (h31 : c.nreg 170031 = F)
    (h11 : c.nreg 170011 = γ) (h20 : c.nreg 170020 = 1) (h25 : c.nreg 170025 = 4)
    (h26 : c.nreg 170026 = 6) (h29 : c.nreg 170029 = 0)
    (hd : ChainDescAt c.nmem B zta ztqg C) (hBh : c.nmem B = hp)
    (hB5 : B + 5 ≤ MD) (hhp : hp + 7 ≤ MD) (hCP : C.P = Qof P) (hCn : C.s + C.m + 1 ≤ P.n)
    (hNW : NFWithin c.nmem F MD N) (hc : IsCanonicalNF ztc zta N γ0 4)
    (hγ : γ0 ≤ γ)
    (hbud : MD + 6 + κG 4 * ztbzq ≤ W) :
    ∃ c' k, Exec P W (granCall sG) c c' k ∧
      k ≤ κG 4 * ztbzq + 30 ∧
      WordsBounded W c' ∧ MD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ MD + k ∧
      (∃ N', NFWithin c'.nmem ztggx ztdo N' ∧
        IsCanonicalNF ztc zta N' γ 4) ∧
      ztiul ∧
      ztium ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ granBands → ¬ MdRG r → r ≠ 170031 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztimx := by
  zuk
  zuc
  zufvv
  obtain ⟨c1, k1, e1, hk1, hw1, m1A, m170, m1z, m1w, m1out, fr1, hrr1, hrm1, ho1⟩ :=
    mdB_exec (P := P) hw hA h30 h20 h26 h29 hB5 by_omega
  have g1 : ∀ r, 170000 ≤ r → r < 170070 → c1.nreg r = c.nreg r := fun r a b =>
    fr1 r (by unfold MdRG; omega) by_omega
  obtain ⟨c2, k2, e2, hk2, hw2, i0, i1, i2, i3, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      (block [.copyN 90000 170070, .copyN 90001 170031, .copyN 90002 170025,
        .copyN 90003 170011]) c1 c2 k2 ∧ k2 = 4 ∧ WordsBounded W c2 ∧
      c2.nreg 90000 = MD ∧ c2.nreg 90001 = F ∧ c2.nreg 90002 = 4 ∧ c2.nreg 90003 = γ ∧
      (∀ r, r ≠ 90000 → r ≠ 90001 → r ≠ 90002 → r ≠ 90003 → c2.nreg r = c1.nreg r) ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    refine ⟨rfl, ‹_›, by_tauto,
      by config_simp; grind,
      by config_simp; grind,
      by config_simp; grind,
      fun r a1 a2 a3 a4 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have hA2 : c2.nreg ALLOC = MD + 6 := by
    grind
  -- memory facts at `c2`
  have mem2 : ∀ a, a < MD → c2.nmem a = c.nmem a := fun a ha => by
    grind
  have hHA : ztbabx := by have := hd.1; grind
  have hHA2 : HostAt c2.nmem hp ztqg :=
    hostAt_agree hHA rfl by_omega mem2
  obtain ⟨-, d1, d2, d3, d4, d5⟩ := hd
  have w : ∀ j, j < 5 → c2.nmem ztqae = c.nmem ztelw := fun j hj => by
    grind
  have hdesc : ChainDescAt c2.nmem ztki zta ztqg C := by
    refine ⟨?_, d1, ?_, ?_, ?_, ?_⟩
    · have := w 0 by_norm_num; grind
    · grind
    · grind
    · grind
    grind
  have hz : c2.nmem MD = 0 := by_grind
  have hwf : ModelDescWF P ztjsq c2.nmem MD := by
    rw [hA2]
    refine ⟨le_rfl, fun _ => ztmqi⟩
    have e0 : c2.nmem ztki = hp := by
      have := w 0 by_norm_num; grind
    have hH : ztpkf := hostAt_unique hC'.1 by_grind
    zulsw
    refine ⟨by zvohn, hostWF_whole hn1, by zvokq; zvohn; omega, ?_⟩
    have hs' : ztidk := by rw [← hC'.2.2.1, ← hdesc.2.2.1]
    have hP' : ztpiu := by
      rw [hC'.2.1]; grind
    grind
  zucm
  have hNW2 : NFWithin c2.nmem F ztjsq N := by
    rw [hA2]; exact (hNW.transport mem2).mono by_omega
  have hFlt : F < MD := nfWithin_lt hNW
  have q1 : 1 ≤ rd c2 bGran 2 := by show 1 ≤ c2.nreg 90002; omega
  have q2 : ModelDescWF P ztjsq c2.nmem ztrvy := by
    show ModelDescWF P _ c2.nmem ztvkl; grind
  have q3 : ModelDescAt c2.nmem ztrvy zta ztc := by
    show ModelDescAt c2.nmem ztvkl zta ztc
    rw [i0]; exact Or.inl ⟨hz, _, C, hdesc, rfl⟩
  have q4 : NFWithin c2.nmem ztlsr ztjsq N := by
    show NFWithin c2.nmem ztqjj ztjsq N; grind
  have q5 : (chainModel C).DegLe ztwjq ztrvz := by
    show (chainModel C).DegLe _ ztmhg; rw [i2]; exact hc.2.1
  have q6 : (chainModel C).Semigranular ztwjq (rd c2 bGran 3) := by
    show (chainModel C).Semigranular _ ztvkm
    rw [i3]; exact Model.Granular.semigranular_of_le _ hc.2.2.1 hγ
  have q7 : c2.nreg ALLOC + κG ztrvz * (c2.nmem ztlsr *
      (Nat.clog 2 (c2.nmem ztlsr) + 1) + 1) ≤ W := by
    show c2.nreg ALLOC + κG ztmhg * (c2.nmem ztqjj *
      ztjkh + 1) ≤ W
    grind
  obtain ⟨c3, k3, e3, hk3, hpost, fr3⟩ := hGr P W c2 hw2
    ⟨hG, hWh, q1, q2, chainModel C, N, q3, Or.inl ⟨C, by_grind, rfl⟩, q4, hc.1, q5,
      q6⟩ q7
  replace hk3 : k3 ≤ κG ztmhg * (c2.nmem ztqjj *
      ztjkh + 1) := hk3
  have hF2 : c2.nmem F = c.nmem F := by_grind
  rw [i1, i2, hF2] at hk3
  obtain ⟨N', -, hNW', -, hc'⟩ := hpost _ N q3 q4.holds
  replace hc' : IsCanonicalNF ztc zta N' ztvkm ztmhg := hc'
  rw [i2, i3] at hc'
  obtain ⟨fr3r, fr3rr, fr3m, fr3rm, fr3o, fr3a, fr3b⟩ := fr3
  zubgh
  obtain ⟨c4, k4, e4, hk4, hw4, o31, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
      (block [.copyN 170031 90004]) c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
      c4.nreg 170031 = c3.nreg 90004 ∧ (∀ r, r ≠ 170031 → c4.nreg r = c3.nreg r) ∧
      c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
    exec_block
    refine ⟨rfl, ‹_›, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have hA4 : c4.nreg ALLOC = c3.nreg ALLOC := fr4 _ by_omega
  have hbb : ∀ r, bandOf r ∉ granBands → r < 90000 ∨ 100000 ≤ r := by
    zuz
    zukr
    exact hr (by rw [show bandOf r = bGran by unfold bandOf bGran; omega]; decide)
  have hA1 : c1.nreg ALLOC = MD + 6 := m1A
  refine ⟨c4, k1 + ztbqj, .seq e1 ztbal, by_omega, hw4,
    by omega,
    by omega,
    ⟨N', by rw [o31, hm4, hA4]; exact hNW', hc'⟩,
    fun a ha => by rw [hm4, fr3m a by_omega, mem2 a ha],
    fun a ha => by rw [hrm4, fr3rm a by_omega, hrm2, hrm1],
    by grind, fun r h1 h2 h3 h4 => ?_,
    fun r h1 => by rw [hrr4, fr3rr r h1, hrr2, hrr1]⟩
  have := hbb r h1
  rw [fr4 r h3, fr3r r h1 h4, fr2 r by_omega by_omega by_omega by_omega, fr1 r h2 h4]
end proofs
variable {n g i : ℕ}
theorem gradeStart_succ (g i : ℕ) : gradeStart ztbs i = gradeStart g ztvd := by
  unfold gradeStart; grind
theorem gradeCount_succ (n g : ℕ) : gradeCount n ztbs = zteud / 2 ^ g / 2 + 1 := by
  unfold gradeCount; zuolh

/-- A chain of a grade has at least one edge and fits in the curve. -/
theorem gradeLen_pos (hn : 2 ≤ n) (hi : i < gradeCount n g) : 1 ≤ gradeLen n g i := by
  unfold gradeLen gradeCount at *
  zubtm
  have : ztmvx := by
    zukr
    have : ztyzk := by
      zujhd
    omega
  omega
theorem gradeLen_le (n g i : ℕ) : gradeLen n g i ≤ 2 ^ g := min_le_left _ _
theorem gradeLen_fit (hn : 2 ≤ n) (hi : i < gradeCount n g) :
    gradeStart g i + gradeLen n g i + 1 ≤ n := by
  unfold gradeLen gradeStart gradeCount at *
  zubtm
  have : ztmvx := by
    zukr
    have : ztyzk := by
      zujhd
    omega
  omega

/-- **The union of two children.** -/
theorem gradeLen_succ_two (hn : 2 ≤ n) (h : 2 * i + 1 < gradeCount n g) :
    gradeLen n g ztvd = 2 ^ g ∧
      gradeLen n ztbs i = gradeLen n g ztvd + gradeLen n g ztmj ∧
      gradeStart g ztmj = gradeStart g ztvd + gradeLen n g ztvd := by
  unfold gradeLen gradeStart gradeCount at *
  zubtm
  have h1 : ztmj * 2 ^ g ≤ n - 2 := by
    zukr
    have : ztycx := by rw [Nat.div_lt_iff_lt_mul hpos]; omega
    omega
  grind

/-- **A single child.** -/
theorem gradeLen_succ_one (hn : 2 ≤ n) (_hi : i < gradeCount n ztbs)
    (h : gradeCount n g ≤ 2 * i + 1) : gradeLen n ztbs i = gradeLen n g ztvd := by
  unfold gradeLen gradeCount at *
  zubtm
  have e2 : i * 2 ^ ztbs = 2 * i * 2 ^ g := by_grind
  zucjj
  have h1 : n - 2 < ztmj * 2 ^ g := by
    have : ztycx := by_omega
    rwa [Nat.div_lt_iff_lt_mul hpos] at this
  grind

/-- The top grade has a single chain. -/
theorem gradeCount_top (hn : 2 ≤ n) : gradeCount n ztcea = 1 := by
  unfold gradeCount topGrade
  have := Nat.le_pow_clog (b := 2) by_norm_num ztkl
  rw [Nat.div_eq_of_lt by_omega]
theorem gradeLen_top (_hn : 2 ≤ n) : gradeLen n ztcea 0 = n - 1 := by
  unfold gradeLen topGrade
  have := Nat.le_pow_clog (b := 2) by_norm_num ztkl
  omega
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey
@[expose] public section
def lenS : Stmt := .seq ztnsi
  (.ifLtN 170033 170010 ztoyp ztoyo)

/-- The descriptor of a chain of grade `g ≥ 1`. -/
def descGS : Stmt := .seq ztjov
  (.ifLtN 170036 170012
    (.seq ztjow
      (.seq unionS ztoys))
    ztoyr)

/-- **The descriptor of chain `(g, i)`.** -/
def descU : Stmt := .ifLtN 170007 170020 (.seq desc0S ztoyt) descGS
section proofs
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 8000000 in
theorem lenS_exec {c : Config} (hw : WordsBounded W c) {n1 s pg : ℕ}
    (h28 : c.nreg 170028 = n1) (h16 : c.nreg 170016 = s) (h10 : c.nreg 170010 = pg) :
    ∃ c' k, Exec P W lenS c c' k ∧ k ≤ 4 ∧ WordsBounded W c' ∧
      c'.nreg 170017 = min pg (n1 - s) ∧
      (∀ r, r ≠ 170017 → r ≠ 170033 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c1, k1, e1, hk1, hw1, i33, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      ztnsi c c1 k1 ∧ k1 = 1 ∧ WordsBounded W c1 ∧
      c1.nreg 170033 = n1 - s ∧ (∀ r, r ≠ 170033 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    simp_all
  have c10 : c1.nreg 170010 = pg := by_simp_all
  by_cases h : c1.nreg 170033 < c1.nreg 170010
  · obtain ⟨c2, k2, e2, hk2, hw2, i17, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        ztoyp c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170017 = c1.nreg 170033 ∧ ztivc ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      simp_all
    refine ⟨c2, k1 + ztcvw, .seq e1 ztspi, by_omega, hw2, ?_,
      by simp_all, by_simp_all, by_simp_all,
      by simp_all, by_simp_all⟩
    omega
  · obtain ⟨c2, k2, e2, hk2, hw2, i17, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        ztoyo c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170017 = c1.nreg 170010 ∧ ztivc ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      simp_all
    refine ⟨c2, k1 + zttqi, .seq e1 (.ifLtN_false h e2), by_omega, hw2, ?_,
      by simp_all, by_simp_all, by_simp_all,
      by simp_all, by_simp_all⟩
    omega
set_option maxHeartbeats 16000000 in
/-- **The descriptor of a grade-0 chain** (the edge `v_i v_{i+1}`). -/
theorem descU_exec0 (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp i : ℕ} (h07 : c.nreg 170007 = 0) (h20 : c.nreg 170020 = 1) (hA : c.nreg ALLOC = TD)
    (h04 : c.nreg 170004 = hp) (h16 : c.nreg 170016 = i) (h01 : c.nreg 170001 = P.n)
    (h23 : c.nreg 170023 = 5) (hi : i + 2 ≤ P.n) (hH : HostAt c.nmem hp ztqg)
    (hhp : hp + 7 ≤ TD) (hW : TD + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 1902 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = TD + 5 ∧ c'.nreg 170030 = TD ∧ c'.nmem TD = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart 0 i → C.m = gradeLen P.n 0 i →
        ChainDescAt c'.nmem TD zta ztqg C) ∧
      ztzu ∧
      (∀ r, ¬ D0RG r → r ≠ 170030 → bandOf r ≠ bBrute → Bk r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztexd ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, h1A, h160, w0, hdesc, hm1, fr1, frr1, hrm1, ho1⟩ :=
    desc0S_exec hG hWn hw hA h04 h16 h01 h20 h23 hi hW hW8
  obtain ⟨c2, k2, e2, hk2, hw2, o30, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
      ztoyt c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
      c2.nreg 170030 = c1.nreg 170060 ∧ ztivd ∧
      c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
    exec_block
    simp_all
  have hH1 : HostAt c1.nmem hp _ :=
    hostAt_agree hH rfl by_omega fun a ha => hm1 a ztbbu
  refine ⟨c2, k1 + k2 + 1, .ifLtN_true by_omega (.seq e1 e2), by_omega, hw2,
    by grind, by_omega, by_grind,
    fun C hCP hCs hCm => by
      rw [hm2]; refine hdesc C hCP (by rw [hCs]; unfold gradeStart; simp) ?_ hH1
      rw [hCm]; unfold gradeLen; omega,
    fun a ha => by_grind, by_grind,
    by grind, by_grind, by_grind⟩
set_option maxHeartbeats 16000000 in
/-- **The descriptor of a chain of grade `g ≥ 1`** from its children. -/
theorem descU_execG (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {TD hp g i R cnt : ℕ} (h07 : c.nreg 170007 = g) (hg : 1 ≤ g) (h20 : c.nreg 170020 = 1)
    (hA : c.nreg ALLOC = TD) (h14 : c.nreg 170014 = R) (h35 : c.nreg 170035 = 6 * i)
    (h36 : c.nreg 170036 = 2 * i + 1) (h12 : c.nreg 170012 = cnt) (h22 : c.nreg 170022 = 3)
    (h23 : c.nreg 170023 = 5) (hcnt : cnt = gradeCount P.n ztfe)
    (hi : i < gradeCount P.n g) (hn : 2 ≤ P.n)
    (hL : ∀ C : Chain, C.P = Qof P → C.s = gradeStart ztfe ztvd →
      C.m = gradeLen P.n ztfe ztvd →
      ChainDescAt c.nmem ztzds zta ztqg C)
    (hLh : c.nmem ztzds = hp) (hL5 : c.nmem ztdlj + 5 ≤ TD)
    (hR : 2 * i + 1 < cnt → ∀ C : Chain, C.P = Qof P → C.s = gradeStart ztfe ztmj →
      C.m = gradeLen P.n ztfe ztmj →
      ChainDescAt c.nmem ztzdr zta ztqg C)
    (hRh : 2 * i + 1 < cnt → c.nmem ztzdr = hp)
    (hR5 : 2 * i + 1 < cnt → c.nmem ztdgd + 5 ≤ TD)
    (hhp : hp + 7 ≤ TD) (hW : TD + 5 ≤ W) (hWR : R + 6 * i + 3 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 320 ∧ WordsBounded W c' ∧
      TD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ TD + 5 ∧ c'.nreg 170030 + 5 ≤ c'.nreg ALLOC ∧
      c'.nmem ztmfc = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ChainDescAt c'.nmem ztmfc zta ztqg C) ∧
      (∀ a, a < TD → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ DescRG r → Bk r = false → r ≠ 160035 → r ≠ 160036 → r ≠ 160037 → r ≠ 160024 →
        r ≠ 170030 → r ≠ 170034 → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      ztcxk ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zuk
  zukch
  zuc
  have hnot : ¬ c.nreg 170007 < c.nreg 170020 := by_omega
  -- the left child
  obtain ⟨c1, k1, e1, hk1, hw1, l34, l35, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      ztjov c c1 k1 ∧ k1 = 2 ∧
      WordsBounded W c1 ∧ c1.nreg 170034 = R + 6 * i ∧ c1.nreg 160035 = c.nmem ztdlj ∧
      (∀ r, r ≠ 170034 → r ≠ 160035 → c1.nreg r = c.nreg r) ∧ c1.nmem = c.nmem ∧
      c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h14, h35]); omega)
    refine ⟨rfl, by_omega, by config_simp; omega, by config_simp; grind,
      fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  zumat
  set BL := c.nmem ztdlj with hBL
  have hs0 : gradeStart g i = gradeStart ztfe ztvd := by
    rw [← gradeStart_succ, hgg]
  by_cases hr : 2 * i + 1 < cnt
  · -- two children
    have htest : c1.nreg 170036 < c1.nreg 170012 := by
      grind
    obtain ⟨c2, k2, e2, hk2, hw2, l34', l36, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        ztjow c1 c2 k2 ∧ k2 = 2 ∧
        WordsBounded W c2 ∧ c2.nreg 170034 = R + 6 * i + 3 ∧
        c2.nreg 160036 = c.nmem ztdgd ∧
        (∀ r, r ≠ 170034 → r ≠ 160036 → c2.nreg r = c1.nreg r) ∧ c2.nmem = c1.nmem ∧
        c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      have c22 : c1.nreg 170022 = 3 := by_grind
      exec_block
      all_goals try (config_simp; (try simp only [l34, c22]); omega)
      refine ⟨rfl, by_omega, by config_simp; omega,
        by config_simp; grind, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
      zubi
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    set BR := c.nmem _ with hBR
    obtain ⟨hl2, hsum, hsR⟩ := gradeLen_succ_two (g := g - 1) (i := i) hn
      by_omega
    rw [hgg] at hsum
    obtain ⟨CL, hCLP, hCLs, hCLm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart ztfe ztvd ∧ C.m = gradeLen P.n ztfe ztvd := by
      have hfit := gradeLen_fit (g := g - 1) (i := 2 * i) hn by_omega
      exact ztfkf
    obtain ⟨CR, hCRP, hCRs, hCRm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart ztfe ztmj ∧ C.m = gradeLen P.n ztfe ztmj := by
      have hfit := gradeLen_fit (g := g - 1) (i := 2 * i + 1) hn by_omega
      exact ztfkf
    have hfitR := gradeLen_fit (g := g - 1) (i := 2 * i + 1) hn by_omega
    have g2 : ∀ r, r ≠ 170034 → r ≠ 160035 → r ≠ 160036 → c2.nreg r = c.nreg r :=
      by grind
    obtain ⟨c3, k3, e3, hk3, hw3, u3A, u37, u3h, udesc, hm3, fr3, frr3, hrm3, ho3⟩ :=
      unionS_exec hG hWn hw2
        by_grind
        by_grind l36
        by_grind
        by_grind
        by_grind
        by_grind by_grind hhp hCLP hCRP
        by_omega by_omega hL5 (hR5 hr) hW
    obtain ⟨c4, k4, e4, hk4, hw4, o30, fr4, hm4, hrr4, hrm4, ho4⟩ : ∃ c4 k4, Exec P W
        ztoys c3 c4 k4 ∧ k4 = 1 ∧ WordsBounded W c4 ∧
        c4.nreg 170030 = c3.nreg 160037 ∧ (∀ r, r ≠ 170030 → c4.nreg r = c3.nreg r) ∧
        c4.nmem = c3.nmem ∧ c4.rreg = c3.rreg ∧ c4.rmem = c3.rmem ∧ c4.output = c3.output := by
      exec_block
      refine ⟨rfl, by_omega, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      zubi
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    have hA4 : c4.nreg ALLOC = TD + 5 := by_grind
    refine ⟨c4, k1 + (k2 + (k3 + k4) + 1) + 2,
      .ifLtN_false hnot (.seq e1 (.ifLtN_true htest ztbal)), by_omega, hw4,
      by omega, by_omega, by_omega, by_grind,
      fun C hCP hCs hCm => by
        grind,
      fun a ha => by_grind,
      by grind,
      by grind, by_grind,
      by grind⟩
  · -- one child
    have htest : ¬ c1.nreg 170036 < c1.nreg 170012 := by
      grind
    obtain ⟨c2, k2, e2, hk2, hw2, o30, fr2, hm2, hrr2, hrm2, ho2⟩ : ∃ c2 k2, Exec P W
        ztoyr c1 c2 k2 ∧ k2 = 1 ∧ WordsBounded W c2 ∧
        c2.nreg 170030 = c1.nreg 160035 ∧ ztivd ∧
        c2.nmem = c1.nmem ∧ c2.rreg = c1.rreg ∧ c2.rmem = c1.rmem ∧ c2.output = c1.output := by
      exec_block
      refine ⟨rfl, by_omega, by config_simp, fun r a1 => ?_, rfl, rfl, rfl, rfl⟩
      zubi
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    have hlen1 := gradeLen_succ_one (g := g - 1) (i := i) hn by_grind
      by_omega
    rw [hgg] at hlen1
    have hA2 : c2.nreg ALLOC = TD := by
      grind
    refine ⟨c2, k1 + zttqi + 2, .ifLtN_false hnot (.seq e1 (.ifLtN_false htest e2)),
      by omega, hw2, by_omega, by_omega, by_omega,
      by grind,
      fun C hCP hCs hCm => by
        grind,
      by grind, by_grind,
      by grind, by_grind, by_grind⟩
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def granU (sG : Stmt) : Stmt := .seq (block [.addN 170034 170014 170035,
  .addN 170034 170034 170020, .loadN 170031 170034]) (granCall sG)

/-- **The normal form of chain `(g, i)`.** -/
def nfU (sB sL sG : Stmt) : Stmt :=
  .ifLtN 170007 170037 zthti (.ifLtN 170019 170017 zthyo (granU sG))

/-- The bands written by the three packages. -/
def pkgBands : Finset ℕ := bruteBands ∪ l41Bands
variable {r : ℕ}
theorem not_brute_of (h : bandOf r ∉ pkgBands) : bandOf r ∉ bruteBands := fun h' =>
  h ztsxn
theorem not_l41_of (h : bandOf r ∉ pkgBands) : bandOf r ∉ l41Bands := fun h' =>
  h (Finset.mem_union_right _ h')
theorem not_gran_of (h : bandOf r ∉ pkgBands) : bandOf r ∉ granBands := fun h' =>
  h (Finset.mem_union_left _ ztsxn)
section proofs
variable {P : Polygon} {W : ℕ}
variable {sB sL sG : Stmt}
set_option maxHeartbeats 16000000 in
/-- **Grades below `7`: brute force.** -/
theorem nfU_brute {κB : ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        ztuu)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust ztdo c'.nmem ztwq ∧
        IsCanonicalNF ztc zta N ztczy 4)
      ztyp)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {s len γ g : ℕ} (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (hg : g < 7)
    (h16 : c.nreg 170016 = s) (h17 : c.nreg 170017 = len)
    (h11 : c.nreg 170011 = γ) (hl : 1 ≤ len) (hsl : s + len + 1 ≤ P.n) (hγ : 1 ≤ γ)
    (hlγ : len = 1 ∨ 2 ≤ γ) (hbud : c.nreg ALLOC + κB * ztkaf ^ 3 ≤ W) :
    ∃ c' k, Exec P W ztftl c c' k ∧ k ≤ κB * ztkaf ^ 3 + 5 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem ztggx ztdo N ∧
        IsCanonicalNF ztc zta N γ 4) ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztdwv := by
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    bruteCall_exec hB hG hWh hw h16 h17 h11 hl hsl hγ hlγ hbud
  exact ⟨c', k + 1, .ifLtN_true by_omega e, by_omega, hw', a1, by_omega,
    hpost, m1, m2, o, fun r h1 _ h3 _ h5 => fr r ztwac h3 h5,
    fun r h1 => frr r ztwac⟩
set_option maxHeartbeats 16000000 in
/-- **Full chains of grade `≥ 7`: Lemma 4.1.** -/
theorem nfU_l41 {O : OracleIface} {sB sL sG : Stmt} {κL : ℕ}
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem ztbdk ztm ∧
        rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust ztdo c'.nmem ztwr ∧
        IsCanonicalNF ztc zta N ztbqg 4)
      ztxk)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {h s len g : ℕ} (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (h7 : 7 ≤ g)
    (h19 : c.nreg 170019 = 2 ^ ztfe) (h05 : c.nreg 170005 = h) (h16 : c.nreg 170016 = s)
    (h17 : c.nreg 170017 = len)
    (hX : (gradeCtx O).holds P c.nmem h ztm) (hgΛ : g ≤ c.nmem h)
    (hsl : s + len + 1 ≤ P.n) (hl1 : 2 ^ ztfe < len) (hl2 : len ≤ 2 ^ g)
    (hbud : c.nreg ALLOC + κL * ztcnv ≤ W) :
    ∃ c' k, Exec P W ztftl c c' k ∧ k ≤ κL * ztcnv + 8 ∧
      WordsBounded W c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      (∃ C N, C.P = Qof P ∧ C.s = s ∧ C.m = len ∧
        NFWithin c'.nmem ztggx ztdo N ∧
        IsCanonicalNF ztc zta N ztcvr 4) ∧
      zth ∧
      ztgo ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztdwv := by
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    l41Call_exec hL hG hWh hw h05 h16 h17 h07 hX hgΛ h7 hsl hl1 hl2 hbud
  exact ⟨c', k + 1 + 2, .ifLtN_false by_omega
      ztdrx, by_omega, hw', a1, by_omega,
    hpost, m1, m2, o, fun r h1 _ h3 _ h5 => fr r ztwaf h3 h5,
    fun r h1 => frr r ztwaf⟩
set_option maxHeartbeats 16000000 in
/-- **Short chains of grade `≥ 7`: coarsen the child's normal form.** The child's NF pointer is
the word `R + q + 1` of the row of grade `g - 1` (`R` in `170014`, `q = 6i` in `170035`). -/
theorem nfU_gran {κG : ℕ → ℕ}
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P ztm c.nmem ztqa ∧
        ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
          NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztqb ∧
          M.Semigranular ztwiv ztbdj)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
        NFAt c.nmem ztbdi N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
          N'.F M zta ⊆ N.F M zta ∧
          IsCanonicalNF M zta N' ztbdj ztqb)
      (fun _ c => κG ztqb *
        ztin))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) {c : Config} (hw : WordsBounded W c)
    {MD B F γ γ0 hp g len R q : ℕ} {C : Chain} {N : NF}
    (h07 : c.nreg 170007 = g) (h37 : c.nreg 170037 = 7) (h7 : 7 ≤ g)
    (h19 : c.nreg 170019 = 2 ^ ztfe) (h17 : c.nreg 170017 = len) (hl : len ≤ 2 ^ ztfe)
    (h14 : c.nreg 170014 = R) (h35 : c.nreg 170035 = q) (hRW : R + q + 1 < W)
    (hF : c.nmem (R + q + 1) = F)
    (hA : c.nreg ALLOC = MD) (h30 : c.nreg 170030 = B)
    (h11 : c.nreg 170011 = γ) (h20 : c.nreg 170020 = 1) (h25 : c.nreg 170025 = 4)
    (h26 : c.nreg 170026 = 6) (h29 : c.nreg 170029 = 0)
    (hd : ChainDescAt c.nmem B zta ztqg C) (hBh : c.nmem B = hp)
    (hB5 : B + 5 ≤ MD) (hhp : hp + 7 ≤ MD) (hCP : C.P = Qof P) (hCn : C.s + C.m + 1 ≤ P.n)
    (hNW : NFWithin c.nmem F MD N) (hc : IsCanonicalNF ztc zta N γ0 4)
    (hγ : γ0 ≤ γ)
    (hbud : MD + 6 + κG 4 * ztbzq ≤ W) :
    ∃ c' k, Exec P W ztftl c c' k ∧
      k ≤ κG 4 * ztbzq + 37 ∧
      WordsBounded W c' ∧ MD ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ MD + k ∧
      (∃ N', NFWithin c'.nmem ztggx ztdo N' ∧
        IsCanonicalNF ztc zta N' γ 4) ∧
      ztiul ∧
      ztium ∧ c'.output = c.output ∧
      (∀ r, bandOf r ∉ pkgBands → ¬ MdRG r → r ≠ 170031 → r ≠ 170034 → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      ztdwv := by
  zuk
  obtain ⟨c1, k1, e1, hk1, hw1, l34, l31, fr1, hm1, hrr1, hrm1, ho1⟩ : ∃ c1 k1, Exec P W
      (block [.addN 170034 170014 170035, .addN 170034 170034 170020, .loadN 170031 170034])
      c c1 k1 ∧ k1 = 3 ∧ WordsBounded W c1 ∧ c1.nreg 170034 = R + q + 1 ∧
      c1.nreg 170031 = F ∧ (∀ r, r ≠ 170034 → r ≠ 170031 → c1.nreg r = c.nreg r) ∧
      c1.nmem = c.nmem ∧ c1.rreg = c.rreg ∧ c1.rmem = c.rmem ∧ c1.output = c.output := by
    exec_block
    all_goals try (config_simp; (try simp only [h14, h35, h20]); omega)
    refine ⟨rfl, ‹_›, by config_simp; omega,
      by config_simp; grind, fun r a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
    zubi
    repeat (rw [Machine.upd_other _ _ _ by_omega])
  have g1 : ∀ r, r ≠ 170034 → r ≠ 170031 → c1.nreg r = c.nreg r := fr1
  obtain ⟨c', k, e, hk, hw', a1, a2, hpost, m1, m2, o, fr, frr⟩ :=
    granCall_exec (P := P) (C := C) (N := N) (γ0 := γ0) (hp := hp) hGr hG hWh hw1
      by_grind
      by_grind l31
      by_grind
      by_grind
      by_grind
      by_grind
      by_grind
      by_grind by_grind hB5 hhp hCP hCn
      by_grind hc hγ by_grind
  zvmxz at hk
  refine ⟨c', (k1 + k) + 2 + 2, .ifLtN_false by_omega
      (.ifLtN_false by_omega (.seq e1 e)), by_omega, hw', a1, by_omega,
    hpost, fun a ha => by_grind, fun a ha => by_grind, by_grind,
    fun r h1 h2 h3 h4 h5 => ?_, fun r h1 => by rw [frr r ztwae, hrr1]⟩
  rw [fr r ztwae h2 h3 h5, g1 r h4 h3]
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Chazelle Chazelle.Core.L41
@[expose] public section
noncomputable def gChain (P : Polygon) (g i : ℕ) (hn : 2 ≤ P.n) (hi : i < gradeCount P.n g) : Chain :=
  ⟨Qof P, gradeStart g i, gradeLen P.n g i, gradeLen_pos hn hi, by
    have := gradeLen_fit hn hi; have hQn : ztx := shear_n _ _; omega⟩

/-- **An entry of chain `(g, i)`**: descriptor `d`, normal form `f`, oracle `o`. -/
def UpEntry (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (A hp g i d f o : ℕ) : Prop :=
  (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
    NodeOK P m A hp d f C ztcvr) ∧
  O.At P m o ∧ m o = d ∧ m ztbql = f ∧ m ztdvm = gradeGran g

/-- The address of entry `(g, i)` of the grade record at `h`. -/
abbrev rowE (m : ℕ → ℕ) (h g i : ℕ) : ℕ := m ztwjz + 3 * i

/-- **The grade record at `h`** with all descriptors on the whole host at `hp`. -/
def UpTab (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h hp A : ℕ) : Prop :=
  m h ≤ topGrade P.n + 1 ∧ SetupAt m ztzgl P.n ztyfh ∧
    ztxez ∧ HostAt m hp ztqg ∧
    hp + 7 ≤ A ∧
    (h + 4 ≤ A ∧ m ztgn + 2 * topGrade P.n + 6 ≤ A ∧ m ztbba + P.n + 1 ≤ A) ∧
    m zteu + m h ≤ A ∧
    (∀ g, g < m h → m ztwjz + 3 * gradeCount P.n g ≤ A) ∧
    ∀ g i, g < m h → i < gradeCount P.n g →
      UpEntry O P m A hp g i (m (rowE m h g i)) (m (rowE m h g i + 1)) (m (rowE m h g i + 2))

/-- **The cells of the current grade**: `Cells … x i` for the cell `x` of chain `i - 1` (and the
cells of the chains before it by the back links). -/
def Cells (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (A hp g : ℕ) : ℕ → ℕ → Prop
  | _, 0 => True
  | x, i + 1 => x + 4 ≤ A ∧ UpEntry O P m A hp g i (m x) ztyjn (m ztewm) ∧
      Cells O P m A hp g (m ztudm) i
section proofs
variable {O : OracleIface} {P : Polygon}
variable {m : ℕ → ℕ} {h hp A : ℕ}
theorem UpEntry.mono {A A' hp g i d f o : ℕ} (h : UpEntry O P m A hp g i d f o)
    (hA : A ≤ A') : UpEntry O P m A' hp g i d f o :=
  ⟨fun C h1 h2 h3 => (h.1 C h1 h2 h3).mono hA, h.2⟩
theorem UpTab.mono {h hp A A' : ℕ} (hT : UpTab O P m h hp A) (hA : A ≤ A') :
    UpTab O P m h hp A' := by
  obtain ⟨h1, h2, h3, h4, h5, ⟨h7, h7b, h7c⟩, h8, h9, h6⟩ := hT
  exact ⟨h1, h2, h3, h4, by_omega, ⟨by_omega, by_omega, by_omega⟩, by_omega,
    fun g hg => by_grind,
    fun g i hg hi => (h6 g i hg hi).mono hA⟩
theorem Cells.mono {A A' hp g : ℕ} (hA : A ≤ A') :
    ∀ {x i : ℕ}, Cells O P m A hp g x i → Cells O P m A' hp g x i
  | _, 0, _ => trivial
  | _, _ + 1, ⟨h1, h2, h3⟩ => ⟨by_omega, h2.mono hA, Cells.mono hA h3⟩

/-- A robust fact implies its consequences, for a larger bound. -/
theorem robust_of {A A' : ℕ} {m : ℕ → ℕ} {Φ Ψ : ztjx → Prop} (h : Robust A m Φ)
    (hA : A ≤ A') (hΦ : ∀ m', Φ m' → Ψ m') : Robust A' m Ψ :=
  fun m' hm' => hΦ m' (h m' fun a ha => hm' a by_omega)

/-- The chain of a table entry: its descriptor is on the whole host. -/
theorem chainWF_of_node {A hp d f γ : ℕ} {C : Chain} (hn : 1 ≤ P.n)
    (hN : NodeOK P m A hp d f C γ) (hH : HostAt m hp ztqg) :
    ChainWF P A m d := by
  obtain ⟨hd, -, hdh, hd5, hhp, hfit, -⟩ := hN
  zuc
  refine ⟨hd5, fun H C' hC => ?_⟩
  have hH' : ztpkf := hostAt_unique hC.1 by_simp_all
  subst hH'
  refine ⟨by zvohn, hostWF_whole hn, by zuoyp; tauto, ?_⟩
  have hs : ztidk := hC.2.2.1.symm.trans hd.2.2.1
  have hP : ztpiu := by
    zuozl; have := L41.poly_whole zta by_omega; simp_all
  grind

/-- **`UpTab` gives the raw grade table.** -/
theorem upTab_gradeRaw (hn : 2 ≤ P.n) (hT : UpTab O P m h hp A) :
    GradeRaw O P m h A := by
  obtain ⟨h1, h2, h3, hH, -, -, -, -, hE⟩ := hT
  refine ztioi
  obtain ⟨hN, hAt, e0, e1, e2⟩ := hE g i hg hi
  have hNo := hN (gChain P g i hn hi) rfl rfl rfl
  have hwf := chainWF_of_node by_omega hNo hH
  obtain ⟨hd, -, -, -, -, -, N, hNW, hc⟩ := hNo
  exact ⟨Host.whole P.n, gChain P g i hn hi, N, hd, hwf, rfl, by zvohn,
    hostWF_whole by_omega, rfl, rfl, hNW, hc, hAt, e0, e1, e2⟩

/-- **The grade context holds** at a robust `UpTab`. -/
theorem holds_of_upTab (hn : 2 ≤ P.n)
    (hR : Robust A m fun m' => UpTab O P m' h hp A) : (gradeCtx O).holds P m h A :=
  fun m' hm' => upTab_gradeRaw hn (hR m' hm')
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def OutB (b : ℕ) : Prop := b = 0 ∨ 25 ≤ b

/-- The registers kept by the parts of a chain step (the chain counters `170015 … 170018`,
`170035`, `170036` included). -/
def Kept (r : ℕ) : Prop :=
  ztgvn ∨
    (bandOf r = bUp ∧ (r < 170030 ∨ ztgxx ∨ 170080 ≤ r))

/-- **The registers fixed during grade `g`.** -/
structure URegs (c : Config) (n hp h g cnt γ cntP R : ℕ) : Prop where
  r01 : c.nreg 170001 = n
  r04 : c.nreg 170004 = hp
  r05 : c.nreg 170005 = h
  r07 : c.nreg 170007 = g
  r08 : c.nreg 170008 = cnt
  r10 : c.nreg 170010 = 2 ^ g
  r11 : c.nreg 170011 = γ
  r12 : c.nreg 170012 = cntP
  r14 : c.nreg 170014 = R
  r19 : c.nreg 170019 = 2 ^ ztfe
  r20 : c.nreg 170020 = 1
  r21 : c.nreg 170021 = 2
  r22 : c.nreg 170022 = 3
  r23 : c.nreg 170023 = 5
  r25 : c.nreg 170025 = 4
  r26 : c.nreg 170026 = 6
  r28 : c.nreg 170028 = n - 1
  r29 : c.nreg 170029 = 0
  r37 : c.nreg 170037 = 7

/-- The cell of a chain and the counters of the next chain. -/
def cellB : Stmt := block [.copyN 170034 9999, .storeN 170034 170030,
  .addN 170034 170034 170020, .storeN 170034 170031,
  .addN 170034 170034 170020, .storeN 170034 170032,
  .addN 170034 170034 170020, .storeN 170034 170018,
  .copyN 170018 9999, .addN 9999 9999 170025,
  .addN 170015 170015 170020, .addN 170016 170016 170010,
  .addN 170035 170035 170026, .addN 170036 170036 170021]
section proofs
variable {P : Polygon} {W : ℕ}
variable {r : ℕ} {B : Finset ℕ} {c c' : Config} {n hp h g cnt γ cntP R : ℕ}
theorem kept_of (h : bandOf r = bUp)
    (h' : r < 170030 ∨ ztgxx ∨ 170080 ≤ r) : Kept r :=
  Or.inr ztfwk
theorem Kept.ne_alloc (h : Kept r) : r ≠ ALLOC := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩
  · zubh
  · intro e; zvmwe at h; tauto

/-- A kept register is outside a set of phase bands without `bCore` and `bUp`. -/
theorem Kept.not_mem (h : Kept r) (hsub : ∀ b ∈ B, 1 ≤ b ∧ b ≤ 24)
    (h23 : bCore ∉ B) (h17 : bUp ∉ B) : bandOf r ∉ B := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨h, -⟩
  · intro hm; have := hsub _ hm; unfold OutB at h1; omega
  · zvmwp; tauto
  simp_all

/-- A register of an outside band is outside a set of phase bands. -/
theorem OutB.not_mem (h : OutB ztmcq)
    (hsub : ∀ b ∈ B, 1 ≤ b ∧ b ≤ 24) : bandOf r ∉ B := by
  intro hm; have := hsub _ hm; unfold OutB at h; omega

/-- A kept register is in one of the listed ranges. -/
theorem Kept.range (h : Kept r) :
    r < 10000 ∨ r = 230000 ∨ 250000 ≤ r ∨ ztekm ∨
      ztgxx ∨ ztgxz := by
  rcases h with ⟨h1 | h1, -⟩ | ⟨h, h'⟩
  · zufdf
  · omega
  · unfold bandOf bUp at h; omega

/-- The registers of `URegs`. -/
def URegR (r : ℕ) : Prop := (170000 ≤ r ∧ r < 170015) ∨ (170019 ≤ r ∧ r < 170030) ∨ r = 170037
theorem URegR.kept (h : URegR r) : Kept r :=
  kept_of (by unfold URegR at h; unfold bandOf bUp; omega) (by unfold URegR at h; omega)
theorem URegs.of_frame
    (hu : URegs c n hp h g cnt γ cntP R) (hk : ∀ r, URegR r → c'.nreg r = c.nreg r) :
    URegs c' n hp h g cnt γ cntP R := by
  have k : ∀ r, 170000 ≤ r → r < 170015 → c'.nreg r = c.nreg r := fun r a b =>
    hk r ztbaer
  have k' : ∀ r, 170019 ≤ r → r < 170030 → c'.nreg r = c.nreg r := fun r a b =>
    hk r (Or.inr ztbaer)
  exact ⟨(k _ by_omega by_omega).trans hu.r01, (k _ by_omega by_omega).trans hu.r04,
    (k _ by_omega by_omega).trans hu.r05, (k _ by_omega by_omega).trans hu.r07,
    (k _ by_omega by_omega).trans hu.r08, (k _ by_omega by_omega).trans hu.r10,
    (k _ by_omega by_omega).trans hu.r11, (k _ by_omega by_omega).trans hu.r12,
    (k _ by_omega by_omega).trans hu.r14, (k' _ by_omega by_omega).trans hu.r19,
    (k' _ by_omega by_omega).trans hu.r20, (k' _ by_omega by_omega).trans hu.r21,
    (k' _ by_omega by_omega).trans hu.r22, (k' _ by_omega by_omega).trans hu.r23,
    (k' _ by_omega by_omega).trans hu.r25, (k' _ by_omega by_omega).trans hu.r26,
    (k' _ by_omega by_omega).trans hu.r28, (k' _ by_omega by_omega).trans hu.r29,
    (hk _ ztwrm).trans hu.r37⟩
theorem URegs.of_kept
    (hu : URegs c n hp h g cnt γ cntP R) (hk : ∀ r, Kept r → c'.nreg r = c.nreg r) :
    URegs c' n hp h g cnt γ cntP R :=
  hu.of_frame fun r hr => hk r hr.kept

/-- A chain is determined by its polygon, start and length. -/
theorem chain_eq {C C' : Chain} (h1 : C.P = C'.P) (h2 : C.s = C'.s) (h3 : C.m = C'.m) :
    C = C' := by
  cases C; simp_all
set_option maxHeartbeats 16000000 in
/-- **The cell of a chain.** -/
theorem cellB_exec {c : Config} (hw : WordsBounded W c) {A d f o x i s pg q t : ℕ}
    (hA : c.nreg ALLOC = A) (h30 : c.nreg 170030 = d) (h31 : c.nreg 170031 = f)
    (h32 : c.nreg 170032 = o) (h18 : c.nreg 170018 = x) (h15 : c.nreg 170015 = i)
    (h16 : c.nreg 170016 = s) (h10 : c.nreg 170010 = pg) (h35 : c.nreg 170035 = q)
    (h36 : c.nreg 170036 = t) (h20 : c.nreg 170020 = 1) (h21 : c.nreg 170021 = 2)
    (h25 : c.nreg 170025 = 4) (h26 : c.nreg 170026 = 6)
    (hWA : A + 4 ≤ W) (hWi : i + 1 ≤ W) (hWs : s + pg ≤ W) (hWq : q + 6 ≤ W) (hWt : t + 2 ≤ W) :
    ∃ c' k, Exec P W cellB c c' k ∧ k = 14 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = A + 4 ∧ c'.nreg 170018 = A ∧ c'.nreg 170015 = i + 1 ∧
      c'.nreg 170016 = s + pg ∧ c'.nreg 170035 = q + 6 ∧ c'.nreg 170036 = t + 2 ∧
      c'.nmem A = d ∧ c'.nmem ztbo = f ∧ c'.nmem ztbcl = o ∧ c'.nmem zttf = x ∧
      ztzt ∧
      (∀ r, r ≠ 170034 → r ≠ 170018 → r ≠ 170015 → r ≠ 170016 → r ≠ 170035 → r ≠ 170036 →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zuk
  zudh
  unfold cellB
  exec_block
  all_goals try (config_simp; (try simp only [hA, h30, h31, h32, h18, h15, h16, h10, h35, h36,
    h20, h21, h25, h26]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 => ?_,
    fun r a1 a2 a3 a4 a5 a6 a7 => ?_, rfl, rfl, rfl⟩
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    grind
  · simp_all
  · simp_all
  · simp_all
  · config_simp; simp only [hA, h20, h30, h31, h32, h18, Machine.upd_apply]
    grind
  simp_all
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41 SweepPrim SignK WalkKey
@[expose] public section
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}

/-- The children of chain `i` of grade `g ≥ 1` exist. -/
theorem two_mul_lt_gradeCount {n g i : ℕ} (hg : 1 ≤ g) (hi : i < gradeCount n g) :
    2 * i < gradeCount n ztfe := by
  have e := gradeCount_succ n ztfe
  rw [show g - 1 + 1 = g by omega] at e
  obtain ⟨Q, hQ⟩ : ∃ Q, (n - 2) / 2 ^ (g - 1) = Q := zths
  zvnao at e
  unfold gradeCount; omega
variable {r : ℕ}
theorem Kept.not_d0 (h : Kept r) : ¬ D0RG r := by
  have := h.range; unfold D0RG; omega
theorem Kept.not_desc (h : Kept r) : ¬ DescRG r := by
  have := h.range; unfold DescRG; omega
theorem Kept.bk (h : Kept r) : Bk r = false := by
  have := h.range; unfold Bk; grind
theorem Kept.not_brute (h : Kept r) : bandOf r ≠ bBrute := by
  have := h.range; unfold bandOf bBrute; omega
theorem outB_bk (h : OutB ztmcq) : Bk r = false := by
  unfold OutB bandOf at h; unfold Bk; grind
set_option maxHeartbeats 16000000 in
/-- **The descriptor of chain `(g, i)`** from the grade record. -/
theorem descU_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R A γ : ℕ}
    (hu : URegs c P.n hp h g ztduv γ ztwwd R)
    (hA : c.nreg ALLOC = A) (h16 : c.nreg 170016 = gradeStart g i)
    (h35 : c.nreg 170035 = 6 * i) (h36 : c.nreg 170036 = 2 * i + 1)
    (hi : i < gradeCount P.n g) (hT : UpTab O P c.nmem h hp A) (hmh : c.nmem h = g)
    (hR : 1 ≤ g → c.nmem (c.nmem zteu + ztfe) = R) (hW : A + 5 ≤ W) (hW8 : 8 ≤ W) :
    ∃ c' k, Exec P W descU c c' k ∧ k ≤ 1902 ∧ WordsBounded W c' ∧
      A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + 5 ∧ c'.nreg 170030 + 5 ≤ c'.nreg ALLOC ∧
      c'.nmem ztmfc = hp ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ChainDescAt c'.nmem ztmfc zta ztqg C) ∧
      zttp ∧
      (∀ r, Kept r → c'.nreg r = c.nreg r) ∧
      zttc ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  zuk
  obtain ⟨-, -, -, hH, hhp, -, -, hrow, hE⟩ := hT
  rcases Nat.eq_zero_or_pos g with hg0 | hg1
  · subst hg0
    have hfit := gradeLen_fit (g := 0) hn hi
    have hl1 : gradeLen P.n 0 i = 1 := by
      have := gradeLen_pos (g := 0) hn hi; have := gradeLen_le P.n 0 i; omega
    unfold gradeStart at h16 hfit; simp only [pow_zero, Nat.mul_one] at h16 hfit
    obtain ⟨c', k, e, hk, hw', hA', o30, w0, hdesc, hm, fr, frr, hrm, ho⟩ :=
      descU_exec0 (P := P) hG hWn hw hu.r07 hu.r20 hA hu.r04 h16 hu.r01 hu.r23 by_omega
        hH by_omega hW hW8
    refine ⟨c', k, e, hk, hw', by_omega, by_omega, by_omega, by_grind,
      fun C h1 h2 h3 => by_grind,
      fun a ha => hm a ztbbu, fun r hr => fr r hr.not_d0 (by
        rintro rfl; have := hr.range; omega) hr.not_brute hr.bk hr.ne_alloc,
      fun r hr => frr r ztwbg (by unfold OutB at hr; unfold bUp; omega)
        (by unfold OutB at hr; unfold bBrute; omega), hrm, ho⟩
  · zuliw
    zujyr
    zukci
    have hrw := hrow ztfe hgm
    zuktb
    obtain ⟨hNL, -⟩ := hE ztfe ztvd hgm h2i
    have e6 : ztxrs := fun x => by_ring
    zughz
    have hL : ∀ C : Chain, C.P = Qof P → C.s = gradeStart ztfe ztvd →
        C.m = gradeLen P.n ztfe ztvd →
        ChainDescAt c.nmem ztzds zta ztqg C :=
      fun C a b d => (hNL C a b d).1
    obtain ⟨CL, hCLP, hCLs, hCLm⟩ : ∃ C : Chain, C.P = Qof P ∧
        C.s = gradeStart ztfe ztvd ∧ C.m = gradeLen P.n ztfe ztvd :=
      ⟨gChain P ztfe ztvd hn h2i, rfl, rfl, rfl⟩
    obtain ⟨-, -, hLh, hL5, -⟩ := hNL CL hCLP hCLs hCLm
    have hRc : 2 * i + 1 < gradeCount P.n ztfe → ∀ C : Chain, C.P = Qof P →
        C.s = gradeStart ztfe ztmj → C.m = gradeLen P.n ztfe ztmj →
        NodeOK P c.nmem A hp ztzdr (c.nmem (R + 6 * i + 3 + 1)) C
          (gradeGran ztfe) := fun h2 C a b d => by
      obtain ⟨hNR, -⟩ := hE ztfe ztmj hgm h2
      grind
    obtain ⟨c', k, e, hk, hw', hA1, hA2, o30, w0, hdesc, hm, fr, frr, hrm, ho⟩ :=
      descU_execG (P := P) (TD := A) (hp := hp) hG hWn hw hu.r07 hg1 hu.r20 hA hu.r14 h35 h36
        hu.r12 hu.r22 hu.r23 rfl hi hn hL hLh hL5
        (fun h2 C a b d => (hRc h2 C a b d).1)
        (fun h2 => by
          obtain ⟨CR, e1, e2, e3⟩ : ∃ C : Chain, C.P = Qof P ∧
              C.s = gradeStart ztfe ztmj ∧ C.m = gradeLen P.n ztfe ztmj :=
            ⟨gChain P ztfe ztmj hn h2, rfl, rfl, rfl⟩
          exact (hRc h2 CR e1 e2 e3).2.2.1)
        (fun h2 => by
          obtain ⟨CR, e1, e2, e3⟩ : ∃ C : Chain, C.P = Qof P ∧
              C.s = gradeStart ztfe ztmj ∧ C.m = gradeLen P.n ztfe ztmj :=
            ⟨gChain P ztfe ztmj hn h2, rfl, rfl, rfl⟩
          exact (hRc h2 CR e1 e2 e3).2.2.2.1)
        by_omega hW by_omega
    refine ⟨c', k, e, by_omega, hw', hA1, hA2, o30, w0, hdesc, hm,
      fun r hr => fr r hr.not_desc hr.bk ?_ ?_ ?_ ?_ ?_ ?_ hr.ne_alloc,
      fun r hr => frr r ztwbg (by rintro rfl; unfold OutB bandOf at hr; omega), hrm,
      ho⟩ <;>
      (rintro rfl; have := hr.range; omega)
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def l23c : ℕ → ℕ := fun D => 140 * ztmo

/-- A bound on the chord count of the child coarsened at grade `g`. -/
noncomputable def FB (g : ℕ) : ℕ := l23c 4 * ztgcj / (gradeGran ztfe + 1)

/-- **The cost bound of the normal form of a chain of grade `g`.** -/
noncomputable def nfB (κB κL : ℕ) (κG : ℕ → ℕ) (g : ℕ) : ℕ :=
  if g < 7 then κB * ztelc ^ 3 + 5 else
    κL * ztcnv + 8 + ztyxs
section proofs

/-- **Lemma 2.3 with the explicit constant `l23c`** (the proof of `lemma23`). -/
theorem l23c_spec (M : Model) (Q : Polygon) (F : Set ztf) (γ D : ℕ) (hM : GoodModel M)
    (hF : M.ChordFamily Q F) (hdeg : M.DegLe F D) (hgran : M.Granular F γ) :
    F.ncard * ztgj ≤ l23c D * ztcep := by
  zugc

  zubrr
  zucyo
  · zuqx
    · simp
    · zugkd
  · zucgc
    calc F.ncard * ztgj ≤ 2 * ztjis := by_nlinarith
      _ ≤ 2 * ztxun := Nat.mul_le_mul_left _ h
      _ ≤ 2 * ztwvy := by gcongr
      _ = l23c D * ztcep := by unfold l23c; ring
variable {O : OracleIface} {P : Polygon} {W : ℕ}

/-- **Lemma 2.3 for a canonical normal form of a chain.** -/
theorem nChords_mul_le {C : Chain} (hP : C.P.Simple) {Q : Polygon} {N : NF} {γ : ℕ}
    (hN : IsCanonicalNF ztc Q N γ 4) : N.nChords * ztgj ≤ l23c 4 * ztgca := by
  zufjw
  have h := l23c_spec _ Q _ γ 4 ztzz hnf.1 hdeg hgr
  zujgo
  have hs := MergeAsm.size_le_n ztc
  rw [MergeAsm.chainModel_n] at hs
  calc N.nChords * ztgj ≤ l23c 4 * zteiv := h
    _ ≤ l23c 4 * ztgca := Nat.mul_le_mul_left _ by_omega
theorem one_le_gradeGran (g : ℕ) : 1 ≤ gradeGran g := by
  unfold gradeGran; grind
theorem two_le_gradeGran {g : ℕ} (hg : 1 ≤ g) : 2 ≤ gradeGran g := by
  unfold gradeGran
  have h1 := Cost.one_le_ceilBeta hg
  grind
theorem clogCost_mono (κ : ℕ) {x y : ℕ} (h : x ≤ y) :
    κ * ztxyj ≤ κ * (y * (Nat.clog 2 y + 1) + 1) := by
  apply Nat.mul_le_mul_left
  have := Nat.clog_mono_right 2 h
  have := Nat.mul_le_mul h (Nat.add_le_add_right this 1)
  omega

/-- A short last chain of grade `g ≥ 1` is the single child `2i`. -/
theorem single_child {n g i : ℕ} (hn : 2 ≤ n) (hg : 1 ≤ g) (hi : i < gradeCount n g)
    (hl : gradeLen n g i ≤ 2 ^ ztfe) :
    gradeCount n ztfe ≤ 2 * i + 1 ∧ gradeLen n ztfe ztvd = gradeLen n g i := by
  zukch
  by_cases h : 2 * i + 1 < gradeCount n ztfe
  · exfalso
    obtain ⟨h1, h2, -⟩ := gradeLen_succ_two hn h
    rw [hgg] at h2
    have := gradeLen_pos hn h
    omega
  · zubsc
    have := gradeLen_succ_one (g := g - 1) (i := i) hn by_simp_all by_omega
    simp_all
set_option maxHeartbeats 32000000 in
/-- **The normal form of chain `(g, i)`**, all three cases. -/
theorem nfU_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        ztuu)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust ztdo c'.nmem ztwq ∧
        IsCanonicalNF ztc zta N ztczy 4)
      ztyp)
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem ztbdk ztm ∧
        rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust ztdo c'.nmem ztwr ∧
        IsCanonicalNF ztc zta N ztbqg 4)
      ztxk)
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P ztm c.nmem ztqa ∧
        ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
          NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztqb ∧
          M.Semigranular ztwiv ztbdj)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
        NFAt c.nmem ztbdi N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
          N'.F M zta ⊆ N.F M zta ∧
          IsCanonicalNF M zta N' ztbdj ztqb)
      (fun _ c => κG ztqb *
        ztin))
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R A d : ℕ}
    (hu : URegs c P.n hp h g ztduv ztcvr ztwwd R)
    (hA : c.nreg ALLOC = A) (h16 : c.nreg 170016 = gradeStart g i)
    (h17 : c.nreg 170017 = gradeLen P.n g i) (h35 : c.nreg 170035 = 6 * i)
    (hi : i < gradeCount P.n g)
    (hT : Robust A c.nmem fun m => UpTab O P m h hp A ∧ m h = g ∧
      ztwvx)
    (h30 : c.nreg 170030 = d) (hd5 : d + 5 ≤ A) (hdh : c.nmem d = hp)
    (hdesc : ∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
      ChainDescAt c.nmem d zta ztqg C)
    (hW : A + nfB κB κL κG g + 6 ≤ W) :
    ∃ c' k, Exec P W ztftl c c' k ∧ k ≤ nfB κB κL κG g ∧ WordsBounded W c' ∧
      A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      (∀ C : Chain, C.P = Qof P → C.s = gradeStart g i → C.m = gradeLen P.n g i →
        ∃ N, NFWithin c'.nmem ztggx ztdo N ∧
          IsCanonicalNF ztc zta N ztcvr 4) ∧
      zttp ∧
      ztbuk ∧ c'.output = c.output ∧
      (∀ r, Kept r ∨ r = 170030 → c'.nreg r = c.nreg r) ∧
      zttc := by
  zuk
  zuc
  zucwg

  have hk0 : ∀ r, Kept r ∨ r = 170030 → bandOf r ∉ pkgBands := fun r hr => by
    zucow
    · exact hr.not_mem by_decide by_decide by_decide
    · decide
  have hkm : ∀ r, Kept r ∨ r = 170030 → ¬ MdRG r := fun r hr => by
    zucow
    · have := hr.range; unfold MdRG; omega
    · unfold MdRG; omega
  have hk31 : ∀ r, Kept r ∨ r = 170030 → r ≠ 170031 := fun r hr => by
    zucow
    · have := hr.range; omega
    · omega
  have hk34 : ∀ r, Kept r ∨ r = 170030 → r ≠ 170034 := fun r hr => by
    zucow
    · have := hr.range; omega
    · omega
  have hkA : ∀ r, Kept r ∨ r = 170030 → r ≠ ALLOC := fun r hr => by
    zucow
    · exact hr.ne_alloc
    · decide
  have hb0 : ∀ r, OutB _ → bandOf r ∉ pkgBands := fun r hr => hr.not_mem by_decide
  -- the chain of the case analysis
  zuhhc
  rcases Nat.lt_or_ge g 7 with hg7 | hg7
  · -- brute force
    have hb : nfB κB κL κG g = κB * ztelc ^ 3 + 5 := by unfold nfB; grind
    zujip
    have hpow : κB * (gradeLen P.n g i + 1) ^ 3 ≤ κB * ztelc ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left by_omega 3)
    obtain ⟨c', k, e, hk, hw', a1, a2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, m1, m2, o, fr, frr⟩ :=
      nfU_brute hB hG hWh hw hu.r07 hu.r37 hg7 h16 h17 hu.r11
        hl1 by_omega (one_le_gradeGran g)
        (by
          zueva
          · grind
          · exact Or.inr (two_le_gradeGran h0))
        by_omega
    refine ⟨c', k, e, by_omega, hw', by_omega, by_omega, fun C' a b f => ?_,
      by grind, by_grind, o,
      by grind,
      by grind⟩
    zuiuf

  · have hb : nfB κB κL κG g = κL * ztcnv + 8 +
        ztyxs := by
      unfold nfB; grind
    zujip
    have hTh := hT.holds
    obtain ⟨hTab, hmh, hR⟩ := hTh
    by_cases hlen : 2 ^ ztfe < gradeLen P.n g i
    · -- Lemma 4.1
      have hX :=
        holds_of_upTab hn (robust_of hT le_rfl fun m' h' => h'.1)
      obtain ⟨c', k, e, hk, hw', a1, a2, ⟨C, N, hCP, hCs, hCm, hNW, hc⟩, m1, m2, o, fr, frr⟩ :=
        nfU_l41 hL hG hWh hw hu.r07 hu.r37 hg7 hu.r19 hu.r05 h16
          h17 by_grind by_omega by_omega hlen hl2
          by_omega
      refine ⟨c', k, e, by_omega, hw', by_omega, by_omega, fun C' a b f => ?_,
      by grind, by_grind, o,
        by grind,
        by grind⟩
      zuiuf

    · -- coarsening the child
      have hg1 : 1 ≤ g := by_omega
      obtain ⟨hsc, hlc⟩ := single_child hn hg1 hi by_omega
      zujyr
      zuliw
      obtain ⟨-, -, -, hH, hhp, -, -, hrow, hE⟩ := hTab
      zukci
      have hrw := hrow _ hgm
      zuktb
      obtain ⟨hNL, -⟩ := hE _ _ hgm h2i
      have e6 : ztxrs := by_omega
      zughz
      have hsc' : gradeStart ztfe ztvd = gradeStart g i := by
        rw [← gradeStart_succ, show g - 1 + 1 = g by omega]
      obtain ⟨-, -, -, -, -, -, N, hNW, hc⟩ := hNL C0 rfl hsc'.symm hlc.symm
      zufga
      have hcnt := nChords_mul_le hP hc
      have hFB : c.nmem (c.nmem (R + 6 * i + 1)) ≤ FB g := by
        zuiwq
        rw [hNA.1]
        unfold FB
        zuhkf
        refine le_trans hcnt zttba
        show 2 * gradeLen P.n g i + 8 ≤ 2 ^ g + 8
        have : ztxiu := by
          rw [← pow_succ', show g - 1 + 1 = g by omega]
        omega
      have hcm := clogCost_mono ztqzn hFB
      obtain ⟨c', k, e, hk, hw', a1, a2, ⟨N', hNW', hc'⟩, m1, m2, o, fr, frr⟩ :=
        nfU_gran
          hGr hG hWh hw hu.r07 hu.r37 hg7 hu.r19 h17 by_omega hu.r14 h35 by_omega rfl hA
          h30 hu.r11 hu.r20 hu.r25 hu.r26 hu.r29 ztqpy hdh hd5 by_omega rfl
          by_tauto hNW hc
          (gradeGran_mono by_omega) by_omega
      refine ⟨c', k, e, by_omega, hw', a1, a2, fun C' a b f => ?_,
      by omega, by_omega, o,
        fun r hr => fr r by_grind by_grind by_grind by_grind by_grind,
        fun r hr => frr r by_grind⟩
      have : C0 = C' := chain_eq a.symm b.symm f.symm
      subst this; exact ⟨N', hNW', hc'⟩
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def chainS (sB sL sG sP : Stmt) : Stmt :=
  .seq lenS (.seq descU (.seq ztftl (.seq (prepCall sP) cellB)))

/-- A bound on the chord count of a normal form of grade `g`. -/
noncomputable def NB (g : ℕ) : ℕ := l23c 4 * (2 ^ ztbs + 8) / ztlpj

/-- **The cost bound of one chain of grade `g`.** -/
noncomputable def stepB (κB κL : ℕ) (κG : ℕ → ℕ) (κO g : ℕ) : ℕ :=
  nfB κB κL κG g + κO * ztxcf + 1924

/-- **The memory invariant of the chain loop**: the grade record at `h` (grade `g` in progress,
the row of grade `g - 1` at `R`) and the cells of chains `< i`. -/
def ChainMem (O : OracleIface) (P : Polygon) (m : ℕ → ℕ) (h hp g R x i A : ℕ) : Prop :=
  UpTab O P m h hp A ∧ m h = g ∧ ztwvx ∧
    Cells O P m A hp g x i
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}
set_option maxHeartbeats 64000000 in
/-- **One chain.** -/
theorem chainS_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        ztuu)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust ztdo c'.nmem ztwq ∧
        IsCanonicalNF ztc zta N ztczy 4)
      ztyp)
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem ztbdk ztm ∧
        rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust ztdo c'.nmem ztwr ∧
        IsCanonicalNF ztc zta N ztbqg 4)
      ztxk)
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P ztm c.nmem ztqa ∧
        ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
          NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztqb ∧
          M.Semigranular ztwiv ztbdj)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
        NFAt c.nmem ztbdi N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
          N'.F M zta ⊆ N.F M zta ∧
          IsCanonicalNF M zta N' ztbdj ztqb)
      (fun _ c => κG ztqb *
        ztin))
    (hV : O.Valid) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g i R x A : ℕ}
    (hu : URegs c P.n hp h g ztduv ztcvr ztwwd R)
    (hA : c.nreg ALLOC = A) (h15 : c.nreg 170015 = i) (h16 : c.nreg 170016 = gradeStart g i)
    (h18 : c.nreg 170018 = x) (h35 : c.nreg 170035 = 6 * i) (h36 : c.nreg 170036 = 2 * i + 1)
    (hi : i < gradeCount P.n g) (h2g : 2 ^ g ≤ 2 * P.n)
    (hM : Robust A c.nmem fun m => ChainMem O P m h hp g R x i A)
    (hW : A + stepB κB κL κG O.κ g + 6 ≤ W) :
    ∃ c' k, Exec P W (chainS sB sL sG O.prep) c c' k ∧ k ≤ stepB κB κL κG O.κ g ∧
      WordsBounded W c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      URegs c' P.n hp h g ztduv ztcvr ztwwd R ∧
      c'.nreg 170015 = i + 1 ∧ c'.nreg 170016 = gradeStart g ztg ∧
      c'.nreg 170035 = 6 * ztg ∧ c'.nreg 170036 = 2 * ztg + 1 ∧
      Robust ztdo c'.nmem
        (fun m => ChainMem O P m h hp g R ztqgw ztg ztdo) ∧
      zttp ∧ ztbuk ∧
      c'.output = c.output ∧
      (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
        r ≠ 170036 → c'.nreg r = c.nreg r) ∧
      zttc := by
  zuk
  zuku
  zucwg

  have hcnt : gradeCount P.n g ≤ P.n := by
    unfold gradeCount; have := Nat.div_le_self ztdfz ztgyk; omega
  unfold stepB at hW
  zufgf
  obtain ⟨hT0, hmh0, hR0, hC0⟩ := hM.holds
  obtain ⟨-, -, -, hH, hhp, -, -, -, -⟩ := hT0
  -- `lenS`
  obtain ⟨c1, k1, e1, hk1, hw1, l17, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    lenS_exec (P := P) hw hu.r28 h16 hu.r10
  have h17 : c1.nreg 170017 = gradeLen P.n g i := by rw [l17]; rfl
  have hu1 := hu.of_frame fun r hr => fr1 r ztmq
    ztmq
  have hA1 : ztupb := by_grind
  zumat
  -- `descU`
  have hM1 : Robust A c1.nmem fun m => ChainMem O P m h hp g R x i A := by_grind
  obtain ⟨c2, k2, e2, hk2, hw2, a21, a22, d5, dh, hdesc, hm2, fr2, frr2, hrm2, ho2⟩ :=
    descU_exec (O := O) hG hWn hn hw1 hu1 hA1 by_grind
      by_grind
      by_grind hi hM1.holds.1 hM1.holds.2.1
      hM1.holds.2.2.1 by_omega by_omega
  obtain ⟨d, hd⟩ : ∃ d, c2.nreg 170030 = d := by_grind
  zvnej at d5 dh hdesc
  have hu2 := hu1.of_kept fr2
  have kk2 : ∀ r, r = 170015 ∨ r = 170016 ∨ r = 170017 ∨ r = 170018 ∨ r = 170035 ∨
      r = 170036 → c2.nreg r = c1.nreg r := fun r hr => fr2 r (kept_of
        ztiiw by_omega)
  -- memory: `c2` agrees with `c` below `A`
  have mc2 : ztfai := fun a ha => by_grind
  have hM2 : Robust _ c2.nmem fun m => UpTab O P m h hp _ ∧
      m h = g ∧ (1 ≤ g → m _ = R) :=
    robust_of (hM.transport mc2) a21 fun m' h' => ⟨h'.1.mono a21, h'.2.1, h'.2.2.1⟩
  -- `nfU`
  have hWnf : c2.nreg ALLOC + nfB κB κL κG g + 6 ≤ W := by_omega
  obtain ⟨c3, k3, e3, hk3, hw3, a31, a32, hnf, m31, m32, o3, fr3, frr3⟩ :=
    nfU_exec (O := O) (sB := sB) (sL := sL) (sG := sG) hB hL hGr hG hWh hn hw2 hu2 rfl
      by_grind
      by_grind
      by_grind hi hM2 hd d5 dh hdesc
      hWnf
  obtain ⟨f, hf⟩ : ∃ f, c3.nreg 170031 = f := by_grind
  rw [hf] at hnf
  have hu3 := hu2.of_kept fun r hr => fr3 r ztcgw
  zuhhc
  obtain ⟨N, hNW, hc⟩ := hnf C0 rfl rfl rfl
  have h30' : c3.nreg 170030 = d := by_grind
  have mc3 := m31
  have hH3 : HostAt c3.nmem hp _ :=
    L41.hostAt_agree (A := A) hH rfl by_omega fun a ha => by
      grind
  have hd3 : ChainDescAt c3.nmem d _ _ C0 :=
    chainDescAt_agree ztqpy d5 dh by_omega mc3
  have dh3 : c3.nmem d = hp := by_grind
  have hNo : NodeOK P c3.nmem _ hp d f C0 _ :=
    ⟨hd3, rfl, dh3, by_omega, by_omega, hfit, N, hNW, hc⟩
  have hwf := chainWF_of_node by_omega hNo hH3
  -- the preprocessing cost
  zufga
  have hcnt3 := nChords_mul_le hP hc
  have hNB : c3.nmem f ≤ NB g := by
    rw [hNW.holds.1]
    unfold NB
    zuhkf
    refine le_trans hcnt3 zttba
    show 2 * gradeLen P.n g i + 8 ≤ 2 ^ ztbs + 8
    omega
  have hlog : Nat.clog 2 ztbagt ≤ g := by
    rw [hd3.2.2.2.1]; exact Nat.clog_le_of_le_pow hl2
  have hpc : O.κ * (c3.nmem f * (Nat.clog 2 ztbagt + 1) + 1) ≤
      O.κ * ztxcf :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul hNB by_omega) 1)
  -- `prepCall`
  obtain ⟨c4, k4, e4, hk4, hw4, a41, a42, o1, o2, t0, t1, t2, hAt, m41, m42, o4, fr4, frr4⟩ :=
    prepCall_exec (P := P) (N := N) hV hG hWh hw3 h30' hf hu3.r11 hwf hd3 rfl hNW hc
      by_omega
  obtain ⟨o, hoo⟩ : ∃ o, c4.nreg 170032 = o := by_grind
  rw [hoo] at o1 o2 t0 t1 t2 hAt
  have kk4 : ∀ r, Kept r → c4.nreg r = c3.nreg r := fun r hr =>
    fr4 r (hr.not_mem by_decide by_decide by_decide) (by have := hr.range; omega)
      hr.ne_alloc
  have hu4 := hu3.of_kept kk4
  have k4' : ∀ r, r = 170015 ∨ r = 170016 ∨ r = 170018 ∨ r = 170035 ∨ r = 170036 →
      c4.nreg r = c.nreg r := fun r hr => by
    have kr : Kept r := kept_of ztiiw by_omega
    rw [kk4 r kr, fr3 r (Or.inl kr), fr2 r kr, g1 r by_omega by_omega]
  -- `cellB`
  have hsb : gradeStart g i + 2 ^ g ≤ 3 * P.n := by_omega
  obtain ⟨c5, k5, e5, hk5, hw5, A5e, x5, i5, s5, q5, t5, w0, w1, w2, w3, mw, fr5, hrr5, hrm5,
      ho5⟩ :=
    cellB_exec (P := P) (d := d) (f := f) (o := o) (x := x) (i := i) (s := gradeStart g i)
      (q := 6 * i) (t := 2 * i + 1) hw4 rfl
      (by rw [fr4 170030 by_decide by_decide by_decide]; omega)
      (by rw [fr4 170031 by_decide by_decide by_decide]; exact hf) hoo
      ztcmg ztcmg
      ztcmg hu4.r10 ztcmg
      ztcmg hu4.r20 hu4.r21 hu4.r25 hu4.r26
      by_omega by_omega by_omega by_omega by_omega
  have mc5 : ztknv := fun a ha => by
    rw [mw a by_omega, m41 a by_omega, mc3 a by_omega, mc2 a ha]
  have mc53 : ∀ a, a < c3.nreg ALLOC → c5.nmem a = c3.nmem a := fun a ha => by
    rw [mw a by_omega, m41 a ha]
  refine ⟨c5, k1 + ztvs, .seq e1 ztbxo,
    by unfold stepB; omega, hw5, by_omega, by_omega,
    hu4.of_frame fun r hr => fr5 r ztmq ztmq
      ztmq ztmq
      ztmq ztmq
      ztmq,
    i5, by rw [s5]; unfold gradeStart; ring, by_omega, by_omega, ?_, mc5,
    fun a ha => by rw [hrm5, m42 a by_omega, m32 a by_omega, hrm2, hrm1], by
      grind, fun r hr a1 a2 a3 a4 a5 a6 => ?_, fun r hr => by
      rw [hrr5, frr4 r (hr.not_mem by_decide), frr3 r hr, frr2 r hr, hrr1]⟩
  · rw [x5, A5e]
    zucng
    have hmc := fun a ha => (hm a by_omega).trans (mc5 a ha)
    have hm3 := fun a ha =>
      (hm a by_omega).trans (mc53 a ha)
    obtain ⟨hT, hmh, hR, hCl⟩ := hM m hmc
    refine ⟨hT.mono by_omega, hmh, hR, ?_⟩
    have e0 : m _ = d := (hm _ by_omega).trans w0
    have e1 : m _ = f := (hm _ by_omega).trans w1
    have e2 : m _ = o := (hm _ by_omega).trans w2
    have e3 : m _ = x := (hm _ by_omega).trans w3
    show _ ∧ _ ∧ _
    zuguf
    refine ⟨by_omega, ⟨fun C a b f' => ?_, hAt m fun a ha => (hm a by_omega).trans
        (mw a ztbbu), (hm o by_omega).trans ((mw o by_omega).trans t0),
      (hm _ by_omega).trans ((mw _ by_omega).trans t1),
      (hm _ by_omega).trans ((mw _ by_omega).trans t2)⟩,
      hCl.mono by_omega⟩
    have : C0 = C := chain_eq a.symm b.symm f'.symm
    zumo
    exact ⟨chainDescAt_agree hd3 by_omega dh3 by_omega hm3, rfl,
      by rw [hm3 _ by_omega]; omega, by_omega, by_omega, hfit, N,
      fun m'' hm'' => hNW m'' fun a ha => (hm'' a by_omega).trans (hm3 a ha), hc⟩
  · have ha5 : r ≠ 170034 := by have := hr.range; omega
    rw [fr5 r ha5 a4 a1 a2 a5 a6 hr.ne_alloc, kk4 r hr, fr3 r ztcgw, fr2 r hr,
      g1 r a3 (by have := hr.range; omega)]
end proofs
end
end Chazelle.Core.Up
namespace Chazelle.Core.Up
open Machine Machine.Stmt Programs Chazelle Chazelle.Core.L41
@[expose] public section
def chainsL (sB sL sG sP : Stmt) : Stmt := .whileLtN 170015 170008 (chainS sB sL sG sP)
section proofs
variable {O : OracleIface} {P : Polygon} {W : ℕ}
set_option maxHeartbeats 32000000 in
/-- **All chains of grade `g`.** -/
theorem chainsL_exec {sB sL sG : Stmt} {κB κL : ℕ} {κG : ℕ → ℕ}
    (hB : Meets sB bruteBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bBrute 1 ∧
        rd c bBrute 0 + rd c bBrute 1 + 1 ≤ P.n ∧ 1 ≤ rd c bBrute 2 ∧
        ztuu)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bBrute 0 ∧ C.m = rd c bBrute 1 ∧
        Robust ztdo c'.nmem ztwq ∧
        IsCanonicalNF ztc zta N ztczy 4)
      ztyp)
    (hL : Meets sL l41Bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
        (gradeCtx O).holds P c.nmem ztbdk ztm ∧
        rd c bL41 3 ≤ c.nmem ztbdk ∧ lemma41Start ≤ rd c bL41 3 ∧
        rd c bL41 1 + rd c bL41 2 + 1 ≤ P.n ∧
        2 ^ ztbwz < rd c bL41 2 ∧ rd c bL41 2 ≤ 2 ^ rd c bL41 3)
      (fun P c c' => ∃ C N, C.P = Qof P ∧ C.s = rd c bL41 1 ∧ C.m = rd c bL41 2 ∧
        Robust ztdo c'.nmem ztwr ∧
        IsCanonicalNF ztc zta N ztbqg 4)
      ztxk)
    (hGr : Meets sG granBands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ 1 ≤ rd c bGran 2 ∧
        ModelDescWF P ztm c.nmem ztqa ∧
        ∃ M N, ModelDescAt c.nmem ztqa zta M ∧ GoodModel M ∧
          NFWithin c.nmem ztbdi ztm N ∧ IsNF M zta N ∧
          M.DegLe ztwiv ztqb ∧
          M.Semigranular ztwiv ztbdj)
      (fun P c c' => ∀ M N, ModelDescAt c.nmem ztqa zta M →
        NFAt c.nmem ztbdi N →
        ∃ N', c.nreg ALLOC ≤ rd c' bGran 4 ∧ NFWithin c'.nmem ztcoh ztdo N' ∧
          N'.F M zta ⊆ N.F M zta ∧
          IsCanonicalNF M zta N' ztbdj ztqb)
      (fun _ c => κG ztqb *
        ztin))
    (hV : O.Valid) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hn : 2 ≤ P.n) {c : Config}
    (hw : WordsBounded W c) {hp h g R x A : ℕ}
    (hu : URegs c P.n hp h g ztduv ztcvr ztwwd R)
    (hA : c.nreg ALLOC = A) (h15 : c.nreg 170015 = 0) (h16 : c.nreg 170016 = 0)
    (h18 : c.nreg 170018 = x) (h35 : c.nreg 170035 = 0) (h36 : c.nreg 170036 = 1)
    (h2g : 2 ^ g ≤ 2 * P.n)
    (hM : Robust A c.nmem fun m => ChainMem O P m h hp g R x 0 A)
    (hW : A + (gradeCount P.n g + 1) * (stepB κB κL κG O.κ g + 8) ≤ W) :
    ∃ c' k, Exec P W (chainsL sB sL sG O.prep) c c' k ∧
      k ≤ gradeCount P.n g * (stepB κB κL κG O.κ g + 2) + 2 ∧
      WordsBounded W c' ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + k ∧
      URegs c' P.n hp h g ztduv ztcvr ztwwd R ∧
      Robust ztdo c'.nmem
        (fun m => ChainMem O P m h hp g R ztqgw ztduv ztdo) ∧
      zttp ∧ ztbuk ∧
      c'.output = c.output ∧
      (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
        r ≠ 170036 → c'.nreg r = c.nreg r) ∧
      zttc := by
  zudbk

  let I : Config → Prop := fun c' => ∃ i, i ≤ cnt ∧ WordsBounded W c' ∧
    URegs c' P.n hp h g cnt ztcvr ztwwd R ∧
    c'.nreg 170015 = i ∧ c'.nreg 170016 = gradeStart g i ∧ c'.nreg 170035 = 6 * i ∧
    c'.nreg 170036 = 2 * i + 1 ∧ A ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A + i * ztnu ∧
    Robust ztdo c'.nmem
      (fun m => ChainMem O P m h hp g R ztqgw i ztdo) ∧
    zttp ∧ ztbuk ∧
    c'.output = c.output ∧
    (∀ r, Kept r → r ≠ 170015 → r ≠ 170016 → r ≠ 170017 → r ≠ 170018 → r ≠ 170035 →
      r ≠ 170036 → c'.nreg r = c.nreg r) ∧
    zttc
  have hI0 : I c := ⟨0, by_omega, hw, hu, h15, by rw [h16]; unfold gradeStart; ring,
    by rw [h35], by rw [h36], by_omega, by_omega, by_grind,
    fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  obtain ⟨c', k, e, ⟨i, hic, hw', hu', i15, i16, i35, i36, a1, a2, hM', mm, mr, mo, fr, frr⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 170015) (b := 170008)
      (body := chainS sB sL sG O.prep) I (fun c' => (cnt - c'.nreg 170015) * ztnu)
      ztcht ztdum
      (fun c2 ⟨i, hic, hw2, hu2, i15, i16, i35, i36, a1, a2, hM2, mm, mr, mo, fr, frr⟩ htest => by
        rw [i15, hu2.r08] at htest
        have hKm : i * ztnu + ztnu ≤ cnt * ztnu := by
          zuoqy; exact Nat.mul_le_mul_right _ htest
        have hW2 : c2.nreg ALLOC + K + 6 ≤ W := by
          grind
        obtain ⟨c3, k3, e3, hk3, hw3, b1, b2, hu3, j15, j16, j35, j36, hM3, m3, r3, o3, f3,
            ff3⟩ :=
          chainS_exec (O := O) (sB := sB) (sL := sL) (sG := sG) hB hL hGr hV hG hWh hn hw2 hu2
            rfl i15 i16 rfl i35 i36 htest h2g hM2 hW2
        refine ⟨c3, k3, e3, ⟨i + 1, by_omega, hw3, hu3, j15, j16, j35, j36, by_omega, ?_, hM3,
          fun a ha => by_grind,
          fun a ha => by_grind, by_grind,
          fun r hr a1 a2 a3 a4 a5 a6 => by_grind,
          fun r hr => by_grind⟩, ?_, by_omega⟩
        · grind
        · rw [j15, i15]
          have : (cnt - i) * ztnu = (cnt - ztg) * ztnu + ztnu := by
            zujly
          omega) hI0
  have hic' : i = cnt := by rw [i15, hu'.r08] at htest; omega
  subst hic'
  refine ⟨c', k, e, by_grind, hw', a1, by_omega, hu', hM', mm, mr, mo,
    fr, frr⟩
