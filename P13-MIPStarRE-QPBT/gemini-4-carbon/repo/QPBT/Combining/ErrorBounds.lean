module

public import QPBT.Games.ErrorFunctions
public import QPBT.Test.LowDegreeGameMeasurements
public import QPBT.Test.SoundnessDefs
public import QPBT.Combining.DirectLowDegreeCore
public import Mathlib.Analysis.MeanInequalitiesPow

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable def directPassingErrorEnvelope (x y : ℝ) : ℝ :=
  3 * (Real.sqrt x + y)

theorem directPassingErrorEnvelope_pos (x y : ℝ) (hy : 0 < y) :
    0 < directPassingErrorEnvelope x y := by
  dsimp [directPassingErrorEnvelope]; nlinarith [Real.sqrt_nonneg x]

theorem seven_branch_capped_error_le_directPassingErrorEnvelope
    (Q L r : ℝ) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hr : 0 ≤ r) :
    min 1 ((Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9) ≤
      directPassingErrorEnvelope (Q + L) r := by
  have hQL : 0 ≤ Q + L := by linarith
  have hroot : Real.sqrt (Q + 2 * L) ≤ 2 * Real.sqrt (Q + L) := by
    nlinarith [Real.sq_sqrt hQL, Real.sq_sqrt (by linarith : 0 ≤ Q + 2 * L),
      Real.sqrt_nonneg (Q + L), Real.sqrt_nonneg (Q + 2 * L)]
  have hdiv : (Q + 16 * L + 4 * Real.sqrt (Q + 2 * L) + 5 * r) / 9 ≤
      2 * (Q + L) + Real.sqrt (Q + L) + r := by nlinarith [Real.sqrt_nonneg (Q + L)]
  refine (min_le_min_left 1 hdiv).trans ?_
  by_cases hx : Q + L ≤ 1
  · have hs : Real.sqrt (Q + L) ≤ 1 := by simpa using Real.sqrt_le_sqrt hx
    exact (min_le_right _ _).trans (by
      dsimp [directPassingErrorEnvelope]; nlinarith [Real.sq_sqrt hQL, Real.sqrt_nonneg (Q + L)])
  · have hs : 1 ≤ Real.sqrt (Q + L) := by simpa using Real.sqrt_le_sqrt (le_of_not_ge hx)
    exact (min_le_left _ _).trans (by
      dsimp [directPassingErrorEnvelope]; nlinarith [Real.sqrt_nonneg (Q + L)])

theorem rpow_quarter_nonneg (x : ℝ) : 0 ≤ Real.rpow x (1 / 4 : ℝ) := by
  change 0 ≤ x ^ (1 / 4 : ℝ)
  rcases lt_or_ge x 0 with hx | hx
  · rw [Real.rpow_def_of_neg hx,
      show (1 / 4 : ℝ) * Real.pi = Real.pi / 4 by ring, Real.cos_pi_div_four]
    positivity
  · exact Real.rpow_nonneg hx _

theorem sqrt_deficit_bound_le (m δP δQ : ℝ) (hm : 1 ≤ m) (hP : 0 ≤ δP) (hQ : 0 ≤ δQ) :
    Real.sqrt (2 * Real.sqrt (4 * m ^ 2 * δP) + 2 * Real.sqrt (4 * δQ)) ≤
      2 * Real.sqrt m * (Real.rpow δP (1 / 4 : ℝ) + Real.rpow δQ (1 / 4 : ℝ)) := by
  have hm0 : 0 ≤ m := by linarith
  let u := Real.rpow δP (1 / 4 : ℝ)
  let v := Real.rpow δQ (1 / 4 : ℝ)
  have hu0 : 0 ≤ u := Real.rpow_nonneg hP _
  have hv0 : 0 ≤ v := Real.rpow_nonneg hQ _
  have hu2 : u ^ (2 : ℕ) = Real.sqrt δP := by
    dsimp [u]; rw [← Real.rpow_natCast, ← Real.rpow_mul hP, Real.sqrt_eq_rpow]; norm_num
  have hv2 : v ^ (2 : ℕ) = Real.sqrt δQ := by
    dsimp [v]; rw [← Real.rpow_natCast, ← Real.rpow_mul hQ, Real.sqrt_eq_rpow]; norm_num
  have h1 : Real.sqrt (4 * m ^ 2 * δP) = 2 * m * u ^ (2 : ℕ) := by
    rw [hu2, Real.sqrt_mul (by positivity), show (4 * m ^ 2 : ℝ) = (2 * m) ^ 2 by ring, Real.sqrt_sq (by linarith)]
  have h2 : Real.sqrt (4 * δQ) = 2 * v ^ (2 : ℕ) := by
    rw [hv2, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h1, h2]
  refine (Real.sqrt_le_left (by positivity)).mpr ?_
  have hsq : (2 * Real.sqrt m * (u + v)) ^ 2 = 4 * m * (u + v) ^ 2 := by
    rw [show (2 * Real.sqrt m * (u + v)) ^ 2 = 4 * Real.sqrt m ^ 2 * (u + v) ^ 2 by ring, Real.sq_sqrt hm0]
  rw [hsq]
  nlinarith [mul_nonneg hm0 (mul_nonneg hu0 hv0), mul_nonneg (show 0 ≤ m - 1 by linarith) (sq_nonneg v)]

theorem sqrt_deltaQld_le {P : AdmissibleParams} {a b epsilon : ℝ}
    (ha : 1 ≤ a) (hepsilon : 0 ≤ epsilon) :
    Real.sqrt (deltaQld a b epsilon P.m P.d P.q) ≤ deltaQld a (b / 2) epsilon P.m P.d P.q := by
  let deg : ℝ := ((P.m * P.d : ℕ) : ℝ)
  have hdeg : 1 ≤ deg := Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  have hpref : 1 ≤ a * deg ^ a := one_le_mul_of_one_le_of_one_le ha (Real.one_le_rpow hdeg (zero_le_one.trans ha))
  have hq : (0 : ℝ) ≤ P.q := Nat.cast_nonneg _
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have hrate : (epsilon ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * deg))) ^ (1 / 2 : ℝ) ≤
      epsilon ^ (b / 2) + (P.q : ℝ) ^ (-(b / 2)) + (2 : ℝ) ^ (-((b / 2) * deg)) := by
    have h := (Real.rpow_add_le_add_rpow (add_nonneg (Real.rpow_nonneg hepsilon b) (Real.rpow_nonneg hq (-b)))
      (Real.rpow_nonneg htwo (-(b * deg))) (by norm_num) (by norm_num)).trans
      (add_le_add (Real.rpow_add_le_add_rpow (Real.rpow_nonneg hepsilon b) (Real.rpow_nonneg hq (-b))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)) le_rfl)
    rw [← Real.rpow_mul hepsilon, ← Real.rpow_mul hq, ← Real.rpow_mul htwo] at h
    simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_assoc, mul_comm, mul_left_comm] using h
  unfold deltaQld
  simp only [Real.rpow_eq_pow, Real.sqrt_eq_rpow]
  change (a * deg ^ a * (epsilon ^ b + (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * deg)))) ^ (1 / 2 : ℝ) ≤ _
  rw [Real.mul_rpow (zero_le_one.trans hpref) (by positivity)]
  exact mul_le_mul (Real.rpow_le_self_of_one_le hpref (by norm_num)) hrate
    (by positivity) (zero_le_one.trans hpref)

theorem scale_deltaQld_le {P : AdmissibleParams} {a b epsilon K : ℝ}
    (ha : 1 ≤ a) (he : 0 ≤ epsilon) (hK : 1 ≤ K) :
    K * deltaQld a b epsilon P.m P.d P.q ≤ deltaQld (K * a) b epsilon P.m P.d P.q := by
  have hmd : (1 : ℝ) ≤ ((P.m * P.d : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.mul_pos P.one_le_m P.hd)
  unfold deltaQld
  rw [← mul_assoc, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hmd
      (le_mul_of_one_le_left (by linarith) hK)) (by nlinarith))
    (add_nonneg (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by norm_num) _))

theorem exists_conditioned_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (constant : ℝ) (hconstant : 1 ≤ constant)
    (pastingError : ℝ → ℝ → ℝ) (hpasting : IsPolyErr₂ pastingError) :
    ∃ lineError : ℝ → ℝ → ℝ, IsPolyErr₂ lineError ∧
      ∀ error ratio mass : ℝ, 0 ≤ error → 0 ≤ ratio → 1 / 2 ≤ mass → mass ≤ 1 →
        min 1 (mass * pastingError ratio
          ((8 * pointError error + constant * (error + Real.sqrt error)) / mass) + ratio) ≤
          lineError error ratio := by
  obtain ⟨Cp, pp, hCp, hpp, hpb⟩ := hpoint
  obtain ⟨Ck, rp, mp, hCk, hrp, hmp, hkb⟩ := hpasting
  let sp := min pp (1 / 2 : ℝ)
  let fr := min rp 1
  let mc := 8 * Cp + 2 * constant
  let pc := (2 * mc) ^ mp
  let fc := Ck * (1 + pc) + 1
  have hsp : 0 < sp := lt_min hpp (by norm_num)
  have hfr : 0 < fr := lt_min hrp zero_lt_one
  have hmc : 0 ≤ mc := by dsimp [mc]; linarith
  have hpc : 0 ≤ pc := Real.rpow_nonneg (by positivity) _
  have hfc : 1 ≤ fc := by dsimp [fc]; nlinarith
  refine ⟨fun e r => fc * (e ^ (sp * mp) + r ^ fr),
    ⟨fc, sp * mp, fr, hfc, mul_pos hsp hmp, hfr, fun e r he hr =>
      ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)), le_rfl⟩⟩, ?_⟩
  intro e r mass he hr hmass hmass1
  have hmassPos : 0 < mass := by linarith
  have hep : 0 ≤ e ^ (sp * mp) := Real.rpow_nonneg he _
  have hrp0 : 0 ≤ r ^ fr := Real.rpow_nonneg hr _
  have hlarge (hl : 1 ≤ e ^ (sp * mp) + r ^ fr) :
      min 1 (mass * pastingError r ((8 * pointError e + constant * (e + Real.sqrt e)) / mass) + r) ≤
        fc * (e ^ (sp * mp) + r ^ fr) :=
    (min_le_left _ _).trans (by nlinarith [mul_nonneg (show 0 ≤ fc - 1 by linarith) (add_nonneg hep hrp0)])
  by_cases he1 : e ≤ 1
  · by_cases hr1 : r ≤ 1
    · have hpv := hpb e he
      have hps : pointError e ≤ Cp * e ^ sp :=
        hpv.2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' he he1 hsp.le (min_le_left _ _)) (by linarith))
      have hes : e ≤ e ^ sp := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' he he1 hsp.le
          (show sp ≤ 1 from (min_le_right _ _).trans (by norm_num))
      have hsqs : Real.sqrt e ≤ e ^ sp := by
        rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_ge' he he1 hsp.le (min_le_right _ _)
      have hmnn : 0 ≤ 8 * pointError e + constant * (e + Real.sqrt e) :=
        add_nonneg (mul_nonneg (by norm_num) hpv.1) (mul_nonneg (by linarith) (add_nonneg he (Real.sqrt_nonneg _)))
      have hms : 8 * pointError e + constant * (e + Real.sqrt e) ≤ mc * e ^ sp := by
        dsimp [mc]; nlinarith [mul_le_mul_of_nonneg_left (add_le_add hes hsqs) (show 0 ≤ constant by linarith)]
      have hds : (8 * pointError e + constant * (e + Real.sqrt e)) / mass ≤ (2 * mc) * e ^ sp :=
        (div_le_iff₀ hmassPos).mpr (hms.trans (by
          nlinarith [mul_nonneg hmc (Real.rpow_nonneg he sp),
            mul_nonneg (show 0 ≤ mass - 1 / 2 by linarith) (mul_nonneg hmc (Real.rpow_nonneg he sp))]))
      have hdp : ((8 * pointError e + constant * (e + Real.sqrt e)) / mass) ^ mp ≤ pc * e ^ (sp * mp) := by
        calc _ ≤ ((2 * mc) * e ^ sp) ^ mp := Real.rpow_le_rpow (div_nonneg hmnn hmassPos.le) hds hmp.le
          _ = _ := by rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg he _), ← Real.rpow_mul he]
      have hrs : r ^ rp ≤ r ^ fr := Real.rpow_le_rpow_of_exponent_ge' hr hr1 hfr.le (min_le_left _ _)
      have hrl : r ≤ r ^ fr := by simpa using Real.rpow_le_rpow_of_exponent_ge' hr hr1 hfr.le (min_le_right _ _)
      have hkv := hkb r _ hr (div_nonneg hmnn hmassPos.le)
      refine (min_le_right _ _).trans ((add_le_add (mul_le_of_le_one_left hkv.1 hmass1) le_rfl).trans ?_)
      refine (add_le_add (hkv.2.trans (mul_le_mul_of_nonneg_left (add_le_add hrs hdp) (by linarith))) hrl).trans ?_
      dsimp [fc]
      nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ Ck by linarith) hpc) hrp0,
        mul_nonneg (show 0 ≤ Ck by linarith) hep]
    · exact hlarge (by linarith [Real.one_le_rpow (le_of_not_ge hr1) hfr.le])
  · exact hlarge (by linarith [Real.one_le_rpow (le_of_not_ge he1) (mul_pos hsp hmp).le])

theorem exists_combining_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (constant : ℝ) (hconstant : 0 ≤ constant) :
    ∃ combinedError : ℝ → ℝ → ℝ, IsPolyErr₂ combinedError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (constant * ((pointError error) ^ (1 / 2 : ℝ) + Real.sqrt dimension *
          ((lineError error ratio) ^ (1 / 4 : ℝ) + (pointError error) ^ (1 / 4 : ℝ) +
            error ^ (1 / 4 : ℝ)))) ≤ dimension * combinedError error ratio := by
  obtain ⟨Cp, pp, hCp, hpp, hpb⟩ := hpoint
  obtain ⟨Cl, ep, rp, hCl, hep, hrp, hlb⟩ := hline
  let fp := min (pp / 4) (min (ep / 4) (1 / 4 : ℝ))
  let coeff := Cp ^ (1 / 2 : ℝ) + Cl ^ (1 / 4 : ℝ) + Cp ^ (1 / 4 : ℝ) + 1
  let fc := 1 + constant * coeff
  have hfp : 0 < fp := by dsimp [fp]; positivity
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hfc : 1 ≤ fc := by dsimp [fc]; linarith [mul_nonneg hconstant hcoeff]
  refine ⟨fun e r => fc * (e ^ fp + r ^ (rp / 4)),
    ⟨fc, fp, rp / 4, hfc, hfp, by positivity, fun e r he hr =>
      ⟨mul_nonneg (by linarith) (add_nonneg (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)), le_rfl⟩⟩, ?_⟩
  intro e r dim he hr hdim
  have hdim0 : 0 ≤ dim := by linarith
  have het : 0 ≤ e ^ fp := Real.rpow_nonneg he _
  have hrt : 0 ≤ r ^ (rp / 4) := Real.rpow_nonneg hr _
  by_cases he1 : e ≤ 1
  · have hpv := hpb e he
    have hlv := hlb e r he hr
    have hproot (pw : ℝ) (hpw : 0 ≤ pw) (hsm : fp ≤ pp * pw) :
        (pointError e) ^ pw ≤ Cp ^ pw * e ^ fp := by
      calc _ ≤ (Cp * e ^ pp) ^ pw := Real.rpow_le_rpow hpv.1 hpv.2 hpw
        _ = Cp ^ pw * e ^ (pp * pw) := by rw [Real.mul_rpow (by linarith) (Real.rpow_nonneg he _), ← Real.rpow_mul he]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge' he he1 hfp.le hsm) (Real.rpow_nonneg (by linarith) _)
    have hp4 := hproot (1 / 4) (by norm_num) (by have := min_le_left (pp / 4) (min (ep / 4) (1 / 4 : ℝ)); dsimp [fp]; linarith)
    have hp2 := hproot (1 / 2) (by norm_num) (by have := min_le_left (pp / 4) (min (ep / 4) (1 / 4 : ℝ)); dsimp [fp]; linarith)
    have hl4 : (lineError e r) ^ (1 / 4 : ℝ) ≤ Cl ^ (1 / 4 : ℝ) * (e ^ fp + r ^ (rp / 4)) := by
      calc _ ≤ (Cl * (e ^ ep + r ^ rp)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hlv.1 hlv.2 (by norm_num)
        _ = Cl ^ (1 / 4 : ℝ) * (e ^ ep + r ^ rp) ^ (1 / 4 : ℝ) := Real.mul_rpow (by linarith) (by positivity)
        _ ≤ Cl ^ (1 / 4 : ℝ) * ((e ^ ep) ^ (1 / 4 : ℝ) + (r ^ rp) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_add_le_add_rpow (Real.rpow_nonneg he _) (Real.rpow_nonneg hr _)
            (by norm_num) (by norm_num)) (Real.rpow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← Real.rpow_mul he, ← Real.rpow_mul hr]
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ (by simp [div_eq_mul_inv])) (Real.rpow_nonneg (by linarith) _)
          exact Real.rpow_le_rpow_of_exponent_ge' he he1 hfp.le (by have := (min_le_right (pp / 4) _).trans (min_le_left (ep / 4) (1 / 4 : ℝ)); dsimp [fp]; linarith)
    have he4 : e ^ (1 / 4 : ℝ) ≤ e ^ fp :=
      Real.rpow_le_rpow_of_exponent_ge' he he1 hfp.le ((min_le_right _ _).trans (min_le_right _ _))
    have hsqd : Real.sqrt dim ≤ dim := by nlinarith [Real.sq_sqrt hdim0, Real.sqrt_nonneg dim]
    have hsum : (pointError e) ^ (1 / 2 : ℝ) + Real.sqrt dim *
        ((lineError e r) ^ (1 / 4 : ℝ) + (pointError e) ^ (1 / 4 : ℝ) + e ^ (1 / 4 : ℝ)) ≤
        dim * (coeff * (e ^ fp + r ^ (rp / 4))) := by
      have hrnn : 0 ≤ (lineError e r) ^ (1 / 4 : ℝ) + (pointError e) ^ (1 / 4 : ℝ) + e ^ (1 / 4 : ℝ) :=
        add_nonneg (add_nonneg (Real.rpow_nonneg hlv.1 _) (Real.rpow_nonneg hpv.1 _)) (Real.rpow_nonneg he _)
      have hsc := mul_le_mul hsqd (add_le_add (add_le_add hl4 hp4) he4) hrnn hdim0
      have hps := mul_le_mul_of_nonneg_right hdim (Real.rpow_nonneg hpv.1 (1 / 2 : ℝ))
      dsimp [coeff]
      nlinarith [mul_nonneg hdim0 (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Cp) (1 / 2 : ℝ)) hrt),
        mul_nonneg hdim0 (mul_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ Cp) (1 / 4 : ℝ)) hrt),
        mul_le_mul_of_nonneg_left hp2 hdim0, mul_nonneg hdim0 hrt]
    refine (min_le_right _ _).trans ((mul_le_mul_of_nonneg_left hsum hconstant).trans ?_)
    dsimp [fc]; nlinarith [mul_nonneg hdim0 (add_nonneg het hrt)]
  · refine (min_le_left _ _).trans ?_
    have hone := Real.one_le_rpow (le_of_not_ge he1) hfp.le
    have hs1 : 1 ≤ fc * (e ^ fp + r ^ (rp / 4)) := by
      nlinarith [mul_nonneg (show 0 ≤ fc - 1 by linarith) (add_nonneg het hrt)]
    nlinarith [mul_nonneg (show 0 ≤ dim - 1 by linarith) (show 0 ≤ fc * (e ^ fp + r ^ (rp / 4)) by linarith)]

theorem exists_direct_passing_polynomial_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (C : ℝ) (hC : 0 ≤ C) :
    ∃ passingError : ℝ → ℝ → ℝ, IsPolyErr₂ passingError ∧
      ∀ error ratio dimension : ℝ, 0 ≤ error → 0 ≤ ratio → 1 ≤ dimension →
        min 1 (directPassingErrorEnvelope
          (pointError error + C * dimension * lineError error ratio) ratio) ≤
            dimension * passingError error ratio := by
  obtain ⟨A, p, hA, hp, hpoint⟩ := hpoint
  obtain ⟨B, r, s, hB, hr, hs, hline⟩ := hline
  let t := min p r
  let u := min s 2
  let K := A + C * B
  let D := 3 * (Real.sqrt K + 1) + 1
  have ht : 0 < t := lt_min hp hr
  have hu : 0 < u := lt_min hs (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Real.sqrt_nonneg K]
  refine ⟨fun e y => D * (e ^ (t / 2) + y ^ (u / 2)),
    ⟨D, t / 2, u / 2, hD, by positivity, by positivity, fun _ _ _ _ => ⟨by positivity, le_rfl⟩⟩, ?_⟩
  intro error ratio dim herror hratio hdim1
  have hdim : 0 ≤ dim := by linarith
  have he : 0 ≤ error ^ (t / 2) := Real.rpow_nonneg herror _
  have hy : 0 ≤ ratio ^ (u / 2) := Real.rpow_nonneg hratio _
  have hlarge (h : 1 ≤ error ^ (t / 2) + ratio ^ (u / 2)) :
      min 1 (directPassingErrorEnvelope (pointError error + C * dim * lineError error ratio) ratio) ≤
        dim * (D * (error ^ (t / 2) + ratio ^ (u / 2))) :=
    (min_le_left _ _).trans (one_le_mul_of_one_le_of_one_le hdim1 (one_le_mul_of_one_le_of_one_le hD h))
  by_cases he1 : error ≤ 1
  · by_cases hr1 : ratio ≤ 1
    · have hpB : pointError error ≤ A * error ^ t :=
        (hpoint error herror).2.trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge' herror he1 ht.le (min_le_left _ _)) (by linarith))
      have hlB : lineError error ratio ≤ B * (error ^ t + ratio ^ u) :=
        (hline error ratio herror hratio).2.trans (mul_le_mul_of_nonneg_left
          (add_le_add (Real.rpow_le_rpow_of_exponent_ge' herror he1 ht.le (min_le_right _ _))
            (Real.rpow_le_rpow_of_exponent_ge' hratio hr1 hu.le (min_le_left _ _))) (by linarith))
      have hsum : pointError error + C * dim * lineError error ratio ≤ dim * K * (error ^ t + ratio ^ u) := by
        have := le_mul_of_one_le_left (by positivity : 0 ≤ A * error ^ t) hdim1
        have := mul_le_mul_of_nonneg_left hlB (mul_nonneg hC hdim)
        dsimp [K]; nlinarith [mul_nonneg (mul_nonneg hdim (by linarith : 0 ≤ A)) (Real.rpow_nonneg hratio u)]
      have heSq : (error ^ (t / 2)) ^ (2 : ℕ) = error ^ t := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul herror]; congr 1; ring
      have hySq : (ratio ^ (u / 2)) ^ (2 : ℕ) = ratio ^ u := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hratio]; congr 1; ring
      have hrootSum : Real.sqrt (error ^ t + ratio ^ u) ≤ error ^ (t / 2) + ratio ^ (u / 2) :=
        (Real.sqrt_le_left (add_nonneg he hy)).mpr (by nlinarith [mul_nonneg he hy])
      have hrootDim : Real.sqrt dim ≤ dim := (Real.sqrt_le_left hdim).mpr (by nlinarith)
      have hroot : Real.sqrt (pointError error + C * dim * lineError error ratio) ≤
          dim * Real.sqrt K * (error ^ (t / 2) + ratio ^ (u / 2)) := by
        calc _ ≤ Real.sqrt (dim * K * (error ^ t + ratio ^ u)) := Real.sqrt_le_sqrt hsum
          _ = Real.sqrt dim * Real.sqrt K * Real.sqrt (error ^ t + ratio ^ u) := by
            rw [Real.sqrt_mul (mul_nonneg hdim hK), Real.sqrt_mul hdim]
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hrootDim (Real.sqrt_nonneg K)) hrootSum
            (Real.sqrt_nonneg _) (mul_nonneg hdim (Real.sqrt_nonneg K))
      have hrSmall : ratio ≤ ratio ^ (u / 2) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hratio hr1 (by positivity : 0 ≤ u / 2)
          (show u / 2 ≤ 1 by have : u ≤ 2 := min_le_right _ _; linarith)
      have hrDim : ratio ≤ dim * ratio ^ (u / 2) := hrSmall.trans (le_mul_of_one_le_left hy hdim1)
      refine (min_le_right _ _).trans ?_
      dsimp [directPassingErrorEnvelope, D]
      nlinarith [mul_nonneg hdim he, mul_nonneg hdim hy]
    · exact hlarge (by linarith [Real.one_le_rpow (le_of_not_ge hr1) (by positivity : 0 ≤ u / 2)])
  · exact hlarge (by linarith [Real.one_le_rpow (le_of_not_ge he1) (by positivity : 0 ≤ t / 2)])

set_option maxHeartbeats 800000 in
theorem exists_global_pair_error_bound_two (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (combinedError : ℝ → ℝ → ℝ)
    (hcombined : IsPolyErr₂ combinedError)
    (a b : ℝ) (ha : 1 ≤ a) (hb : 0 < b) (hbOne : b ≤ 1) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (error : ℝ), 0 ≤ error →
        min 1 (2 * (deltaLd a b ((P.m : ℝ) * combinedError error ((P.m * P.d : ℕ) / (P.q : ℝ)) + error)
          P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) + ((P.m * P.d : ℕ) / (P.q : ℝ)))) ≤
          deltaQld A B error P.m P.d P.q := by
  obtain ⟨Cp, pp, hCp, hpp, hpb⟩ := hpoint
  obtain ⟨Cl, ep, rp, hCl, hep, hrp, hlb⟩ := hcombined
  let fp := min (1 / 2 : ℝ) (min b (min (ep * b) (min (rp * b) (pp / 2))))
  have hfp : 0 < fp := by dsimp [fp]; positivity
  have hhalf : fp ≤ 1 / 2 := min_le_left _ _
  have hpow : fp ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have heExp : fp ≤ ep * b := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrExp : fp ≤ rp * b := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hpExp : fp ≤ pp / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let lg := b + rp * b
  let gr := a + lg + 1
  let lc := a * (4 : ℝ) ^ a * (Cl ^ b + 2)
  let coeff := 2 * (lc + Real.sqrt Cp + 1)
  let fc := coeff + gr + 2
  have hlg : 0 ≤ lg := by dsimp [lg]; positivity
  have hgr : 1 ≤ gr := by dsimp [gr]; linarith
  have hlc : 0 ≤ lc := by dsimp [lc]; positivity
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  have hfc : 1 < fc := by dsimp [fc]; linarith
  refine ⟨fc, fp, hfc, hfp, by linarith, ?_⟩
  intro P error herror
  let size : ℝ := ((P.m * P.d : ℕ) : ℝ)
  let extSize : ℝ := (((2 * P.m + 2) * P.d : ℕ) : ℝ)
  let ratio : ℝ := size / (P.q : ℝ)
  let env := error ^ fp + (P.q : ℝ) ^ (-fp) + (2 : ℝ) ^ (-(fp * size))
  have hsize : 1 ≤ size := by dsimp [size]; exact_mod_cast Nat.mul_pos P.one_le_m P.hd
  have hsize0 : 0 ≤ size := by linarith
  have hsizePos : 0 < size := by linarith
  have hmSize : (P.m : ℝ) ≤ size := by
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    dsimp [size]; push_cast; nlinarith
  have hq : (1 : ℝ) ≤ (P.q : ℝ) := by
    obtain ⟨pw, _, hq⟩ := P.hq; rw [hq]; exact_mod_cast Nat.one_le_pow _ _ (by norm_num)
  have hq0 : 0 ≤ (P.q : ℝ) := by linarith
  have hratio : 0 ≤ ratio := by dsimp [ratio]; positivity
  have henv : 0 ≤ env := by dsimp [env]; positivity
  have henvE : error ^ fp ≤ env := by
    dsimp [env]; linarith [Real.rpow_nonneg hq0 (-fp), Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(fp * size))]
  have henvF : (P.q : ℝ) ^ (-fp) ≤ env := by
    dsimp [env]; linarith [Real.rpow_nonneg herror fp, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(fp * size))]
  change min 1 (2 * (deltaLd a b ((P.m : ℝ) * combinedError error ratio + error)
    P.q (2 * P.m + 2) P.d 1 + Real.sqrt (pointError error) + ratio)) ≤ fc * size ^ fc * env
  by_cases he1 : error ≤ 1
  · have heMono (pw : ℝ) (hpw : fp ≤ pw) : error ^ pw ≤ error ^ fp :=
      Real.rpow_le_rpow_of_exponent_ge' herror he1 hfp.le hpw
    have hfMono (pw : ℝ) (hpw : fp ≤ pw) : (P.q : ℝ) ^ (-pw) ≤ (P.q : ℝ) ^ (-fp) :=
      Real.rpow_le_rpow_of_exponent_le hq (neg_le_neg hpw)
    have hsRatio : 1 ≤ size ^ (rp * b) := Real.one_le_rpow hsize (mul_nonneg hrp.le hb.le)
    have hsLine : 1 ≤ size ^ lg := Real.one_le_rpow hsize hlg
    have hpolySum : error ^ (ep * b) + ratio ^ (rp * b) ≤ size ^ (rp * b) * env := by
      have hreq : ratio ^ (rp * b) = size ^ (rp * b) * (P.q : ℝ) ^ (-(rp * b)) := by
        dsimp [ratio]; rw [Real.div_rpow hsize0 hq0, div_eq_mul_inv, Real.rpow_neg hq0]
      rw [hreq]
      refine (add_le_add ((heMono _ heExp).trans (le_mul_of_one_le_left (Real.rpow_nonneg herror _) hsRatio))
        (mul_le_mul_of_nonneg_left (hfMono _ hrExp) (Real.rpow_nonneg hsize0 _))).trans ?_
      dsimp [env]; nlinarith [mul_nonneg (Real.rpow_nonneg hsize0 (rp * b))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(fp * size)))]
    have hcv := hlb error ratio herror hratio
    have hpoly : (combinedError error ratio) ^ b ≤ Cl ^ b * (size ^ (rp * b) * env) := by
      calc _ ≤ (Cl * (error ^ ep + ratio ^ rp)) ^ b := Real.rpow_le_rpow hcv.1 hcv.2 hb.le
        _ = Cl ^ b * (error ^ ep + ratio ^ rp) ^ b := Real.mul_rpow (by linarith) (by positivity)
        _ ≤ Cl ^ b * (error ^ (ep * b) + ratio ^ (rp * b)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by linarith) _)
          simpa only [← Real.rpow_mul herror, ← Real.rpow_mul hratio] using
            Real.rpow_add_le_add_rpow (Real.rpow_nonneg herror ep) (Real.rpow_nonneg hratio rp) hb.le hbOne
        _ ≤ _ := mul_le_mul_of_nonneg_left hpolySum (Real.rpow_nonneg (by linarith) _)
    have hprod : ((P.m : ℝ) * combinedError error ratio) ^ b ≤ Cl ^ b * size ^ lg * env := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) hcv.1]
      calc _ ≤ size ^ b * (Cl ^ b * (size ^ (rp * b) * env)) :=
            mul_le_mul (Real.rpow_le_rpow (Nat.cast_nonneg _) hmSize hb.le) hpoly
              (Real.rpow_nonneg hcv.1 _) (by positivity)
        _ = _ := by dsimp [lg]; rw [Real.rpow_add hsizePos]; ring
    have hinp : ((P.m : ℝ) * combinedError error ratio + error) ^ b ≤ (Cl ^ b + 1) * size ^ lg * env := by
      refine (Real.rpow_add_le_add_rpow (mul_nonneg (Nat.cast_nonneg _) hcv.1) herror hb.le hbOne).trans
        ((add_le_add hprod ((heMono _ hpow).trans henvE)).trans ?_)
      nlinarith [mul_le_mul_of_nonneg_right hsLine henv]
    have hext : size ≤ extSize ∧ extSize ≤ 4 * size := by
      have : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
      have : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
      dsimp [size, extSize]; push_cast; constructor <;> nlinarith
    have hexp : (2 : ℝ) ^ (-(b * extSize)) ≤ (2 : ℝ) ^ (-(fp * size)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg
        ((mul_le_mul_of_nonneg_right hpow hsize0).trans (mul_le_mul_of_nonneg_left hext.1 hb.le)))
    have hbr : ((P.m : ℝ) * combinedError error ratio + error) ^ b + (P.q : ℝ) ^ (-b) +
        (2 : ℝ) ^ (-(b * extSize)) ≤ (Cl ^ b + 2) * size ^ lg * env := by
      have hrest : (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * extSize)) ≤ env := by
        have := add_le_add (hfMono _ hpow) hexp; dsimp [env]; linarith [Real.rpow_nonneg herror fp]
      have := add_le_add hinp hrest; nlinarith [mul_le_mul_of_nonneg_right hsLine henv]
    have hpref : a * extSize ^ a ≤ a * ((4 : ℝ) ^ a * size ^ a) :=
      mul_le_mul_of_nonneg_left ((Real.rpow_le_rpow (hsize0.trans hext.1) hext.2 (by linarith)).trans_eq
        (Real.mul_rpow (by norm_num) hsize0)) (by linarith)
    have hld : deltaLd a b ((P.m : ℝ) * combinedError error ratio + error) P.q (2 * P.m + 2) P.d 1 ≤
        lc * size ^ (a + lg) * env := by
      have heq : deltaLd a b ((P.m : ℝ) * combinedError error ratio + error) P.q (2 * P.m + 2) P.d 1 =
          a * extSize ^ a * (((P.m : ℝ) * combinedError error ratio + error) ^ b +
            (P.q : ℝ) ^ (-b) + (2 : ℝ) ^ (-(b * extSize))) := by
        simp only [deltaLd, extSize, Nat.mul_one, Real.rpow_eq_pow, Nat.mul_comm P.d (2 * P.m + 2)]
      rw [heq]
      refine (mul_le_mul hpref hbr
        (add_nonneg (add_nonneg (Real.rpow_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hcv.1) herror) _)
          (Real.rpow_nonneg hq0 _)) (Real.rpow_nonneg (by norm_num) _)) (by positivity)).trans_eq ?_
      dsimp [lc]; rw [Real.rpow_add hsizePos a lg]; ring
    have hroot : Real.sqrt (pointError error) ≤ Real.sqrt Cp * env := by
      calc _ ≤ Real.sqrt (Cp * error ^ pp) := Real.sqrt_le_sqrt (hpb error herror).2
        _ = Real.sqrt Cp * error ^ (pp / 2) := by
          rw [Real.sqrt_mul (by linarith)]; congr 1; rw [Real.sqrt_eq_rpow, ← Real.rpow_mul herror]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left ((heMono _ hpExp).trans henvE) (Real.sqrt_nonneg _)
    have hratB : ratio ≤ size * env := by
      dsimp [ratio]; rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left ((hfMono 1 (by linarith)).trans henvF) hsize0
    have hsPow : size ^ (a + lg) ≤ size ^ gr := Real.rpow_le_rpow_of_exponent_le hsize (by dsimp [gr]; linarith)
    have hsGr : size ≤ size ^ gr := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hsize hgr
    have h1Gr : 1 ≤ size ^ gr := Real.one_le_rpow hsize (by linarith)
    have hfin : 2 * (deltaLd a b ((P.m : ℝ) * combinedError error ratio + error) P.q (2 * P.m + 2) P.d 1 +
        Real.sqrt (pointError error) + ratio) ≤ coeff * size ^ gr * env :=
      (mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (hld.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsPow hlc) henv))
        (hroot.trans (le_mul_of_one_le_left (mul_nonneg (Real.sqrt_nonneg _) henv) h1Gr)))
        (hratB.trans (mul_le_mul_of_nonneg_right hsGr henv))) (by norm_num)).trans_eq (by dsimp [coeff]; ring)
    refine (min_le_right _ _).trans (hfin.trans ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul (by dsimp [fc]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hsize (by dsimp [fc]; linarith))
      (Real.rpow_nonneg hsize0 gr) (by linarith)) henv
  · have henv1 : 1 ≤ env := (Real.one_le_rpow (le_of_not_ge he1) hfp.le).trans henvE
    have hpref1 : 1 ≤ fc * size ^ fc := by
      simpa only [one_mul] using mul_le_mul hfc.le (Real.one_le_rpow hsize (by linarith))
        (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
    refine (min_le_left _ _).trans ?_
    simpa only [one_mul] using mul_le_mul hpref1 henv1 (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hpref1)

theorem actual_rounding_error_le_root {delta point ratio t : ℝ}
    (hd : 0 ≤ delta) (hp : 0 ≤ point)
    (hdt : delta ≤ t) (hpt : Real.sqrt point ≤ t) (hrt : ratio ≤ t) :
    min 1 (32 * delta + 32 * Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) +
      64 * Real.sqrt (2 * delta) + 64 * point + 30 * ratio) ≤
      1024 * Real.sqrt (Real.sqrt (Real.sqrt (min 1 t))) := by
  have ht : 0 ≤ t := hd.trans hdt
  by_cases ht1 : t ≤ 1
  · rw [min_eq_right ht1]
    have hroot : Real.sqrt (Real.sqrt (Real.sqrt t)) = t ^ (1 / 8 : ℝ) := by
      simp only [Real.sqrt_eq_rpow]; rw [← Real.rpow_mul ht, ← Real.rpow_mul ht]; norm_num
    rw [hroot]
    have h18 : t ≤ t ^ (1 / 8 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1 (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1)
    have hsqrt : Real.sqrt (t ^ (1 / 4 : ℝ)) = t ^ (1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht]; norm_num
    have hround : Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) ≤ 15 * t ^ (1 / 8 : ℝ) := by
      calc _ ≤ Real.sqrt (225 * t ^ (1 / 4 : ℝ)) := Real.sqrt_le_sqrt
            (mul_le_mul (by norm_num) (Real.rpow_le_rpow hd hdt (by norm_num)) (Real.rpow_nonneg hd _) (by norm_num))
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have h14 : t ≤ t ^ (1 / 4 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' ht ht1 (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1)
    have hsecond : Real.sqrt (2 * delta) ≤ 2 * t ^ (1 / 8 : ℝ) := by
      calc _ ≤ Real.sqrt (4 * t ^ (1 / 4 : ℝ)) := Real.sqrt_le_sqrt (by nlinarith [Real.rpow_nonneg ht (1 / 4 : ℝ)])
        _ = _ := by rw [Real.sqrt_mul (by norm_num), hsqrt]; norm_num
    have hpoint : point ≤ t := by nlinarith [Real.sq_sqrt hp, Real.sqrt_nonneg point]
    exact (min_le_right _ _).trans (by nlinarith [Real.rpow_nonneg ht (1 / 8 : ℝ)])
  · rw [min_eq_left (le_of_not_ge ht1)]; norm_num

theorem exists_actual_rounded_global_pair_error_bound (pointError : ℝ → ℝ)
    (hpoint : IsPolyErr pointError) (lineError : ℝ → ℝ → ℝ)
    (hline : IsPolyErr₂ lineError) (C a b : ℝ) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ A B : ℝ, 1 < A ∧ 0 < B ∧ B < 1 ∧
      ∀ (P : AdmissibleParams) (epsilon : ℝ), 0 ≤ epsilon →
        let delta := deltaLd a b
          (directPassingErrorEnvelope
            (pointError epsilon + C * (P.m : ℝ) * lineError epsilon ((P.m * P.d : ℕ) / (P.q : ℝ)))
            ((P.m * P.d : ℕ) / (P.q : ℝ))) P.q (2 * P.m + 2) P.d 1
        let eta := delta + Real.sqrt (220 * delta ^ (1 / 4 : ℝ)) + 2 * Real.sqrt (2 * delta)
        min 1 (8 * (4 * eta + 8 * pointError epsilon) +
          (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q)) ≤
          deltaQld A B epsilon P.m P.d P.q := by
  obtain ⟨passingError, hpassing, hpBound⟩ :=
    exists_direct_passing_polynomial_bound pointError hpoint lineError hline C hC
  obtain ⟨A, B, hA, hB, hB1, habs⟩ :=
    exists_global_pair_error_bound_two pointError hpoint passingError hpassing a b ha hb hb1
  refine ⟨1024 * A, B / 2 / 2 / 2, by linarith, by positivity, by linarith, ?_⟩
  intro P epsilon he delta eta
  let ratio : ℝ := ((P.m * P.d : ℕ) : ℝ) / P.q
  let passing := directPassingErrorEnvelope (pointError epsilon + C * (P.m : ℝ) * lineError epsilon ratio) ratio
  let slack := deltaLd a b (passing + epsilon) P.q (2 * P.m + 2) P.d 1
  let t := slack + Real.sqrt (pointError epsilon) + ratio
  have hr : 0 ≤ ratio := by dsimp [ratio]; positivity
  have hpass : 0 ≤ passing := by dsimp [passing, directPassingErrorEnvelope]; positivity
  have hp : 0 ≤ pointError epsilon := by obtain ⟨_, _, _, _, h⟩ := hpoint; exact (h epsilon he).1
  have ha0 : 0 ≤ a := by linarith
  have hd : 0 ≤ delta := by dsimp [delta, deltaLd, directPassingErrorEnvelope]; positivity
  have hds : delta ≤ slack := by
    change deltaLd a b passing P.q (2 * P.m + 2) P.d 1 ≤ _
    dsimp [slack, deltaLd]
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
      (Real.rpow_le_rpow hpass (by linarith) hb.le) le_rfl) le_rfl) (by positivity)
  have hdt : delta ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon)]
  have hpt : Real.sqrt (pointError epsilon) ≤ t := by dsimp [t]; linarith [ show 0 ≤ slack by dsimp [slack, deltaLd]; positivity]
  have hrt : ratio ≤ t := by dsimp [t]; linarith [Real.sqrt_nonneg (pointError epsilon), show 0 ≤ slack by dsimp [slack, deltaLd]; positivity]
  have hratio : (((12 * P.m * P.d + 4 * P.d + 14 : ℕ) : ℝ) / P.q) ≤ 30 * ratio := by
    have : (1 : ℝ) ≤ P.m := by exact_mod_cast P.one_le_m
    have : (1 : ℝ) ≤ P.d := by exact_mod_cast P.hd
    dsimp [ratio]; rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by push_cast; nlinarith) (Nat.cast_nonneg _)
  have hcap_mid : min 1 (2 * (deltaLd a b (min 1 passing + epsilon) P.q (2 * P.m + 2) P.d 1 +
      Real.sqrt (pointError epsilon) + ratio)) ≤ deltaQld A B epsilon P.m P.d P.q := by
    have hmp0 : 0 ≤ min 1 passing := by positivity
    refine le_trans ?_ (habs P epsilon he)
    apply min_le_min_left 1
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    unfold deltaLd
    exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
      (Real.rpow_le_rpow (add_nonneg hmp0 he) (add_le_add (hpBound epsilon ratio (P.m : ℝ) he hr
        (by exact_mod_cast P.one_le_m)) le_rfl) hb.le) le_rfl) le_rfl)
      (mul_nonneg ha0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hcap : min 1 t ≤ deltaQld A B epsilon P.m P.d P.q := by
    by_cases hsm : passing ≤ 1
    · rw [min_eq_right hsm] at hcap_mid
      refine le_trans (min_le_min_left 1 ?_) hcap_mid
      change t ≤ 2 * t
      linarith [hd.trans hdt]
    · rw [min_eq_left (le_of_not_ge hsm)] at hcap_mid
      have hld1 : 1 ≤ deltaLd a b (1 + epsilon) P.q (2 * P.m + 2) P.d 1 :=
        one_le_deltaLd_of_one_le_error ha hb.le (by linarith) (by omega) P.hd le_rfl
      rw [min_eq_left (by linarith [Real.sqrt_nonneg (pointError epsilon)])] at hcap_mid
      exact (min_le_left _ _).trans hcap_mid
  have hroot := Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hcap))
  have hrootBound := (Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (sqrt_deltaQld_le (P := P) hA.le he))).trans
    ((Real.sqrt_le_sqrt (sqrt_deltaQld_le (P := P) (b := B / 2) hA.le he)).trans
      (sqrt_deltaQld_le (P := P) (b := B / 2 / 2) hA.le he))
  refine (min_le_min_left 1 ?_).trans
    ((actual_rounding_error_le_root hd hp hdt hpt hrt).trans
      ((mul_le_mul_of_nonneg_left (hroot.trans hrootBound) (by norm_num)).trans
        (scale_deltaQld_le hA.le he (by norm_num : (1 : ℝ) ≤ 1024))))
  dsimp [eta]; linarith

end MIPStarRE.QPBT
