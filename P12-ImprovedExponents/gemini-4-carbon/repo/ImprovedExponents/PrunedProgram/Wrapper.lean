module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ThreeSumApsp.Programs.Sec4.Corollary26.AllInstances
public import ThreeSumApsp.Programs.LightModel
public import ImprovedExponents.PrunedProgram.Shared
public import ImprovedExponents.PrunedProgram.Pre.Preprocessing
public import ImprovedExponents.PrunedProgram.Query.Query
public import ImprovedExponents.Cost8P.Offline

@[expose] public section

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec4 Real

def Fits18 (G : RatParams) : Prop :=
  ∀ N D₀ : ℕ, D₀ ^ 18 ≤ N → G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀)

def allBody (pPow off : ℕ) : Stmt :=
  .call pPow [v 1, k 18, v 0 +' k 1] 10 ;;
  .ite (k 0 <' v 10)
    (.call off [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
    (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)

theorem ratParams_L_le_mul (G : RatParams) (m : ℕ) : G.L m ≤ G.a * m := by
  unfold RatParams.L; rw [Nat.div_le_iff_le_mul_add_pred G.hb]
  have := Nat.le_mul_of_pos_left (G.a * m) G.hb; omega

def offline32Need (G : RatParams) : List ℕ → Need
  | [N, D, _, U] =>
    ⟨1000 + 100 * D + N * D + D * (U * U) + ((N + 1) ^ 5) ^ 3 * (U * U)
        + 7 * ((N + 1) ^ 5 * U) + 10 * (N + 1) ^ 5
        + (G.a * (4 * D) + G.p * (4 * D) + G.b + G.q + G.m₀),
      5 + 2 * N + 8 * (N * D) + 222 * ((N + 1) ^ 5) ^ 4, G.a * (4 * D) + 14⟩
  | _ => ⟨0, 0, 0⟩

theorem lim31_of_need {lim : Limits} {G : RatParams} {N D₀ w U fr d : ℕ} (hD : 1 ≤ D₀)
    (hfit : G.m₀ ≤ logFour D₀ → Hyp30 (parOf G N D₀) (switchOf31 G D₀))
    (ok : (offline32Need G [N, D₀, w, U]).Ok lim fr d) : Lim31 lim G N D₀ fr (U : ℤ) := by
  have hcells := ok.cells
  have fits {n : ℕ} (hn : n ≤ (offline32Need G [N, D₀, w, U]).word) : (n : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast hn) ok.word
  simp only [offline32Need] at hcells fits
  have h4 : 4 ^ logFour D₀ ≤ 4 * D₀ := Nat.pow_clog_le_mul (b := 4) (by norm_num) hD
  have hm4 : logFour D₀ ≤ 4 * D₀ := logFour_le_four_mul hD
  have ha := Nat.mul_le_mul_left G.a hm4; have hp := Nat.mul_le_mul_left G.p hm4
  have std : Std lim := ⟨ok.space, fits (n := 100) (by omega)⟩
  have large (hm : G.m₀ ≤ logFour D₀) : Lim30 lim (parOf G N D₀) (switchOf31 G D₀)
      (blockAt N D₀ fr) (U : ℤ) := by
    have H := hfit hm
    have hB : Below (parOf G N D₀) (switchOf31 G D₀) ((N + 1) ^ 5) := below H
    have hblock : top (parOf G N D₀) (switchOf31 G D₀) (blockAt N D₀ fr) - blockAt N D₀ fr
        ≤ 222 * ((N + 1) ^ 5) ^ 4 := top_sub_le_pow H hB _
    have hpad : N * D (logFour D₀) ≤ 4 * (N * D₀) := (Nat.mul_le_mul_left N h4).trans_eq (by ring)
    have hbase : blockAt N D₀ fr = fr + 3 + N * D (logFour D₀) + N * D (logFour D₀) := rfl
    generalize (N + 1) ^ 5 = B at hB fits ⊢
    have hten := hB.T; have hseven := hB.S7; have htenm := hB.tenm
    have hval : 10 ^ (parOf G N D₀).m * ((7 ^ (parOf G N D₀).L * U) * (7 ^ (parOf G N D₀).L * U))
        ≤ B ^ 3 * (U * U) := (by gcongr : _ ≤ B * ((B * U) * (B * U))).trans_eq (by ring)
    have henc : 7 ^ ((parOf G N D₀).L + 1) * U ≤ 7 * (B * U) := by
      rw [pow_succ']; exact (by gcongr : 7 * 7 ^ (parOf G N D₀).L * U ≤ 7 * B * U).trans_eq (by ring)
    have hpow : 10 ^ ((parOf G N D₀).L + 1) ≤ 10 * B := by rw [pow_succ']; gcongr
    exact ⟨std, by omega, by exact_mod_cast fits (hval.trans (by omega)),
      by exact_mod_cast fits (henc.trans (by omega)), fits (hpow.trans (by omega))⟩
  exact ⟨std, by unfold structEnd; split_ifs with h <;> [omega; exact (large (not_lt.mp h)).space],
    fits (by omega), fits (by omega), fits (n := G.m₀) (by omega),
    by exact_mod_cast fits (n := D₀ * (U * U)) (by omega), large⟩

theorem offline32Need_poly (G : RatParams) : PolyNeedN (offline32Need G) := by
  refine ⟨12 + (4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14), 20, fun ps => ?_⟩
  match ps with
  | [N, D, w, U] =>
    rw [show polyBound _ 20 [N, D, w, U] =
      2 ^ (12 + (4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14)) *
        ((N + 1) * ((D + 1) * ((w + 1) * (U + 1)))) ^ 20 by simp [polyBound]]
    simp only [offline32Need]
    have hN : N + 1 ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    have hD : D ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) := (Nat.le_succ D).trans <|
      (Nat.le_mul_of_pos_right _ (by positivity)).trans (Nat.le_mul_of_pos_left _ (by positivity))
    have hU : U ≤ (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) := (Nat.le_succ U).trans <|
      (Nat.le_mul_of_pos_left _ (by positivity)).trans <|
      (Nat.le_mul_of_pos_left _ (by positivity)).trans (Nat.le_mul_of_pos_left _ (by positivity))
    generalize (N + 1) * ((D + 1) * ((w + 1) * (U + 1))) = Q at hN hD hU ⊢
    generalize hκdef : 4 * G.a + 4 * G.p + G.b + G.q + G.m₀ + 14 = κ
    have hQ1 : 1 ≤ Q := by omega
    have hN' : N ≤ Q := by omega
    have lp {x i : ℕ} (hi : i ≤ 20) (hx : x ≤ Q ^ i) : x ≤ Q ^ 20 :=
      hx.trans (Nat.pow_le_pow_right hQ1 hi)
    have h1 := lp (i := 0) (by norm_num) (le_refl 1)
    have hN1 := lp (i := 1) (by norm_num) (by simpa using hN')
    have hD1 := lp (i := 1) (by norm_num) (by simpa using hD)
    have hND := lp (i := 2) (by norm_num) ((Nat.mul_le_mul hN' hD).trans_eq (sq Q).symm)
    have hDUU := lp (i := 3) (by norm_num) ((Nat.mul_le_mul hD (Nat.mul_le_mul hU hU)).trans_eq (by ring))
    have h5 := lp (i := 5) (by norm_num) (Nat.pow_le_pow_left hN 5)
    have h6 := lp (i := 6) (by norm_num) ((Nat.mul_le_mul (Nat.pow_le_pow_left hN 5) hU).trans_eq (by ring))
    have h17 := lp (i := 17) (by norm_num)
      ((Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.pow_le_pow_left hN 5) 3) (Nat.mul_le_mul hU hU)).trans_eq (by ring))
    have h20 : ((N + 1) ^ 5) ^ 4 ≤ Q ^ 20 := (Nat.pow_le_pow_left (Nat.pow_le_pow_left hN 5) 4).trans_eq (by ring)
    have hκ : (2 ^ 11 + κ) * Q ^ 20 ≤ 2 ^ (12 + κ) * Q ^ 20 :=
      Nat.mul_le_mul_right _ (by have := Nat.lt_two_pow_self (n := κ); have : 1 ≤ 2 ^ κ := Nat.one_le_two_pow; rw [pow_add]; omega)
    have haD : G.a * (4 * D) ≤ 4 * G.a * Q ^ 20 := (by ring : G.a * (4 * D) = 4 * G.a * D).trans_le (Nat.mul_le_mul_left _ hD1)
    have hpD : G.p * (4 * D) ≤ 4 * G.p * Q ^ 20 := (by ring : G.p * (4 * D) = 4 * G.p * D).trans_le (Nat.mul_le_mul_left _ hD1)
    have hrest : G.b + G.q + G.m₀ + 14 ≤ (G.b + G.q + G.m₀ + 14) * Q ^ 20 := Nat.le_mul_of_pos_right _ (by omega)
    have hκQ : (2 ^ 11 + κ) * Q ^ 20 = 2 ^ 11 * Q ^ 20 + 4 * G.a * Q ^ 20 + 4 * G.p * Q ^ 20
        + (G.b + G.q + G.m₀ + 14) * Q ^ 20 := by rw [← hκdef]; ring
    exact ⟨by omega, by omega, by omega⟩
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem pow18_le_of_le_rpow {N D₀ : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 18) (hN : 1 ≤ N)
    (hDN : (D₀ : ℝ) ≤ (N : ℝ) ^ ε) : D₀ ^ 18 ≤ N := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h : ((D₀ : ℝ)) ^ 18 ≤ N :=
    calc ((D₀ : ℝ)) ^ 18 ≤ ((N : ℝ) ^ ε) ^ 18 := pow_le_pow_left₀ (by positivity) hDN 18
      _ = (N : ℝ) ^ (ε * 18) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; rfl
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR (by linarith)
      _ = N := Real.rpow_one _
  exact_mod_cast h

theorem exists_fits18 {a b p q : ℕ} (hb : 1 ≤ b) (hq : 1 ≤ q) (hc : 10 * b < a) (hp : 1 ≤ p)
    (hθ : 10 * p < 9 * q) (h : basePruned ((a : ℝ) / b) < 18 * log 4) :
    ∃ m₂ : ℕ, ∀ (m₀ : ℕ) (hm₀ : 1 ≤ m₀), m₂ ≤ m₀ →
      Fits18 ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR : (10 : ℝ) < (a : ℝ) / b := (lt_div_iff₀ hbR).2 (by exact_mod_cast hc)
  set c : ℝ := (a : ℝ) / b
  set B : ℝ := (basePruned c + 18 * log 4) / 2 with hBdef
  have hB1 : basePruned c < B := by rw [hBdef]; linarith
  have hgap : 0 < 18 * log 4 - B := by rw [hBdef]; linarith
  obtain ⟨δ₀, hδ₀, hnear⟩ := Metric.eventually_nhds_iff.1
    ((basePruned_continuousOn.continuousAt (Ioi_mem_nhds hcR)).eventually (gt_mem_nhds hB1))
  refine ⟨max ⌈1 / δ₀⌉₊ ⌈18 * log 4 / (18 * log 4 - B)⌉₊, fun m₀ hm₀ hm₂ N D₀ hN hm => ?_⟩
  set m := logFour D₀
  have hm1 : 1 ≤ m := hm₀.trans hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hmδ : 1 / δ₀ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast (le_max_left _ _).trans (hm₂.trans hm))
  have hmB : 18 * log 4 / (18 * log 4 - B) ≤ (m : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans (hm₂.trans hm))
  have hLdef : (parOf ⟨a, b, p, q, m₀, hb, hq, hc, hp, hθ, hm₀⟩ N D₀).L = levelsOf c m := by
    rw [levelsOf_div a _ hb]; rfl
  have hLge : c * m ≤ (levelsOf c m : ℝ) := Nat.le_ceil _
  have hLlt : (levelsOf c m : ℝ) < c * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmL : m < levelsOf c m := by exact_mod_cast (show (m : ℝ) < levelsOf c m by nlinarith)
  have hbase : basePruned ((levelsOf c m : ℝ) / m) < B := by
    refine hnear ?_; rw [Real.dist_eq, abs_lt]
    have := (div_le_iff₀ hδ₀).1 hmδ
    have : c ≤ (levelsOf c m : ℝ) / m := (le_div_iff₀ hm0).2 hLge
    exact ⟨by linarith, by rw [sub_lt_iff_lt_add, div_lt_iff₀ hm0]; nlinarith⟩
  have hexp : (m : ℝ) * B ≤ ((18 * (m - 1) : ℕ) : ℝ) * log 4 := by
    have := (div_le_iff₀ hgap).1 hmB; push_cast [Nat.cast_sub hm1]; linarith
  have hpow : 4 ^ (m - 1) < D₀ := Nat.pow_pred_clog_lt_self (by norm_num) (two_le_of_clog hm1)
  have hNge : (4 : ℝ) ^ (18 * (m - 1)) ≤ N := by
    have h' : (4 ^ (m - 1)) ^ 18 ≤ N := (Nat.pow_le_pow_left hpow.le 18).trans hN
    rw [← pow_mul, mul_comm] at h'; exact_mod_cast h'
  refine ⟨hm1, RatParams.ten_le_L _ _, RatParams.t_le _ _, ?_⟩
  rw [hLdef]
  exact (sqrtKN0_le_exp hm1 hmL).trans <|
    (exp_le_exp.2 (mul_le_mul_of_nonneg_left hbase.le hm0.le)).trans <|
    (exp_le_exp.2 hexp).trans <| (by rw [exp_nat_mul, exp_log (by norm_num)] : _ = (4 : ℝ) ^ _).trans_le hNge

end ImprovedExponents

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec ImprovedExponents

def procsP (G : RatParams) : List Stmt :=
  [Sec3.powLtBody, Sec2.encodePBody Sec2.pEncStep Proc.encodeP, Sec2.encodeBandsPBody,
    Sec2.sharedPBody, preCorePBody,
    .call Proc.log4 [v Pre31.Dim, v Pre31.Free +' k 2] Pre31.Log ;;
      .ite (v Pre31.Log <' k G.m₀) (.store (v Pre31.Free) (k 0))
        (prePad31 ;;
          .call Proc.preCoreP [v Pre31.Levels, v Pre31.Log, v Pre31.Switch, v Pre31.Size,
            v Pre31.Padded, v Pre31.PadX, v Pre31.PadY, v Pre31.Block] Pre31.Res ;;
          .store (v Pre31.Free +' k 1) (v Pre31.Block) ;;
          .store (v Pre31.Free) (k 1)),
    .call Proc.pre31P [v Offline32.Size, v Offline32.Dim, v Offline32.MatX, v Offline32.MatY,
      v Offline32.Free] Offline32.Res ;;
      .for Offline32.Pos (v Offline32.Count) offlineAsk32,
    allBody Proc.powRS Proc.offline32P]

def programP (G : RatParams) : Program := program31 G ++ procsP G

private theorem programPQ_at (G : RatParams) (Q : Program) (n : ℕ) {body : Stmt}
    (hn : 74 ≤ n := by norm_num) (h : (procsP G)[n - 74]? = some body := by rfl) :
    (programP G ++ Q)[n]? = some body := by
  refine getElem?_append_of_eq_some ?_ Q
  rw [programP, List.getElem?_append_right (show (program31 G).length ≤ n from hn),
    show (program31 G).length = 74 from rfl]
  exact h

private theorem programPQ_at31 (G : RatParams) (Q : Program) (n : ℕ) {body : Stmt}
    (hn : 58 ≤ n := by norm_num) (h : (procs31 G)[n - 58]? = some body := by rfl) :
    (programP G ++ Q)[n]? = some body :=
  getElem?_append_of_eq_some (getElem?_append_of_eq_some (program31_at G n hn h) _) Q

private theorem programPQ_eq_base58 (G : RatParams) (Q : Program) :
    programP G ++ Q = base58 ++ (procs31 G ++ procsP G ++ Q) := by
  simp [programP, program31]

private theorem programPQ_eq_program5 (G : RatParams) (Q : Program) :
    programP G ++ Q = Sec2.program5 ++
      (([.skip, Sec2.thinBruteBody, .skip] ++ List.replicate 11 .skip ++ procs40
        ++ [.skip, queryAtBody, .skip, .skip]) ++ (procs31 G ++ procsP G ++ Q)) := by
  rw [programPQ_eq_base58]; simp [base58, Sec2.programThin]

private theorem sharedP_programPQ (G : RatParams) (Q : Program) (lim : Limits) (std : Std lim) :
    Sec2.SharedSpecP lim (programP G ++ Q) cShared30 := by
  have e := programPQ_eq_program5 G Q
  refine Sec2.sharedP_entry std (programPQ_at G Q Proc.sharedP)
    (programPQ_at G Q Proc.encodeBandsP) ?_ ?_ (programPQ_at G Q Proc.encodeP)
    (c := Sec2.cShared5) ?_ (by norm_num [Sec2.cShared5, Sec2.cBandArray, Sec2.cEncP]) le_rfl
  · rw [e]; exact Sec2.at_prefix rfl _
  · rw [e]; exact Sec2.at_prefix rfl _
  · rw [e]; exact Sec2.sharedCallees_of_prefix _ lim std

private theorem preCoreP_programPQ (G : RatParams) (Q : Program) (lim : Limits) :
    PreCoreSpecP lim (programP G ++ Q) cShared30 :=
  fun p t hmL aX aY b0 X Y U μ ht hlim =>
    preCoreP_of_base58 (programPQ_eq_base58 G Q) (programPQ_at G Q Proc.preCoreP)
      (sharedP_programPQ G Q lim hlim.std) p t hmL aX aY b0 X Y U μ ht hlim

abbrev Built31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (fr : ℕ) (μ : ℕ → ℤ) : Prop :=
  DSReadyP (parOf G N D₀) (switchOf31 G D₀) (logFour_le_levels G N D₀) (paddedXAt fr)
    (paddedYAt N D₀ fr) (blockAt N D₀ fr) (padInnerCols (D (logFour D₀)) X)
    (padInnerRows (D (logFour D₀)) Y) μ

structure Ready31P (G : RatParams) {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ)
    (Y : Matrix (Fin D₀) (Fin N) ℤ) (aX aY fr : ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  small : logFour D₀ < G.m₀ → μ fr = 0
  large : G.m₀ ≤ logFour D₀ → μ fr = 1 ∧ μ (fr + 1) = blockAt N D₀ fr ∧ Built31P G X Y fr μ

section Routines

variable {lim : Limits} {G : RatParams} {Q : Program} {N D₀ : ℕ}
  {X : Matrix (Fin N) (Fin D₀) ℤ} {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ}
  {μ μ' : ℕ → ℤ}

private theorem query31P_meets (hin : Input31 lim G X Y aX aY fr U)
    (hR : Ready31P G X Y aX aY fr μ) (I J : Fin N) {d : ℕ} (hd : d + 3 ≤ lim.depth) :
    Meets lim (programP G ++ Q) Proc.query31 d [(I : ℕ), (J : ℕ), N, D₀, aX, aY, fr] μ
      (tQuery31 G D₀) fun r μ' =>
        r = (X * Y) I J ∧ Ready31P G X Y aX aY fr μ' ∧
          SameOutside μ μ' (fr + 3) (structEnd G N D₀ fr - (fr + 3)) := by
  have hlim := hin.lim; have bX := hin.belowX; have bY := hin.belowY
  refine ⟨query31Body, programPQ_at31 G Q Proc.query31, ?_⟩
  have hw := hlim.std.space_le; have hU0 := hin.zero_le_U
  have hfr3 := add_three_le_structEnd G N D₀ fr; have hsp := hlim.space
  refine Ends.iteLast (fun hflag => ?_) (fun hflag => ?_) (hT := by simp [tQuery31])
  · have hlarge : G.m₀ ≤ logFour D₀ := by
      by_contra hc; have := hR.small (by omega); have : μ fr = 1 := by simpa using hflag
      omega
    obtain ⟨h1, hbase, hDS⟩ := hR.large hlarge
    have haddr : ((fr : ℤ) + 1).toNat = fr + 1 := by omega
    refine Ends.callTo
      (queryAtP_of_base58 (programPQ_eq_base58 G Q) (parOf G N D₀) (switchOf31 G D₀)
        (logFour_le_levels G N D₀) (paddedXAt fr) (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ I J
        (G.t_le _) (hlim.large hlarge) (abs_padInnerCols_le hin.absX hU0)
        (abs_padInnerRows_le hin.absY hU0) hDS _ (by omega)) ?_
      (by light_side [haddr, hbase])
      (hT := by simp [tQuery31, ite_eq_right (not_lt.mpr hlarge), parOf]; omega)
    rintro r μ' ⟨hr, hDS', hout⟩
    have hscratch := G.scratch_in_block N D₀ fr
    have hb0 := add_three_le_blockAt N D₀ fr
    have htop := structEnd_large hlarge N fr
    have hkept (a : ℕ) (ha : a < blockAt N D₀ fr) : μ' a = μ a := hout a (by omega)
    exact ⟨hr.trans (congrFun (congrFun (Corollary26.padding _ (le_D_logFour D₀) X Y) I) J),
      ⟨hR.matX.congr_below hkept (by omega), hR.matY.congr_below hkept (by omega),
        fun hm' => absurd hlarge (by omega),
        fun _ => ⟨(hkept _ (by omega)).trans h1, (hkept _ (by omega)).trans hbase, hDS'⟩⟩,
      fun a ha => hout a (by omega)⟩
  · have hsmall : logFour D₀ < G.m₀ := by
      by_contra hc; exact hflag (by simpa using (hR.large (by omega)).1)
    refine Ends.callTo (ipAt_meets (programPQ_at31 G Q Proc.ipAt) hlim.std N D₀ aX aY X Y U μ I J
      hin.one_le_D hR.matX hR.matY hin.absX hin.absY (by omega) (by omega) hlim.ip _ (by omega)) ?_
      (hT := by simp [tQuery31, ite_eq_left hsmall]; omega)
    rintro r μ' ⟨hr, rfl⟩
    exact ⟨hr, hR, .refl⟩

private theorem prePad31_endsP {d : ℕ} (h : PreInput31 lim G X Y aX aY fr U μ)
    (hm : G.m₀ ≤ logFour D₀) (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) :
    Ends lim (programP G ++ Q) d prePad31
      ⟨frame [N, D₀, aX, aY, fr, logFour D₀], Function.update μ (fr + 2) ((D (logFour D₀) : ℕ) : ℤ)⟩
      (tPrePad31 G N D₀) (Padded31 G X Y aX aY fr μ) := by
  have A := h.areas hm; have std := h.lim.std
  have hcopy := copy_ok (programPQ_at31 G Q Proc.copy) std
  have hfill := fill_ok (programPQ_at31 G Q Proc.fill) std
  unfold prePad31 tPrePad31 Padded31 paddedXAt paddedYAt
  rw [A.base]
  generalize D (logFour D₀) = F at A ⊢; generalize (F - D₀) * N = R at A ⊢
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁, μ₁ = Function.update μ (fr + 2) ((F : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hμ₁]
  obtain ⟨-, hR, hb0, hb0lt, hDF, hrows, hFN⟩ := A
  have hw := std.space_le; have h100 := std.const_le; have hD := h.one_le_D
  have hbX := h.belowX; have hbY := h.belowY
  have hRZ : ((F : ℤ) - D₀) * N = R := by rw [hR]; push_cast [Nat.cast_sub hDF]; rfl
  have hread : μ₁ (fr + 2) = F := by rw [hμ₁]; exact Function.update_self ..
  have hout₁ : SameOutside μ μ₁ (fr + 2) 1 := hμ₁ ▸ SameOn.refl.write (by omega) _
  have hkept₁ : ∀ b < fr, μ₁ b = μ b := fun b hb => hout₁ b (.inl (by omega))
  have haddr : ((fr : ℤ) + 2).toNat = fr + 2 := by omega
  light_set F using haddr, hread
  light_call (ceilMul_meets G.hb (programPQ_at31 G Q Proc.levels31) (logFour D₀) μ₁ h.lim.wordL _
    (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  light_call (ceilMul_meets G.hq (programPQ_at31 G Q Proc.switch31) (logFour D₀) μ₁ h.lim.wordT _
    (by omega)) with _ μ₁ ⟨rfl, rfl⟩
  light_set (fr + 3 : ℕ); light_set (N * F : ℕ)
  light_set (fr + 3 + N * F : ℕ); light_set (fr + 3 + N * F + N * F : ℕ)
  light_call (padX_meets (programPQ_at31 G Q Proc.padX) hcopy hfill std N D₀ F aX (fr + 3) X μ₁ hDF
    (by omega) (h.matX.congr_below hkept₁ hbX) (by omega) (by omega) _ (by omega))
    with - μ₂ ⟨hpadX, hout₂⟩
  light_call (hcopy aY (fr + 3 + N * F) (D₀ * N) μ₂ (by omega) (by omega) (by omega)
    (.inl (by omega)) _ (by omega)) with - μ₃ ⟨hc, hout₃⟩
  light_call (hfill (fr + 3 + N * F + D₀ * N) R 0 μ₃ (by omega) (by omega) _ (by omega))
    using hRZ with r μ₄ ⟨hf, hout₄⟩
  refine ⟨r, μ₄, rfl, hpadX.congr fun b _ hb => by
    rw [hout₄ b (.inl (by omega)), hout₃ b (.inl (by omega))], ?_, fun b hb => by
    rw [hout₄ b (by omega), hout₃ b (by omega), hout₂ b (by omega), hout₁ b (by omega)]⟩
  refine matAt_padInnerRows (h.matY.congr_below hkept₁ hbY) (fun i hi => ?_) (hR ▸ hf)
  rw [hout₄ _ (.inl (by omega)), hc i hi, hout₂ _ (.inl (by omega))]

private theorem pre31P_meets (hin : Input31 lim G X Y aX aY fr U)
    (mX : MatAt μ aX X) (mY : MatAt μ aY Y) {d : ℕ} (hd : d + (G.L (logFour D₀) + 7) ≤ lim.depth) :
    Meets lim (programP G ++ Q) Proc.pre31P d [N, D₀, aX, aY, fr] μ (tPre31P cShared30 G N D₀)
      fun _ μ' => Ready31P G X Y aX aY fr μ' ∧ SameOutside μ μ' fr (structEnd G N D₀ fr - fr) := by
  have h : PreInput31 lim G X Y aX aY fr U μ := ⟨hin, mX, mY⟩
  have hlim := hin.lim; have hw := hlim.std.space_le; have hfr3 := add_three_le_structEnd G N D₀ fr; have hsp := hlim.space
  have hm₀word := hlim.m0word
  have hmword : (logFour D₀ : ℤ) ≤ lim.word := by
    have : logFour D₀ ≤ G.a * logFour D₀ := Nat.le_mul_of_pos_left _ (by have := G.hc; omega)
    exact le_trans (by exact_mod_cast (by omega :
      logFour D₀ ≤ G.a * logFour D₀ + G.b + G.p * logFour D₀ + G.q)) hlim.mword
  refine ⟨_, programPQ_at G Q Proc.pre31P, ?_⟩
  refine Ends.callToThen (log4_meets (programPQ_at31 G Q Proc.log4) hlim.std D₀ (fr + 2) μ
    (by omega) hlim.pow hmword _ (by omega)) ?_ (hT := by simp [tPre31P, logFour]; omega)
  rintro _ _ ⟨rfl, rfl⟩
  refine Ends.iteLast (fun hsmall => ?_) (fun hlarge => ?_) (hT := by simp [tPre31P, logFour]; omega)
  · have hm : logFour D₀ < G.m₀ := by simpa [logFour] using hsmall
    have htop : structEnd G N D₀ fr - fr = 3 := by rw [structEnd_small hm]; omega
    refine Ends.storeTo fr 0 ⟨⟨h.matX.congr_below (fun b hb => ?_) h.belowX,
      h.matY.congr_below (fun b hb => ?_) h.belowY, fun _ => Function.update_self ..,
      fun hm' => absurd hm' (by omega)⟩, ?_⟩ (hT := by simp [tPre31P, logFour]; omega)
    · change Function.update (Function.update μ _ _) fr 0 b = μ b
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · change Function.update (Function.update μ _ _) fr 0 b = μ b
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    · rw [htop]; exact (SameOn.refl.write (by omega) _).write (by omega) _
  · have hm : G.m₀ ≤ logFour D₀ := by simpa [logFour] using hlarge
    refine Ends.next (tPrePad31 G N D₀) ((prePad31_endsP h hm hd).mono le_rfl fun σ hσ => ?_)
      (by simp only [tPre31P, tPrePad31, ite_eq_right (not_lt.mpr hm)]; simp [logFour]; omega)
    obtain ⟨r, μ₄, rfl, pmX, pmY, hout₄⟩ := hσ
    have hb0 := (h.areas hm).base; have hb0lt := (h.areas hm).base_lt
    have hb0top := G.blockAt_lt_blockEnd N D₀ fr
    refine Ends.mono (T := tPreCoreP cShared30 (parOf G N D₀) (switchOf31 G D₀) + 60)
      (Q := fun σ' => Ready31P G X Y aX aY fr σ'.mem ∧ SameOutside μ σ'.mem fr (structEnd G N D₀ fr - fr))
      ?_ (by simp only [tPre31P, tPrePad31, ite_eq_right (not_lt.mpr hm)]; simp [logFour]; omega)
      fun _ hQ => hQ
    light_call (preCoreP_programPQ G Q lim (parOf G N D₀) (switchOf31 G D₀)
      (logFour_le_levels G N D₀) (paddedXAt fr) (paddedYAt N D₀ fr) (blockAt N D₀ fr) _ _ U μ₄
      (G.t_le _) (hlim.large hm) (abs_padInnerCols_le h.absX h.zero_le_U)
      (abs_padInnerRows_le h.absY h.zero_le_U) pmX pmY
      (by change fr + 3 + N * D (logFour D₀) ≤ _; omega)
      (by change fr + 3 + N * D (logFour D₀) + D (logFour D₀) * N ≤ _
          rw [Nat.mul_comm (D (logFour D₀)) N]; omega) _
      (by change d + 1 + (G.L (logFour D₀) + 6) ≤ _; omega)) using parOf, switchOf31, Sec2.Par.D
      with - μ₅ ⟨hDS, hout₅⟩
    have hout₅' : SameOutside μ₄ μ₅ (blockAt N D₀ fr) (G.blockEnd N D₀ fr - blockAt N D₀ fr) := hout₅
    light_store (fr + 1) (blockAt N D₀ fr)
    light_store fr 1
    dsimp only
    have hsame : SameOutside μ μ₅ fr (structEnd G N D₀ fr - fr) := by
      rw [structEnd_large hm]
      exact fun b hb => (hout₅' b (by omega)).trans (hout₄ b (by omega))
    have hkept (b : ℕ) (hb : b < fr) :
        Function.update (Function.update μ₅ (fr + 1) (blockAt N D₀ fr)) fr 1 b = μ b := by
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hsame b (.inl hb)]
    exact ⟨⟨h.matX.congr_below hkept h.belowX, h.matY.congr_below hkept h.belowY,
      fun hm' => absurd hm (by omega), fun _ => ⟨Function.update_self ..,
        by rw [Function.update_of_ne (by omega), Function.update_self],
        dsReadyP_congr hDS fun a ha => by
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]⟩⟩,
      (hsame.write (by omega) _).write (by omega) _⟩

private theorem ready31P_congr (h : Ready31P G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31P G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => (hfr _ le_rfl).trans (h.small hs), fun hl => ?_⟩
  · rw [hX _ (by omega) (by have := Nat.mul_add_le_mul i.isLt (le_refl D₀); omega)]
    exact h.matX i j
  · rw [hY _ (by omega) (by have := Nat.mul_add_le_mul i.isLt (le_refl N); omega)]
    exact h.matY i j
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    exact ⟨by grind, by grind, dsReadyP_congr h3 fun a ha => hfr a (by unfold blockAt at ha; omega)⟩

private theorem offline32P_meets {aI aJ out d : ℕ} {u : ℤ} {WI WJ : List ℕ}
    (hg : Input31 lim G X Y aX aY fr U) (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ)
    (hd : d + (G.L (logFour D₀) + 8) ≤ lim.depth) :
    Meets lim (programP G ++ Q) Proc.offline32P d [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ
      (tOffline32P cShared30 G N D₀ WI.length) fun _ μ' =>
        Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
          ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a := by
  refine ⟨_, programPQ_at G Q Proc.offline32P, ?_⟩
  have hw := hg.lim.std.space_le; have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq; have hout := hin.out_le
  have hrows := hin.rows_le; have hcols := hin.cols_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  refine Ends.callToThen (pre31P_meets hg hin.matX hin.matY (by omega)) ?_
    (hT := by simp [tOffline32P]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31P G X Y aX aY fr) (· < fr) out
        ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done (by rintro _ _ - - ⟨_, _, rfl, -⟩; simp)
    (hT := by simp [tOffline32P]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    exact ⟨hinv.all, fun a ha hoff => hinv.same a ⟨by simpa [hlen] using hoff, ha⟩⟩
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    have hiJ : i < WJ.length := by omega
    have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
    have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
    have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
      (hinv.read hin.rows (j := i) (by simpa using hi)
        (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
    have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
      (hinv.read hin.cols (j := i) (by simpa using hiJ)
        (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
    have hround : Ends lim (programP G ++ Q) d offlineAsk32
        ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ (tQuery31 G D₀ + 20)
        fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
          σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
          Answered (Ready31P G X Y aX aY fr) (· < fr) out
            ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
      refine Ends.callToThen (query31P_meets hg hinv.ready ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ (by omega))
        (fun _ μ₂ ⟨rfl, hready', hquery⟩ => ?_) (ha := by light_side [hrow, hcol])
      light_store (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩)
      have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
        (fun a ha => Or.inl (by omega)) (ready31P_congr hready'
          (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
          (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
          fun a ha => Function.update_of_ne (by omega) _ _)
      rw [List.getElem_map, List.getElem_zip, entryN, dite_eq_left ⟨hIN, hJN⟩] at hstep
      exact ⟨_, _, rfl, hstep⟩
    refine hround.mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Routines

end Light.Sec4

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3 Light.Sec4

open Classical in
noncomputable def allTimeP (G : RatParams) : List ℕ → ℕ
  | [N, D, w, _] => 370 + if D ^ 18 ≤ N then tOffline32P cShared30 G N D w else 40 * ((w + 1) * (D + 1))
  | _ => 0

open Classical in
theorem thinClaim_programP {G : RatParams} {ε γ q : ℝ} (hfit : Fits18 G) (hε : ε ≤ 1 / 18)
    (h : OfflineWithinT (tOffline32P cShared30 G) ε γ q) : ThinClaim lightModel ε γ q := by
  obtain ⟨A, hA⟩ := h
  refine ⟨A, fun N D₀ w _ => (allTimeP G [N, D₀, w, 0] : ℝ),
    ⟨programP G, Proc.allP, allTimeP G, offline32Need G, offline32Need_poly G,
      ⟨allBody Proc.powRS Proc.offline32P, ?_, fun Q lim d (x : ThinInst) μ fr (hpre : x.Pre μ fr) ok => ?_⟩,
      fun N D₀ w w' U _ _ _ _ hw _ => ?_⟩,
    fun N D₀ w _ hN hD hDN => ?_⟩
  · simpa using programPQ_at G [] Proc.allP
  · have ok' : (offline32Need G [x.N, x.D, x.w, x.U]).Ok lim fr d := ok
    have hword := ok'.word; have hcells := ok'.cells; have hdepth := ok'.depth
    simp only [offline32Need] at hword hcells hdepth
    have fits (n : ℕ) (hn : n ≤ 1000 + 100 * x.D + x.N * x.D + x.D * (x.U * x.U)) :
        (n : ℤ) ≤ lim.word := le_trans (by omega) hword
    have h100 := fits 100 (by omega)
    have hpow := powLt_meets (lim := lim) (P := programP G ++ Q) (d := d + 1) (μ := μ)
      (g := x.D) (e := 18) (t := x.N + 1) (programPQ_at G Q Proc.powRS) hpre.D_pos
      (fits _ (by nlinarith))
    have hsp := ok'.space; change Ends lim (programP G ++ Q) d (allBody Proc.powRS Proc.offline32P)
      ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩
      (370 + if x.D ^ 18 ≤ x.N then tOffline32P cShared30 G x.N x.D x.w
        else 40 * ((x.w + 1) * (x.D + 1))) _
    unfold allBody
    refine Ends.callToThen hpow (fun r μ' ⟨hr, hμ⟩ => ?_)
      (ha := by light_side) (hd := by omega) (hT := by simp; omega)
    subst μ'
    have hrw : |r| ≤ lim.word := by
      rw [hr]; split_ifs <;> [simpa using fits 1 (by omega); exact le_trans (by norm_num) h100]
    have := hpre.belowX; have := hpre.belowY; have := hpre.belowWI; have := hpre.belowWJ
    have := hpre.belowOut
    refine Ends.iteLast (fun hpos => ?_) (fun hneg => ?_) (hs := by light_side)
    · have hreg : x.D ^ 18 ≤ x.N := by
        split_ifs at hr with hlt <;> [omega; simp [hr, frame, setLocal] at hpos]
      rw [ite_eq_left hreg]
      have hU0 : (0 : ℤ) ≤ (x.U : ℤ) := by positivity
      have hL : G.L (logFour x.D) ≤ G.a * (4 * x.D) :=
        (ratParams_L_le_mul G _).trans (Nat.mul_le_mul_left _ (logFour_le_four_mul hpre.D_pos))
      have spec := offline32P_meets (Q := Q) (X := thinMX x) (Y := thinMY x) (u := x.U) (d := d + 1)
        ⟨hpre.D_pos, hpre.N_pos, lim31_of_need hpre.D_pos (hfit _ _ hreg) ok',
          fun _ _ => hpre.leX.abs_getD_le hU0 _, fun _ _ => hpre.leY.abs_getD_le hU0 _,
          hpre.belowX, hpre.belowY⟩
        ⟨matAt_thinMX hpre, matAt_thinMY hpre, hpre.segWI, hpre.segWJ,
          by rw [hpre.lenWI, hpre.lenWJ], hpre.ltWI, hpre.ltWJ,
          hpre.lenWI ▸ hpre.belowWI, hpre.lenWI ▸ hpre.belowWJ, hpre.lenWI ▸ hpre.belowOut,
          hpre.lenWI ▸ hpre.apartX, hpre.lenWI ▸ hpre.apartY, hpre.lenWI ▸ hpre.apartWI,
          hpre.lenWI ▸ hpre.apartWJ⟩ (by omega)
      rw [hpre.lenWI, map_entryN_thin hpre] at spec
      exact Ends.callTo (spec.mono le_rfl fun r μ' h => ⟨h.1, fun a ha => h.2 a ha.1 ha.2⟩)
        (fun _ _ h => h) (ha := by light_side)
    · have hreg : ¬ x.D ^ 18 ≤ x.N := fun hle => by
        rw [ite_eq_left (by omega : x.D ^ 18 < x.N + 1)] at hr; simp [hr, frame, setLocal] at hneg
      rw [ite_eq_right hreg]
      exact Ends.callTo (.of_body
          (by rw [programPQ_eq_base58]; exact at_base58 rfl _)
          (Sec2.thinBrute_spec ⟨ok'.space, h100⟩ x μ fr (x.U : ℤ) hpre (by omega)
            (fits _ (by omega))))
        (fun _ _ h => h) (ha := by light_side)
  · simp only [allTimeP]; norm_cast; split_ifs
    · unfold tOffline32P
      have := Nat.mul_le_mul_right (tQuery31 G D₀ + 30) hw; omega
    · have := Nat.mul_le_mul_right (D₀ + 1) (show w + 1 ≤ w' + 1 by omega); omega
  · simp only [allTimeP, ite_eq_left (pow18_le_of_le_rpow hε hN hDN)]
    push_cast; linarith [hA N D₀ w hN hD hDN]

end ImprovedExponents
