module

public import ImprovedExponents.AllEdges.Pairs.Bridge
public import ImprovedExponents.AllEdges.Chain
public import ThreeSumApsp.Programs.Sec3.Theorem21b.NegativeTriangle.Passes
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-! ## The pairsAE host program -/

def paInit : Stmt :=
  .set 7 (v 0 *' v 0) ;; .set 12 (k 3 *' v 1) ;; .set 22 (k 9 *' v 1) ;;
  .set 13 (v 6 +' v 7) ;; .set 14 (v 13 +' v 7) ;; .set 15 (v 14 +' v 7) ;;
  .set 16 (v 15 +' v 7) ;; .set 17 (v 16 +' v 7) ;; .set 18 (v 17 +' v 7) ;;
  .set 19 (v 18 +' v 7) ;; .set 20 (v 19 +' v 7) ;; .set 21 (k 3 *' v 7) ;;
  .set 8 (k 1) ;; .set 9 (k 0)

def paPow : Stmt := .while (v 8 ≤' v 12) (.set 8 (k 2 *' v 8) ;; .set 9 (v 9 +' k 1))

def paFill (pAff pTr : ℕ) : Stmt :=
  .call pAff [v 7, v 2, k 1, v 1, v 15] 11 ;;
  .call pTr [v 0, v 3, v 1, v 16] 11 ;;
  .call pAff [v 7, v 4, k 1, k 2 *' v 1, v 17] 11 ;;
  .call pAff [v 21, v 15, k 0, k 0, v 6] 11 ;;
  .call pAff [v 7, v 2, k 0, k 0, v 5] 11

def paProbe (pAE pAff pOr e : ℕ) : Stmt :=
  .call pAff [v 7, v 14, k 0 -' k 1, k e, v 18] 11 ;;
  .call pAE [v 0, v 22, v 18, v 13, v 6, v 19, v 20] 11 ;;
  .call pOr [v 7, v 19, v 5] 11

def paRound (pAE pAff pOr pDown : ℕ) : Stmt :=
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;; .call pDown [v 21, v 6, v 15, v 8] 11

def paBody (pAE pAff pTr pOr pDown : ℕ) : Stmt :=
  paInit ;; paPow ;; paFill pAff pTr ;; .for 10 (v 9) (paRound pAE pAff pOr pDown) ;;
  paProbe pAE pAff pOr 2 ;; paProbe pAE pAff pOr 3 ;; paProbe pAE pAff pOr 1 ;; .set 0 (k 0)

def pairsTimeAE (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  (2 * aeLevels U + 3) * (T n (9 * U) + 108 * (n * n) + 60) + 200 * (n * n) + 150

def pairsNeedAE (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨24 * U + 8 + (r n (9 * U)).word, 8 * (n * n) + (r n (9 * U)).cells, (r n (9 * U)).depth + 1⟩

namespace PairsHost

abbrev locals (x : PairsInst) (fr : ℕ) (pw lv rd res : ℤ) : List ℤ :=
  [x.n, x.U, x.x, x.y, x.v, x.out, fr, (x.n * x.n : ℕ), pw, lv, rd, res, (3 * x.U : ℕ),
    (fr + x.n * x.n : ℕ), (fr + 2 * (x.n * x.n) : ℕ), (fr + 3 * (x.n * x.n) : ℕ),
    (fr + 4 * (x.n * x.n) : ℕ), (fr + 5 * (x.n * x.n) : ℕ), (fr + 6 * (x.n * x.n) : ℕ),
    (fr + 7 * (x.n * x.n) : ℕ), (fr + 8 * (x.n * x.n) : ℕ), (3 * (x.n * x.n) : ℕ), (9 * x.U : ℕ)]

structure Ctx (P₀ R' : Program) (p pAff pTr pOr pDown : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  solver : Solves aeTask P₀ p T r
  aff : (P₀ ++ R')[pAff]? = some affineBody
  tr : (P₀ ++ R')[pTr]? = some transposeBody
  orp : (P₀ ++ R')[pOr]? = some orBody
  down : (P₀ ++ R')[pDown]? = some prefDownBody
  pre : x.Pre μ fr
  ok : (pairsNeedAE r x.n x.U).Ok lim fr d

variable {P₀ R' : Program} {p pAff pTr pOr pDown : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
  {lim : Limits} {d : ℕ} {x : PairsInst} {μ : ℕ → ℤ} {fr : ℕ}

abbrev Z (x : PairsInst) : List ℤ := pStart x.n x.U x.X x.Y x.V

def hit (x : PairsInst) (c : ℕ × ℤ) (q : ℕ) : Prop :=
  (aeFlags x.n (instAB x.U x.V c.1 c.2) (instBC x.n x.U x.Y c.1) (instAC x.U x.X c.1)).getD q 0 = 1

private theorem Ctx.places (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    ((lim.space : ℤ) ≤ lim.word ∧ 24 * (x.U : ℤ) + 8 + (r x.n (9 * x.U)).word ≤ lim.word ∧
      fr + (8 * (x.n * x.n) + (r x.n (9 * x.U)).cells) ≤ lim.space ∧
      d + ((r x.n (9 * x.U)).depth + 1) ≤ lim.depth) ∧ 1 ≤ x.n * x.n ∧ 1 ≤ x.U ∧
      (x.X.length = x.n * x.n ∧ x.Y.length = x.n * x.n ∧ x.V.length = x.n * x.n) ∧
      x.x + x.n * x.n ≤ fr ∧ x.y + x.n * x.n ≤ fr ∧ x.v + x.n * x.n ≤ fr ∧
      x.out + x.n * x.n ≤ fr ∧ (Z x).length = 3 * (x.n * x.n) ∧
      3 * x.U < 2 ^ aeLevels x.U ∧ 2 ^ aeLevels x.U ≤ 6 * x.U :=
  ⟨⟨C.ok.space, by exact_mod_cast C.ok.word, C.ok.cells, C.ok.depth⟩,
    Nat.mul_pos C.pre.n_pos C.pre.n_pos, C.pre.U_pos, ⟨C.pre.lenX, C.pre.lenY, C.pre.lenV⟩,
    C.pre.belowX, C.pre.belowY, C.pre.belowV, C.pre.belowOut,
    length_pStart C.pre.lenX C.pre.lenV, lt_two_pow_aeLevels _, two_pow_aeLevels_le C.pre.U_pos⟩

private theorem Ctx.affine_meets (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {μ' : ℕ → ℤ}
    {l : List ℤ} {src dst : ℕ} {m c : ℤ} (hl : Seg μ' src l)
    (hplace : src + l.length ≤ fr + 8 * (x.n * x.n) ∧ dst + l.length ≤ fr + 8 * (x.n * x.n) ∧
      (src + l.length ≤ dst ∨ dst + l.length ≤ src))
    (hfits : ∀ w ∈ l, |m * w| ≤ lim.word ∧ |m * w + c| ≤ lim.word) :
    Meets lim (P₀ ++ R') pAff (d + 1) [l.length, src, m, c, dst] μ' (20 * l.length + 6)
      fun _ μ'' => Seg μ'' dst (affL m c l) ∧ SameOutside μ' μ'' dst l.length := by
  have := C.places
  exact Sec3.affine_meets C.aff hl C.ok.space (by omega) (by omega) hplace.2.2 hfits

private theorem init_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paInit ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ paInit.blockCost
      fun σ' => σ' = ⟨frame (locals x fr 1 0 0 0), μ⟩ := by
  have := C.places
  unfold paInit
  light_set (x.n * x.n : ℕ); light_set (3 * x.U : ℕ); light_set (9 * x.U : ℕ)
  light_set (fr + x.n * x.n : ℕ); light_set (fr + 2 * (x.n * x.n) : ℕ)
  light_set (fr + 3 * (x.n * x.n) : ℕ); light_set (fr + 4 * (x.n * x.n) : ℕ)
  light_set (fr + 5 * (x.n * x.n) : ℕ); light_set (fr + 6 * (x.n * x.n) : ℕ)
  light_set (fr + 7 * (x.n * x.n) : ℕ); light_set (fr + 8 * (x.n * x.n) : ℕ)
  light_set (3 * (x.n * x.n) : ℕ); light_set 1; light_set 0
  rfl

private theorem pow_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d paPow ⟨frame (locals x fr 1 0 0 0), μ⟩ (14 * aeLevels x.U + 6)
      fun σ' => σ' = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 0), μ⟩ := by
  have hplaces := C.places
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (locals x fr (2 ^ i : ℕ) i 0 0), μ⟩)
    (aeLevels x.U) (by simp) ?round ?done (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hpow : 2 ^ (i + 1) ≤ 2 ^ aeLevels x.U := Nat.pow_le_pow_right (by norm_num) hi
    have hlt : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
    rw [pow_succ'] at hpow hlt
    generalize hpw : 2 ^ i = pw at hpow hlt ⊢
    exact ⟨by light_side, by simp; omega, by light_side,
      by simp [pow_succ', hpw, update_frame_setLocal, locals]⟩
  case done =>
    rintro _ rfl
    generalize 2 ^ aeLevels x.U = pw at hplaces ⊢
    exact ⟨by light_side, by simp; omega, rfl⟩

def PMem (x : PairsInst) (μ : ℕ → ℤ) (fr ℓ : ℕ) (S : ℕ × ℤ → Prop) (μ' : ℕ → ℤ) : Prop :=
  Seg μ' fr ((Z x).map (prefQ ℓ)) ∧
    Seg μ' (fr + 3 * (x.n * x.n)) ((Z x).map (prefR (aeLevels x.U) ℓ)) ∧
    Seg μ' x.out (orFlags (x.n * x.n) S (hit x)) ∧ KeptBut μ μ' fr x.out (x.n * x.n)

private theorem Z_range (hpre : x.Pre μ fr) :
    ∀ z ∈ Z x, 0 ≤ z ∧ z ≤ 3 * (x.U : ℤ) ∧ z < 2 ^ aeLevels x.U := fun z hz => by
  obtain ⟨h0, h1⟩ := pStart_range hpre.leX hpre.leY hpre.leV hpre.lenY z hz
  have h2 : ((3 * x.U : ℕ) : ℤ) < ((2 ^ aeLevels x.U : ℕ) : ℤ) := by
    exact_mod_cast lt_two_pow_aeLevels x.U
  grind

private theorem seg_parts (hpre : x.Pre μ fr) {μ' : ℕ → ℤ} {ℓ : ℕ}
    (hq : Seg μ' fr ((Z x).map (prefQ ℓ))) :
    Seg μ' fr (instAC x.U x.X ℓ) ∧ Seg μ' (fr + x.n * x.n) (instBC x.n x.U x.Y ℓ) ∧
      Seg μ' (fr + 2 * (x.n * x.n)) ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)) := by
  simp  [pStart] at hq
  rw [seg_append, seg_append] at hq
  simp  [hpre.lenX] at hq
  rwa [show fr + x.n * x.n + x.n * x.n = fr + 2 * (x.n * x.n) by omega] at hq

private theorem fill_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) (pw lv rd res : ℤ) :
    Ends lim (P₀ ++ R') d (paFill pAff pTr) ⟨frame (locals x fr pw lv rd res), μ⟩
      (170 * (x.n * x.n) + 70) fun σ' => ∃ res' μ',
        σ' = ⟨frame (locals x fr pw lv rd res'), μ'⟩ ∧
          PMem x μ fr (aeLevels x.U) (fun _ => False) μ' := by
  have hpre := C.pre; have hplaces := C.places; have hZ := Z_range hpre
  have hn := Nat.le_mul_self x.n; have hapX := hpre.apartX
  have hW : 24 * (x.U : ℤ) + 8 ≤ lim.word := by omega
  have hfit1 (c : ℤ) (hc : c = x.U ∨ c = 2 * x.U) (w : ℤ) (hw : w ∈ x.V ++ x.X) :
      |1 * w| ≤ lim.word ∧ |1 * w + c| ≤ lim.word := by
    have := abs_le.1 ((List.mem_append.1 hw).elim (hpre.leV w) (hpre.leX w))
    simp only [one_mul, abs_le]; rcases hc with rfl | rfl <;> omega
  unfold paFill
  refine Ends.callToThen (C.affine_meets (m := 1) (c := x.U) (dst := fr + 3 * (x.n * x.n))
    hpre.segX (by omega) fun w hw => hfit1 _ (Or.inl rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenX]) (hT := by simp [hpre.lenX]; omega)
  rintro r₁ μ₁ ⟨s₁, o₁⟩
  refine Ends.callToThen (transpose_meets C.tr (dst := fr + 4 * (x.n * x.n)) (c := x.U)
    hpre.segY.keep hpre.lenY (by omega) ⟨C.ok.space, by omega, by omega⟩ fun w hw => by
      have := abs_le.1 (hpre.leY w hw); rw [abs_le]; omega) ?_
    (ha := by light_side) (hT := by simp [hpre.lenX]; omega)
  rintro r₂ μ₂ ⟨s₂, o₂⟩
  refine Ends.callToThen (C.affine_meets (m := 1) (c := 2 * x.U) (dst := fr + 5 * (x.n * x.n))
    hpre.segV.keep (by omega) fun w hw => hfit1 _ (Or.inr rfl) w (by simp [hw])) ?_
    (ha := by light_side [hpre.lenV]) (hT := by simp [hpre.lenX, hpre.lenV]; omega)
  rintro r₃ μ₃ ⟨s₃, o₃⟩
  have sZ : Seg μ₃ (fr + 3 * (x.n * x.n)) (Z x) := by
    rw [Z, pStart, seg_append, seg_append]
    simp only [length_affL, length_transposeL, hpre.lenX]
    rw [show fr + 3 * (x.n * x.n) + x.n * x.n = fr + 4 * (x.n * x.n) by omega,
      show fr + 4 * (x.n * x.n) + x.n * x.n = fr + 5 * (x.n * x.n) by omega]
    exact ⟨s₁.keep, s₂.keep, s₃⟩
  refine Ends.callToThen (C.affine_meets (m := 0) (c := 0) (dst := fr) sZ (by omega)
    fun _ _ => by simp; omega) ?_ (ha := by light_side) (hT := by simp; omega)
  rintro r₄ μ₄ ⟨s₄, o₄⟩
  refine Ends.callTo (C.affine_meets (m := 0) (c := 0) (dst := x.out) hpre.segX.keep (by omega)
    fun _ _ => by simp; omega) ?_ (ha := by light_side [hpre.lenX]) (hT := by simp [hpre.lenX]; omega)
  rintro r₅ μ₅ ⟨s₅, o₅⟩
  exact ⟨r₅, μ₅, rfl,
    by rw [map_prefQ_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]; exact s₄.keep,
    by rw [map_prefR_start fun z hz => ⟨(hZ z hz).1, (hZ z hz).2.2⟩]; exact sZ.keep,
    by rw [orFlags_false _ _ hpre.lenX]; exact s₅, fun _ _ => by light_keep⟩

def question (x : PairsInst) (fr ℓ : ℕ) (e : ℤ) : AeInst :=
  ⟨x.n, 9 * x.U, fr + 6 * (x.n * x.n), fr + x.n * x.n, fr, fr + 7 * (x.n * x.n),
    instAB x.U x.V ℓ e, instBC x.n x.U x.Y ℓ, instAC x.U x.X ℓ⟩

def St (x : PairsInst) (μ : ℕ → ℤ) (fr : ℕ) (rd : ℤ) (ℓ : ℕ) (S : ℕ × ℤ → Prop) (σ : State) : Prop :=
  ∃ (res : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) rd res), μ'⟩ ∧ PMem x μ fr ℓ S μ'

abbrev probeTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 51 * (x.n * x.n) + 35 + T x.n (9 * x.U)

private theorem probe_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ e : ℕ}
    (he : 1 ≤ e ∧ e ≤ 3) {rd : ℤ} {S : ℕ × ℤ → Prop} {σ : State} (hσ : St x μ fr rd ℓ S σ) :
    Ends lim (P₀ ++ R') d (paProbe p pAff pOr e) σ (probeTime T x)
      (St x μ fr rd ℓ (fun c => S c ∨ c = (ℓ, (e : ℤ)))) := by
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ
  have hpre := C.pre; have hplaces := C.places
  have he' : 1 ≤ (e : ℤ) ∧ (e : ℤ) ≤ 3 := by omega
  have hlenV : ((affL 1 (2 * x.U) x.V).map (prefQ ℓ)).length = x.n * x.n := by simp [hpre.lenV]
  have hV3 := (absLe_pStart_parts hpre.leX hpre.leY hpre.leV hpre.lenY ℓ).2.2
  have h01 (f : ℤ) (hf : f ∈ aeFlags x.n (instAB x.U x.V ℓ e) (instBC x.n x.U x.Y ℓ) (instAC x.U x.X ℓ)) :
      f = 0 ∨ f = 1 := by
    simp only [aeFlags, List.mem_map] at hf; obtain ⟨_, -, rfl⟩ := hf; unfold flag; split_ifs <;> simp
  unfold paProbe
  refine Ends.callToThen (C.affine_meets (m := -1) (c := e) (dst := fr + 6 * (x.n * x.n))
    (seg_parts hpre hq).2.2 (by omega) fun w hw => by have := hV3 w hw; simp [abs_le]; omega) ?_
    (ha := by light_side [hlenV]) (hT := by simp [hlenV, probeTime]; omega)
  rintro r₁ μ₁ ⟨hthird, h₁⟩
  rw [hlenV] at h₁
  have hq₁ : Seg μ₁ fr ((Z x).map (prefQ ℓ)) := hq.keep (by light_keep)
  obtain ⟨hqX, hqY, -⟩ := seg_parts hpre hq₁
  obtain ⟨b1, b2, b3⟩ := absLe_inst hpre.leX hpre.leY hpre.leV hpre.lenY hpre.U_pos (ℓ := ℓ) he'
  have qpre : (question x fr ℓ e).Pre μ₁ (fr + 8 * (x.n * x.n)) :=
    ⟨hpre.n_pos, by simp [question]; omega, by simp [question, instAB, hpre.lenV],
      by simp [question, instBC], by simp [question, instAC, hpre.lenX],
      hthird, hqY, hqX, b1, b2, b3, by simp [question]; omega, by simp [question]; omega,
      by simp [question]; omega, by simp [question]; omega⟩
  refine Ends.callToThen (C.solver.meets R' (question x fr ℓ e) (fr + 8 * (x.n * x.n)) qpre
    ⟨by simp [aeTask, question]; omega, by simp [aeTask, question]; omega, C.ok.space,
      by simp [aeTask, question]; omega⟩) ?_ (by simp [aeTask, question])
    (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₂ μ₂ ⟨hflg, h₂⟩
  simp only [question] at hflg h₂
  have hout₂ : Seg μ₂ x.out (orFlags (x.n * x.n) S (hit x)) := hout.keep (by light_keep)
  refine Ends.callTo (or_meets C.orp (len := x.n * x.n) hflg hout₂ (by simp) (by omega)
    ⟨C.ok.space, by omega, by omega⟩ h01 (orFlags_mem _ _ _) (by omega)) ?_
    (ha := by light_side) (hT := by simp [aeTask, question, probeTime]; omega)
  rintro r₃ μ₃ ⟨hout₃, h₃⟩
  rw [orL_orFlags (S := S) (c := (ℓ, (e : ℤ))) (length_aeFlags x.n _ _ _)
    (fun _ _ => Iff.rfl) h01] at hout₃
  exact ⟨r₃, μ₃, rfl, hq₁.keep (by light_keep), hr.keep (by light_keep), hout₃,
    fun _ _ => by light_keep⟩

abbrev roundTime (T : ℕ → ℕ → ℕ) (x : PairsInst) : ℕ := 2 * probeTime T x + 114 * (x.n * x.n) + 12

private theorem round_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {ℓ : ℕ}
    (hℓ : ℓ + 1 ≤ aeLevels x.U) {rd : ℤ} {σ : State}
    (hσ : St x μ fr rd (ℓ + 1) (Above (ℓ + 1) (aeLevels x.U)) σ) :
    Ends lim (P₀ ++ R') d (paRound p pAff pOr pDown) σ (roundTime T x)
      (St x μ fr rd ℓ (Above ℓ (aeLevels x.U))) := by
  have hplaces := C.places; have hZ := Z_range C.pre
  have hZl : (Z x).length = 3 * (x.n * x.n) := length_pStart C.pre.lenX C.pre.lenV
  have hL : (2 : ℤ) ^ aeLevels x.U ≤ 6 * x.U := by exact_mod_cast two_pow_aeLevels_le C.pre.U_pos
  refine Ends.next _ ((probe_spec C (by norm_num) hσ).mono le_rfl fun σ₂ hσ₂ => ?_)
    (by grind)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_)
    (by simp only [roundTime, probeTime]; omega)
  obtain ⟨res, μ₀, rfl, hq, hr, hout, hk⟩ := hσ₃
  have dpre : PrefPre lim μ₀ fr (fr + 3 * (x.n * x.n)) (2 ^ aeLevels x.U)
      ((Z x).map (prefQ (ℓ + 1))) ((Z x).map (prefR (aeLevels x.U) (ℓ + 1))) :=
    ⟨hq, hr, by simp, C.ok.space, by simp; omega, by simp; omega, by simp; omega, by omega,
      fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; simp only [abs_le]
        have := prefQ_nonneg (hZ z hz).1 (ℓ + 1)
        have := (prefQ_le (hZ z hz).1 (ℓ + 1)).trans (hZ z hz).2.1; omega,
      fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy; simp only [abs_le]
        have := prefR_nonneg (aeLevels x.U) (ℓ + 1) z
        have := prefR_lt hℓ z; omega⟩
  refine Ends.callTo (prefDown_meets C.down dpre) ?_ (by simp [hZl])
    (hT := by simp [roundTime, probeTime]; omega)
  rintro r₁ μ₁ ⟨hq', hr', hrest⟩
  rw [zipWith_shiftQ hℓ] at hq'; rw [map_shiftR hℓ] at hr'
  simp only [List.length_map] at hrest
  refine ⟨r₁, μ₁, rfl, hq', hr', ?_,
    fun c hc => (hrest c (Or.inl (by omega)) (Or.inl (by omega))).trans (hk c hc)⟩
  have heq : orFlags (x.n * x.n) (fun c => (Above (ℓ + 1) (aeLevels x.U) c ∨ c = (ℓ + 1, 2)) ∨
      c = (ℓ + 1, 3)) (hit x) = orFlags (x.n * x.n) (Above ℓ (aeLevels x.U)) (hit x) :=
    List.map_congr_left fun q _ => flag_congr (exists_congr fun c => and_congr_left fun _ => above_step hℓ c)
  rw [← heq]
  exact hout.keep fun a ha => by
    rw [length_orFlags] at ha; exact hrest a (Or.inl (by omega)) (Or.inl (by omega))

private theorem rounds_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) {res : ℤ}
    {μ' : ℕ → ℤ} (hm : PMem x μ fr (aeLevels x.U) (fun _ => False) μ') :
    Ends lim (P₀ ++ R') d (.for 10 (v 9) (paRound p pAff pOr pDown))
      ⟨frame (locals x fr (2 ^ aeLevels x.U : ℕ) (aeLevels x.U) 0 res), μ'⟩
      (aeLevels x.U * (roundTime T x + 8) + 6)
      (St x μ fr (aeLevels x.U) 0 (Above 0 (aeLevels x.U))) := by
  have hplaces := C.places
  have hL : aeLevels x.U ≤ 6 * x.U :=
    (Nat.lt_two_pow_self (n := aeLevels x.U)).le.trans (two_pow_aeLevels_le C.pre.U_pos)
  refine Ends.for (fun t σ => St x μ fr t (aeLevels x.U - t) (Above (aeLevels x.U - t) (aeLevels x.U)) σ)
    (aeLevels x.U) (roundTime T x) ?start ?round (fun _ _ h => by simpa using h)
    (by rintro _ _ - - ⟨_, _, rfl, -⟩; exact ⟨trivial, rfl⟩) (by omega) (by simp; ring_nf; omega)
  case start =>
    obtain ⟨h1, h2, h3, h4⟩ := hm
    have heq : orFlags (x.n * x.n) (Above (aeLevels x.U) (aeLevels x.U)) (hit x) =
        orFlags (x.n * x.n) (fun _ => False) (hit x) :=
      List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
        and_congr_left fun _ => iff_of_false (above_self _ c) id)
    exact ⟨res, μ', by simp, by simpa using h1, by simpa using h2,
      by grind, h4⟩
  case round =>
    intro t σ ht _ hσ
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, aeLevels x.U - t = ℓ + 1 := ⟨aeLevels x.U - t - 1, by omega⟩
    rw [show aeLevels x.U - (t + 1) = ℓ by omega]; rw [hℓ] at hσ
    refine (round_spec C (by omega) hσ).mono le_rfl fun σ' hσ' => ?_
    obtain ⟨res', μ'', rfl, hm'⟩ := hσ'
    exact ⟨rfl, res', μ'', by rw [update_frame_setLocal]; rfl, hm'⟩

theorem pairsAE_spec (C : Ctx P₀ R' p pAff pTr pOr pDown T r lim d x μ fr) :
    Ends lim (P₀ ++ R') d (paBody p pAff pTr pOr pDown)
      ⟨frame [x.n, x.U, x.x, x.y, x.v, x.out, fr], μ⟩ (pairsTimeAE T x.n x.U) fun σ' =>
        Seg σ'.mem x.out (pairFlags x.n x.X x.Y x.V) ∧ KeptBut μ σ'.mem fr x.out (x.n * x.n) := by
  have hpre := C.pre; have hplaces := C.places
  rw [show pairsTimeAE T x.n x.U = aeLevels x.U * (roundTime T x + 8) + 6 +
    (3 * probeTime T x + 30 * aeLevels x.U + 371 * (x.n * x.n) + 219) by
      simp  [pairsTimeAE, roundTime, probeTime]; ring]
  refine Ends.next _ ((init_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  refine Ends.next _ ((pow_spec C).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ rfl
  refine Ends.next _ ((fill_spec C _ _ _ _).mono le_rfl ?_) (by simp [paInit]; omega)
  rintro _ ⟨res, μ₁, rfl, hm⟩
  refine Ends.next _ ((rounds_spec C hm).mono le_rfl ?_) (by simp [paInit]; omega)
  intro σ₂ hσ₂
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₂).mono le_rfl fun σ₃ hσ₃ => ?_) (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₃).mono le_rfl fun σ₄ hσ₄ => ?_) (by simp [paInit]; omega)
  refine Ends.next _ ((probe_spec C (by norm_num) hσ₄).mono le_rfl fun σ₅ hσ₅ => ?_) (by simp [paInit]; omega)
  obtain ⟨res', μ₅, rfl, -, -, hout, hk⟩ := hσ₅
  refine Ends.setTo 0 ⟨?_, hk⟩ (hT := by simp [paInit]; omega)
  rw [← orFlags_eq_pairFlags hpre.leX hpre.leY hpre.leV hpre.lenX hpre.lenY hpre.lenV]
  have heq : orFlags (x.n * x.n) (fun c => ((Above 0 (aeLevels x.U) c ∨ c = (0, ((2 : ℕ) : ℤ))) ∨
      c = (0, ((3 : ℕ) : ℤ))) ∨ c = (0, ((1 : ℕ) : ℤ))) (hit x) =
      orFlags (x.n * x.n) (fun c => c ∈ lemmaFInstances (aeLevels x.U)) (hit x) :=
    List.map_congr_left fun q _ => flag_congr (exists_congr fun c =>
      and_congr_left fun _ => by exact above_zero_iff _ c)
  exact heq ▸ hout

end PairsHost

theorem isHost_pairsAE : IsHost aeTask pairsTask pairsTimeAE pairsNeedAE := by
  refine ⟨fun P p T r hsol => ⟨[affineBody, transposeBody, orBody, prefDownBody,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3)], P.length + 4,
    paBody p P.length (P.length + 1) (P.length + 2) (P.length + 3), by simp,
    fun R lim d x μ fr hpre hok => ?_⟩,
    fun r h => by unfold pairsNeedAE; poly_need [h.word, h.cells, h.depth]⟩
  rw [List.append_assoc]
  exact PairsHost.pairsAE_spec ⟨hsol, by simp, by simp, by simp, by simp, hpre, hok⟩

/-! ## Real time bound -/

noncomputable def CA : ℝ := 2000

theorem CA_nonneg : 0 ≤ CA := by unfold CA; norm_num

theorem pairsFromAllEdges : PairsFromAllEdges CA := by
  refine fun T h => isHost_pairsAE.solvedIn h fun Tn hT n U u hn hU hu => ?_
  have hhalf := Real.one_half_lt_log_two
  have h2u := log_two_le_logU u
  have hpow : 2 ^ Nat.log 2 (3 * U) ≤ 3 * U := Nat.pow_log_le_self 2 (by omega)
  have hlog : (Nat.log 2 (3 * U) : ℝ) * Real.log 2 ≤ Real.log 3 + Real.log U := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_four]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hUu : Real.log U ≤ logU u := (Real.log_le_log (by positivity) hu).trans (log_le_logU (by linarith))
  have hb : (aeLevels U : ℝ) ≤ 3 * (1 + logU u) := by
    simp only [aeLevels]; push_cast
    rcases le_or_gt (Nat.log 2 (3 * U)) 1 with hL | hL
    · have : (Nat.log 2 (3 * U) : ℝ) ≤ 1 := by exact_mod_cast hL
      linarith
    · have : (2 : ℝ) ≤ Nat.log 2 (3 * U) := by exact_mod_cast hL
      nlinarith
  have hL0 := (logU_pos u).le
  have hTn := hT n (9 * U) (9 * u) hn (by omega) (by push_cast; linarith)
  have hT0 : (0 : ℝ) ≤ T n (9 * u) := (Nat.cast_nonneg _).trans hTn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hn)
  have := Nat.cast_nonneg (α := ℝ) (Tn n (9 * U))
  have hprod := mul_le_mul (by linarith : 2 * (aeLevels U : ℝ) + 3 ≤ 9 * (1 + logU u))
    (by linarith : (Tn n (9 * U) : ℝ) + 108 * (n : ℝ) ^ 2 + 60 ≤ 168 * (T n (9 * u) + (n : ℝ) ^ 2))
    (by linarith) (by linarith)
  have hstart := mul_le_mul_of_nonneg_left
    (le_mul_of_one_le_left (add_nonneg hT0 (sq_nonneg (n : ℝ))) (by linarith : 1 ≤ 1 + logU u))
    (by norm_num : (0 : ℝ) ≤ 350)
  simp only [pairsTimeAE, CA]; push_cast; rw [← sq (n : ℝ)]
  nlinarith

end ImprovedExponents.AllEdges
