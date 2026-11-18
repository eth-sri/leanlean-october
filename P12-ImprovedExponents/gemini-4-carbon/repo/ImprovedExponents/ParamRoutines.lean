module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Sizes
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Total
public import ThreeSumApsp.Lang.PolyBounded

@[expose] public section

namespace ImprovedExponents.ParamRoutines

open ThreeSumApsp ThreeSumApsp.Spec Light Light.Sec3

noncomputable def paramDRat (a b n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((a : ℝ) / b)⌋₊
noncomputable def paramGRat (c d D : ℕ) : ℕ := ⌈(D : ℝ) ^ ((c : ℝ) / d)⌉₊
noncomputable def paramGRatOf (a b c d n : ℕ) : ℕ := paramGRat c d (paramDRat a b n)

def paramDRatNat (a b n : ℕ) : ℕ := rootFloor b (n ^ a)
def paramGRatNat (c d D : ℕ) : ℕ := rootCeil d (D ^ c)

theorem rpow_natCast_div (n a b : ℕ) :
    (n : ℝ) ^ ((a : ℝ) / b) = ((n ^ a : ℕ) : ℝ) ^ ((b : ℝ)⁻¹) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul n.cast_nonneg, div_eq_mul_inv]

theorem paramDRatNat_eq {b : ℕ} (hb : b ≠ 0) (a n : ℕ) : paramDRatNat a b n = paramDRat a b n := by
  rw [paramDRatNat, paramDRat, rpow_natCast_div, floor_rpow_inv hb]

theorem paramGRatNat_eq {d : ℕ} (hd : d ≠ 0) (c : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    paramGRatNat c d D = paramGRat c d D := by
  rw [paramGRatNat, paramGRat, rpow_natCast_div, ceil_rpow_inv hd (Nat.one_le_pow _ _ hD)]

theorem paramGRatNat_paramDRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) {n : ℕ}
    (hD : 1 ≤ paramDRat a b n) :
    paramGRatNat c d (paramDRat a b n) = paramGRatOf a b c d n :=
  paramGRatNat_eq hd c hD

theorem one_le_paramDRatNat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRatNat a b n :=
  le_rootFloor hb (by simpa using Nat.one_le_pow a n hn)

theorem one_le_paramDRat {b : ℕ} (hb : b ≠ 0) (a : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ paramDRat a b n :=
  paramDRatNat_eq hb a n ▸ one_le_paramDRatNat hb a hn

theorem one_le_paramGRatNat (c d D : ℕ) : 1 ≤ paramGRatNat c d D := Nat.succ_le_succ (Nat.zero_le _)
theorem paramDRatNat_le (a b n : ℕ) : paramDRatNat a b n ≤ n ^ a := Nat.findGreatest_le _
theorem paramGRatNat_le (c d D : ℕ) : paramGRatNat c d D ≤ D ^ c + 1 :=
  Nat.succ_le_succ (Nat.findGreatest_le _)

theorem paramDRatNat_le_pow {a b k : ℕ} (hb : b ≠ 0) (h : a ≤ k * b) {n : ℕ} (hn : 1 ≤ n) :
    paramDRatNat a b n ≤ n ^ k := by
  refine (Nat.pow_le_pow_iff_left hb).1 ((rootFloor_pow_le hb _).trans ?_)
  rw [← pow_mul]; exact Nat.pow_le_pow_right hn h

theorem paramGRatNat_le_pow {c d k : ℕ} (hd : d ≠ 0) (h : c ≤ k * d) {D : ℕ} (hD : 1 ≤ D) :
    paramGRatNat c d D ≤ D ^ k := by
  refine rootCeil_le hd (Nat.one_le_pow _ _ hD) ?_
  rw [← pow_mul]; exact Nat.pow_le_pow_right hD h

variable {lim : Limits} {P : Program} {d : ℕ}

def powThen (e : ℕ) (s : Stmt) : Stmt :=
  .set 1 (k 0) ;; .set 2 (k 1) ;;
  .while (v 1 <' k e) (.set 2 (v 2 *' v 0) ;; .set 1 (v 1 +' k 1)) ;; s

theorem powThen_ends {μ : ℕ → ℤ} {x e B T : ℕ} {s : Stmt} {Q : State → Prop}
    (hB : ∀ i ≤ e, x ^ i ≤ B) (hword : ((B + e + 1 : ℕ) : ℤ) ≤ lim.word) (hT : 12 * e + 8 ≤ T)
    (h : Ends lim P d s ⟨frame [x, e, (x ^ e : ℕ)], μ⟩ (T - (12 * e + 8)) Q) :
    Ends lim P d (powThen e s) ⟨frame [(x : ℤ)], μ⟩ T Q := by
  light_set (0 : ℕ); light_set (1 : ℕ)
  refine Ends.next (12 * e + 4) (Ends.whileBlock
    (fun i σ => σ = ⟨frame [x, i, (x ^ i : ℕ)], μ⟩) e (by simp) ?round ?done
    (by simp; omega)) (by simp; omega)
  case round =>
    rintro i _ hi rfl
    have hle : ((x ^ (i + 1) : ℕ) : ℤ) ≤ B := by grind
    have hmul : ((x ^ i : ℕ) : ℤ) * x = ((x ^ (i + 1) : ℕ) : ℤ) := by push_cast; ring
    have hmul0 : (0 : ℤ) ≤ ((x ^ (i + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((x ^ (i + 1) : ℕ) : ℤ) = q' at hle hmul hmul0
    generalize ((x ^ i : ℕ) : ℤ) = q at hmul
    exact ⟨by light_side, by light_side, by light_side ,
      by simp [update_frame_setLocal, hmul]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, h.mono (by simp; omega) fun _ hQ => hQ⟩

def dRatBody (a b pRoot : ℕ) : Stmt :=
  powThen a (.call pRoot [k b, v 2 +' k 1] 1 ;; .set 0 (v 1 -' k 1))

def tDRat (a b n : ℕ) : ℕ := (paramDRatNat a b n + 1) * (16 * b + 27) + 12 * a + 18
def wDRat (a b n : ℕ) : ℕ := (n ^ a + 1) * (paramDRatNat a b n + 1) + a + b + 1

theorem dRat_spec {μ : ℕ → ℤ} {a b pRoot pPow n : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (hb : b ≠ 0)
    (hword : ((wDRat a b n : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (dRatBody a b pRoot) ⟨frame [(n : ℤ)], μ⟩ (tDRat a b n) fun σ' =>
      σ'.loc 0 = (paramDRatNat a b n : ℕ) ∧ σ'.mem = μ := by
  have hroot : rootCeil b (n ^ a + 1) = paramDRatNat a b n + 1 := rootCeil_succ hb _
  have hpows : ∀ i ≤ a, n ^ i ≤ n ^ a + 1 := fun i hi => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases i with _ | i <;> simp
    · exact (Nat.pow_le_pow_right hn hi).trans (Nat.le_succ _)
  have hmul : n ^ a + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hmul' : paramDRatNat a b n + 1 ≤ (n ^ a + 1) * (paramDRatNat a b n + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold wDRat at hword; unfold dRatBody tDRat
  generalize hD : paramDRatNat a b n = D at hroot hmul hmul' hword
  generalize hN : n ^ a = N at hroot hmul hmul' hword hpows
  have hfits : (((N + 1) * (D + 1) + b + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (by omega)) hword
  generalize hM : (N + 1) * (D + 1) = M at hmul hmul' hword hfits
  refine powThen_ends (B := N + 1) hpows (le_trans (by exact_mod_cast (by omega)) hword)
    (by omega) ?_
  rw [hN]
  refine Ends.callToThen (rootCeil_meets (e := b) (t := N + 1) hR hP hb (by omega)
    (by rw [hroot, hM]; exact hfits) (by omega)) ?_ (hT := by simp [tRootCeil, hroot]; omega)
  rintro _ μ' ⟨rfl, hμ⟩
  rw [hroot, hμ]
  exact Ends.setTo D (by simp) (he := by light_side) (hT := by simp [tRootCeil, hroot]; omega)

def gRatBody (c d pRoot : ℕ) : Stmt := powThen c (.call pRoot [k d, v 2] 0)
def tGRat (c d D : ℕ) : ℕ := paramGRatNat c d D * (16 * d + 27) + 12 * c + 12
def wGRat (c d D : ℕ) : ℕ := D ^ c * paramGRatNat c d D + c + d + 1

theorem gRat_spec {μ : ℕ → ℤ} {c e pRoot pPow D : ℕ} (hR : P[pRoot]? = some (rootCeilBody pPow))
    (hP : P[pPow]? = some powLtBody) (he : e ≠ 0) (hD : 1 ≤ D)
    (hword : ((wGRat c e D : ℕ) : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth) :
    Ends lim P d (gRatBody c e pRoot) ⟨frame [(D : ℤ)], μ⟩ (tGRat c e D) fun σ' =>
      σ'.loc 0 = (paramGRatNat c e D : ℕ) ∧ σ'.mem = μ := by
  have hpos : 1 ≤ paramGRatNat c e D := one_le_paramGRatNat c e D
  have hmul : D ^ c ≤ D ^ c * paramGRatNat c e D := Nat.le_mul_of_pos_right _ hpos
  have hN0 : 1 ≤ D ^ c := Nat.one_le_pow _ _ hD
  have hpows : ∀ i ≤ c, D ^ i ≤ D ^ c := fun i hi => Nat.pow_le_pow_right hD hi
  unfold wGRat at hword; unfold gRatBody tGRat
  unfold paramGRatNat at hpos hmul hword ⊢
  generalize hN : D ^ c = N at hpos hmul hword hpows hN0
  have hfits : ((N * rootCeil e N + e + 1 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by omega) hword
  generalize hG : rootCeil e N = G at hpos hmul hword hfits
  generalize hM : N * G = M at hmul hword hfits
  refine powThen_ends (B := N) hpows (le_trans (by omega) hword) (by omega) ?_
  rw [hN]
  exact Ends.callTo (rootCeil_meets (e := e) (t := N) hR hP he hN0
    (by grind) (by omega)) (fun r μ' h => by simpa [hG] using h)
    (hT := by simp [tRootCeil, hG]; omega)

theorem getElem?_behind (Q L R : Program) {i : ℕ} {body : Stmt} (h : L[i]? = some body) :
    (Q ++ L ++ R)[Q.length + i]? = some body := by
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getElem?_append_of_eq_some h R

def ratProcs (a b c d o : ℕ) : Program :=
  [powLtBody, rootCeilBody o, dRatBody a b (o + 1), gRatBody c d (o + 1)]

theorem paramProc_dRat {b : ℕ} (hb : b ≠ 0) (a c d : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 2) (paramDRatNat a b)
      (tDRat a b) (wDRat a b) :=
  fun _ _ _ _ _ _ hw hd => Meets.of_body (getElem?_behind Q _ R (i := 2) rfl)
    (dRat_spec (getElem?_behind Q _ R (i := 1) rfl) (getElem?_behind Q _ R (i := 0) rfl)
      hb hw (by omega))

theorem paramProc_gRat {d : ℕ} (hd : d ≠ 0) (a b c : ℕ) (Q R : Program) :
    ParamProc (Q ++ ratProcs a b c d Q.length ++ R) (Q.length + 3) (paramGRatNat c d)
      (tGRat c d) (wGRat c d) :=
  fun _ _ _ _ hx _ hw hd' => Meets.of_body (getElem?_behind Q _ R (i := 3) rfl)
    (gRat_spec (getElem?_behind Q _ R (i := 1) rfl) (getElem?_behind Q _ R (i := 0) rfl)
      hd hx hw (by omega))

theorem polyBounded_paramDRatNat (a b : ℕ) : PolyBounded fun n _ => paramDRatNat a b n :=
  (by growth_poly [] : PolyBounded fun n _ => n ^ a).of_le fun n _ => paramDRatNat_le a b n

theorem polyBounded_paramGRatNat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => paramGRatNat c d (D n) :=
  (by growth_poly [hD] : PolyBounded fun n _ => D n ^ c + 1).of_le fun n _ =>
    paramGRatNat_le c d (D n)

theorem polyBounded_wDRat (a b : ℕ) : PolyBounded fun n _ => wDRat a b n := by
  unfold wDRat; growth_poly [polyBounded_paramDRatNat a b]

theorem polyBounded_wGRat (c d : ℕ) {D : ℕ → ℕ} (hD : PolyBounded fun n _ => D n) :
    PolyBounded fun n _ => wGRat c d (D n) := by
  unfold wGRat; growth_poly [hD, polyBounded_paramGRatNat c d hD]

theorem steps_tDRat {a b : ℕ} (hb : b ≠ 0) (hab : a ≤ 2 * b) :
    StepsMon (fun θ => tDRat a b θ.n) 2 2 0 := by
  have hD : StepsMon (fun θ => paramDRatNat a b θ.n) 2 0 0 :=
    ((steps_n.pow 2).mono fun i => by fin_cases i <;> simp).of_le fun _ hθ =>
      paramDRatNat_le_pow hb hab hθ.one_le_n_nat
  unfold tDRat
  exact Scale.SoftO.mono (by growth_rules [hD]) (by decide)

theorem steps_tGRat {c d : ℕ} (hd : d ≠ 0) (hcd : c ≤ 3 * d) :
    StepsMon (fun θ => tGRat c d θ.D) 2 2 0 := by
  have hG : StepsMon (fun θ => paramGRatNat c d θ.D) 2 2 0 :=
    (by growth [steps_n, steps_D] : StepsMon (fun θ => θ.n ^ 2 * θ.D) 2 2 0).of_le fun θ hθ =>
      (paramGRatNat_le_pow hd hcd hθ.one_le_D_nat).trans
        (by rw [pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hθ.hDn 2))
  unfold tGRat; growth [hG]

end ImprovedExponents.ParamRoutines
