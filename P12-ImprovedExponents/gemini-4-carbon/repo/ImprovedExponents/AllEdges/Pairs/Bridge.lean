module

public import ImprovedExponents.AllEdges.Task
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Lang.Frames
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle
public import ThreeSumApsp.Programs.Sec3.Theorem21b.MinPlus.Tasks

@[expose] public section

namespace ImprovedExponents

open Finset

def shiftDiff (x y u ℓ : ℕ) : ℤ :=
  ((u / 2 ^ ℓ : ℕ) : ℤ) - ((x / 2 ^ ℓ : ℕ) : ℤ) - ((y / 2 ^ ℓ : ℕ) : ℤ)

private theorem shiftDiff_succ_bounds (x y u ℓ : ℕ) :
    2 * shiftDiff x y u (ℓ + 1) - 2 ≤ shiftDiff x y u ℓ
      ∧ shiftDiff x y u ℓ ≤ 2 * shiftDiff x y u (ℓ + 1) + 1 := by
  have h (n : ℕ) : n / 2 ^ (ℓ + 1) = n / 2 ^ ℓ / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  unfold shiftDiff; rw [h x, h y, h u]; omega

private theorem two_le_shiftDiff_zero {x y u : ℕ} :
    ∀ ℓ, 2 ≤ shiftDiff x y u ℓ → 2 ≤ shiftDiff x y u 0
  | 0, h => h
  | ℓ + 1, h => two_le_shiftDiff_zero ℓ (by have := (shiftDiff_succ_bounds x y u ℓ).1; omega)

def lemmaFInstances (b : ℕ) : Finset (ℕ × ℤ) := insert (0, 1) (range (b + 1) ×ˢ {2, 3})

theorem lt_iff_exists_instance {b W : ℕ} {p q t : ℤ} (hp : |p| ≤ W) (hq : |q| ≤ W)
    (hW : 2 * W < 2 ^ b) (ht : -(2 * W : ℤ) ≤ t) (ht' : t + 2 * W < 2 ^ b) :
    p + q < t ↔ ∃ c ∈ lemmaFInstances b,
      (p + W) / 2 ^ c.1 + (q + W) / 2 ^ c.1 + (c.2 - (t + 2 * W) / 2 ^ c.1) = 0 := by
  have hp' := abs_le.mp hp; have hq' := abs_le.mp hq
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p + W)
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q + W)
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ t + 2 * W)
  have hxb : x < 2 ^ b := by omega
  have hyb : y < 2 ^ b := by omega
  have hub : u < 2 ^ b := by grind
  have hex : ∀ d ℓ, ℓ + d = b → 2 ≤ shiftDiff x y u ℓ →
      ∃ ℓ' ≤ b, shiftDiff x y u ℓ' = 2 ∨ shiftDiff x y u ℓ' = 3 := by
    intro d; induction d with
    | zero =>
      intro ℓ hℓ h2
      have hpow : 2 ^ b ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) (by omega)
      simp [shiftDiff, Nat.div_eq_of_lt (hxb.trans_le hpow), Nat.div_eq_of_lt (hyb.trans_le hpow),
        Nat.div_eq_of_lt (hub.trans_le hpow)] at h2
    | succ d ih =>
      intro ℓ hℓ h2
      by_cases h : 2 ≤ shiftDiff x y u (ℓ + 1)
      · exact ih (ℓ + 1) (by omega) h
      · have := (shiftDiff_succ_bounds x y u ℓ).2; exact ⟨ℓ, by omega, by omega⟩
  have hiff : x + y < u ↔ shiftDiff x y u 0 = 1 ∨ ∃ ℓ ≤ b, shiftDiff x y u ℓ = 2 ∨ shiftDiff x y u ℓ = 3 := by
    have h0 : shiftDiff x y u 0 = (u : ℤ) - x - y := by simp [shiftDiff]
    refine ⟨fun h => ?_, ?_⟩
    · by_cases h1 : shiftDiff x y u 0 = 1
      · exact Or.inl h1
      · exact Or.inr (hex b 0 (by omega) (by omega))
    · rintro (h1 | ⟨ℓ, -, h2⟩)
      · omega
      · have hge : 2 ≤ shiftDiff x y u ℓ := by rcases h2 with h2 | h2 <;> omega
        have := two_le_shiftDiff_zero ℓ hge; omega
  have hmem (f : ℕ → ℤ) : (∃ c ∈ lemmaFInstances b, f c.1 = c.2) ↔
      f 0 = 1 ∨ ∃ ℓ ≤ b, f ℓ = 2 ∨ f ℓ = 3 := by
    constructor
    · rintro ⟨⟨ℓ, r⟩, hc, hf⟩
      simp only [lemmaFInstances, mem_insert, Prod.mk.injEq, mem_product, mem_range, mem_singleton] at hc
      rcases hc with ⟨rfl, rfl⟩ | ⟨hℓ, rfl | rfl⟩
      · exact Or.inl hf
      · exact Or.inr ⟨ℓ, by omega, Or.inl hf⟩
      · exact Or.inr ⟨ℓ, by omega, Or.inr hf⟩
    · rintro (h | ⟨ℓ, hℓ, h | h⟩)
      · exact ⟨(0, 1), mem_insert_self _ _, h⟩
      · exact ⟨(ℓ, 2), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩
      · exact ⟨(ℓ, 3), mem_insert_of_mem (mem_product.mpr ⟨mem_range.mpr (by omega), by simp⟩), h⟩
  have hdiv (z ℓ : ℕ) : (z : ℤ) / 2 ^ ℓ = ((z / 2 ^ ℓ : ℕ) : ℤ) := by norm_cast
  rw [show (p + q < t) ↔ x + y < u by omega, hiff, ← hmem, hx, hy, hu]
  exact exists_congr fun c => and_congr_right fun _ => by
    rw [hdiv, hdiv, hdiv]; unfold shiftDiff; omega

end ImprovedExponents

namespace ImprovedExponents.AllEdges

open Light Light.Sec3 ThreeSumApsp ThreeSumApsp.Spec

/-! ## Array passes: or and transpose -/

def orBody : Stmt :=
  pass 3 (v 0) (v 2) (M (v 2 +' v 3) +' M (v 1 +' v 3) -' M (v 2 +' v 3) *' M (v 1 +' v 3))

def orL (L F : List ℤ) : List ℤ := List.zipWith (fun o f => o + f - o * f) L F

@[simp] theorem length_orL (L F : List ℤ) : (orL L F).length = min L.length F.length := by
  simp [orL]

theorem or_meets {lim : Limits} {P : Program} {d p : ℕ} (hp : P[p]? = some orBody) {μ : ℕ → ℤ}
    {fl out len : ℕ} {F L : List ℤ} (hF : Seg μ fl F) (hL : Seg μ out L)
    (hlen : F.length = len ∧ L.length = len) (hsep : Apart fl len out len)
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ fl + len ≤ lim.space ∧ out + len ≤ lim.space)
    (hflag : ∀ f ∈ F, f = 0 ∨ f = 1) (hL01 : ∀ o ∈ L, o = 0 ∨ o = 1) (hw : 1 ≤ lim.word) :
    Meets lim P p d [(len : ℤ), fl, out] μ (31 * len + 6) fun _ μ' =>
      Seg μ' out (orL L F) ∧ SameOutside μ μ' out len := by
  obtain ⟨lF, lL⟩ := hlen; obtain ⟨hsp, hfl, hout⟩ := hlim
  set f : ℕ → ℤ := fun i => L.getD i 0 + F.getD i 0 - L.getD i 0 * F.getD i 0 with hf
  have hfi (i : ℕ) (hF' : i < F.length) (hL' : i < L.length) : f i = L[i] + F[i] - L[i] * F[i] := by grind
  refine .of_body hp (Ends.pass f (fun j hj => ?_) ?_ hsp hout rfl rfl)
  · have hreadF : wrote μ out f j (fl + j) = F[j] := (wrote_rest (by omega)).trans (hF j (by omega))
    have hreadL : wrote μ out f j (out + j) = L[j] := (wrote_rest (by omega)).trans (hL j (by omega))
    rw [update_frame_setLocal]
    rcases hflag _ (List.getElem_mem (show j < F.length by omega)) with h | h <;>
    rcases hL01 _ (List.getElem_mem (show j < L.length by omega)) with h' | h'
    all_goals simp [Limits.Addr, abs_le, hreadF, hfi j (by omega) (by omega), h]; omega
  · refine ⟨seg_wrote (by simp [orL, lF, lL]) fun i hi => ?_, sameOutside_wrote le_rfl⟩
    simp only [orL, List.length_zipWith] at hi ⊢
    rw [List.getElem_zipWith]; exact (hfi i (by omega) (by omega)).symm

def transposeRow : Stmt :=
  .set 5 (v 3 +' v 4 *' v 0) ;; pass 6 (v 0) (v 5) (M (v 1 +' v 6 *' v 0 +' v 4) +' v 2)

def transposeBody : Stmt := .for 4 (v 0) transposeRow

def transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) : List ℤ :=
  (List.range (n * n)).map fun q => Y.getD (q % n * n + q / n) 0 + c

@[simp] theorem length_transposeL (n : ℕ) (c : ℤ) (Y : List ℤ) :
    (transposeL n c Y).length = n * n := by simp [transposeL]

theorem transposeL_getD {n : ℕ} (c : ℤ) (Y : List ℤ) {j k : ℕ} (hj : j < n) (hk : k < n) :
    (transposeL n c Y).getD (j * n + k) 0 = Y.getD (k * n + j) 0 + c := by
  have hq : j * n + k < n * n := by nlinarith
  simp [transposeL, List.getElem?_range hq,
    show (j * n + k) / n = j by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk]; simp,
    show (j * n + k) % n = k by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]]

theorem mem_transposeL_bounds {n : ℕ} {Y : List ℤ} {U : ℤ} (hY : AbsLe Y U)
    (hlen : Y.length = n * n) (c : ℤ) : ∀ z ∈ transposeL n c Y, c - U ≤ z ∧ z ≤ c + U := by
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hz
  simp  at hq
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hidx : q % n * n + q / n < n * n := by
    nlinarith [Nat.mod_lt q hn, (Nat.div_lt_iff_lt_mul hn).2 hq]
  have hmem : Y.getD (q % n * n + q / n) 0 ∈ Y := by
    rw [List.getD_eq_getElem _ _ (hlen ▸ hidx)]; exact List.getElem_mem _
  have := abs_le.1 (hY _ hmem); omega

private def tMem (μ : ℕ → ℤ) (dst n : ℕ) (c : ℤ) (Y : List ℤ) (j : ℕ) : ℕ → ℤ :=
  wrote μ dst (fun q => (transposeL n c Y).getD q 0) (j * n)

theorem transpose_meets {lim : Limits} {P : Program} {d p : ℕ} (hp : P[p]? = some transposeBody)
    {μ : ℕ → ℤ} {src dst n : ℕ} {c : ℤ} {Y : List ℤ} (hY : Seg μ src Y) (hlen : Y.length = n * n)
    (hsep : Apart src (n * n) dst (n * n))
    (hlim : (lim.space : ℤ) ≤ lim.word ∧ src + n * n ≤ lim.space ∧ dst + n * n ≤ lim.space)
    (hfits : ∀ y ∈ Y, |y + c| ≤ lim.word) :
    Meets lim P p d [(n : ℤ), src, c, dst] μ (30 * (n * n) + 20 * n + 6) fun _ μ' =>
      Seg μ' dst (transposeL n c Y) ∧ SameOutside μ μ' dst (n * n) := by
  obtain ⟨hsp, hsrc, hdst⟩ := hlim
  have hn : (n : ℤ) ≤ lim.word :=
    le_trans (by exact_mod_cast (Nat.le_mul_self n).trans (by omega : n * n ≤ lim.space)) hsp
  refine .of_body hp ?_
  refine Ends.forShape (fun j (s : ℤ × ℤ) μ' => ⟨frame [n, src, c, dst, j, s.1, s.2], μ'⟩)
    (fun j μ' => μ' = tMem μ dst n c Y j) n (30 * n + 11) (0, 0) (by simp [tMem, wrote_zero])
    ?round ?done
    (first := by rw [update_frame_setLocal]; exact congrArg (State.mk · μ) (frame_append_zeros _ 2).symm)
    (hT := by simp; nlinarith)
  case round =>
    rintro j s μ' hj rfl
    have hjn : j * n + n ≤ n * n := by nlinarith
    light_set (dst + j * n : ℕ)
    refine Ends.pass (fun i => Y.getD (i * n + j) 0 + c) (fun i hi => ?_) ?_ hsp (by omega) rfl rfl
      (hT := by simp; omega)
    · have hin : i * n + j < n * n := by nlinarith
      have hread : wrote (tMem μ dst n c Y j) (dst + j * n) (fun i => Y.getD (i * n + j) 0 + c) i
          (src + (i * n + j)) = Y.getD (i * n + j) 0 := by
        rw [wrote_rest (by omega), tMem, wrote_rest (by omega), hY.getD (hlen ▸ hin)]
      have hmem : Y.getD (i * n + j) 0 ∈ Y := by
        rw [List.getD_eq_getElem _ _ (hlen ▸ hin)]; exact List.getElem_mem _
      have hfit := abs_le.1 (hfits _ hmem)
      have htoNat : ((src : ℤ) + (i : ℤ) * n + j).toNat = src + (i * n + j) := by omega
      rw [update_frame_setLocal]
      simp only [List.getD_eq_getElem?_getD] at hread hfit
      simp [Limits.Addr, abs_le, htoNat, hread]
      omega
    · refine ⟨((dst + j * n : ℕ), n), tMem μ dst n c Y (j + 1), ?_, rfl⟩
      rw [update_frame_setLocal]; congr 1
      funext a; simp only [tMem, wrote, Nat.succ_mul]
      by_cases h1 : dst + j * n ≤ a ∧ a < dst + j * n + n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
        obtain ⟨i, hi, rfl⟩ : ∃ i < n, a = dst + (j * n + i) := ⟨a - dst - j * n, by omega, by omega⟩
        rw [show dst + (j * n + i) - (dst + j * n) = i by omega, Nat.add_sub_cancel_left,
          transposeL_getD c Y hj hi]
      · rw [ite_eq_right h1]
        by_cases h2 : dst ≤ a ∧ a < dst + j * n
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  case done =>
    rintro s μ' rfl
    refine ⟨fun i hi => ?_, show SameOutside μ (tMem μ dst n c Y n) dst (n * n) from
      sameOutside_wrote le_rfl⟩
    simp only [length_transposeL] at hi
    change wrote μ dst (fun q => (transposeL n c Y).getD q 0) (n * n) (dst + i) = _
    rw [wrote_done hi, List.getD_eq_getElem _ _ (by simpa using hi)]

/-! ## Bridge from pairsTask to aeTask -/

def aeLevels (U : ℕ) : ℕ := Nat.log 2 (3 * U) + 1

theorem lt_two_pow_aeLevels (U : ℕ) : 3 * U < 2 ^ aeLevels U :=
  Nat.lt_pow_succ_log_self (by norm_num) _

theorem two_pow_aeLevels_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ aeLevels U ≤ 6 * U := by
  have := Nat.pow_log_le_self 2 (show 3 * U ≠ 0 by omega)
  rw [aeLevels, pow_succ]; omega

def pStart (n U : ℕ) (X Y V : List ℤ) : List ℤ :=
  affL 1 U X ++ (transposeL n U Y ++ affL 1 (2 * U) V)

def instAC (U : ℕ) (X : List ℤ) (ℓ : ℕ) : List ℤ := (affL 1 U X).map (prefQ ℓ)
def instBC (n U : ℕ) (Y : List ℤ) (ℓ : ℕ) : List ℤ := (transposeL n U Y).map (prefQ ℓ)
def instAB (U : ℕ) (V : List ℤ) (ℓ : ℕ) (r : ℤ) : List ℤ :=
  affL (-1) r ((affL 1 (2 * U) V).map (prefQ ℓ))

section Lists
variable {n U : ℕ} {X Y V : List ℤ}

theorem length_pStart (hX : X.length = n * n) (hV : V.length = n * n) :
    (pStart n U X Y V).length = 3 * (n * n) := by
  simp  [pStart]; omega

theorem pStart_range (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n) :
    ∀ z ∈ pStart n U X Y V, 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  intro z hz; simp  [pStart] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; have := abs_le.1 (hX x hx); omega
  · have := mem_transposeL_bounds hY hlenY U z hz; omega
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; have := abs_le.1 (hV x hx); omega

theorem absLe_pStart_parts (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlenY : Y.length = n * n) (ℓ : ℕ) :
    (∀ z ∈ instAC U X ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      (∀ z ∈ instBC n U Y ℓ, 0 ≤ z ∧ z ≤ 3 * (U : ℤ)) ∧
      ∀ z ∈ (affL 1 (2 * U) V).map (prefQ ℓ), 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
  have hp := pStart_range hX hY hV hlenY
  have h : ∀ z ∈ (pStart n U X Y V).map (prefQ ℓ), 0 ≤ z ∧ z ≤ 3 * (U : ℤ) := by
    intro z hz; obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact ⟨prefQ_nonneg (hp y hy).1 ℓ, (prefQ_le (hp y hy).1 ℓ).trans (hp y hy).2⟩
  simp only [pStart, List.map_append, List.mem_append] at h
  exact ⟨fun z hz => h z (Or.inl hz), fun z hz => h z (Or.inr (Or.inl hz)),
    fun z hz => h z (Or.inr (Or.inr hz))⟩

theorem absLe_inst (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U) (hlenY : Y.length = n * n)
    (hU : 1 ≤ U) {ℓ : ℕ} {r : ℤ} (hr : 1 ≤ r ∧ r ≤ 3) :
    AbsLe (instAB U V ℓ r) ((9 * U : ℕ) : ℤ) ∧ AbsLe (instBC n U Y ℓ) ((9 * U : ℕ) : ℤ) ∧
      AbsLe (instAC U X ℓ) ((9 * U : ℕ) : ℤ) := by
  obtain ⟨h1, h2, h3⟩ := absLe_pStart_parts hX hY hV hlenY ℓ
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz; have := h3 y hy; exact abs_le.2 ⟨by omega, by omega⟩
  · have := h2 z hz; exact abs_le.2 ⟨by omega, by omega⟩
  grind

theorem pairFlags_iff (hX : AbsLe X U) (hY : AbsLe Y U) (hV : AbsLe V U)
    (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) {q : ℕ}
    (hq : q < n * n) :
    (pairFlags n X Y V).getD q 0 = 1 ↔ ∃ c ∈ lemmaFInstances (aeLevels U),
      (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1 := by
  have hn : 0 < n := by rcases n with _ | n <;> simp_all
  have hi : q / n < n := (Nat.div_lt_iff_lt_mul hn).2 hq
  have hj : q % n < n := Nat.mod_lt q hn
  have hbN := lt_two_pow_aeLevels U
  have hb : (3 * U : ℤ) < 2 ^ aeLevels U := by exact_mod_cast hbN
  have hmap {l : List ℤ} (f : ℤ → ℤ) {idx : ℕ} (h : idx < l.length) :
      (l.map f).getD idx 0 = f (l.getD idx 0) := by
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ h, List.getElem_map]
  have hmem {l : List ℤ} (hl : l.length = n * n) {idx : ℕ} (h : idx < n * n) : l.getD idx 0 ∈ l := by
    rw [List.getD_eq_getElem _ _ (hl ▸ h)]; exact List.getElem_mem _
  simp only [pairFlags, aeFlags, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hq, Option.map_some, Option.getD_some, flag_eq_one_iff]
  simp only [← List.getD_eq_getElem?_getD]
  have hv := abs_le.1 (hV _ (hmem hlV hq))
  have step (k : ℕ) (hk : k < n) (c : ℕ × ℤ) :
      (instAB U V c.1 c.2).getD q 0 + (instBC n U Y c.1).getD (q % n * n + k) 0
        + (instAC U X c.1).getD (q / n * n + k) 0 =
        (X.getD (q / n * n + k) 0 + U) / 2 ^ c.1 + (Y.getD (k * n + q % n) 0 + U) / 2 ^ c.1
          + (c.2 - (V.getD q 0 + 2 * U) / 2 ^ c.1) := by
    have hk1 : q % n * n + k < n * n := by nlinarith
    have hk2 : q / n * n + k < n * n := by nlinarith
    simp only [instAB, instBC, instAC, affL]
    rw [hmap _ (by simp [hlV, hq]), hmap _ (by simp [hlV, hq]), hmap _ (hlV ▸ hq),
      hmap _ (by simp [hk1]), transposeL_getD _ _ hj hk,
      hmap _ (by simp [hlX, hk2]), hmap _ (hlX ▸ hk2)]
    simp only [prefQ, one_mul]; ring
  constructor
  · rintro ⟨k, hk, hlt⟩
    have hkx : q / n * n + k < n * n := by nlinarith
    have hky : k * n + q % n < n * n := by nlinarith
    obtain ⟨c, hc, heq⟩ := (lt_iff_exists_instance (b := aeLevels U) (hX _ (hmem hlX hkx))
      (hY _ (hmem hlY hky)) (by omega) (by linarith) (by linarith)).mp hlt
    exact ⟨c, hc, k, hk, by rw [step k hk c]; exact heq⟩
  · rintro ⟨c, hc, k, hk, heq⟩
    have hkx : q / n * n + k < n * n := by nlinarith
    have hky : k * n + q % n < n * n := by nlinarith
    exact ⟨k, hk, (lt_iff_exists_instance (b := aeLevels U) (hX _ (hmem hlX hkx))
      (hY _ (hmem hlY hky)) (by omega) (by linarith) (by linarith)).mpr
        ⟨c, hc, by rw [← step k hk c]; exact heq⟩⟩

end Lists

/-! ## Disjunction of flags across instances -/

noncomputable def orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) : List ℤ :=
  (List.range N).map fun q => flag (∃ c, S c ∧ hit c q)

@[simp] theorem length_orFlags (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    (orFlags N S hit).length = N := by simp [orFlags]

theorem orFlags_mem (N : ℕ) (S : ℕ × ℤ → Prop) (hit : ℕ × ℤ → ℕ → Prop) :
    ∀ z ∈ orFlags N S hit, z = 0 ∨ z = 1 := by
  intro z hz; obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz; unfold flag; split_ifs <;> simp

theorem orFlags_false (N : ℕ) (hit : ℕ × ℤ → ℕ → Prop) {l : List ℤ} (hl : l.length = N) :
    orFlags N (fun _ => False) hit = affL 0 0 l :=
  List.ext_getElem (by simp_all) fun _ _ _ => by simp [orFlags, affL, flag]

theorem orL_orFlags {N : ℕ} {S : ℕ × ℤ → Prop} {hit : ℕ × ℤ → ℕ → Prop} {c : ℕ × ℤ} {F : List ℤ}
    (hF : F.length = N) (hhit : ∀ q < N, hit c q ↔ F.getD q 0 = 1)
    (h01 : ∀ f ∈ F, f = 0 ∨ f = 1) :
    orL (orFlags N S hit) F = orFlags N (fun c' => S c' ∨ c' = c) hit := by
  refine List.ext_getElem (by light_side) fun i _ h2 => ?_
  have hi : i < N := by simpa using h2
  have hc := hhit i hi
  rw [List.getD_eq_getElem _ _ (hF ▸ hi)] at hc
  simp only [orL, orFlags, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  rcases h01 _ (List.getElem_mem (hF ▸ hi)) with h | h
  · rw [h, flag_congr (show (∃ c', (S c' ∨ c' = c) ∧ hit c' i) ↔ ∃ c', S c' ∧ hit c' i from
      ⟨fun ⟨c', hc', hh⟩ => ⟨c', hc'.resolve_right fun he => by grind, hh⟩,
        fun ⟨c', hc', hh⟩ => ⟨c', Or.inl hc', hh⟩⟩)]; ring
  · rw [h, flag_of (p := ∃ c', (S c' ∨ c' = c) ∧ hit c' i) ⟨c, Or.inr rfl, hc.2 h⟩]
    unfold flag; split_ifs <;> ring

def Above (ℓ b : ℕ) (c : ℕ × ℤ) : Prop := ℓ < c.1 ∧ c.1 ≤ b ∧ (c.2 = 2 ∨ c.2 = 3)

theorem above_step {ℓ b : ℕ} (h : ℓ + 1 ≤ b) :
    ∀ c, ((Above (ℓ + 1) b c ∨ c = (ℓ + 1, 2)) ∨ c = (ℓ + 1, 3)) ↔ Above ℓ b c := by
  rintro ⟨l, r⟩; simp  [Above]; omega

theorem above_self (b : ℕ) (c : ℕ × ℤ) : ¬ Above b b c := fun h => by
  have := h.1; have := h.2.1; omega

theorem above_zero_iff (b : ℕ) :
    ∀ c, (((Above 0 b c ∨ c = (0, 2)) ∨ c = (0, 3)) ∨ c = (0, 1)) ↔ c ∈ lemmaFInstances b := by
  rintro ⟨l, r⟩
  simp  [lemmaFInstances]
  constructor
  · rintro (((⟨h1, h2, h3⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
    · exact Or.inr ⟨by omega, h3⟩
    · exact Or.inr ⟨by omega, Or.inl rfl⟩
    · exact Or.inr ⟨by omega, Or.inr rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨h1, h3⟩)
    · exact Or.inr ⟨rfl, rfl⟩
    · by_cases hl : l = 0
      · subst hl; rcases h3 with rfl | rfl <;> simp
      · exact Or.inl (Or.inl (Or.inl ⟨by omega, by omega, h3⟩))

theorem orFlags_eq_pairFlags {n U : ℕ} {X Y V : List ℤ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (hV : AbsLe V U) (hlX : X.length = n * n) (hlY : Y.length = n * n) (hlV : V.length = n * n) :
    orFlags (n * n) (fun c => c ∈ lemmaFInstances (aeLevels U))
      (fun c q => (aeFlags n (instAB U V c.1 c.2) (instBC n U Y c.1) (instAC U X c.1)).getD q 0 = 1)
      = pairFlags n X Y V := by
  refine List.ext_getElem (by simp [pairFlags]) fun q h1 _ => ?_
  have hq : q < n * n := by simpa using h1
  have h := pairFlags_iff hX hY hV hlX hlY hlV hq
  rw [List.getD_eq_getElem _ _ (by omega)] at h
  simp only [orFlags, List.getElem_map, List.getElem_range]
  by_cases hp : (pairFlags n X Y V)[q] = 1
  · rw [hp, flag_of (h.1 hp)]
  · rw [flag_of_not fun hh => hp (h.2 hh)]
    have : (pairFlags n X Y V)[q] = 0 ∨ (pairFlags n X Y V)[q] = 1 := by
      simp  [pairFlags]; unfold flag; split_ifs <;> simp
    omega

end ImprovedExponents.AllEdges
