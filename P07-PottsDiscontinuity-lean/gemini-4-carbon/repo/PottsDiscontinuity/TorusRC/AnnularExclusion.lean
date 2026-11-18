module

public import PottsDiscontinuity.Torus.DiamondDualTranslation
public import PottsDiscontinuity.TorusCrossing.Cochain
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.WindingClosure

/-! # A genuine dual vertical winding blocks primal strip crossings -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology TorusCrossing SixVertex

variable {N M : ℕ}

private def walkCochain {G : SimpleGraph RotatedVertex} {a b : RotatedVertex} :
    G.Walk a b → Cell → ZMod 2
  | .nil => fun _ => 0
  | @SimpleGraph.Walk.cons _ _ u w _ _ rest =>
      fun m => ind {(max u.val.1 w.val.1, max u.val.2 w.val.2)} m + walkCochain rest m

private lemma primalEnds_max_of_adj {u w : RotatedVertex} (h : rotatedLattice.Adj u w) :
    let m : Cell := (max u.val.1 w.val.1, max u.val.2 w.val.2)
    primalEnds m = (u.val, w.val) ∨ primalEnds m = (w.val, u.val) := by
  have hu := Int.even_iff.mp u.property; unfold primalEnds; dsimp only
  rcases (abs_eq (by norm_num)).mp h.1 with h1 | h1 <;> rcases (abs_eq (by norm_num)).mp h.2 with h2 | h2
  · rw [max_eq_left (by omega), max_eq_left (by omega), ite_eq_left (by omega)]; left; ext <;> dsimp only <;> omega
  · rw [max_eq_left (by omega), max_eq_right (by omega), ite_eq_right (by omega)]; right; ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega), max_eq_left (by omega), ite_eq_right (by omega)]; left; ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega), max_eq_right (by omega), ite_eq_left (by omega)]; right; ext <;> dsimp only <;> omega

private lemma dualEnds_shift_of_adj {u w : RotatedVertex} (h : rotatedLattice.Adj u w) :
    let m : Cell := (max u.val.1 w.val.1 - 1, max u.val.2 w.val.2)
    dualEnds m = ((u.val.1 - 1, u.val.2), (w.val.1 - 1, w.val.2)) ∨
      dualEnds m = ((w.val.1 - 1, w.val.2), (u.val.1 - 1, u.val.2)) := by
  have hu := Int.even_iff.mp u.property; unfold dualEnds; dsimp only
  rcases (abs_eq (by norm_num)).mp h.1 with h1 | h1 <;> rcases (abs_eq (by norm_num)).mp h.2 with h2 | h2
  · rw [max_eq_left (by omega), max_eq_left (by omega), ite_eq_right (by omega)]; left; ext <;> dsimp only <;> omega
  · rw [max_eq_left (by omega), max_eq_right (by omega), ite_eq_left (by omega)]; right; ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega), max_eq_left (by omega), ite_eq_left (by omega)]; left; ext <;> dsimp only <;> omega
  · rw [max_eq_right (by omega), max_eq_right (by omega), ite_eq_right (by omega)]; right; ext <;> dsimp only <;> omega

private lemma cdeg_walkCochain (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (lo hi : ℤ)
    {a b : RotatedVertex} (q : (liftedStripGraph hNp hMp A lo hi).Walk a b)
    (c : Cell) (hc : TorusCrossing.IsPrimal c) :
    cdeg (walkCochain q) c = (if c = a.val then 1 else 0) + (if c = b.val then 1 else 0) := by
  induction q with
  | nil => simp [walkCochain, cdeg_zero, zmod2_two]
  | @cons u w b hadj rest ih =>
    simp only [walkCochain]; rw [cdeg_add, cdeg_ind_single _ c hc, ih]
    rcases primalEnds_max_of_adj hadj.1 with he | he <;>
    · rw [congrArg Prod.fst he, congrArg Prod.snd he]
      generalize (if c = u.val then (1 : ZMod 2) else 0) = x
      generalize (if c = w.val then (1 : ZMod 2) else 0) = y
      generalize (if c = b.val then (1 : ZMod 2) else 0) = z
      revert x y z; decide

private lemma walkCochain_support (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) (lo hi ylo yhi : ℤ)
    {a b : RotatedVertex} (q : (liftedStripGraph hNp hMp A lo hi).Walk a b)
    (hsupp : ∀ z ∈ q.support, lo ≤ z.val.1 ∧ z.val.1 ≤ hi ∧ ylo ≤ z.val.2 ∧ z.val.2 ≤ yhi)
    {m : Cell} (hm : walkCochain q m ≠ 0) :
    lo + 1 ≤ m.1 ∧ m.1 ≤ hi ∧ ylo + 1 ≤ m.2 ∧ m.2 ≤ yhi ∧
      A (periodicCoordinate hNp m.1, periodicCoordinate hMp m.2) = true := by
  induction q with
  | nil => simp [walkCochain] at hm
  | @cons u w b hadj rest ih =>
    simp only [walkCochain] at hm
    by_cases h0 : ind {(max u.val.1 w.val.1, max u.val.2 w.val.2)} m = 0
    · rw [h0, zero_add] at hm; exact ih (fun z hz => hsupp z (List.mem_cons_of_mem _ hz)) hm
    · have : m = (max u.val.1 w.val.1, max u.val.2 w.val.2) := by
        by_contra hne; exact h0 (ind_apply_of_not_mem (by simp [hne]))
      subst this
      have hu := hsupp u (by simp); have hw := hsupp w (by simp)
      have := (abs_eq (by norm_num)).mp hadj.1.1; have := (abs_eq (by norm_num)).mp hadj.1.2
      exact ⟨by omega, by omega, by omega, by omega, hadj.2.1⟩

private def periodSite (hM : Even M) (x : ℤ) (hx : Even x) (l : ℤ) : RotatedVertex :=
  liftedColumnSite x ((M : ℤ) * l) hx ((show Even (M : ℤ) by exact_mod_cast hM).mul_right l)

private lemma winding_repeat (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (K x : ℤ) (hx : Even x)
    (hpath : liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0, rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) (l : ℤ) (k : ℕ) :
    liftedBoundedConnection hNp hMp A 0 K ((M : ℤ) * l) ((M : ℤ) * (l + k))
      (periodSite hM x hx l) (periodSite hM x hx (l + k)) := by
  obtain ⟨w₀, hw₀⟩ := hpath
  have hstep (j : ℤ) : liftedBoundedConnection hNp hMp A 0 K ((M : ℤ) * j) ((M : ℤ) * (j + 1))
      (periodSite hM x hx j) (periodSite hM x hx (j + 1)) := by
    let F : liftedStripGraph hNp hMp A 0 K →g liftedStripGraph hNp hMp A 0 K :=
      ⟨verticalDeck hM j, fun h => ⟨verticalDeck_adj hM j h.1, by rw [verticalDeck_index]; exact h.2.1, h.2.2⟩⟩
    have hconn : liftedBoundedConnection hNp hMp A 0 K ((M : ℤ) * j) ((M : ℤ) * (j + 1))
        (F (liftedColumnSite x 0 hx ⟨0, rfl⟩)) (F (liftedColumnSite x M hx (by exact_mod_cast hM))) :=
      ⟨w₀.map F, fun z hz => by
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp (SimpleGraph.Walk.support_map F w₀ ▸ hz)
        have := hw₀ z' hz'; change (M : ℤ) * j ≤ z'.val.2 + (M : ℤ) * j ∧ z'.val.2 + (M : ℤ) * j ≤ (M : ℤ) * (j + 1)
        constructor <;> nlinarith⟩
    have hstart : F (liftedColumnSite x 0 hx ⟨0, rfl⟩) = periodSite hM x hx j :=
      Subtype.ext (by change (x, 0 + (M : ℤ) * j) = (x, (M : ℤ) * j); simp)
    have hend : F (liftedColumnSite x M hx (by exact_mod_cast hM)) = periodSite hM x hx (j + 1) :=
      Subtype.ext (by change (x, (M : ℤ) + (M : ℤ) * j) = (x, (M : ℤ) * (j + 1)); ext <;> ring)
    simpa only [hstart, hend] using hconn
  induction k with
  | zero => simp only [Nat.cast_zero, add_zero]; exact ⟨.nil, fun z hz => by simp at hz; subst hz; exact ⟨le_rfl, le_rfl⟩⟩
  | succ k ih =>
    obtain ⟨p, hp⟩ := ih; obtain ⟨q, hq⟩ := hstep (l + k)
    rw [show l + ((k + 1 : ℕ) : ℤ) = (l + k) + 1 by push_cast; ring]
    refine ⟨p.append q, fun z hz => ?_⟩
    rcases List.mem_append.mp (SimpleGraph.Walk.support_append _ _ ▸ hz) with hz | hz
    · have := hp z hz; constructor <;> nlinarith [show (0 : ℤ) < M by exact_mod_cast hMp]
    · have := hq z (List.mem_of_mem_tail hz); constructor <;> nlinarith [show (0 : ℤ) ≤ (M : ℤ) * k by positivity]

private lemma stripWalk_horiz (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b : ℤ) {u v : RotatedVertex}
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) (hu : a ≤ u.val.1 ∧ u.val.1 ≤ b) :
    ∀ z ∈ p.support, a ≤ z.val.1 ∧ z.val.1 ≤ b := by
  induction p with
  | nil => intro z hz; simp at hz; subst hz; exact hu
  | cons hadj _ ih => intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exact hu; exact ih hadj.2.2.2 z hz

private lemma translatedDual_succ (A : RCConfig N M) (hNp : 0 < N) (hMp : 0 < M) (i j : ℤ) :
    translatedDualConfig A (periodicCoordinate hNp (i + 1), periodicCoordinate hMp j) =
      !(A (periodicCoordinate hNp i, periodicCoordinate hMp j)) := by
  have h := congrArg nxt (periodicCoordinate_sub_one hNp (i + 1))
  rw [show periodicCoordinate hNp (i + 1) = nxt (periodicCoordinate hNp i) by
    simpa only [add_sub_cancel_right, nxt, prv, Equiv.apply_symm_apply] using h.symm]
  exact shiftRCConfig_nxt (dualConfig A) (periodicCoordinate hNp i, periodicCoordinate hMp j)

/-- A vertical primal period in A, shifted into the odd cells of its
complementary translated dual, blocks every left-to-right crossing. -/
theorem winding_blocks_dual_strip_crossing (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
    (K n : ℕ) (hmargin : K + 1 ≤ 3 * n) (x : ℤ) (hx : Even x)
    (hx0 : 0 ≤ x) (hxK : x ≤ K)
    (hpath : liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0, rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) :
    ¬ torusRCLeftStripCrossing hNp hMp (translatedDualConfig A) n := by
  rintro ⟨u, v, hu, hv, ⟨p⟩⟩
  classical
  let L : ℕ := ∑ z ∈ p.support.toFinset, z.val.2.natAbs
  have hpY (z) (hz : z ∈ p.support) : -(M : ℤ) * L ≤ z.val.2 ∧ z.val.2 ≤ (M : ℤ) * L := by
    have hc : (z.val.2.natAbs : ℤ) ≤ L := by
      exact_mod_cast Finset.single_le_sum (f := fun z : RotatedVertex => z.val.2.natAbs)
        (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr hz)
    have h1 : -z.val.2 ≤ (z.val.2.natAbs : ℤ) := by simpa using Int.le_natAbs (a := -z.val.2)
    have h2 : z.val.2 ≤ (z.val.2.natAbs : ℤ) := Int.le_natAbs
    have hM1 : (1 : ℤ) ≤ M := by exact_mod_cast hMp
    constructor <;> nlinarith
  have hpX := stripWalk_horiz hNp hMp (translatedDualConfig A) 0 ((3 * n : ℕ) : ℤ) p ⟨by omega, by omega⟩
  let L1 : ℤ := (L : ℤ) + 1
  have hrep := winding_repeat hM hNp hMp A K x hx hpath (-L1) (2 * (L + 1))
  rw [show -L1 + ((2 * (L + 1) : ℕ) : ℤ) = L1 by dsimp [L1]; omega] at hrep
  obtain ⟨q, hqY⟩ := hrep
  have hqX := stripWalk_horiz hNp hMp A 0 K q ⟨hx0, hxK⟩
  let yb : ℤ := (M : ℤ) * (-L1); let yt : ℤ := (M : ℤ) * L1; let Xf : ℤ := 4 * (n : ℤ) + 2
  have hM2 : (2 : ℤ) ≤ M := by obtain ⟨m, rfl⟩ := hM; omega
  have hyb_lt_L : yb + 2 ≤ -(M : ℤ) * L := by dsimp [yb, L1]; nlinarith
  have hL_lt_yt : (M : ℤ) * L + 2 ≤ yt := by dsimp [yt, L1]; nlinarith
  have hxXf : x ≤ Xf := by omega
  have hXf_even : Even Xf := ⟨2 * n + 1, by dsimp [Xf]; ring⟩
  have hyb_even : Even yb := (show Even (M : ℤ) by exact_mod_cast hM).mul_right (-L1)
  have hyt_even : Even yt := (show Even (M : ℤ) by exact_mod_cast hM).mul_right L1
  let C₀ (m : Cell) : ZMod 2 := walkCochain q m + ind (collar yb x Xf) m + ind (collar (yt + 1) x Xf) m
  have hq_supp {m : Cell} := walkCochain_support hNp hMp A 0 K yb yt q
    (fun z hz => ⟨(hqX z hz).1, (hqX z hz).2, (hqY z hz).1, (hqY z hz).2⟩) (m := m)
  have hx0_zero (m : Cell) (hm : m.1 ≤ 0) : C₀ m = 0 := by
    dsimp [C₀]
    rw [show walkCochain q m = 0 by by_contra hne; have := (hq_supp hne).1; omega,
      ind_apply_of_not_mem (by rw [mem_collar]; omega), ind_apply_of_not_mem (by rw [mem_collar]; omega)]; simp
  have hy0_zero (m : Cell) (hm : m.2 ≤ yb - 1) : C₀ m = 0 := by
    have : yb < yt := by linarith [hyb_lt_L, hL_lt_yt, show (0 : ℤ) ≤ (M : ℤ) * L by positivity]
    dsimp [C₀]
    rw [show walkCochain q m = 0 by by_contra hne; have := (hq_supp hne).2.2.1; omega,
      ind_apply_of_not_mem (by rw [mem_collar]; omega), ind_apply_of_not_mem (by rw [mem_collar]; omega)]; simp
  have hdeg_zero (c : Cell) (hc : TorusCrossing.IsPrimal c) (_ : -1 < c.1) (hc2 : c.1 < -1 + (3 * (n : ℤ) + 2)) : cdeg C₀ c = 0 := by
    change cdeg (fun m => (walkCochain q m + ind (collar yb x Xf) m) + ind (collar (yt + 1) x Xf) m) c = 0
    rw [cdeg_add, cdeg_add, cdeg_walkCochain hNp hMp A 0 K q c hc,
      cdeg_collar yb x Xf hxXf yb (.inl rfl) (Int.even_iff.mp (hx.add hyb_even)) (Int.even_iff.mp (hXf_even.add hyb_even)) c hc,
      cdeg_collar (yt + 1) x Xf hxXf yt (.inr (by ring)) (Int.even_iff.mp (hx.add hyt_even)) (Int.even_iff.mp (hXf_even.add hyt_even)) c hc]
    change (if c = (x, yb) then 1 else 0) + (if c = (x, yt) then 1 else 0) +
      ((if c = (x, yb) then 1 else 0) + (if c = (Xf, yb) then 1 else 0)) +
      ((if c = (x, yt) then 1 else 0) + (if c = (Xf, yt) then 1 else 0)) = 0
    rw [ite_eq_right (fun h => by subst h; dsimp [Xf] at hc2; omega : c ≠ (Xf, yb)),
      ite_eq_right (fun h => by subst h; dsimp [Xf] at hc2; omega : c ≠ (Xf, yt))]
    generalize (if c = (x, yb) then (1 : ZMod 2) else 0) = a
    generalize (if c = (x, yt) then (1 : ZMod 2) else 0) = b; revert a b; decide
  set g := leftPotential (-1) (yb - 1) C₀
  have hprim : ∀ m : Cell, -1 < m.1 → m.1 ≤ -1 + (3 * (n : ℤ) + 2) → g (dualEnds m).1 + g (dualEnds m).2 = C₀ m :=
    leftPotential_primitive (-1) (yb - 1) (3 * (n : ℤ) + 2) C₀ (fun m hm => hx0_zero m (by omega)) hy0_zero hdeg_zero
  have hp_inv {a b : RotatedVertex} (w : (liftedStripGraph hNp hMp (translatedDualConfig A) 0 ((3 * n : ℕ) : ℤ)).Walk a b)
      (hwY : ∀ z ∈ w.support, -(M : ℤ) * L ≤ z.val.2 ∧ z.val.2 ≤ (M : ℤ) * L)
      (hwX : ∀ z ∈ w.support, 0 ≤ z.val.1 ∧ z.val.1 ≤ ((3 * n : ℕ) : ℤ)) :
      g (a.val.1 - 1, a.val.2) = g (b.val.1 - 1, b.val.2) := by
    induction w with
    | nil => rfl
    | @cons z₁ z₂ b hadj _ ih =>
      have hz₁Y := hwY z₁ (by simp); have hz₂Y := hwY z₂ (by simp)
      have hz₁X := hwX z₁ (by simp); have hz₂X := hwX z₂ (by simp)
      have := (abs_eq (by norm_num)).mp hadj.1.1
      let m : Cell := (max z₁.val.1 z₂.val.1 - 1, max z₁.val.2 z₂.val.2)
      have hmY1 : yb < m.2 := by have : z₁.val.2 ≤ m.2 := le_max_left _ _; linarith [hyb_lt_L, hz₁Y.1]
      have hmY2 : m.2 ≤ yt := by have : m.2 ≤ (M : ℤ) * L := max_le hz₁Y.2 hz₂Y.2; linarith [hL_lt_yt]
      have hs := hprim m (by dsimp [m]; omega) (by dsimp [m]; omega)
      have hCm : C₀ m = 0 := by
        dsimp [C₀]; rw [show walkCochain q m = 0 by
          by_contra hne; have htd := hadj.2.1
          rw [show liftedEdgeIndex hNp hMp z₁ z₂ = (periodicCoordinate hNp (m.1 + 1), periodicCoordinate hMp m.2) by
            simp [liftedEdgeIndex, m, sub_add_cancel], translatedDual_succ, (hq_supp hne).2.2.2.2] at htd
          exact Bool.false_ne_true htd,
          ind_apply_of_not_mem (by rw [mem_collar]; omega), ind_apply_of_not_mem (by rw [mem_collar]; omega)]; simp
      rw [hCm] at hs
      have hstep_eq : g (z₁.val.1 - 1, z₁.val.2) = g (z₂.val.1 - 1, z₂.val.2) := by
        rcases dualEnds_shift_of_adj hadj.1 with hd | hd <;>
          (rw [congrArg Prod.fst hd, congrArg Prod.snd hd] at hs; dsimp only at hs
           generalize g (z₁.val.1 - 1, z₁.val.2) = ga at hs ⊢
           generalize g (z₂.val.1 - 1, z₂.val.2) = gb at hs ⊢; revert ga gb hs; decide)
      exact hstep_eq.trans (ih (fun z hz => hwY z (List.mem_cons_of_mem _ hz)) (fun z hz => hwX z (List.mem_cons_of_mem _ hz)))
  have hguv : g (-1, u.val.2) = g (3 * (n : ℤ) - 1, v.val.2) := by simpa [hu, hv] using hp_inv p hpY hpX
  have hgu : g (-1, u.val.2) = 0 := by
    dsimp [g, leftPotential]; rw [rowSum_of_le (-1) C₀ u.val.2 (-1) le_rfl, zero_add]
    refine Finset.sum_eq_zero fun k _ => ?_
    unfold leftDefect; split_ifs
    · unfold cdeg; simp [hx0_zero (-1, k) (by omega), hx0_zero (-1, k + 1) (by omega), hx0_zero (0, k) le_rfl, hx0_zero (0, k + 1) le_rfl]
    · rfl
  have hC3n (y : ℤ) (hy : y ≤ yt) : C₀ (3 * (n : ℤ), y) = if y = yb then 1 else 0 := by
    dsimp [C₀]
    rw [show walkCochain q (3 * (n : ℤ), y) = 0 by by_contra hne; have := (hq_supp hne).2.1; omega, zero_add,
      show ind (collar (yt + 1) x Xf) (3 * (n : ℤ), y) = 0 from ind_apply_of_not_mem (by rw [mem_collar]; omega), add_zero]
    by_cases hyb : y = yb
    · subst hyb; rw [ite_eq_left rfl]; exact ind_apply_of_mem (by rw [mem_collar]; dsimp [Xf]; omega)
    · rw [ite_eq_right hyb]; exact ind_apply_of_not_mem (by rw [mem_collar]; omega)
  have hdesc_step (z₂ : ℤ) (hpar : (3 * (n : ℤ) + z₂) % 2 = 0) (hzyt : z₂ ≤ yt) :
      g (3 * (n : ℤ) - 1, z₂) = g (3 * (n : ℤ) - 1, z₂ - 2) + (if z₂ - 2 < yb ∧ yb ≤ z₂ then 1 else 0) := by
    have hm1 : dualEnds (3 * (n : ℤ), z₂) = ((3 * (n : ℤ) - 1, z₂), (3 * (n : ℤ), z₂ - 1)) := by
      unfold dualEnds; rw [ite_eq_left hpar]
    have hm2 : dualEnds (3 * (n : ℤ), z₂ - 1) = ((3 * (n : ℤ), z₂ - 1), (3 * (n : ℤ) - 1, z₂ - 2)) := by
      unfold dualEnds; rw [ite_eq_right (by omega)]; exact Prod.ext rfl (Prod.ext rfl (by dsimp only; omega))
    have hs1 := hprim (3 * (n : ℤ), z₂) (by omega) (by omega)
    have hs2 := hprim (3 * (n : ℤ), z₂ - 1) (by omega) (by omega)
    rw [hm1, hC3n z₂ hzyt] at hs1; rw [hm2, hC3n (z₂ - 1) (by omega)] at hs2; dsimp only at hs1 hs2
    have hcond : (if z₂ = yb then (1 : ZMod 2) else 0) + (if z₂ - 1 = yb then 1 else 0) =
        if z₂ - 2 < yb ∧ yb ≤ z₂ then 1 else 0 := by split_ifs <;> first | decide | omega
    rw [← hcond]
    generalize g (3 * (n : ℤ) - 1, z₂) = a at hs1 ⊢
    generalize g (3 * (n : ℤ), z₂ - 1) = b at hs1 hs2
    generalize g (3 * (n : ℤ) - 1, z₂ - 2) = c at hs2 ⊢
    generalize (if z₂ = yb then (1 : ZMod 2) else 0) = d1 at hs1 ⊢
    generalize (if z₂ - 1 = yb then (1 : ZMod 2) else 0) = d2 at hs2 ⊢
    revert a b c d1 d2 hs1 hs2; decide
  have hdesc_iter (k : ℕ) : ∀ (z₂ : ℤ), (3 * (n : ℤ) + z₂) % 2 = 0 → z₂ ≤ yt →
      g (3 * (n : ℤ) - 1, z₂) = g (3 * (n : ℤ) - 1, z₂ - 2 * (k : ℤ)) +
        if z₂ - 2 * (k : ℤ) < yb ∧ yb ≤ z₂ then 1 else 0 := by
    induction k with
    | zero => intro z₂ _ _; simp
    | succ k ih =>
      intro z₂ hpar hzyt
      rw [hdesc_step z₂ hpar hzyt, ih (z₂ - 2) (by omega) (by omega),
        show z₂ - 2 - 2 * (k : ℤ) = z₂ - 2 * ((k + 1 : ℕ) : ℤ) by push_cast; ring, add_assoc]
      congr 1; split_ifs <;> first | decide | (push_cast at *; omega)
  have hvpar : (3 * (n : ℤ) + v.val.2) % 2 = 0 := by simpa [hv] using Int.even_iff.mp v.property
  have hvY := hpY v p.end_mem_support
  let k : ℕ := (v.val.2 - yb).toNat + 1
  have hgv : g (3 * (n : ℤ) - 1, v.val.2) = 1 := by
    rw [hdesc_iter k v.val.2 hvpar (by linarith [hvY.2, hL_lt_yt]),
      ite_eq_left ⟨by dsimp [k]; omega, by linarith [hvY.1, hyb_lt_L]⟩]
    have hg_bot : g (3 * (n : ℤ) - 1, v.val.2 - 2 * (k : ℤ)) = 0 := by
      dsimp [g, leftPotential]; unfold TorusCrossing.rowSum
      rw [Finset.sum_eq_zero fun a _ => hy0_zero _ (by omega),
        show leftCorr (-1) (yb - 1) C₀ _ = 0 by unfold leftCorr; rw [Finset.Ico_eq_empty (by dsimp [k]; omega)]; simp, add_zero]
    rw [hg_bot, zero_add]
  rw [hgu, hgv] at hguv; exact absurd hguv (by decide)

/-- The actual winding-and-single-open-seam event transfers into the source
barrier B under translated complementary duality. -/
theorem primalWinding_translatedDual_mem_barrier (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (K n : ℕ) (hmargin : K + 1 ≤ 3 * n)
    (A : RCConfig N M) (hA : A ∈ primalWindingSingleSeam hNp hMp hM K) :
    translatedDualConfig A ∈ torusRCBarrier hNp hMp n := by
  obtain ⟨x, hx, hx0, hxK, hpath, i₀, hopen, hclosed⟩ := hA
  refine ⟨winding_blocks_dual_strip_crossing hM hNp hMp A K n hmargin x hx hx0 hxK hpath, nxt i₀, ?_, fun i hi => ?_⟩
  · change shiftRCConfig (dualConfig A) (nxt i₀, ⟨0, hMp⟩) = false
    rw [shiftRCConfig_nxt (dualConfig A) (i₀, ⟨0, hMp⟩)]; change Bool.not (A (i₀, ⟨0, hMp⟩)) = false; rw [hopen]; rfl
  · change Bool.not (A (prv i, ⟨0, hMp⟩)) = true
    rw [hclosed (prv i) fun heq => hi (by simpa only [nxt, prv, Equiv.apply_symm_apply] using congrArg nxt heq)]; rfl

end PottsDiscontinuity.TorusRC
