module

public import PottsDiscontinuity.TorusTopology.MidpointCyclicTurning

/-! The essential-loop turning classification, on the exact torus loop carrier
`Torus.Loop` used in Corollary 3.13. -/

@[expose] public section

namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Finset Torus TorusLoops TorusRC Planar.Medial
open PottsDiscontinuity.SixVertex

private def compassWordTurn : List (Fin 4) → ℤ
  | [] | [_] => 0
  | a :: b :: l => primalCompassQuarterTurn a b + compassWordTurn (b :: l)

private lemma compassWordTurn_replicate (a : Fin 4) : ∀ n : ℕ, compassWordTurn (List.replicate n a) = 0
  | 0 | 1 => rfl
  | n + 2 => by
    have : primalCompassQuarterTurn a a = 0 := by fin_cases a <;> decide
    simpa [List.replicate_succ, compassWordTurn, this] using compassWordTurn_replicate a (n + 1)

private lemma compassWord_zip_close (a b : Fin 4) (l : List (Fin 4)) :
    ((a :: l).zipWith primalCompassQuarterTurn (l ++ [b])).sum =
      compassWordTurn (a :: l) + primalCompassQuarterTurn ((a :: l).getLast (by simp)) b := by
  induction l generalizing a with
  | nil => simp [compassWordTurn]
  | cons c l ih =>
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons, compassWordTurn]
    rw [ih]; change _ = _ + primalCompassQuarterTurn ((c :: l).getLast (by simp)) b; omega

private lemma compassWordTurn_append_nonempty (a b : Fin 4) (l r : List (Fin 4)) :
    compassWordTurn ((a :: l) ++ b :: r) = compassWordTurn (a :: l) +
      primalCompassQuarterTurn ((a :: l).getLast (by simp)) b + compassWordTurn (b :: r) := by
  induction l generalizing a with
  | nil => simp [compassWordTurn]
  | cons c l ih =>
    simp only [List.cons_append, compassWordTurn] at ih ⊢
    rw [ih]; change _ = _ + primalCompassQuarterTurn ((c :: l).getLast (by simp)) b + _; omega

private def cycTurn (l : List (Fin 4)) : ℤ := (l.zipWith primalCompassQuarterTurn (l.rotate 1)).sum

private lemma cycTurn_append_rep_bound {l : List (Fin 4)} (hl : l ≠ []) (b : Fin 4) {n : ℕ} (hn : 0 < n) :
    |cycTurn (l ++ List.replicate n b) - cycTurn l| ≤ 6 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  cases l with
  | nil => exact (hl rfl).elim
  | cons a l =>
    have hcons (x : Fin 4) (xs : List (Fin 4)) :
        cycTurn (x :: xs) = compassWordTurn (x :: xs) + primalCompassQuarterTurn ((x :: xs).getLast (by simp)) x := by
      unfold cycTurn; rw [List.rotate_cons_succ, List.rotate_zero]; exact compassWord_zip_close x x xs
    have hlast : ((a :: l) ++ b :: List.replicate k b).getLast (by simp) = b := by
      rw [List.getLast_append_of_right_ne_nil _ _ (by simp)]
      simpa only [List.replicate_succ] using List.getLast_replicate_succ k b
    have hc := hcons a (l ++ b :: List.replicate k b)
    change cycTurn ((a :: l) ++ b :: List.replicate k b) =
      compassWordTurn ((a :: l) ++ b :: List.replicate k b) +
        primalCompassQuarterTurn (((a :: l) ++ b :: List.replicate k b).getLast (by simp)) a at hc
    have hb0 : compassWordTurn (b :: List.replicate k b) = 0 := by
      simpa only [List.replicate_succ] using compassWordTurn_replicate b (k + 1)
    rw [hlast, compassWordTurn_append_nonempty, hb0] at hc
    have hq (x y : Fin 4) : |primalCompassQuarterTurn x y| ≤ 2 := by fin_cases x <;> fin_cases y <;> decide
    have h1 := abs_le.mp (hq ((a :: l).getLast (by simp)) b)
    have h2 := abs_le.mp (hq b a)
    have h3 := abs_le.mp (hq ((a :: l).getLast (by simp)) a)
    have ho := hcons a l
    rw [List.replicate_succ, abs_le]; omega

private def seqCompass (f : ℕ → ℤ × ℤ) (h : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1))) (n : ℕ) : Fin 4 :=
  squareDartCompass ⟨⟨f n, f (n + 1)⟩, h n⟩

private def seqWalk (f : ℕ → ℤ × ℤ) (h : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1))) :
    (n : ℕ) → FK.squareLattice.Walk (f 0) (f n)
  | 0 => .nil
  | n + 1 => (seqWalk f h n).concat (h n)

private lemma seqWalk_props (f : ℕ → ℤ × ℤ) (h : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1))) (n : ℕ) :
    (seqWalk f h n).length = n ∧
    (seqWalk f h n).support = (List.range (n + 1)).map f ∧
    squareWalkCompassDirections (seqWalk f h n) = (List.range n).map (seqCompass f h) := by
  induction n with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hl, hs, hc⟩ := ih
    refine ⟨by simp [seqWalk, hl], by simp [seqWalk, Walk.support_concat, hs, List.range_succ], ?_⟩
    simp only [seqWalk, squareWalkCompassDirections, Walk.darts_concat, List.concat_eq_append, List.map_append, List.map_singleton]
    change squareWalkCompassDirections (seqWalk f h n) ++ _ = _
    rw [hc, List.range_succ, List.map_append, List.map_singleton]; rfl

private def straightWalk (z : ℤ × ℤ) (p : Port) : (n : ℕ) → FK.squareLattice.Walk z (z + n • portVector p)
  | 0 => (Walk.nil : FK.squareLattice.Walk z z).copy rfl (by simp)
  | n + 1 => ((straightWalk z p n).concat (squareLattice_adj_portVector (z + n • portVector p) p)).copy rfl
      (by rw [add_nsmul, one_nsmul, add_assoc])

private lemma straightWalk_props (z : ℤ × ℤ) (p : Port) (n : ℕ) :
    (straightWalk z p n).support = (List.range (n + 1)).map (fun k => z + k • portVector p) ∧
    (straightWalk z p n).IsPath ∧
    squareWalkCompassDirections (straightWalk z p n) = List.replicate n (portCompass p) := by
  have hs : ∀ m, (straightWalk z p m).support = (List.range (m + 1)).map (fun k => z + k • portVector p) := by
    intro m; induction m with
    | zero => simp [straightWalk]
    | succ m ih => simp [straightWalk, Walk.support_copy, Walk.support_concat, ih, List.range_succ]; ext <;> simp <;> ring
  have hinj : Function.Injective (fun k : ℕ => z + k • portVector p) := fun a b hab => by
    cases p <;> (have hx := congrArg Prod.fst hab; have hy := congrArg Prod.snd hab; simp [portVector] at hx hy; omega)
  have hc : ∀ m, squareWalkCompassDirections (straightWalk z p m) = List.replicate m (portCompass p) := by
    intro m; induction m with
    | zero => simp [straightWalk, squareWalkCompassDirections]
    | succ m ih =>
      simp only [straightWalk, squareWalkCompassDirections, Walk.darts_copy, Walk.darts_concat,
        List.concat_eq_append, List.map_append, List.map_singleton]
      change squareWalkCompassDirections (straightWalk z p m) ++ _ = _
      rw [ih, List.replicate_succ']
      exact congrArg (List.replicate m (portCompass p) ++ [·])
        (squareDartCompass_eq_portCompass _ p rfl)
  exact ⟨hs n, by rw [Walk.isPath_def, hs n]; exact List.nodup_range.map hinj, hc n⟩

private lemma per_decomp (f : ℕ → ℤ × ℤ) (L : ℕ) (D : ℤ × ℤ) (hp : ∀ n, f (n + L) = f n + D) (n : ℕ) :
    f n = f (n % L) + (n / L) • D := by
  have hh (a k : ℕ) : f (a + k * L) = f a + k • D := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, ← Nat.add_assoc, hp, ih, add_nsmul, one_nsmul]; abel
  conv_lhs => rw [← Nat.mod_add_div n L, Nat.mul_comm L, hh]

private lemma rightward_periodic_turn_zero
    (f : ℕ → ℤ × ℤ) (hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1)))
    (hf : Function.Injective f) (L : ℕ) (D : ℤ × ℤ) (hL : 0 < L)
    (hDx : 0 < D.1) (hper : ∀ n, f (n + L) = f n + D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (seqCompass f hadj n) (seqCompass f hadj (n + 1))) = 0 := by
  let H (z : ℤ × ℤ) : ℤ := D.1 * z.2 - D.2 * z.1
  have hHd (z : ℤ × ℤ) (m : ℕ) : H (z + m • D) = H z := by
    change D.1 * (z.2 + m • D.2) - D.2 * (z.1 + m • D.1) = _; simp only [nsmul_eq_mul, H]; ring
  obtain ⟨k, hk, hmax0⟩ := Finset.exists_max_image (range L) (fun n => H (f n)) ⟨0, mem_range.mpr hL⟩
  have hmax (n : ℕ) : H (f n) ≤ H (f k) := by
    rw [per_decomp f L D hper n, hHd]; exact hmax0 (n % L) (mem_range.mpr (Nat.mod_lt n hL))
  let g (n : ℕ) := f (k + n)
  have hgadj (n : ℕ) : FK.squareLattice.Adj (g n) (g (n + 1)) := by simpa [g, Nat.add_assoc] using hadj (k + n)
  have hginj : Function.Injective g := fun a b he => by have := hf he; omega
  have hgper (n : ℕ) : g (n + L) = g n + D := by simpa [g, Nat.add_assoc] using hper (k + n)
  let p := seqWalk g hgadj (32 * L)
  obtain ⟨hplen, hpsupp, hpdirs⟩ := seqWalk_props g hgadj (32 * L)
  have hpPath : p.IsPath := by rw [Walk.isPath_def, hpsupp]; exact List.nodup_range.map hginj
  let u := g 0; let v := g (32 * L)
  have hv_eq : v = u + (32 : ℕ) • D := by
    have := per_decomp g L D hgper (32 * L)
    rwa [Nat.mul_mod_left, Nat.mul_div_cancel _ hL] at this
  have hxy : u.1 < v.1 := by rw [hv_eq]; change u.1 < u.1 + (32 : ℕ) • D.1; simp only [nsmul_eq_mul]; omega
  have hHeq : H u = H v := by rw [hv_eq, hHd]
  let Y := max u.2 v.2 + 1
  have huY : u.2 < Y := by dsimp [Y]; omega
  have hvY : u.2 ≤ Y ∧ v.2 < Y := ⟨huY.le, by dsimp [Y]; omega⟩
  let wN : FK.squareLattice.Walk v (v.1, Y) :=
    (straightWalk v .north (Y - v.2).toNat).copy rfl (by ext <;> simp [portVector, Int.toNat_of_nonneg (by omega : 0 ≤ Y - v.2)])
  let wW : FK.squareLattice.Walk (v.1, Y) (u.1, Y) :=
    (straightWalk (v.1, Y) .west (v.1 - u.1).toNat).copy rfl (by ext <;> simp [portVector, Int.toNat_of_nonneg (by omega : 0 ≤ v.1 - u.1)])
  let wS : FK.squareLattice.Walk (u.1, Y) u :=
    (straightWalk (u.1, Y) .south (Y - u.2).toNat).copy rfl (by ext <;> simp [portVector, Int.toNat_of_nonneg (by omega : 0 ≤ Y - u.2)])
  let ret := (wN.append wW).append wS
  have hmN (z : ℤ × ℤ) : z ∈ wN.support → z.1 = v.1 ∧ v.2 ≤ z.2 ∧ z.2 ≤ Y := fun hz => by
    rw [Walk.support_copy, (straightWalk_props v .north _).1, List.mem_map] at hz
    obtain ⟨m, hm, rfl⟩ := hz; have := List.mem_range.mp hm
    have := Int.toNat_of_nonneg (by omega : 0 ≤ Y - v.2); simp [portVector]; omega
  have hmW (z : ℤ × ℤ) : z ∈ wW.support → z.2 = Y ∧ u.1 ≤ z.1 ∧ z.1 ≤ v.1 := fun hz => by
    rw [Walk.support_copy, (straightWalk_props (v.1, Y) .west _).1, List.mem_map] at hz
    obtain ⟨m, hm, rfl⟩ := hz; have := List.mem_range.mp hm
    have := Int.toNat_of_nonneg (by omega : 0 ≤ v.1 - u.1); simp [portVector]; omega
  have hmS (z : ℤ × ℤ) : z ∈ wS.support → z.1 = u.1 ∧ u.2 ≤ z.2 ∧ z.2 ≤ Y := fun hz => by
    rw [Walk.support_copy, (straightWalk_props (u.1, Y) .south _).1, List.mem_map] at hz
    obtain ⟨m, hm, rfl⟩ := hz; have := List.mem_range.mp hm
    have := Int.toNat_of_nonneg (by omega : 0 ≤ Y - u.2); simp [portVector]; omega
  have htail {a b : ℤ × ℤ} {w : FK.squareLattice.Walk a b} (hw : w.IsPath) {z : ℤ × ℤ} (hz : z ∈ w.support.tail) :
      z ∈ w.support ∧ z ≠ a := by
    have hn := hw.support_nodup; rw [← w.cons_tail_support, List.nodup_cons] at hn
    exact ⟨List.mem_of_mem_tail hz, fun h => hn.1 (h ▸ hz)⟩
  have hpN : wN.IsPath := by simp only [wN, Walk.isPath_copy]; exact (straightWalk_props _ _ _).2.1
  have hpW : wW.IsPath := by simp only [wW, Walk.isPath_copy]; exact (straightWalk_props _ _ _).2.1
  have hpS : wS.IsPath := by simp only [wS, Walk.isPath_copy]; exact (straightWalk_props _ _ _).2.1
  have hretPath : ret.IsPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_append]
    refine List.Nodup.append (List.Nodup.append hpN.support_nodup hpW.support_nodup.tail ?_) hpS.support_nodup.tail ?_
    · rw [List.disjoint_left]; intro z hzN hzW
      exact (htail hpW hzW).2 (Prod.ext (hmN z hzN).1 (hmW z (List.mem_of_mem_tail hzW)).1)
    · rw [List.disjoint_left]; intro z hzNW hzS
      obtain ⟨hzS_mem, hzSu⟩ := htail hpS hzS
      have hS' := hmS z hzS_mem
      rcases List.mem_append.mp hzNW with hzN | hzW
      · have := hmN z hzN; omega
      · exact hzSu (Prod.ext hS'.1 (hmW z (List.mem_of_mem_tail hzW)).1)
  have hcycle : (p.append ret).IsCycle := by
    refine hpPath.isCycle_append hretPath ?_ (Or.inl (by rw [hplen]; omega))
    rw [List.disjoint_left]; intro z hzp hzr
    obtain ⟨hzp_mem, hzu⟩ := htail hpPath hzp
    obtain ⟨hzr_mem, hzv⟩ := htail hretPath hzr
    rw [hpsupp, List.mem_map] at hzp_mem
    obtain ⟨n, _, rfl⟩ := hzp_mem
    have hle : H (g n) ≤ H u := hmax (k + n)
    simp only [ret, Walk.support_append, List.mem_append] at hzr_mem
    rcases hzr_mem with (hzN | hzW) | hzS
    · obtain ⟨hx, hy1, _⟩ := hmN _ hzN
      have hy : v.2 < (g n).2 := lt_of_le_of_ne hy1 fun he => hzv (Prod.ext hx he.symm)
      dsimp [H] at hHeq hle; rw [hx] at hle; nlinarith [mul_pos hDx (sub_pos.mpr hy)]
    · obtain ⟨hy, hx1, hx2⟩ := hmW _ (List.mem_of_mem_tail hzW)
      dsimp [H] at hHeq hle; rw [hy] at hle
      rcases le_total 0 D.2 with hDy | hDy
      · nlinarith [mul_pos hDx (sub_pos.mpr hvY.2), mul_nonneg hDy (sub_nonneg.mpr hx2)]
      · nlinarith [mul_pos hDx (sub_pos.mpr huY), mul_nonneg (neg_nonneg.mpr hDy) (sub_nonneg.mpr hx1)]
    · obtain ⟨hx, hy1, _⟩ := hmS _ (List.mem_of_mem_tail hzS)
      have hy : u.2 < (g n).2 := lt_of_le_of_ne hy1 fun he => hzu (Prod.ext hx he.symm)
      dsimp [H] at hle; rw [hx] at hle; nlinarith [mul_pos hDx (sub_pos.mpr hy)]
  have hturn := squareWalkCyclicTurn_eq_four_or_neg_four _ hcycle
  change cycTurn (squareWalkCompassDirections (p.append ret)) = 4 ∨
    cycTurn (squareWalkCompassDirections (p.append ret)) = -4 at hturn
  let a := seqCompass g hgadj
  let W := (List.range (32 * L)).map a
  have hdirs : squareWalkCompassDirections (p.append ret) =
      W ++ List.replicate (Y - v.2).toNat 1 ++ List.replicate (v.1 - u.1).toNat 2 ++ List.replicate (Y - u.2).toNat 3 := by
    simp only [ret, wN, wW, wS, squareWalkCompassDirections, Walk.darts_append, Walk.darts_copy, List.map_append]
    change squareWalkCompassDirections p ++ (squareWalkCompassDirections (straightWalk v .north _) ++
      squareWalkCompassDirections (straightWalk (v.1, Y) .west _) ++
      squareWalkCompassDirections (straightWalk (u.1, Y) .south _)) = _
    dsimp only [p]
    rw [hpdirs, (straightWalk_props _ _ _).2.2, (straightWalk_props _ _ _).2.2, (straightWalk_props _ _ _).2.2]
    simp [W, a, portCompass, List.append_assoc]
  rw [hdirs] at hturn
  have hWne : W ≠ [] := by simp [W]; omega
  have hW1 : W ++ List.replicate (Y - v.2).toNat 1 ≠ [] := fun h => hWne (List.append_eq_nil_iff.mp h).1
  have hW2 : W ++ List.replicate (Y - v.2).toNat 1 ++ List.replicate (v.1 - u.1).toNat 2 ≠ [] :=
    fun h => hW1 (List.append_eq_nil_iff.mp h).1
  have hb1 := abs_le.mp (cycTurn_append_rep_bound hWne 1 (by omega : 0 < (Y - v.2).toNat))
  have hb2 := abs_le.mp (cycTurn_append_rep_bound hW1 2 (by omega : 0 < (v.1 - u.1).toNat))
  have hb3 := abs_le.mp (cycTurn_append_rep_bound hW2 3 (by omega : 0 < (Y - u.2).toNat))
  have ha_per (n : ℕ) : a (n + L) = a n := by
    dsimp only [a, seqCompass, squareDartCompass]
    simp only [show n + L + 1 = n + 1 + L by omega, hgper, Prod.fst_add, Prod.snd_add, add_lt_add_iff_right]
  have ha32 : a (32 * L) = a 0 := by
    have hm (r : ℕ) : a (r * L) = a 0 := by induction r with | zero => simp | succ r ih => rw [Nat.succ_mul, ha_per, ih]
    exact hm 32
  have hsum_list (t : ℕ → ℤ) (m : ℕ) : ((List.range m).map t).sum = ∑ i ∈ range m, t i := by
    induction m with | zero => simp | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  let t (n : ℕ) := primalCompassQuarterTurn (a n) (a (n + 1))
  have ht_per (n : ℕ) : t (n + L) = t n := by dsimp [t]; rw [ha_per, show n + L + 1 = n + 1 + L by omega, ha_per]
  have hshift_per (q : ℕ → ℤ) (hq : ∀ n, q (n + L) = q n) (m : ℕ) : (∑ i ∈ range L, q (m + i)) = ∑ i ∈ range L, q i := by
    have h1 := Finset.sum_range_add q m L; have h2 := Finset.sum_range_add q L m
    have hh : (∑ i ∈ range m, q (L + i)) = ∑ i ∈ range m, q i := Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm, hq]
    rw [hh, Nat.add_comm L m] at h2; omega
  have hmul_per (r : ℕ) : (∑ i ∈ range (r * L), t i) = (r : ℤ) * ∑ i ∈ range L, t i := by
    induction r with
    | zero => simp
    | succ r ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, hshift_per t ht_per]; push_cast; ring
  have hW_eq : cycTurn W = 32 * ∑ i ∈ range L, t i := by
    unfold cycTurn; rw [rotate_range_map_one a (32 * L) (by omega) ha32, List.zipWith_map, List.zipWith_self, hsum_list]
    simpa using hmul_per 32
  have hz : (∑ i ∈ range L, t i) = 0 := by rcases hturn with ht | ht <;> omega
  let tf (n : ℕ) := primalCompassQuarterTurn (seqCompass f hadj n) (seqCompass f hadj (n + 1))
  have htf_per (n : ℕ) : tf (n + L) = tf n := by
    have hf_per (m : ℕ) : seqCompass f hadj (m + L) = seqCompass f hadj m := by
      dsimp only [seqCompass, squareDartCompass]
      simp only [show m + L + 1 = m + 1 + L by omega, hper, Prod.fst_add, Prod.snd_add, add_lt_add_iff_right]
    dsimp [tf]; rw [hf_per, show n + L + 1 = n + 1 + L by omega, hf_per]
  have htk (i : ℕ) : t i = tf (k + i) := by simp only [t, tf, a, seqCompass, squareDartCompass, g, Nat.add_assoc]
  simp_rw [htk] at hz
  exact (hshift_per tf htf_per k).symm.trans hz

private lemma periodic_lattice_turn_zero
    (f : ℕ → ℤ × ℤ) (hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1)))
    (hf : Function.Injective f) (L : ℕ) (D : ℤ × ℤ) (hL : 0 < L)
    (hD : D ≠ (0, 0)) (hper : ∀ n, f (n + L) = f n + D) :
    (∑ n ∈ range L, primalCompassQuarterTurn (seqCompass f hadj n) (seqCompass f hadj (n + 1))) = 0 := by
  let rot (z : ℤ × ℤ) : ℤ × ℤ := (-z.2, z.1)
  have rot_inj : Function.Injective rot := fun u v h => Prod.ext (congrArg Prod.snd h) (by have := congrArg Prod.fst h; dsimp [rot] at this; omega)
  have rot_add (u v : ℤ × ℤ) : rot (u + v) = rot u + rot v := by ext <;> simp [rot, add_comm]
  have rot_adj (u v : ℤ × ℤ) : FK.squareLattice.Adj (rot u) (rot v) ↔ FK.squareLattice.Adj u v := by
    rw [FK.squareLattice_adj_iff, FK.squareLattice_adj_iff]; dsimp [rot]; omega
  have rot_turn (g : ℕ → ℤ × ℤ) (hg : ∀ n, FK.squareLattice.Adj (g n) (g (n + 1))) :
      (∑ n ∈ range L, primalCompassQuarterTurn
        (seqCompass (fun n => rot (g n)) (fun n => (rot_adj _ _).mpr (hg n)) n)
        (seqCompass (fun n => rot (g n)) (fun n => (rot_adj _ _).mpr (hg n)) (n + 1))) =
      ∑ n ∈ range L, primalCompassQuarterTurn (seqCompass g hg n) (seqCompass g hg (n + 1)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    have hcomp {u v : ℤ × ℤ} (h : FK.squareLattice.Adj u v) :
        squareDartCompass ⟨⟨rot u, rot v⟩, (rot_adj u v).mpr h⟩ = squareDartCompass ⟨⟨u, v⟩, h⟩ + 1 := by
      rcases (FK.squareLattice_adj_iff u v).mp h with ⟨hx | hx, hy⟩ | ⟨hx, hy | hy⟩ <;>
        (dsimp only [squareDartCompass, rot]; simp only [neg_lt_neg_iff]; split_ifs <;> norm_num <;> omega)
    have hadd1 (a b : Fin 4) : primalCompassQuarterTurn (a + 1) (b + 1) = primalCompassQuarterTurn a b := by
      fin_cases a <;> fin_cases b <;> decide
    dsimp [seqCompass]; rw [hcomp, hcomp, hadd1]
  let f₁ := fun n => rot (f n); let f₂ := fun n => rot (f₁ n); let f₃ := fun n => rot (f₂ n)
  let D₁ := rot D; let D₂ := rot D₁; let D₃ := rot D₂
  have ha₁ (n : ℕ) := (rot_adj _ _).mpr (hadj n)
  have ha₂ (n : ℕ) := (rot_adj _ _).mpr (ha₁ n)
  have ha₃ (n : ℕ) := (rot_adj _ _).mpr (ha₂ n)
  have hp₁ (n : ℕ) : f₁ (n + L) = f₁ n + D₁ := by dsimp [f₁, D₁]; rw [hper, rot_add]
  have hp₂ (n : ℕ) : f₂ (n + L) = f₂ n + D₂ := by dsimp [f₂, D₂]; rw [hp₁, rot_add]
  have hp₃ (n : ℕ) : f₃ (n + L) = f₃ n + D₃ := by dsimp [f₃, D₃]; rw [hp₂, rot_add]
  have hpos : 0 < D.1 ∨ 0 < D₁.1 ∨ 0 < D₂.1 ∨ 0 < D₃.1 := by
    dsimp [D₁, D₂, D₃, rot]; by_contra hn; simp only [not_or, not_lt] at hn; exact hD (Prod.ext (by omega) (by omega))
  rcases hpos with h0 | h1 | h2 | h3
  · exact rightward_periodic_turn_zero f hadj hf L D hL h0 hper
  · rw [← rot_turn f hadj]; exact rightward_periodic_turn_zero f₁ ha₁ (rot_inj.comp hf) L D₁ hL h1 hp₁
  · rw [← rot_turn f hadj, ← rot_turn f₁ ha₁]
    exact rightward_periodic_turn_zero f₂ ha₂ (rot_inj.comp (rot_inj.comp hf)) L D₂ hL h2 hp₂
  · rw [← rot_turn f hadj, ← rot_turn f₁ ha₁, ← rot_turn f₂ ha₂]
    exact rightward_periodic_turn_zero f₃ ha₃ (rot_inj.comp (rot_inj.comp (rot_inj.comp hf))) L D₃ hL h3 hp₃

/-- A loop with nonzero homological winding has rotation number zero. -/
theorem loopRotationNumber_eq_zero_of_nonzero_winding {N M : ℕ}
    (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
    (q : Loop hN hM (rcSmoothing A))
    (hw : loopVertical (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A))
        (PottsDiscontinuity.TorusLoops.horizontalCross i) q ≠ 0) :
    loopRotationNumber (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)) q = 0 := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep q
  let ω := checkerArrows N M; let s := rcSmoothing A; let h := checkerArrows_compatible hN hM s
  let f := loopMidpointPosition ω s h d
  let L := loopPeriod ω s h d
  let D := ((loopDeckDisplacement ω s h d i j).1 + (loopDeckDisplacement ω s h d i j).2,
    (loopDeckDisplacement ω s h d i j).2 - (loopDeckDisplacement ω s h d i j).1)
  have hD : D ≠ (0, 0) := (rotated_loopDeckDisplacement_ne_zero_iff ω s h d i j).mpr hw
  have hL : 0 < L := loopPeriod_pos ω s h d
  have hper : ∀ n, f (n + L) = f n + D := loopMidpointPosition_add_period ω s h d i j
  have hadj : ∀ n, FK.squareLattice.Adj (f n) (f (n + 1)) := loopMidpointPosition_adj ω s h d
  have hinj : Function.Injective f := fun a b he => by
    have hlift : loopLiftPosition ω s h d a = loopLiftPosition ω s h d b ∧
        ((directedStep ω s h)^[a] d).val.2 = ((directedStep ω s h)^[b] d).val.2 := by
      rcases (rotatedMidpoint_eq_iff _ _ _ _).mp he with hh | ⟨hz, hp⟩
      · exact hh
      · let e := (directedStep ω s h)^[a] d; let e' := (directedStep ω s h)^[b] d
        have hpz := loopLiftPosition_projection ω s h d a
        have hpf := loopLiftPosition_projection ω s h d b
        have hstep := loopLiftPosition_step_projection (Fin.pos d.val.1.1) (Fin.pos d.val.1.2)
          s e.val (loopLiftPosition ω s h d a) (congrArg Prod.fst hpz) (congrArg Prod.snd hpz)
        have hinc : (horizontalIncrement e.val, verticalIncrement e.val) = portVector e.val.2 := by
          rcases e with ⟨⟨v, p⟩, _⟩; cases p <;> rfl
        have heq : e'.val = edgeReverse e.val := Prod.ext (by rw [← hpf, hz, ← hinc]; exact hstep)
          (by change e'.val.2 = oppositePort e.val.2 at hp; rw [hp]; rcases e with ⟨⟨v, p⟩, _⟩; cases p <;> rfl)
        have hout := e'.property; rw [heq, dartOut_edgeReverse, e.property] at hout; cases hout
    have horbit : (directedStep ω s h)^[a] d = (directedStep ω s h)^[b] d :=
      Subtype.ext (Prod.ext (by rw [← loopLiftPosition_projection, ← loopLiftPosition_projection, hlift.1]) hlift.2)
    have hmod : a % L = b % L :=
      (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (Nat.mod_lt a hL) (Nat.mod_lt b hL)).mp
        (by simpa only [L, Function.iterate_mod_minimalPeriod_eq] using horbit)
    rw [per_decomp f L D hper a, per_decomp f L D hper b, hmod] at he
    have hsmul : (a / L) • D = (b / L) • D := add_left_cancel he
    have hdiv : a / L = b / L := by
      have hx : ((a / L : ℕ) : ℤ) * D.1 = ((b / L : ℕ) : ℤ) * D.1 := by simpa [nsmul_eq_mul] using congrArg Prod.fst hsmul
      have hy : ((a / L : ℕ) : ℤ) * D.2 = ((b / L : ℕ) : ℤ) * D.2 := by simpa [nsmul_eq_mul] using congrArg Prod.snd hsmul
      by_cases hx0 : D.1 = 0
      · have hy0 : D.2 ≠ 0 := fun h0 => hD (Prod.ext hx0 h0)
        exact_mod_cast mul_right_cancel₀ hy0 hy
      · exact_mod_cast mul_right_cancel₀ hx0 hx
    have ha := Nat.mod_add_div a L; have hb := Nat.mod_add_div b L
    rw [hmod, hdiv] at ha; exact ha.symm.trans hb
  have hz := periodic_lattice_turn_zero f hadj hinj L D hL hD hper
  have hturn : (∑ n ∈ range L, midpointQuarterTurn s ((directedStep ω s h)^[n] d).val) = 0 := by
    rw [← hz]; refine Finset.sum_congr rfl fun n _ => ?_
    have hd (m : ℕ) : seqCompass f hadj m = portCompass (midpointDirection s ((directedStep ω s h)^[m] d).val) :=
      squareDartCompass_eq_portCompass _ _ (loopMidpointPosition_succ_direction ω s h d m)
    rw [hd, hd, portCompass_quarterTurn, Function.iterate_succ_apply', directedStep_val]; rfl
  have ht := sum_period_midpointQuarterTurn_eq_four_mul_rotationNumber ω s h d
  rw [hturn] at ht; dsimp [ω, s, h, directedLoopOf] at ht; omega

end PottsDiscontinuity.TorusTopology
