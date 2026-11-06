module

public import Chazelle.Core.ClusterRegsRam
public import Chazelle.RewriteTactics
set_option maxHeartbeats 8000000

/-!
# WP-I, part 62: the initial state of the split driver

`dinv_init`: after stage D and the stack scan, the memory satisfies the driver invariant `DInv`
with the stack `segL`, the finished blocks `finL`, no separator vertex and `nsp = 0`. The
blocks are the slabs of `k'` levels shifted by `cs`, minus the light levels (the set `Hset`).
-/

namespace Chazelle.Core.Cluster

open Machine Chazelle.Separator Chazelle.Separator.CombMap

@[expose] public section

/-- The preorder numbering is injective. -/
theorem BTree.PreInv.pre_inj {R : BTree} {pre slot : ℕ → ℕ} (hR : R.OK)
    (hP : R.PreInv pre slot R.n) {g h : ℕ} (hg : g < R.n) (hh : h < R.n) (he : pre g = pre h) :
    g = h := by
  have s1 := BTree.one_le_card_sub (R := R) hg
  have s2 := BTree.one_le_card_sub (R := R) hh
  have a1 := (hP.anc_iff hR hg hh).mpr ⟨le_of_eq he, by omega⟩
  have a2 := (hP.anc_iff hR hh hg).mpr ⟨le_of_eq he.symm, by omega⟩
  exact hR.anc_antisymm hh hg a1 a2

theorem div_succ_eq {a k : ℕ} (hk : 0 < k) (h : a % k ≠ k - 1) : (a + 1) / k = a / k := by
  apply Nat.succ_div_of_not_dvd
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have := Nat.mod_lt a hk
  have hk1 : k ≠ 1 := by rintro rfl; exact h (Nat.mod_one a)
  rw [Nat.one_mod_eq_one.mpr hk1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Adjacent levels off the boundary levels are in one slab. -/
theorem div_eq_of_adj {a b k : ℕ} (hk : 0 < k) (h1 : b ≤ a + 1) (h2 : a ≤ b + 1)
    (ha : a % k ≠ k - 1) (hb : b % k ≠ k - 1) : a / k = b / k := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [show b = a + 1 by omega, div_succ_eq hk ha]
  · rw [h]
  · rw [show a = b + 1 by omega, div_succ_eq hk hb]

variable {W : ℕ}

/-- **The initial driver invariant.** -/
theorem dinv_init {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face (a f) = f} {C : CoTree (starTree T a ha)} {R : BTree} {first : Fin g.μ → Fin g.N}
    {preE slot : ℕ → ℕ} {upT : ℕ → ℕ} {cs : ℕ} {m : ℕ → ℕ}
    (hSF : SFacts M T a ha C R first preE slot upT g.k' cs (ssOf g) g.A0 g.U W m)
    (hhead : ∀ d : Fin g.N, T.level (M.head d) ≤ T.level (M.vert d) + 1)
    (hk : 0 < g.k') (hcs : cs < g.k') (_hkμ : g.k' ≤ g.μ)
    (hlv : ∀ l, l < g.μ → LvOK g m cs l)
    (hpos : ∀ v, v < g.μ → m (g.base 44 + v) =
      if blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l)) v < g.μ then
      plPos g.μ (blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l))) (fun v => m (g.base 29 + m (g.base 0 + v))) v else g.μ)
    (hact : ∀ v, v < g.μ → blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l)) v < g.μ →
      m (g.base 43 + plPos g.μ (blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l))) (fun v => m (g.base 29 + m (g.base 0 + v))) v) = v)
    (hdf : ∀ v, v < g.μ → m (g.base 48 + v) = 0)
    (hstk : segL g.s g.μ (blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l))) g.μ = stkList m (g.base 46) (segL g.s g.μ
        (blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l))) g.μ).length) :
    DInv M T g.k' cs (ssOf g) m (segL g.s g.μ (blkOf g.μ (fun v => m (g.base 3 + v))
      (fun l => m (g.base 36 + l)) (fun l => m (g.base 35 + l))) g.μ)
      (finL g.s g.μ (blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
        (fun l => m (g.base 35 + l)))) ∅ 0 := by
  set bo := blkOf g.μ (fun v => m (g.base 3 + v)) (fun l => m (g.base 36 + l))
    (fun l => m (g.base 35 + l)) with hbo
  set key : ℕ → ℕ := fun v => m (g.base 29 + m (g.base 0 + v)) with hkey
  have hN : (ssOf g).N = g.N := rfl
  -- the key is the preorder of the first dart
  have hkeyv : ∀ v : Fin g.μ, key v = preE (first v) := fun v => by
    simp only [hkey]
    have h1 : m (g.base 0 + v) = first v := hSF.first v
    rw [h1]; exact hSF.pre _ (first v).2
  have hinj : ∀ v w, v < g.μ → w < g.μ → key v = key w → v = w := fun v w hv hw h => by
    have e := (hkeyv ⟨v, hv⟩).symm.trans (h.trans (hkeyv ⟨w, hw⟩))
    have hn := hSF.R_n
    have := BTree.PreInv.pre_inj hSF.R_ok hSF.R_pre (by rw [hn]; exact (first ⟨v, hv⟩).2)
      (by rw [hn]; exact (first ⟨w, hw⟩).2) e
    have hf : first ⟨v, hv⟩ = first ⟨w, hw⟩ := Fin.ext this
    have := congrArg M.vert hf
    rw [hSF.vert_first, hSF.vert_first] at this
    exact congrArg Fin.val this
  -- the blocks
  have hlev : ∀ v (hv : v < g.μ), m (g.base 3 + v) = T.level ⟨v, hv⟩ := fun v hv => hSF.lev ⟨v, hv⟩
  have hbo_eq : ∀ v (hv : v < g.μ), bo v = if (T.level ⟨v, hv⟩ + cs) % g.k' < g.k' - 1 then
      (T.level ⟨v, hv⟩ + cs) / g.k' else g.μ := fun v hv => by
    obtain ⟨-, -, h35, h36⟩ := hlv _ (hSF.lev_lt ⟨v, hv⟩)
    simp only [hbo, blkOf]; rw [hlev v hv, h36, h35]
    split_ifs <;> simp_all
  have hdivlt : ∀ l, l < g.μ → (l + cs) / g.k' < g.μ := fun l hl => by
    rw [Nat.div_lt_iff_lt_mul hk]
    obtain ⟨t, ht⟩ : ∃ t, g.μ = t + 1 := ⟨g.μ - 1, by omega⟩
    rw [ht, Nat.succ_mul]
    have : t ≤ t * g.k' := Nat.le_mul_of_pos_right _ hk
    omega
  have hbo_lt : ∀ v (hv : v < g.μ), bo v < g.μ ↔ (T.level ⟨v, hv⟩ + cs) % g.k' < g.k' - 1 :=
    fun v hv => by
      rw [hbo_eq v hv]
      split_ifs with h
      · exact ⟨fun _ => h, fun _ => hdivlt _ (by have := hSF.lev_lt ⟨v, hv⟩; omega)⟩
      · exact ⟨fun h' => by omega, fun h' => absurd h' h⟩
  have hH : ∀ v, v < g.μ → (v ∈ Hset T cs g.k' ↔ ¬ bo v < g.μ) := fun v hv => by
    rw [hbo_lt v hv]
    simp only [Hset, Finset.mem_filter, Finset.mem_range]
    have := Nat.mod_lt (T.level ⟨v, hv⟩ + cs) hk
    constructor
    · rintro ⟨-, h, h'⟩; omega
    · intro h; exact ⟨hv, hv, by omega⟩
  have hHμ : ∀ v ∈ Hset T cs g.k', v < g.μ := fun v h => by
    simp only [Hset, Finset.mem_filter, Finset.mem_range] at h; exact h.1
  have hslab : ∀ v w, v < g.μ → w < g.μ → bo v < g.μ → bo v = bo w →
      slabN T cs g.k' v = slabN T cs g.k' w := fun v w hv hw hb he => by
    have hb' := hb; rw [he] at hb'
    have e1 := hbo_eq v hv; have e2 := hbo_eq w hw
    rw [ite_eq_left ((hbo_lt v hv).mp hb)] at e1
    rw [ite_eq_left ((hbo_lt w hw).mp hb')] at e2
    simp only [slabN, dite_eq_left hv, dite_eq_left hw]
    rw [← e1, ← e2, he]
  have hedge : ∀ x y, AdjN M x y → x ∉ Hset T cs g.k' → y ∉ Hset T cs g.k' →
      x < g.μ ∧ y < g.μ ∧ bo x = bo y := fun x y hxy hx hy => by
    obtain ⟨d, rfl, rfl⟩ := hxy
    have hxμ := (M.vert d).2; have hyμ := (M.head d).2
    refine ⟨hxμ, hyμ, ?_⟩
    have hx' := (hH _ hxμ).not.mp hx; have hy' := (hH _ hyμ).not.mp hy
    simp only [not_not] at hx' hy'
    rw [hbo_lt _ hxμ] at hx'; rw [hbo_lt _ hyμ] at hy'
    rw [hbo_eq _ hxμ, hbo_eq _ hyμ, ite_eq_left hx', ite_eq_left hy']
    have h1 := hhead d
    have h2 := hhead (M.opp d)
    have e1 : M.head (M.opp d) = M.vert d := by simp [CombMap.head, M.opp_opp]
    have e2 : M.vert (M.opp d) = M.head d := rfl
    rw [e1, e2] at h2
    simp only [Fin.eta] at hx' hy' ⊢
    exact div_eq_of_adj hk (by omega) (by omega) (by omega) (by omega)
  have hsinv := SInv.init (k := g.k') (s := g.s) (μ := g.μ) (bo := bo) (key := key)
    (act := fun i => m (g.base 43 + i)) hinj hact hH hHμ hslab hedge
  refine ⟨hsinv, fun v hv => ?_, fun v hv => by simp at hv, fun p hp i h1 h2 => ?_,
    fun w hw => ?_, fun p hp => ?_, hstk, fun p hp => ?_⟩
  · show m (g.base 48 + v) = 1 ↔ v ∈ (∅ : Finset ℕ)
    rws [hdf v hv]
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp
    obtain ⟨v, hv, hbv, rfl⟩ := exists_plPos (key := key) hinj h1 h2
    show m (g.base 44 + m (g.base 43 + plPos g.μ bo key v)) = plPos g.μ bo key v
    rw [hact v hv (by omega), hpos v hv, ite_eq_left (by omega)]
  · show m (g.base 44 + w) = g.μ ∨ _
    by_cases hb : bo w < g.μ
    · right
      have e := hpos w hw; rw [ite_eq_left hb] at e
      rw [show (ssOf g).bPOS = g.base 44 from rfl, show (ssOf g).bACT = g.base 43 from rfl, e]
      exact ⟨seg g.μ bo (bo w), lv_iff.mpr ⟨bo w, hb, rfl⟩, plPos_ge w, plPos_lt hw,
        hact w hw hb⟩
    · left; rw [hpos w hw, ite_eq_right hb]
  · obtain ⟨b, hb, -, rfl⟩ := mem_segL.mp hp
    intro i i' h1 h2 h3
    simp only [seg] at h1 h3
    obtain ⟨v, hv, hbv, rfl⟩ := exists_plPos (key := key) hinj h1 (by omega)
    obtain ⟨v', hv', hbv', rfl⟩ := exists_plPos (key := key) hinj (by omega) h3
    show m (g.base 29 + m (g.base 0 + m (g.base 43 + plPos g.μ bo key v))) ≤
      m (g.base 29 + m (g.base 0 + m (g.base 43 + plPos g.μ bo key v')))
    rw [hact v hv (by omega), hact v' hv' (by omega)]
    exact key_le_of_plPos (bo := bo) (key := key) hv' (by rw [hbv, hbv']) h2
  · obtain ⟨b, hb, rfl⟩ := lv_iff.mp hp
    exact cntLt_le bo g.μ (b + 1)

end

end Chazelle.Core.Cluster
