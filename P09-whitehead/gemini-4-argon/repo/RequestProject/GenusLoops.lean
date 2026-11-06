module

public import RequestProject.GenusData
public import RequestProject.SurfaceRev

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis.Genus

open RACG Mirror Comb PresModel Cell

variable (q : ℕ) [NeZero q]

abbrev gc : Compat (gvc q) (gec q) := genus_compat q

def gBase : NeSpx (cmpRel (SCell (gvc q) (gec q) (gc q))) :=
  spx1 (cV (gc q) (cyc (8 * q) 0))

theorem cyc_mod_two (k : ℕ) : (cyc (8 * q) k).val % 2 = k % 2 :=
  Nat.mod_mod_of_dvd k ⟨4 * q, by ring⟩

theorem gvc_even {k : ℕ} (hk : k % 2 = 0) : gvc q (cyc (8 * q) k) = none :=
  if_pos ((cyc_mod_two q k).trans hk)

theorem gvc_congr_lt {k k' : ℕ} (hk : k < 8 * q := by omega) (hk' : k' < 8 * q := by omega)
    (ho : k % 2 = 1 := by omega) (ho' : k' % 2 = 1 := by omega)
    (h1 : k / 2 / 4 = k' / 2 / 4 := by omega)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1) := by omega) :
    gvc q (cyc (8 * q) k) = gvc q (cyc (8 * q) k') := by
  have v : (cyc (8 * q) k).val = k := Nat.mod_eq_of_lt hk
  have v' : (cyc (8 * q) k').val = k' := Nat.mod_eq_of_lt hk'
  rw [gvc, gvc, if_neg (by rw [v]; omega), if_neg (by rw [v']; omega)]
  simp only [Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide, v, v']
  exact ⟨h1, h2⟩

theorem gec_congr_lt {k k' : ℕ} (hk : k < 8 * q := by omega) (hk' : k' < 8 * q := by omega)
    (h1 : k / 2 / 4 = k' / 2 / 4 := by omega)
    (h2 : (k / 2 % 4 % 2 = 1) ↔ (k' / 2 % 4 % 2 = 1) := by omega)
    (h3 : xor (decide (k % 2 = 1)) (decide (2 ≤ k / 2 % 4))
      = xor (decide (k' % 2 = 1)) (decide (2 ≤ k' / 2 % 4))) :
    gec q (cyc (8 * q) k) = gec q (cyc (8 * q) k') := by
  simp only [gec, Prod.mk.injEq, Fin.mk.injEq, decide_eq_decide,
    show (cyc (8 * q) k).val = k from Nat.mod_eq_of_lt hk,
    show (cyc (8 * q) k').val = k' from Nat.mod_eq_of_lt hk']
  exact ⟨h1, h2, h3⟩

theorem cV_even {k : ℕ} (hk : k % 2 = 0) :
    cV (gc q) (cyc (8 * q) k) = cV (gc q) (cyc (8 * q) 0) :=
  congrArg (fun x => toS (gvc q) (gec q) (gc q) (vtx x))
    ((gvc_even q hk).trans (gvc_even q (k := 0) rfl).symm)

abbrev gPath (m : ℕ) : List ((sdCx (gc q)).E × Bool) := pPath (gc q) m

theorem isPath_gPath {m : ℕ} (hm : m % 2 = 0) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gPath q m) (gBase q) (gBase q) := by
  have h1 := isPath_bdEdge (gc q) (cyc (8 * q) m); rw [← cyc_succ] at h1
  have h2 := isPath_bdEdge (gc q) (cyc (8 * q) (m + 1)); rw [← cyc_succ] at h2
  have h3 := h1.append h2
  rwa [cV_even q hm, cV_even q (k := m + 1 + 1) (by omega)] at h3

theorem isPath_bdPath8 (n : ℕ) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (bdPath (gc q) (8 * n)) (gBase q) (gBase q) := by
  have h := isPath_bdPath (gc q) (8 * n)
  rwa [cV_even q (k := 8 * n) (by omega)] at h

theorem gPath_rev_a {h : ℕ} (hh : h < q) :
    gPath q (8 * h + 4) = revPath (gPath q (8 * h)) := by
  show pPath (gc q) (8 * h + 4) = revPath (pPath (gc q) (8 * h))
  rw [pPath_eq, pPath_eq, show 8 * h + 4 + 1 = 8 * h + 5 by omega, revPath_append]
  congr 1
  · refine bdEdge_rev (gc q) ?_ ?_ ?_
    · apply gec_congr_lt q
      rw [show (8 * h + 4) % 2 = 0 by omega, show (8 * h + 4) / 2 % 4 = 2 by omega,
          show (8 * h + 1) % 2 = 1 by omega, show (8 * h + 1) / 2 % 4 = 0 by omega]; rfl
    · rw [← cyc_succ]; exact (gvc_even q (by omega)).trans (gvc_even q (k := 8 * h + 1 + 1) (by omega)).symm
    · rw [← cyc_succ]; exact gvc_congr_lt q
  · refine bdEdge_rev (gc q) ?_ ?_ ?_
    · apply gec_congr_lt q
      rw [show (8 * h + 5) % 2 = 1 by omega, show (8 * h + 5) / 2 % 4 = 2 by omega,
          show (8 * h) % 2 = 0 by omega, show (8 * h) / 2 % 4 = 0 by omega]; rfl
    · rw [← cyc_succ]; exact gvc_congr_lt q
    · rw [← cyc_succ]; exact (gvc_even q (k := 8 * h + 5 + 1) (by omega)).trans (gvc_even q (by omega)).symm

theorem gPath_rev_b {h : ℕ} (hh : h < q) :
    gPath q (8 * h + 6) = revPath (gPath q (8 * h + 2)) := by
  show pPath (gc q) (8 * h + 6) = revPath (pPath (gc q) (8 * h + 2))
  rw [pPath_eq, pPath_eq, show 8 * h + 6 + 1 = 8 * h + 7 by omega,
    show 8 * h + 2 + 1 = 8 * h + 3 by omega, revPath_append]
  congr 1
  · refine bdEdge_rev (gc q) ?_ ?_ ?_
    · apply gec_congr_lt q
      rw [show (8 * h + 6) % 2 = 0 by omega, show (8 * h + 6) / 2 % 4 = 3 by omega,
          show (8 * h + 3) % 2 = 1 by omega, show (8 * h + 3) / 2 % 4 = 1 by omega]; rfl
    · rw [← cyc_succ]; exact (gvc_even q (by omega)).trans (gvc_even q (k := 8 * h + 3 + 1) (by omega)).symm
    · rw [← cyc_succ]; exact gvc_congr_lt q
  · refine bdEdge_rev (gc q) ?_ ?_ ?_
    · apply gec_congr_lt q
      rw [show (8 * h + 7) % 2 = 1 by omega, show (8 * h + 7) / 2 % 4 = 3 by omega,
          show (8 * h + 2) % 2 = 0 by omega, show (8 * h + 2) / 2 % 4 = 1 by omega]; rfl
    · rw [← cyc_succ]; exact gvc_congr_lt q
    · rw [← cyc_succ]; exact (gvc_even q (k := 8 * h + 7 + 1) (by omega)).trans (gvc_even q (by omega)).symm

def gcl {m : ℕ} (hm : m % 2 = 0) : Pi1 (sdCx (gc q)) (gBase q) :=
  Pi1.mk ⟨gPath q m, isPath_gPath q hm⟩

def bcl (n : ℕ) : Pi1 (sdCx (gc q)) (gBase q) :=
  Pi1.mk ⟨bdPath (gc q) (8 * n), isPath_bdPath8 q n⟩

theorem gcl_inv {m m' : ℕ} (hm : m % 2 = 0) (hm' : m' % 2 = 0)
    (e : gPath q m' = revPath (gPath q m)) : gcl q hm' = (gcl q hm)⁻¹ :=
  (pi1_mk_congr _ (e ▸ isPath_gPath q hm') e).trans (pi1_mk_rev (isPath_gPath q hm) _)

theorem gIdx_even (x : ℕ × Bool) : (8 * x.1 + (if x.2 then 2 else 0)) % 2 = 0 := by
  rcases x with ⟨n, _ | _⟩ <;> simp <;> omega

def gGen (x : ℕ × Bool) : Pi1 (sdCx (gc q)) (gBase q) :=
  gcl q (m := 8 * x.1 + (if x.2 then 2 else 0)) (gIdx_even x)

abbrev gBlock (n : ℕ) : List ((sdCx (gc q)).E × Bool) :=
  ((gPath q (8 * n) ++ gPath q (8 * n + 2)) ++ gPath q (8 * n + 4)) ++ gPath q (8 * n + 6)

theorem bdPath_block (n : ℕ) :
    bdPath (gc q) (8 * (n + 1)) = bdPath (gc q) (8 * n) ++ gBlock q n := by
  rw [show 8 * (n + 1) = 8 * n + 2 + 2 + 2 + 2 by ring,
    bdPath_add_two, bdPath_add_two, bdPath_add_two, bdPath_add_two,
    show 8 * n + 2 + 2 + 2 = 8 * n + 6 by omega, show 8 * n + 2 + 2 = 8 * n + 4 by omega]
  simp [List.append_assoc]

theorem bcl_eq_commWord {n : ℕ} (hn : n ≤ q) :
    bcl q n = commWord (gGen q) (genPairs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn' : n < q := by omega
      have h0 : (8 * n) % 2 = 0 := by omega
      have h2 : (8 * n + 2) % 2 = 0 := by omega
      have h4 : (8 * n + 4) % 2 = 0 := by omega
      have h6 : (8 * n + 6) % 2 = 0 := by omega
      have hp02 := (isPath_gPath q h0).append (isPath_gPath q h2)
      have hp04 := hp02.append (isPath_gPath q h4)
      have hp06 := hp04.append (isPath_gPath q h6)
      have hsucc : bcl q (n + 1) = bcl q n * (gGen q (n, false) * gGen q (n, true)
          * (gGen q (n, false))⁻¹ * (gGen q (n, true))⁻¹) := by
        rw [bcl, bcl, pi1_mk_congr (isPath_bdPath8 q (n + 1))
          ((isPath_bdPath8 q n).append hp06) (bdPath_block q n),
          pi1_mk_append (isPath_bdPath8 q n) hp06,
          pi1_mk_append hp04 (isPath_gPath q h6),
          pi1_mk_append hp02 (isPath_gPath q h4),
          pi1_mk_append (isPath_gPath q h0) (isPath_gPath q h2)]
        change bcl q n * (gcl q h0 * gcl q h2 * gcl q h4 * gcl q h6) = _
        rw [gcl_inv q h0 h4 (gPath_rev_a q hn'), gcl_inv q h2 h6 (gPath_rev_b q hn')]; rfl
      rw [hsucc, ih (by omega), show genPairs (n + 1) = genPairs n ++ [((n, false), (n, true))]
        by simp [genPairs, List.range_succ], commWord_append, commWord_cons, commWord_nil, mul_one]

def gSig (x : ℕ × Bool) : List ((sdCx (gc q)).E × Bool) :=
  gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0))

theorem gSig_eq (x : ℕ × Bool) :
    gSig q x = gPath q (8 * (x.1 % q) + (if x.2 then 2 else 0)) := rfl

theorem isPath_gSig (x : ℕ × Bool) :
    IsPath (sdCx (gc q)).src (sdCx (gc q)).tgt (gSig q x) (gBase q) (gBase q) :=
  isPath_gPath q (gIdx_even (x.1 % q, x.2))

theorem genus_hfilling :
    commWord (fun x => Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)))
      (genPairs q) = 1 := by
  have hcls {x : ℕ × Bool} (hx : x.1 < q) :
      Pi1.mk (⟨gSig q x, isPath_gSig q x⟩ : Loop (sdCx (gc q)) (gBase q)) = gGen q x :=
    pi1_mk_congr _ _ (by rw [gSig_eq, Nat.mod_eq_of_lt hx])
  rw [commWord_congr_on fun p hp => by
      simp only [genPairs, List.mem_map, List.mem_range] at hp
      obtain ⟨h, hh, rfl⟩ := hp; exact ⟨hcls hh, hcls hh⟩,
    ← bcl_eq_commWord q le_rfl]
  exact pi1_mk_eq_one _ (htpy_bdLoop_nil (gc q))
