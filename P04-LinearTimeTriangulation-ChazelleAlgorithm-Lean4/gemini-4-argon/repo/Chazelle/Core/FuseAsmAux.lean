module

public import Chazelle.Core.FuseAsmBuild
public import Chazelle.Core.FuseAsmCost
public import Chazelle.Core.FuseAsmDedupRun

/-!
# WP-F fusion assembly, part 27: auxiliary facts of the driver

* `frame_side`: the frame of a side stage.
* `junction_eq`, `chords_eq_of_nfAt`: the junction and the chords of a normal form are fixed by
  their descriptors.
* `tlist_eq`: the stored triples of a chord list are the list.
* `side₀_ok`, `side₁_ok`, `capAns_of`: the validity of the query lists and the cap queries.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim

@[expose] public section

theorem bside_of_band {S r : ℕ} (hS : S = 70150 ∨ S = 70151) (hr : bandOf r ∉ FB)
    (ha : r ≠ ALLOC) : Bside S r = false := by
  have h1 : bandOf r ≠ 1 := fun h => hr (by rw [h]; decide)
  have h5 : bandOf r ≠ 5 := fun h => hr (by rw [h]; decide)
  have h7 : bandOf r ≠ 7 := fun h => hr (by rw [h]; decide)
  unfold bandOf at h1 h5 h7
  unfold ALLOC at ha
  simp only [Bside, Bend, Bpt, Bcs, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega

theorem bside_lo {S r : ℕ} (hS : S = 70150 ∨ S = 70151) (h1 : 70000 ≤ r) (h2 : r < 70100) :
    Bside S r = false := by
  simp only [Bside, Bend, Bpt, Bcs, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega

theorem br_of_band {r : ℕ} (hr : bandOf r ∉ FB) : BR r = false := by
  have h1 : bandOf r ≠ 1 := fun h => hr (by rw [h]; decide)
  have h5 : bandOf r ≠ 5 := fun h => hr (by rw [h]; decide)
  unfold bandOf at h1 h5
  simp only [BR, Btp, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega

/-- **The frame of a side stage.** -/
theorem frame_side {S : ℕ} (hS : S = 70150 ∨ S = 70151) {c c' : Config} {k x : ℕ}
    (hr : ∀ r, Bside S r = false → c'.nreg r = c.nreg r)
    (hrr : ∀ r, BR r = false → c'.rreg r = c.rreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (ha : c'.nreg ALLOC = c.nreg ALLOC + x) (hk : x ≤ k) :
    Frame FB c c' k :=
  ⟨fun r h1 h2 => hr r (bside_of_band hS h1 h2), fun r h1 => hrr r (br_of_band h1), hm,
    fun a _ => by rw [hrm], ho, by omega, by omega⟩

theorem junction_eq {m : ℕ → ℕ} {bl br bw : ℕ} {Q : Polygon} {H H' : Host}
    {J J' : Merge.Junction} (h : JunctionAt m bl br bw Q H J) (h' : JunctionAt m bl br bw Q H' J') :
    J = J' := by
  have e1 := NFLoc.chain_eq_of_desc h.1 h'.1
  have e2 := NFLoc.chain_eq_of_desc h.2.1 h'.2.1
  obtain ⟨P, s, m₁, m₂, a1, a2, a3⟩ := J
  obtain ⟨P', s', m₁', m₂', b1, b2, b3⟩ := J'
  simp only [Merge.Junction.left, Merge.Junction.right, Chain.mk.injEq] at e1 e2
  obtain ⟨rfl, rfl, rfl⟩ := e1
  obtain ⟨-, -, rfl⟩ := e2
  rfl

theorem chords_eq_of_nfAt {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N') :
    N.chords = N'.chords := by
  obtain ⟨hl, -, -, -, -, hc, -⟩ := h
  obtain ⟨hl', -, -, -, -, hc', -⟩ := h'
  have hext : ∀ r r' : CRec, r.h = r'.h → r.lp = r'.lp → r.rp = r'.rp → r.up = r'.up →
      r.dn = r'.dn → r = r' := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3 h4 h5; simp_all
  apply List.ext_getElem (by omega)
  intro i hi hi'
  obtain ⟨a0, a1, a2, a3, a4⟩ := hc i hi
  obtain ⟨b0, b1, b2, b3, b4⟩ := hc' i hi'
  have e := hext _ _ (a0.symm.trans b0) (a1.symm.trans b1) (a2.symm.trans b2)
    (a3.symm.trans b3) (a4.symm.trans b4)
  unfold NF.chord at e
  rwa [getD_lt hi, getD_lt hi'] at e

theorem tlist_eq {m : ℕ → ℕ} {T : ℕ} {C : List (ℕ × ℕ × ℕ)} (h : ChordListAt m T C) :
    tlist m T C.length = C := by
  apply List.ext_getElem (by simp [tlist])
  intro j h1 h2
  simp only [tlist, List.getElem_map, List.getElem_range, trip]
  obtain ⟨a, b, c⟩ := h j h2
  rw [getD_lt h2] at a b c
  rw [a, b, c]

theorem side₀_ok (J : Merge.Junction) (Q : Polygon) {N : NF}
    (hN : IsNF (chainModel J.left) Q N) {v₁ v₀ t₁ t₀ k₀ : List (ℕ × ℕ × ℕ)}
    (pv₁ : PtAns J Q 0 (J.whole.vertex J.m₁) 1 v₁)
    (pv₀ : PtAns J Q 0 (J.whole.vertex J.m₁) (-1) v₀)
    (pt₁ : PtAns J Q 0 (J.whole.vertex J.left.topIdx) 1 t₁)
    (pt₀ : PtAns J Q 0 (J.whole.vertex J.left.topIdx) (-1) t₀)
    (pk : SharedExtremum J → ¬ NearU J → PtAns J Q 0 (capOrigin J) (capDir J) k₀)
    (nk : ¬ (SharedExtremum J ∧ ¬ NearU J) → k₀ = []) :
    ∀ q ∈ endQL N.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀), QueryOK J Q 0 q ∧ HeightOK J Q 0 q := by
  have hN' : IsNF (chainModel (sideChain J 0)) Q N := hN
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with h | ((((h | h) | h) | h) | h)
  · exact ⟨(endQL_ok J Q 0 hN').1 q h, endQL_height J Q 0 hN' q h⟩
  · exact ok_ptAns J Q pv₁ q h
  · exact ok_ptAns J Q pv₀ q h
  · exact ok_ptAns J Q pt₁ q h
  · exact ok_ptAns J Q pt₀ q h
  · by_cases hx : SharedExtremum J ∧ ¬ NearU J
    · exact ok_ptAns J Q (pk hx.1 hx.2) q h
    · rw [nk hx] at h; simp at h

theorem side₁_ok (J : Merge.Junction) (Q : Polygon) {N : NF}
    (hN : IsNF (chainModel J.right) Q N) {t₁ t₀ k₁ : List (ℕ × ℕ × ℕ)}
    (pt₁ : PtAns J Q 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) 1 t₁)
    (pt₀ : PtAns J Q 1 (J.whole.vertex (J.m₁ + J.right.topIdx)) (-1) t₀)
    (pk : SharedExtremum J → NearU J → PtAns J Q 1 (capOrigin J) (capDir J) k₁)
    (nk : ¬ (SharedExtremum J ∧ NearU J) → k₁ = []) :
    ∀ q ∈ endQL N.chords ++ (t₁ ++ t₀ ++ k₁), QueryOK J Q 1 q ∧ HeightOK J Q 1 q := by
  have hN' : IsNF (chainModel (sideChain J 1)) Q N := hN
  intro q hq
  simp only [List.mem_append] at hq
  rcases hq with h | ((h | h) | h)
  · exact ⟨(endQL_ok J Q 1 hN').1 q h, endQL_height J Q 1 hN' q h⟩
  · exact ok_ptAns J Q pt₁ q h
  · exact ok_ptAns J Q pt₀ q h
  · by_cases hx : SharedExtremum J ∧ NearU J
    · exact ok_ptAns J Q (pk hx.1 hx.2) q h
    · rw [nk hx] at h; simp at h

theorem capAns_of (J : Merge.Junction) (Q : Polygon) {k₀ k₁ : List (ℕ × ℕ × ℕ)}
    (pk₀ : SharedExtremum J → ¬ NearU J → PtAns J Q 0 (capOrigin J) (capDir J) k₀)
    (nk₀ : ¬ (SharedExtremum J ∧ ¬ NearU J) → k₀ = [])
    (pk₁ : SharedExtremum J → NearU J → PtAns J Q 1 (capOrigin J) (capDir J) k₁)
    (nk₁ : ¬ (SharedExtremum J ∧ NearU J) → k₁ = []) (h₀ : k₀.length ≤ 1)
    (h₁ : k₁.length ≤ 1) :
    CapAns J Q k₀ k₁ ∧ k₀.length + k₁.length ≤ 1 := by
  refine ⟨⟨fun hx => ⟨fun hu => ⟨pk₀ hx hu, nk₁ fun h => hu h.2⟩,
    fun hu => ⟨nk₀ fun h => h.2 hu, pk₁ hx hu⟩⟩, fun hx => ⟨nk₀ fun h => hx h.1,
    nk₁ fun h => hx h.1⟩⟩, ?_⟩
  by_cases hu : NearU J
  · rw [nk₀ fun h => h.2 hu]; simpa using h₁
  · rw [nk₁ fun h => hu h.2]; simpa using h₀

end

end FuseAsm

end Chazelle.Core
