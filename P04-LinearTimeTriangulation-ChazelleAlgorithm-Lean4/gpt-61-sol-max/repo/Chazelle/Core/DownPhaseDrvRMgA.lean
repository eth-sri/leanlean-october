module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.Lemma41Node

/-!
# Down-phase driver (RAM side): merges on a region host, the precondition

`mergePreR`: two consecutive sub-chains `C₁`, `C₂` of a region host `H` (well formed, regular,
simple, at most `64` items) with descriptors on the host handle, the descriptor of their union,
canonical normal forms of both, a generic junction and the degree cap of the union give
`MergePre X OkModel` (the analogue of `L41.mergePre_of` for an arbitrary host).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Chazelle Chazelle.Merge L41

@[expose] public section

/-- The models of chains on a well-formed, regular, simple host are served by the oracles. -/
theorem okModel_host {P : Polygon} {H : Host} {C : Chain} (hHok : H.length ≤ 64)
    (hreg : HostRegular (Qof P).n H) (hP : C.P = H.poly (Qof P)) (hsimp : (H.poly (Qof P)).Simple) :
    OkModel P (chainModel C) :=
  ⟨H, C, hHok, hreg, hP, by simp_all, rfl⟩

/-- A chain descriptor on a well-formed host is well formed. -/
theorem chainWF_host {P : Polygon} {E : ℕ} {m : ℕ → ℕ} {d HB : ℕ} {H : Host} {C : Chain}
    (hHA : HostAt m HB H) (hHok : H.length ≤ 64) (hwf : HostWF P.n H)
    (hHB : HB + 3 * H.length + 4 ≤ E) (hd : ChainDescAt m d (Qof P) H C) (hdh : m d = HB)
    (hdA : d + 5 ≤ E) (hs : C.s < C.P.n) : ChainWF P E m d := by
  refine ⟨hdA, fun H' C' hC' => ?_⟩
  have hH : H' = H := NFLoc.hostAt_unique hC'.1 (by simp_all)
  ram_grind

/-- **The precondition of a merge on a region host** (`L41.mergePre_of` for an arbitrary host). -/
theorem mergePreR {P : Polygon} {W : ℕ} {c : Config} {X : MemCtx} (hG : GoodEnv P)
    (hWh : hostWords P.n ≤ W) (hX : X.holds P c.nmem (rd c bMerge 9) (c.nreg ALLOC))
    (hcap : rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem (rd c bMerge 9))
    (h7 : 4 ≤ rd c bMerge 7) (h56 : rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6)
    {HB d1 f1 d2 f2 TD : ℕ} {H : Host} {C1 C2 : Chain} {γ1 γ2 : ℕ} {N1 N2 : NF}
    (hHA : HostAt c.nmem HB H) (hHok : H.length ≤ 64) (hwf : HostWF P.n H)
    (hreg : HostRegular (Qof P).n H) (hsimp : (H.poly (Qof P)).Simple)
    (hHB : HB + 3 * H.length + 4 ≤ c.nreg ALLOC)
    (hd1 : ChainDescAt c.nmem d1 (Qof P) H C1) (hd1h : c.nmem d1 = HB) (hd1A : d1 + 5 ≤ c.nreg ALLOC)
    (hd2 : ChainDescAt c.nmem d2 (Qof P) H C2) (hd2h : c.nmem d2 = HB) (hd2A : d2 + 5 ≤ c.nreg ALLOC)
    (hcons : C2.s = C1.s + C1.m) (hlen : C1.m + C2.m + 1 ≤ C1.P.n)
    (hs1 : C1.s < C1.P.n) (hs2 : C2.s < C2.P.n)
    (hTD : ChainDescAt c.nmem TD (Qof P) H (jOf C1 C2 hlen).whole) (hTDh : c.nmem TD = HB)
    (hTDA : TD + 5 ≤ c.nreg ALLOC)
    (r0 : rd c bMerge 0 = d1) (r1 : rd c bMerge 1 = d2) (r2 : rd c bMerge 2 = TD)
    (r3 : rd c bMerge 3 = f1) (r4 : rd c bMerge 4 = f2)
    (hN1 : NFWithin c.nmem f1 (c.nreg ALLOC) N1) (hN2 : NFWithin c.nmem f2 (c.nreg ALLOC) N2)
    (hc1 : IsCanonicalNF (chainModel C1) (Qof P) N1 γ1 (rd c bMerge 7))
    (hc2 : IsCanonicalNF (chainModel C2) (Qof P) N2 γ2 (rd c bMerge 7))
    (hγ1 : γ1 ≤ rd c bMerge 5) (hγ2 : γ2 ≤ rd c bMerge 5)
    (hgen : SharedGeneric (jOf C1 C2 hlen))
    (hfd : (chainModel (jOf C1 C2 hlen).whole).FullDegLe (Qof P) (rd c bMerge 7)) :
    MergePre X OkModel P W c := by
  set J := jOf C1 C2 hlen with hJ
  have hP1 : C1.P = H.poly (Qof P) := hd1.2.1
  have hP2 : C2.P = H.poly (Qof P) := hd2.2.1
  have hl : J.left = C1 := jOf_left C1 C2 hlen
  have hr : J.right = C2 := jOf_right hlen (by simp_all) hcons
  have hwP : J.whole.P = H.poly (Qof P) := by grind [jOf_whole_P]
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hsT : J.whole.s < J.whole.P.n := by grind [jOf_whole_s, jOf_whole_P]
  refine ⟨hG, hWh, hX, hcap, h7, h56,
    ⟨?_, ?_, ?_, fun H' hH' => ?_⟩, H, J, N1, N2, ⟨?_, ?_, ?_⟩,
    (hP1.symm ▸ hsimp : C1.P.Simple), hgen,
    by rw [hl]; exact okModel_host hHok hreg hP1 hsimp,
    by rw [hr]; exact okModel_host hHok hreg hP2 hsimp, okModel_host hHok hreg hwP hsimp,
    hfd, by simp_all, by simp_all, ⟨γ1, hγ1, by simp_all⟩,
    ⟨γ2, hγ2, by simp_all⟩⟩
  · rw [r0]; exact chainWF_host hHA hHok hwf hHB hd1 hd1h hd1A hs1
  · rw [r1]; exact chainWF_host hHA hHok hwf hHB hd2 hd2h hd2A hs2
  · rw [r2]; exact chainWF_host hHA hHok hwf hHB hTD hTDh hTDA hsT
  · rw [r2, hTDh] at hH'
    rw [NFLoc.hostAt_unique hH' hHA, ← hQn]; exact hreg
  all_goals grind

end

end DrvR

end Chazelle.Core
