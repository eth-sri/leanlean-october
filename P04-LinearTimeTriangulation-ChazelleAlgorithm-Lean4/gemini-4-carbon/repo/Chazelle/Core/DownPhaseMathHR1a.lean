module

public import Chazelle.Core.DownPhaseMathHostMir
public import Chazelle.Core.DownPhaseMathRot
public import Chazelle.Core.DownPhaseMathHostList

/-!
# Down phase, math (H-R1): the extraction facts for rotated and reversed host polygons

* `extractOK_of_model`: `ExtractOK` depends on the chain only through its model;
* `extractOK_rot` (counterclockwise): a chain from index `0` of the host polygon rotated by `i0`,
  where the host key before `i0` is a chord gap, satisfies `ExtractOK`;
* `extractOK_rev` (clockwise): the same for the reversed rotated host polygon, through the mirror
  (`Mir.extractOK_of_mir`, `hk_mir`, `chordGap_mir`).
-/

namespace Chazelle.Core

namespace DownMath

@[expose] public section

open Set
open DownHost Mir

variable {Q : Polygon} {S : Set (Set Point)} {R : Set Point}

/-- `x mod K` for `x < 3 K`. -/
theorem mod3_cases {x K : ℕ} (hK : 0 < K) (hx : x < 3 * K) :
    x % K < K ∧ (x % K = x ∨ x % K + K = x ∨ x % K + 2 * K = x) := by
  refine ⟨Nat.mod_lt _ hK, ?_⟩
  by_cases h1 : x < K
  · exact Or.inl (Nat.mod_eq_of_lt h1)
  · by_cases h2 : x < 2 * K
    · right; left
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · right; right
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)]; omega

theorem idx_I1 {K a i k : ℕ} (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hk : k < K) :
    (a + K - 1 - ((a + K - i) % K + k) % K) % K = (i + (K - 1 - k)) % K := by
  have e1 := mod3_cases hK (show a + K - i < 3 * K by omega)
  generalize (a + K - i) % K = s at e1 ⊢
  have e2 := mod3_cases hK (show s + k < 3 * K by omega)
  generalize (s + k) % K = u at e2 ⊢
  have e3 := mod3_cases hK (show a + K - 1 - u < 3 * K by omega)
  have e4 := mod3_cases hK (show i + (K - 1 - k) < 3 * K by omega)
  generalize (a + K - 1 - u) % K = v at e3 ⊢
  generalize (i + (K - 1 - k)) % K = w at e4 ⊢
  omega

theorem idx_I2 {K a i g : ℕ} (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hg : g < K)
    (hgi : (g + 1) % K = i) :
    (a + K - 1 - ((a + K - i) % K + K - 1) % K) % K = (g + 1) % K := by
  have e0 := mod3_cases hK (show g + 1 < 3 * K by omega)
  rw [hgi] at e0 ⊢
  have e1 := mod3_cases hK (show a + K - i < 3 * K by omega)
  generalize (a + K - i) % K = s at e1 ⊢
  have e2 := mod3_cases hK (show s + K - 1 < 3 * K by omega)
  generalize (s + K - 1) % K = u at e2 ⊢
  have e3 := mod3_cases hK (show a + K - 1 - u < 3 * K by omega)
  generalize (a + K - 1 - u) % K = v at e3 ⊢
  omega

theorem idx_I3 {K a i g : ℕ} (hK : 0 < K) (ha : a ≤ K) (hi : i < K) (hg : g < K)
    (hgi : (g + 1) % K = i) :
    (a + K - 1 - (((a + K - i) % K + K - 1) % K + 1) % K) % K = g := by
  have e0 := mod3_cases hK (show g + 1 < 3 * K by omega)
  rw [hgi] at e0
  have e1 := mod3_cases hK (show a + K - i < 3 * K by omega)
  generalize (a + K - i) % K = s at e1 ⊢
  have e2 := mod3_cases hK (show s + K - 1 < 3 * K by omega)
  generalize (s + K - 1) % K = u at e2 ⊢
  have e3 := mod3_cases hK (show u + 1 < 3 * K by omega)
  generalize (u + 1) % K = u' at e3 ⊢
  have e4 := mod3_cases hK (show a + K - 1 - u' < 3 * K by omega)
  generalize (a + K - 1 - u') % K = v at e4 ⊢
  omega

/-- **`ExtractOK` depends on the chain only through its model.** -/
theorem extractOK_of_model {C C' : Chain} (h : chainModel C = chainModel C')
    (hE : DownDrv.ExtractOK Q S R C') : DownDrv.ExtractOK Q S R C := by
  obtain ⟨h1, h2, h3, h4⟩ := hE
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; exact h1
  · rw [h]; exact h2
  · rw [h]; exact h3
  · rw [h]; exact h4

/-- **Counterclockwise extraction** for a chain from index `0` of the host polygon rotated by `i0`,
the host key before `i0` being a chord gap. -/
theorem extractOK_rot (X : Extract.Ctx Q S R) {g i0 : ℕ} (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g)
    (hgi : (g + 1) % nk (interiorModel Q) S R = i0 % nk (interiorModel Q) S R) {C : Chain}
    (hP : C.P = (hostPoly Q S R).rotate i0) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) :
    DownDrv.ExtractOK Q S R C := by
  have h3 := X.three
  set K := nk (interiorModel Q) S R with hK
  have hPn : C.P.n = K := by rw [hP, Existence.n_rotate, hostPoly_n]
  refine extractOK_of_model (C' := hostChain Q S R g h3) ?_ (DownDrv.extractOK_host X hg hgc)
  refine chainModel_congr ?_ (fun k => ?_) ?_
  · rw [hostChain_m]; omega
  · show C.P.vtx ((C.s + k) % C.P.n) = (hostPoly Q S R).vtx (((g + 1) % K + k) % (hostPoly Q S R).n)
    rw [hs, zero_add, hPn, hostPoly_n, hP, Existence.vtx_rotate _ _ (by rw [hostPoly_n]; exact Nat.mod_lt _ (by omega)),
      hostPoly_n, hgi, Nat.add_mod_mod, Nat.mod_add_mod]
  · rw [hP, coordBound_rotate]
    rfl

/-- **Clockwise extraction** for a chain from index `0` of the reversed rotated host polygon
(`C.P.vtx k = hostPoly.vtx (i0 + (K - 1 - k))`), through the mirror. -/
theorem extractOK_rev (X : Extract.Ctx Q S R) {g i0 : ℕ} (hg : g < nk (interiorModel Q) S R)
    (hgc : ChordGap (interiorModel Q) S R g)
    (hgi : (g + 1) % nk (interiorModel Q) S R = i0 % nk (interiorModel Q) S R) {C : Chain}
    (hPn : C.P.n = nk (interiorModel Q) S R)
    (hPv : ∀ k, k < nk (interiorModel Q) S R → C.P.vtx k =
      (hostPoly Q S R).vtx ((i0 + (nk (interiorModel Q) S R - 1 - k)) % nk (interiorModel Q) S R))
    (hPs : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) :
    DownDrv.ExtractOK Q S R C := by
  have h3 := X.three
  set K := nk (interiorModel Q) S R with hK
  have hK0 : 0 < K := by omega
  obtain ⟨a, hnk'0, haK0, hk'0⟩ := hk_mir X.hQ X.hFam X.hne X.hR
  have haK : a ≤ K := haK0
  have hk' : ∀ j, j < K → hk (interiorModel Q.mir) (mirF S) (mir '' R) j =
      rk (interiorModel Q).W.n (Q.n - 1) (hk (interiorModel Q) S R ((a + K - 1 - j) % K)) := hk'0
  set K' := nk (interiorModel Q.mir) (mirF S) (mir '' R) with hK'
  have hnk' : K' = K := hnk'0
  set i₀ := i0 % K with hi₀
  have hi₀K : i₀ < K := Nat.mod_lt _ hK0
  set s' := (a + K - i₀) % K with hs'
  set g' := (s' + K - 1) % K with hg'
  have hs'K : s' < K := Nat.mod_lt _ hK0
  have hg'K : g' < K := Nat.mod_lt _ hK0
  have X' := DownDrv.ctx_mir X
  have h := modelMir_interior X.hQ
  have hc := h.walk.c_lt
  have hWn : (interiorModel Q).W.n = Q.n := walk_n Q
  -- the mirrored host polygon at a reflected index
  have hvtx' : ∀ j, j < K → (hostPoly Q.mir (mirF S) (mir '' R)).vtx j =
      mir ((hostPoly Q S R).vtx ((a + K - 1 - j) % K)) := by
    intro j hj
    have hσ : (a + K - 1 - j) % K < K := Nat.mod_lt _ hK0
    have hb := hostKeys_bounds (hk_mem (walkAx_interiorModel X.hQ) X.hFam.2.1 X.hFam.1 hσ)
    obtain ⟨r0, rn⟩ := rk_bounds hc hb.1 hb.2
    rw [hostPoly_vtx (by rw [← hK', hnk']; exact hj), hk' j hj, hostPt_mir X.hQ r0 rn,
      rk_rk hc hb.1 hb.2, hostPoly_vtx hσ]
  -- the mirrored chain is a rotation of the mirrored host polygon
  have hPm : C.mir.P = (hostPoly Q.mir (mirF S) (mir '' R)).rotate s' := by
    apply poly_eq_of_vtx
    · rw [chainMir_P, mir_n, Existence.n_rotate, hostPoly_n, hPn, ← hK', hnk']
    · intro k hk
      rw [chainMir_P, mir_n, hPn] at hk
      have e1 : (i0 + (K - 1 - k)) % K = (i₀ + (K - 1 - k)) % K := by rw [hi₀, Nat.mod_add_mod]
      have e2 : (a + K - 1 - (s' + k) % K) % K = (i₀ + (K - 1 - k)) % K := by
        rw [hs']; exact idx_I1 hK0 haK hi₀K hk
      rw [chainMir_P, mir_vtx, hPv k hk,
        Existence.vtx_rotate _ _ (by rw [hostPoly_n, ← hK', hnk']; exact hk),
        hostPoly_n, ← hK', hnk', hvtx' _ (Nat.mod_lt _ hK0), e2, e1]
  -- the chord gap of the mirrored region
  have hgc' : ChordGap (interiorModel Q.mir) (mirF S) (mir '' R) g' := by
    have hgi' : (g + 1) % K = i₀ := hgi
    apply chordGap_mir X.hQ hgc
    · have e : (a + K - 1 - g') % K = (g + 1) % K := by
        rw [hg', hs']; exact idx_I2 hK0 haK hi₀K hg hgi'
      rw [hk' g' hg'K, e]
    · have e : (a + K - 1 - (g' + 1) % K) % K = g := by
        rw [hg', hs']; exact idx_I3 hK0 haK hi₀K hg hgi'
      show hk (interiorModel Q.mir) (mirF S) (mir '' R) ((g' + 1) % K') = _
      rw [hnk', hk' _ (Nat.mod_lt _ hK0), e]
  have hg'K' : g' < nk (interiorModel Q.mir) (mirF S) (mir '' R) := by
    rw [← hK', hnk']; exact hg'K
  -- extraction for the mirrored chain
  have hE' := DownDrv.extractOK_host X' hg'K' hgc'
  refine DownDrv.extractOK_of_mir X.hQ hPs (extractOK_of_model ?_ hE')
  refine chainModel_congr ?_ (fun k => ?_) ?_
  · rw [chainMir_m, hostChain_m, ← hK', hnk']; rw [hPn] at hm; omega
  · show C.mir.P.vtx ((C.mir.s + k) % C.mir.P.n) =
      (hostPoly Q.mir (mirF S) (mir '' R)).vtx
        (((g' + 1) % K' + k) % (hostPoly Q.mir (mirF S) (mir '' R)).n)
    have hsm : C.mir.s = 0 := hs
    have hg1 : (g' + 1) % K = s' := by
      rw [hg', Nat.mod_add_mod, show s' + K - 1 + 1 = s' + K by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hs'K]
    rw [hsm, zero_add, hPm, Existence.n_rotate, hostPoly_n, ← hK', hnk',
      Existence.vtx_rotate _ _ (by rw [hostPoly_n, ← hK', hnk']; exact Nat.mod_lt _ hK0), hostPoly_n,
      ← hK', hnk', hg1, Nat.add_mod_mod]
  · rw [hPm, coordBound_rotate]
    rfl

end

end DownMath

end Chazelle.Core
