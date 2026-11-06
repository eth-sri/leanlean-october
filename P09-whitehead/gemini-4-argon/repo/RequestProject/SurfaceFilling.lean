module

public import RequestProject.SurfaceCells

@[expose] public section

namespace FiniteChains.Davis

open RACG Mirror Comb Cell

universe u

variable {κ ι : Type u} {M : ℕ} [NeZero M] [DecidableEq κ] [DecidableEq ι]
  {vc : Fin M → κ} {ec : Fin M → ι} (hc : Compat vc ec)

theorem htpy_ray_step (p : Fin M) :
    Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p) (ray hc (p + 1)) := by
  have hA : Htpy (sdCx hc) (spx1 (cV hc p)) (spx1 (cV hc (p + 1)))
      (bdEdge hc p) (gg hc p ++ delta hc (p + 1)) :=
    htpy_of_loop_nil (isPath_bdEdge hc p) ((isPath_gg hc p).append (isPath_delta hc (p + 1)))
      (htpy_nil_of_star (cT1 hc p) (starCh_spx1 (cV_le_cT1 hc p))
        ((isPath_bdEdge hc p).append (isPath_revPath ((isPath_gg hc p).append (isPath_delta hc (p + 1)))))
        (pathIn_append' (pathIn_bdEdge_T1 hc p)
          (pathIn_revPath (pathIn_append' (pathIn_gg_T1 hc p) (pathIn_delta1_T1 hc p)))))
  have hB : Htpy (sdCx hc) (spx1 (cV hc p)) (spx1 (cW hc (p + 1)))
      (revPath (delta hc p) ++ gam hc p) (gg hc p) :=
    htpy_of_loop_nil ((isPath_revPath (isPath_delta hc p)).append (isPath_gam hc p)) (isPath_gg hc p)
      (htpy_nil_of_star (cT2 hc p) (starCh_spx1 (cV_le_cT2 hc p))
        (((isPath_revPath (isPath_delta hc p)).append (isPath_gam hc p)).append (isPath_revPath (isPath_gg hc p)))
        (pathIn_append' (pathIn_append' (pathIn_revPath (pathIn_delta_T2 hc p)) (pathIn_gam_T2 hc p))
          (pathIn_revPath (pathIn_gg_T2 hc p))))
  have hC : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cW hc (p + 1)))
      (alph hc p ++ gam hc p) (alph hc (p + 1)) :=
    htpy_of_loop_nil ((isPath_alph hc p).append (isPath_gam hc p)) (isPath_alph hc (p + 1))
      (htpy_nil_of_star (cI hc p) (starCh_spx1 (cC_le_cI hc p))
        (((isPath_alph hc p).append (isPath_gam hc p)).append (isPath_revPath (isPath_alph hc (p + 1))))
        (pathIn_append' (pathIn_append' (pathIn_alph_I hc p) (pathIn_gam_I hc p))
          (pathIn_revPath (pathIn_alph1_I hc p))))
  have hD : Htpy (sdCx hc) (spx1 (cW hc p)) (spx1 (cW hc (p + 1)))
      (delta hc p ++ gg hc p) (gam hc p) :=
    (htpy_append_left (isPath_delta hc p) (isPath_gg hc p) hB.symm).trans
      (by simpa [List.append_assoc] using
        (htpy_append_right ((isPath_delta hc p).append (isPath_revPath (isPath_delta hc p)))
          (isPath_gam hc p) (htpy_append_revPath (isPath_delta hc p))))
  have e1 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (ray hc p ++ bdEdge hc p) (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1)))) := by
    simpa [ray, List.append_assoc] using (htpy_append_left (isPath_ray hc p) (isPath_bdEdge hc p) hA)
  have e2 : Htpy (sdCx hc) (spx1 (cC hc)) (spx1 (cV hc (p + 1)))
      (alph hc p ++ (delta hc p ++ (gg hc p ++ delta hc (p + 1))))
      (alph hc p ++ (gam hc p ++ delta hc (p + 1))) := by
    simpa [List.append_assoc] using
      (htpy_append_left (isPath_alph hc p)
        (((isPath_delta hc p).append (isPath_gg hc p)).append (isPath_delta hc (p + 1)))
        (htpy_append_right ((isPath_delta hc p).append (isPath_gg hc p)) (isPath_delta hc (p + 1)) hD))
  exact e1.trans (e2.trans (by simpa [ray, List.append_assoc] using
    (htpy_append_right ((isPath_alph hc p).append (isPath_gam hc p)) (isPath_delta hc (p + 1)) hC)))

def cyc (M : ℕ) [NeZero M] (n : ℕ) : Fin M := ⟨n % M, Nat.mod_lt _ (NeZero.pos M)⟩

theorem cyc_succ (n : ℕ) : cyc M (n + 1) = cyc M n + 1 :=
  Fin.ext (by show (n + 1) % M = (n % M + 1 % M) % M; rw [← Nat.add_mod])

def bdPath : ℕ → List ((sdCx hc).E × Bool)
  | 0 => []
  | n + 1 => bdPath n ++ bdEdge hc (cyc M n)

theorem isPath_bdPath : ∀ n : ℕ,
    IsPath (sdCx hc).src (sdCx hc).tgt (bdPath hc n)
      (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n)))
  | 0 => rfl
  | n + 1 => cyc_succ (M := M) n ▸ (isPath_bdPath n).append (isPath_bdEdge hc (cyc M n))

theorem htpy_bdLoop_nil :
    Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M 0))) (bdPath hc M) [] := by
  have hbd : ∀ n : ℕ, Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n)))
      (bdPath hc n) (revPath (ray hc (cyc M 0)) ++ ray hc (cyc M n)) := by
    intro n; induction n with
    | zero => exact (htpy_revPath_append (isPath_ray hc (cyc M 0))).symm
    | succ n ih =>
        rw [cyc_succ]
        exact (show Htpy (sdCx hc) (spx1 (cV hc (cyc M 0))) (spx1 (cV hc (cyc M n + 1)))
            (bdPath hc (n + 1))
            (revPath (ray hc (cyc M 0)) ++ (ray hc (cyc M n) ++ bdEdge hc (cyc M n))) from
          by simpa [bdPath, List.append_assoc] using
            (htpy_append_right (isPath_bdPath hc n) (isPath_bdEdge hc (cyc M n)) ih)).trans
          (htpy_append_left (isPath_revPath (isPath_ray hc (cyc M 0)))
            ((isPath_ray hc (cyc M n)).append (isPath_bdEdge hc (cyc M n)))
            (htpy_ray_step hc (cyc M n)))
  have h := hbd M
  rw [show cyc M M = cyc M 0 from Fin.ext (by show M % M = 0 % M; rw [Nat.mod_self, Nat.zero_mod])] at h
  exact h.trans (htpy_revPath_append (isPath_ray hc (cyc M 0)))
