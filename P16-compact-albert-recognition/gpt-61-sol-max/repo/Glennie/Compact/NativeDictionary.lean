/- Explicit real coordinate decoder from the 27-coordinate model to the native
compact Albert carrier of `Glennie.Native`, in the Sector gauge (hidden columns
-o12, +o02, -o01; last imaginary octonion coordinate with sign i(j l) = -k l).

Full index 0 is the unit. Full index n+1 is traceless index n, in the order
  t s a01 b01 a02 b02 a12 b12 u00 v00 u01 v01 u02 v02 u10 v10 u11 v11 u12 v12
  u20 v20 u21 v21 u22 v22,
with H = [[t+s, a01+i b01, a02+i b02], [conj, -t+s, a12+i b12], [conj, conj, -2s]]
and the ROW-major hidden matrix M[r][c] = u_rc + i v_rc.

Raw native conventions: T(1)=3, halved Jordan product,
B(x,y) = T(x o y) = 3 g, hidden metric factor 2, no factor 4 anywhere. -/
module

public import Glennie.SectorModel

@[expose] public section

namespace Glennie.Compact.NativeDictionary

noncomputable section

@[simp] def extDecode0 (a : Fin 26 → ℝ) : Albert :=
  ⟨a 0 + a 1, -a 0 + a 1, -2 * a 1,
    (⟨a 2, a 3, -a 12, -a 13⟩, ⟨-a 18, -a 19, -a 24, a 25⟩),
    (⟨a 4, a 5, a 10, a 11⟩, ⟨a 16, a 17, a 22, -a 23⟩),
    (⟨a 6, a 7, -a 8, -a 9⟩, ⟨-a 14, -a 15, -a 20, a 21⟩)⟩

/-! ## Full 27-coordinate decoder -/

/-- Drop the unit coordinate: full index `i.succ` is traceless index `i`. -/
@[simp] def extTail (a : Fin 27 → ℝ) : Fin 26 → ℝ := fun i => a i.succ

/-- Full decode: coordinate 0 multiplies the native unit (raw trace 3). -/
def extDecode (a : Fin 27 → ℝ) : Albert := a 0 • (1 : Albert) + extDecode0 (extTail a)

end
end Glennie.Compact.NativeDictionary
