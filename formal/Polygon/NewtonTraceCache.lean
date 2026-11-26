import Polygon.NewtonInterpolant
import Polygon.Finite64Columns.B001
import Polygon.Finite64Columns.B013
import Polygon.Finite64Columns.B025
import Polygon.Finite64Columns.B037
import Polygon.Finite64Columns.B049
import Polygon.Finite64Columns.B061
import Polygon.Finite64Columns.B073
import Polygon.Finite64Columns.B085
import Polygon.Finite64Columns.B097
import Polygon.Finite64Columns.B109
import Polygon.Finite64Columns.B121

/-! Reuse checked Newton histories across side counts. -/
namespace Polygon.NewtonTraceCache

def column (m : ℕ) : List ℤ :=
  if m ≤ 12 then Finite64Columns.B001.entries.getD (m - 1) [] else
  if m ≤ 24 then Finite64Columns.B013.entries.getD (m - 13) [] else
  if m ≤ 36 then Finite64Columns.B025.entries.getD (m - 25) [] else
  if m ≤ 48 then Finite64Columns.B037.entries.getD (m - 37) [] else
  if m ≤ 60 then Finite64Columns.B049.entries.getD (m - 49) [] else
  if m ≤ 72 then Finite64Columns.B061.entries.getD (m - 61) [] else
  if m ≤ 84 then Finite64Columns.B073.entries.getD (m - 73) [] else
  if m ≤ 96 then Finite64Columns.B085.entries.getD (m - 85) [] else
  if m ≤ 108 then Finite64Columns.B097.entries.getD (m - 97) [] else
  if m ≤ 120 then Finite64Columns.B109.entries.getD (m - 109) [] else
  if m ≤ 131 then Finite64Columns.B121.entries.getD (m - 121) [] else
  []

private theorem column_eq (m : ℕ) (lo : 1 ≤ m) (hi : m ≤ 131) :
    column m = NewtonExecutor.history m (NewtonExecutor.coefficientRow m 64) 64 := by
  unfold column
  split_ifs
  · have e := Finite64Columns.B001.checked ⟨m - 1, by omega⟩
    have eq : m - 1 + 1 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B013.checked ⟨m - 13, by omega⟩
    have eq : m - 13 + 13 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B025.checked ⟨m - 25, by omega⟩
    have eq : m - 25 + 25 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B037.checked ⟨m - 37, by omega⟩
    have eq : m - 37 + 37 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B049.checked ⟨m - 49, by omega⟩
    have eq : m - 49 + 49 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B061.checked ⟨m - 61, by omega⟩
    have eq : m - 61 + 61 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B073.checked ⟨m - 73, by omega⟩
    have eq : m - 73 + 73 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B085.checked ⟨m - 85, by omega⟩
    have eq : m - 85 + 85 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B097.checked ⟨m - 97, by omega⟩
    have eq : m - 97 + 97 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B109.checked ⟨m - 109, by omega⟩
    have eq : m - 109 + 109 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm
  · have e := Finite64Columns.B121.checked ⟨m - 121, by omega⟩
    have eq : m - 121 + 121 = m := by omega
    simpa only [Fin.val_mk, eq] using e.symm

def traceRow (n width : ℕ) : List ℕ :=
  (List.range width).map fun i ↦ ((column (i + 1)).getD (64 - n) 0).toNat

/-- Every cached integer read is tied to the actual trace by the executable
Newton recurrence, regardless of the downstream polynomial witness. -/
theorem trace_list_certificate (n width : ℕ) {traces : List ℕ}
    (hn : n ≤ 64) (hw : width ≤ 131) (h : traceRow n width = traces) (i : Fin width) :
    Cert.traceCount n (i.val + 1) = traces.getD i.val 0 := by
  rw [← h]
  have hi : i.val < (traceRow n width).length := by simp [traceRow]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [traceRow, List.getElem_map, List.getElem_range]
  rw [column_eq _ (by omega) (by have := i.isLt; omega),
    NewtonExecutor.history_get _ _ _ _ (by omega) (by omega),
    show 64 - (64 - n) = n by omega]
  simp

#print axioms trace_list_certificate

end Polygon.NewtonTraceCache
