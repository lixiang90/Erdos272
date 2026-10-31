import Erdos272.Arithmetic.CleanupEval208
import Mathlib.Algebra.BigOperators.Fin

namespace JSP233.CleanupChecked208
open CleanupEval208 CleanupNet208
open scoped BigOperators
set_option maxHeartbeats 0

theorem fold_summary (field : BandValue → ℕ) (hz : field bandZero=0)
    (ha : ∀ a b,field (bandAdd a b)=field a+field b) (r : Row) (d : ℕ) (bs : List Band) :
    field (foldBands r d bs).value=(bs.map (fun b=>field (bandValue r d b))).sum := by
  induction bs with
  | nil => simpa only [foldBands,List.map_nil,List.sum_nil] using hz
  | cons b bs ih => simpa only [foldBands,ha,List.map_cons,List.sum_cons,ih]

theorem fold_sum (field : BandValue → ℕ) (hz : field bandZero=0)
    (ha : ∀ a b,field (bandAdd a b)=field a+field b) (r : Row) (d : ℕ) (bs : List Band) :
    field (foldBands r d bs).value=∑ j : Fin bs.length,field (bandValue r d bs[j.val]) := by
  have hh := fold_summary field hz ha r d bs
  rw [←List.ofFn_getElem_eq_map,List.sum_ofFn] at hh
  exact hh

theorem band_credit_eq (r : Row) (d : ℕ) (b : Band) :
    (bandValue r d b).credit=(bandValue r d b).count*(b.T*r.grid/r.high) := by
  unfold bandValue
  split_ifs <;> simp only [bandZero,Nat.zero_mul]

theorem step_substitution {r : Row} {d : ℕ} (h : (step r d).good=true)
    (actual : Fin r.bands.length → ℕ)
    (ha : ∀ j,actual j≤(bandValue r d r.bands[j.val]).count) :
    (∑ j : Fin r.bands.length,(actual j : ℝ)*
      (((min r.grid (foldBands r d r.bands).value.windows+Ceil (r.i*r.grid) r.low : ℕ) : ℝ)/r.grid-
        (r.bands[j.val].T : ℝ)/r.high))≤((step r d).totals.net : ℝ)/r.grid := by
  rcases step_good h with ⟨hband,hG,hL,hLH,hD⟩
  let T : Fin r.bands.length → ℕ := fun j=>r.bands[j.val].T
  let E : Fin r.bands.length → ℕ := fun j=>r.bands[j.val].E
  let z : Fin r.bands.length → ℕ := fun j=>(bandValue r d r.bands[j.val]).windows
  let H : Fin r.bands.length → ℕ := fun j=>(bandValue r d r.bands[j.val]).count
  have hET : ∀ j∈Finset.univ,E j≤T j := by
    intro j hj
    have hb := hband r.bands[j.val] (List.getElem_mem j.isLt)
    rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact h3
  have hEi : ∀ j∈Finset.univ,E j≤r.i := by
    intro j hj
    have hb := hband r.bands[j.val] (List.getElem_mem j.isLt)
    rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact h2
  have hown : ∀ j∈Finset.univ,0<H j → (T j-E j+1)*r.grid≤min r.grid (z j)*r.high := by
    intro j hj
    have hb := hband r.bands[j.val] (List.getElem_mem j.isLt)
    rcases hb with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    exact h9
  have hh := actual_count_substitution Finset.univ T E z H hG hL hLH hET hEi hown
    actual (fun j hj=>ha j)
  have hz : (∑ j,z j)=(foldBands r d r.bands).value.windows :=
    (fold_sum BandValue.windows rfl (fun a b=>rfl) r d r.bands).symm
  have hn : (∑ j,H j)=(foldBands r d r.bands).value.count :=
    (fold_sum BandValue.count rfl (fun a b=>rfl) r d r.bands).symm
  have hc : (∑ j,H j*(T j*r.grid/r.high))=(foldBands r d r.bands).value.credit := by
    rw [fold_sum BandValue.credit rfl (fun a b=>rfl) r d r.bands]
    apply Finset.sum_congr rfl
    intro j hj
    exact (band_credit_eq r d r.bands[j.val]).symm
  rw [hz,hn,hc] at hh
  have hnet : (step r d).totals.net=
      (foldBands r d r.bands).value.count*
        (min r.grid (foldBands r d r.bands).value.windows+Ceil (r.i*r.grid) r.low)-
          (foldBands r d r.bands).value.credit := by
    simp only [step,Nat.mul_add]
  rw [hnet]
  exact hh

#print axioms fold_sum
#print axioms step_substitution
end JSP233.CleanupChecked208
