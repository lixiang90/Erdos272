module

public import Erdos272.Counting.N86412.APGridTools86412

@[expose] public section

namespace JSP233.APGridGeometry86412
open OrderedFinite86412 APReflection86412 APGridTools86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem grid_append (a d : ℤ) (m n : ℕ) :
    Grid a d m ∪ Grid (a+(m : ℤ)*d) d n=Grid a d (m+n) := by
  ext x
  constructor
  · intro hx
    obtain hx | hx := Finset.mem_union.mp hx
    · obtain ⟨i, hi, he⟩ := mem_grid.mp hx
      exact mem_grid.mpr ⟨i, by omega, he⟩
    · obtain ⟨j, hj, he⟩ := mem_grid.mp hx
      apply mem_grid.mpr
      refine ⟨m+j, by omega, ?_⟩
      push_cast
      rw [he]
      ring
  · intro hx
    obtain ⟨i, hi, he⟩ := mem_grid.mp hx
    by_cases him : i<m
    · exact Finset.mem_union_left _ (mem_grid.mpr ⟨i, him, he⟩)
    · apply Finset.mem_union_right
      apply mem_grid.mpr
      refine ⟨i-m, by omega, ?_⟩
      rw [Nat.cast_sub (by omega : m≤ i)]
      rw [he]
      ring

theorem grid_adjacent {S : Finset ℤ} {a d x y : ℤ} {m : ℕ}
    (hd : 0<d) (hsub : Grid a d m⊆S)
    (hx : x∈Grid a d m) (hy : y∈Grid a d m) (hxy : x<y)
    (hgap : ∀ z∈S, x<z → z<y → False) : y-x=d := by
  obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
  obtain ⟨j, hj, rfl⟩ := mem_grid.mp hy
  have hij : i<j := by
    by_contra hh
    have hhR : (j : ℤ)≤(i : ℤ) := by omega
    have hp := mul_le_mul_of_nonneg_right hhR hd.le
    omega
  have hji : j=i+1 := by
    by_contra hh
    have hij2 : i+1<j := by omega
    have hz := hsub (mem_grid.mpr ⟨i+1, by omega, rfl⟩)
    apply hgap _ hz
    · push_cast
      linarith only [hd]
    · have hhR : ((i+1 : ℕ) : ℤ)<(j : ℤ) := by exact_mod_cast hij2
      have hp := mul_lt_mul_of_pos_right hhR hd
      omega
  rw [hji]
  push_cast
  ring

theorem neg_grid (a d : ℤ) (m : ℕ) :
    NegSet (Grid a d m)=Grid (-a-((m : ℤ)-1)*d) d m := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, he⟩ := mem_grid.mp (mem_negset.mp hx)
    let j := m-1-i
    have hji : j+i+1=m := by dsimp only [j]; omega
    have hj : j<m := by omega
    have hjiR : (j : ℤ)+(i : ℤ)+1=(m : ℤ) := by exact_mod_cast hji
    apply mem_grid.mpr
    refine ⟨j, hj, ?_⟩
    have hjR : (j : ℤ)=(m : ℤ)-1-(i : ℤ) := by omega
    rw [hjR]
    linarith only [he]
  · intro hx
    obtain ⟨j, hj, he⟩ := mem_grid.mp hx
    let i := m-1-j
    have hij : i+j+1=m := by dsimp only [i]; omega
    have hi : i<m := by omega
    have hijR : (i : ℤ)+(j : ℤ)+1=(m : ℤ) := by exact_mod_cast hij
    apply mem_negset.mpr
    apply mem_grid.mpr
    refine ⟨i, hi, ?_⟩
    have hiR : (i : ℤ)=(m : ℤ)-1-(j : ℤ) := by omega
    rw [hiR]
    linarith only [he]

#print axioms grid_append
#print axioms grid_adjacent
#print axioms neg_grid
end
end JSP233.APGridGeometry86412
