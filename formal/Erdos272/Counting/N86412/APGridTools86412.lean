module

public import Erdos272.Counting.N86412.OrderedFinite86412
public import Erdos272.Geometry.N86412.APReflection86412

@[expose] public section

namespace JSP233.APGridTools86412
open OrderedFinite86412 APReflection86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def OnLattice (a d x : ℤ) : Prop := ∃ i : ℤ, x=a+i*d

theorem grid_lower {a d x : ℤ} {m : ℕ} (hd : 0<d)
    (hx : x∈Grid a d m) : a≤x := by
  obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
  exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg i) hd.le)

theorem grid_upper {a d x : ℤ} {m : ℕ} (hd : 0<d)
    (hx : x∈Grid a d m) : x<a+(m : ℤ)*d := by
  obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
  have hiR : (i : ℤ)<(m : ℤ) := by exact_mod_cast hi
  linarith only [mul_lt_mul_of_pos_right hiR hd]

theorem grid_lattice {a d x : ℤ} {m : ℕ} (hx : x∈Grid a d m) :
    OnLattice a d x := by
  obtain ⟨i, hi, he⟩ := mem_grid.mp hx
  exact ⟨i, he⟩

theorem grid_last {a d x : ℤ} {m : ℕ} (hd : 0<d)
    (hx : x∈Grid a d m) : x≤a+((m : ℤ)-1)*d := by
  obtain ⟨i, hi, rfl⟩ := mem_grid.mp hx
  have hiR : (i : ℤ)≤(m : ℤ)-1 := by omega
  linarith only [mul_le_mul_of_nonneg_right hiR hd.le]

theorem mem_grid_of_lattice {a d x : ℤ} {m : ℕ} (hd : 0<d)
    (hlo : a≤x) (hhi : x<a+(m : ℤ)*d) (hx : OnLattice a d x) :
    x∈Grid a d m := by
  obtain ⟨i, rfl⟩ := hx
  have hi0 : 0≤ i := by
    by_contra hh
    have hp := mul_neg_of_neg_of_pos (by omega : i<0) hd
    omega
  have him : i<(m : ℤ) := by
    by_contra hh
    have hp := mul_le_mul_of_nonneg_right (by omega : (m : ℤ)≤ i) hd.le
    omega
  apply mem_grid.mpr
  refine ⟨i.toNat, ?_, ?_⟩
  · omega
  · rw [Int.toNat_of_nonneg hi0]

theorem lattice_translate {a d x y : ℤ} (hx : OnLattice a d x)
    (hy : OnLattice a d y) : OnLattice x d y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  exact ⟨j-i, by ring⟩

theorem lattice_no_between {a d x : ℤ} (hd : 0<d)
    (hx : OnLattice a d x) (hlo : a<x) (hhi : x<a+d) : False := by
  obtain ⟨i, rfl⟩ := hx
  have hi : 1≤ i := by
    by_contra hh
    have hp := mul_nonpos_of_nonpos_of_nonneg (by omega : i≤0) hd.le
    omega
  have hp := mul_le_mul_of_nonneg_right hi hd.le
  omega

theorem lattice_one_between {a d x : ℤ} (hd : 0<d)
    (hx : OnLattice a d x) (hlo : a<x) (hhi : x<a+2*d) : x=a+d := by
  obtain ⟨i, rfl⟩ := hx
  have hi1 : 1≤ i := by
    by_contra hh
    have hp := mul_nonpos_of_nonpos_of_nonneg (by omega : i≤0) hd.le
    omega
  have hi2 : i<2 := by
    by_contra hh
    have hp := mul_le_mul_of_nonneg_right (by omega : 2≤ i) hd.le
    omega
  have hi : i=1 := by omega
  rw [hi, one_mul]

theorem one_extra_point {A G : Finset ℤ} (hG : G⊆A)
    (hcard : A.card≤G.card+1) {x : ℤ} (hx : x∈A) (hxG : x∉G) :
    A=insert x G := by
  apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · exact Finset.insert_subset hx hG
  · rw [Finset.card_insert_of_notMem hxG]
    exact hcard

#print axioms grid_lower
#print axioms grid_upper
#print axioms grid_lattice
#print axioms grid_last
#print axioms mem_grid_of_lattice
#print axioms lattice_translate
#print axioms lattice_no_between
#print axioms lattice_one_between
#print axioms one_extra_point
end
end JSP233.APGridTools86412
