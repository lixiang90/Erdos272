module

public import Erdos272.Geometry.N86412.APGridGeometry86412
public import Erdos272.Counting.N86412.APSegments86412

@[expose] public section

namespace JSP233.APTemplatePrefix86412
open ActualAPCount208 OrderedFinite86412 APGridTools86412 APGridGeometry86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Template (a d : ℤ) (n l r : ℕ) : Finset ℤ :=
  insert a (insert (a+((n-1+l+r : ℕ) : ℤ)*d)
    (Grid (a+((1+l : ℕ) : ℤ)*d) d (n-2)))

def TemplatePrefix (a d : ℤ) (l m : ℕ) : Finset ℤ :=
  insert a (Grid (a+((1+l : ℕ) : ℤ)*d) d (m-1))

theorem prefix_card {a d : ℤ} {l m : ℕ} (hd : 0<d) (hm : 1≤m) :
    (TemplatePrefix a d l m).card=m := by
  have hnot : a∉Grid (a+((1+l : ℕ) : ℤ)*d) d (m-1) := by
    intro hh
    have hlo := grid_lower hd hh
    have hpos : 0<((1+l : ℕ) : ℤ) := by omega
    have hp := mul_pos hpos hd
    omega
  rw [TemplatePrefix, Finset.card_insert_of_notMem hnot, grid_card hd]
  omega

theorem prefix_subset {a d : ℤ} {n l r m : ℕ} (hm : m≤n-1) :
    TemplatePrefix a d l m⊆Template a d n l r := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hx0 | hxG
  · rw [hx0]
    exact Finset.mem_insert_self _ _
  · obtain ⟨i, hi, he⟩ := mem_grid.mp hxG
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    exact mem_grid.mpr ⟨i, by omega, he⟩

theorem prefix_initial {a d : ℤ} {n l r m : ℕ} (hd : 0<d)
    (hn : 2≤n) (hm : m≤n-1) :
    IsInitial (Template a d n l r) (TemplatePrefix a d l m) := by
  refine ⟨prefix_subset hm, ?_⟩
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hx0 | hx
  · rw [hx0]
    exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp hx with rfl | hxG
  · rcases Finset.mem_insert.mp hy with rfl | hyG
    · have hnum : 0<((n-1+l+r : ℕ) : ℤ) := by omega
      have hp := mul_pos hnum hd
      omega
    · obtain ⟨j, hj, he⟩ := mem_grid.mp hyG
      have hnum : 1+l+j<n-1+l+r := by omega
      have hnumR : ((1+l+j : ℕ) : ℤ)<((n-1+l+r : ℕ) : ℤ) := by exact_mod_cast hnum
      have hp := mul_lt_mul_of_pos_right hnumR hd
      push_cast at hp hxy he
      linarith only [hp, hxy, he]
  · obtain ⟨i, hi, rfl⟩ := mem_grid.mp hxG
    rcases Finset.mem_insert.mp hy with rfl | hyG
    · have hnum : 0<((1+l : ℕ) : ℤ)+(i : ℤ) := by omega
      have hp := mul_pos hnum hd
      linarith only [hp, hxy]
    · obtain ⟨j, hj, he⟩ := mem_grid.mp hyG
      have hij : i≤j := by
        by_contra hh
        have hnumR : (j : ℤ)<(i : ℤ) := by omega
        have hp := mul_lt_mul_of_pos_right hnumR hd
        linarith only [hp, hxy, he]
      exact Finset.mem_insert_of_mem (mem_grid.mpr ⟨i, by omega, rfl⟩)

theorem prefix_nested {a d : ℤ} {n l k m : ℕ} (hd : 0<d)
    (hn : 2≤n) (hkm : k≤m) (hm : m≤n-1) :
    IsInitial (TemplatePrefix a d l m) (TemplatePrefix a d l k) := by
  constructor
  · intro x hx
    rcases Finset.mem_insert.mp hx with hx0 | hxG
    · rw [hx0]
      exact Finset.mem_insert_self _ _
    · obtain ⟨i, hi, he⟩ := mem_grid.mp hxG
      exact Finset.mem_insert_of_mem (mem_grid.mpr ⟨i, by omega, he⟩)
  · intro x hx y hy hxy
    exact (prefix_initial (r := 0) hd hn (hkm.trans hm)).2 x (prefix_subset hm hx) y hy hxy

theorem middle_mem_prefix {a d : ℤ} {l m i : ℕ} (hd : 0<d) :
    a+((1+l+i : ℕ) : ℤ)*d∈TemplatePrefix a d l m ↔ i<m-1 := by
  constructor
  · intro hx
    rcases Finset.mem_insert.mp hx with he | hxG
    · have hp := mul_pos (by omega : 0<((1+l+i : ℕ) : ℤ)) hd
      omega
    · obtain ⟨j, hj, he⟩ := mem_grid.mp hxG
      push_cast at he
      have hij : (i : ℤ)=(j : ℤ) := by nlinarith only [he, hd]
      omega
  · intro hi
    apply Finset.mem_insert_of_mem
    apply mem_grid.mpr
    refine ⟨i, hi, ?_⟩
    push_cast
    ring

theorem prefix_last {a d : ℤ} {l m : ℕ} (hm : 2≤m) :
    a+((m-1+l : ℕ) : ℤ)*d∈TemplatePrefix a d l m := by
  apply Finset.mem_insert_of_mem
  apply mem_grid.mpr
  refine ⟨m-2, by omega, ?_⟩
  have he : m-1+l=(1+l)+(m-2) := by omega
  rw [he]
  push_cast
  ring

#print axioms prefix_card
#print axioms prefix_subset
#print axioms prefix_initial
#print axioms prefix_nested
#print axioms middle_mem_prefix
#print axioms prefix_last
end
end JSP233.APTemplatePrefix86412
