module

public import Erdos272.Counting.N86412.APTemplatePrefix86412
public import Erdos272.Resources.SourceBridge208

@[expose] public section

namespace JSP233.APTemplateSets86412
open StarCompletion SourceBridge208 OrderedFinite86412 APGridTools86412
open APGridGeometry86412 APTemplatePrefix86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem grid_one (a d : ℤ) : Grid a d 1={a} := by
  ext x
  simp only [mem_grid, Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, he⟩
    have hi0 : i=0 := by omega
    simpa only [hi0, Nat.cast_zero, zero_mul, add_zero] using he
  · intro he
    exact ⟨0, by omega, by simpa only [Nat.cast_zero, zero_mul, add_zero] using he⟩

theorem grid_insert_first (a d : ℤ) (m : ℕ) :
    insert a (Grid (a+d) d m)=Grid a d (m+1) := by
  have hh := grid_append a d 1 m
  simpa only [grid_one, Nat.cast_one, one_mul, Finset.singleton_union, Nat.add_comm 1 m] using hh

theorem grid_insert_last (a d : ℤ) (m : ℕ) :
    insert (a+(m : ℤ)*d) (Grid a d m)=Grid a d (m+1) := by
  have hh := grid_append a d m 1
  simpa only [grid_one, Finset.union_singleton] using hh

theorem template_lower {a d x : ℤ} {n l r : ℕ}
    (hd : 0<d) (hx : x∈Template a d n l r) : a≤x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  rcases Finset.mem_insert.mp hx with rfl | hxG
  · exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hd.le)
  · have hh := grid_lower hd hxG
    have hp := mul_nonneg (Int.natCast_nonneg (1+l)) hd.le
    omega

theorem template_upper {a d x : ℤ} {n l r : ℕ}
    (hd : 0<d) (hn : 2≤n) (hx : x∈Template a d n l r) :
    x≤a+((n-1+l+r : ℕ) : ℤ)*d := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg _) hd.le)
  rcases Finset.mem_insert.mp hx with rfl | hxG
  · exact le_rfl
  · obtain ⟨i, hi, rfl⟩ := mem_grid.mp hxG
    have hnum : 1+l+i≤n-1+l+r := by omega
    have hnumR : ((1+l+i : ℕ) : ℤ)≤((n-1+l+r : ℕ) : ℤ) := by exact_mod_cast hnum
    have hp := mul_le_mul_of_nonneg_right hnumR hd.le
    push_cast at hp ⊢
    linarith only [hp]

theorem double_missing {a d : ℤ} {n : ℕ} (hd : 0<d) (hn : 4≤n) :
    a+(n : ℤ)*d∉Template a d n 1 1 := by
  intro hx
  rcases Finset.mem_insert.mp hx with he | hx
  · have hp := mul_pos (by omega : 0<(n : ℤ)) hd
    omega
  rcases Finset.mem_insert.mp hx with he | hxG
  · have hne : n-1+1+1=n+1 := by omega
    rw [hne] at he
    push_cast at he
    nlinarith only [he, hd]
  · have hlast := grid_last hd hxG
    have hnm : ((n-2 : ℕ) : ℤ)=(n : ℤ)-2 := by omega
    norm_num only at hlast
    rw [hnm] at hlast
    nlinarith only [hlast, hd]

theorem template_isAP {a d : ℤ} {n : ℕ} (hd : 0<d) (hn : 4≤n) :
    StarCompletion.IsAP (Template a d n 0 0) := by
  have he : a+((n-1 : ℕ) : ℤ)*d=(a+d)+((n-2 : ℕ) : ℤ)*d := by
    have hh : ((n-1 : ℕ) : ℤ)=((n-2 : ℕ) : ℤ)+1 := by omega
    rw [hh]
    ring
  have hn2 : n-2+1=n-1 := by omega
  have hn1 : n-1+1=n := by omega
  have hform : Template a d n 0 0=Grid a d n := by
    unfold Template
    simp only [Nat.add_zero, Nat.cast_one, one_mul]
    rw [he, grid_insert_last, hn2, grid_insert_first, hn1]
  rw [hform]
  exact grid_isAP hd (by omega)

theorem template_large_AP {a d : ℤ} {n l r : ℕ} (hd : 0<d) (hn : 4≤n)
    (hedge : l=0 ∨ r=0) : n-1≤MaxAPSize (Template a d n l r) := by
  have hn2 : n-2+1=n-1 := by omega
  rcases hedge with hl | hr
  · subst l
    let P := insert a (Grid (a+d) d (n-2))
    have hPeq : P=Grid a d (n-1) := by
      simpa only [hn2] using grid_insert_first a d (n-2)
    have hPsub : P⊆Template a d n 0 r := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx0 | hxG
      · rw [hx0]
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_insert_of_mem
        simpa only [Nat.add_zero, Nat.cast_one, one_mul] using hxG
    have hbound := AP_card_le_max (S := Template a d n 0 r)
      (by rw [hPeq]; exact grid_isAP hd (by omega : 0<n-1)) hPsub
    simpa only [hPeq, grid_card hd] using hbound
  · subst r
    let P := insert (a+((n-1+l : ℕ) : ℤ)*d)
      (Grid (a+((1+l : ℕ) : ℤ)*d) d (n-2))
    have he : a+((n-1+l : ℕ) : ℤ)*d=
        (a+((1+l : ℕ) : ℤ)*d)+((n-2 : ℕ) : ℤ)*d := by
      have hh : n-1+l=(1+l)+(n-2) := by omega
      rw [hh]
      push_cast
      ring
    have hPeq : P=Grid (a+((1+l : ℕ) : ℤ)*d) d (n-1) := by
      dsimp only [P]
      rw [he, grid_insert_last, hn2]
    have hPsub : P⊆Template a d n l 0 := Finset.subset_insert a _
    have hbound := AP_card_le_max (S := Template a d n l 0)
      (by rw [hPeq]; exact grid_isAP hd (by omega : 0<n-1)) hPsub
    simpa only [hPeq, grid_card hd] using hbound

#print axioms grid_one
#print axioms grid_insert_first
#print axioms grid_insert_last
#print axioms template_lower
#print axioms template_upper
#print axioms double_missing
#print axioms template_isAP
#print axioms template_large_AP
end
end JSP233.APTemplateSets86412
