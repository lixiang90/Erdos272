module

public import Erdos272.Counting.N86412.APLeftPattern86412
public import Erdos272.Geometry.N86412.APGridGeometry86412
public import Erdos272.Counting.N86412.GapShape86412

@[expose] public section

namespace JSP233.APOneEnd86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open APSegments86412 OrderedFinite86412 APGridTools86412 APLeftFill86412
open APLeftPattern86412 APGridGeometry86412 GapShape86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem grid_left_shape {a d : ℤ} {m : ℕ} (hd : 0<d) :
    LeftGapShape (Grid a d m) d := by
  intro x hx y hy hxy hgap
  exact Or.inl (grid_adjacent hd (Finset.Subset.refl _) hx hy hxy hgap)

theorem insert_grid_left_shape {a d x : ℤ} {m : ℕ}
    (hd : 0<d) (hm : 1≤m) (hx : x=a-d ∨ x=a-2*d) :
    LeftGapShape (insert x (Grid a d m)) d := by
  have hxa : x<a := by rcases hx with rfl | rfl <;> omega
  intro u hu v hv huv hgap
  rcases Finset.mem_insert.mp hu with rfl | huG
  · rcases Finset.mem_insert.mp hv with rfl | hvG
    · omega
    have hav : a≤v := grid_lower hd hvG
    have haG : a∈Grid a d m := mem_grid.mpr ⟨0, by omega, by simp⟩
    have hva : v=a := by
      by_contra hh
      exact hgap a (Finset.mem_insert_of_mem haG) hxa (by omega)
    rw [hva]
    rcases hx with rfl | rfl
    · exact Or.inl (by ring)
    · apply Or.inr
      refine ⟨by ring, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzG
      · exact le_rfl
      · have hza := grid_lower hd hzG
        omega
  · rcases Finset.mem_insert.mp hv with rfl | hvG
    · have hua := grid_lower hd huG
      omega
    · exact Or.inl (grid_adjacent hd (Finset.subset_insert x _) huG hvG huv hgap)

theorem left_half_shape {S T A : Finset ℤ} {a d : ℤ} {b : ℕ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hb : 2≤b) (hd : 0<d)
    (hB : T\A=Grid a d b) (hcard : A.card≤b)
    (hbA2 : BalancedTail T.card 2 A.card)
    (hbB2 : BalancedTail T.card 2 (T\A).card)
    (hbA3 : BalancedTail S.card 3 A.card)
    (heq2 : (Codes T 2).card=intervalMultiplicity T.card 2)
    (heq3 : (Codes S 3).card=intervalMultiplicity S.card 3) :
    LeftGapShape T d := by
  have hp := left_pattern hT hA hb hd hB hcard hbA2 hbB2 hbA3 heq2 heq3
  let m := b-1
  let c := a-(m : ℤ)*d
  let G := Grid c d m
  change A=G ∨ A=insert (c-d) G ∨ A=insert (c-2*d) G at hp
  have hcenter : c+(m : ℤ)*d=a := by dsimp only [c]; ring
  have hcombine : G∪Grid a d b=Grid c d (m+b) := by
    simpa only [hcenter] using grid_append c d m b
  have hdecomp : T=A∪(T\A) := (Finset.union_sdiff_of_subset hA.1).symm
  rcases hp with hp | hp | hp
  · have he : T=Grid c d (m+b) := by rw [hdecomp, hB, hp, hcombine]
    rw [he]
    exact grid_left_shape hd
  · have he : T=insert (c-d) (Grid c d (m+b)) := by
      rw [hdecomp, hB, hp, Finset.insert_union, hcombine]
    rw [he]
    exact insert_grid_left_shape hd (by omega) (Or.inl rfl)
  · have he : T=insert (c-2*d) (Grid c d (m+b)) := by
      rw [hdecomp, hB, hp, Finset.insert_union, hcombine]
    rw [he]
    exact insert_grid_left_shape hd (by omega) (Or.inr rfl)

#print axioms grid_left_shape
#print axioms insert_grid_left_shape
#print axioms left_half_shape
end
end JSP233.APOneEnd86412
