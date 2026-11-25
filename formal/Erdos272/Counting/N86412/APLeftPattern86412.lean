module

public import Erdos272.Counting.N86412.APLeftLattice86412

@[expose] public section

namespace JSP233.APLeftPattern86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open APSegments86412 OrderedFinite86412 APGridTools86412 APLeftFill86412
open APLeftLattice86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem left_pattern {S T A : Finset ℤ} {a d : ℤ} {b : ℕ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hb : 2≤b) (hd : 0<d)
    (hB : T\A=Grid a d b) (hcard : A.card≤b)
    (hbA2 : BalancedTail T.card 2 A.card)
    (hbB2 : BalancedTail T.card 2 (T\A).card)
    (hbA3 : BalancedTail S.card 3 A.card)
    (heq2 : (Codes T 2).card=intervalMultiplicity T.card 2)
    (heq3 : (Codes S 3).card=intervalMultiplicity S.card 3) :
    let c := a-((b-1 : ℕ) : ℤ)*d
    let G := Grid c d (b-1)
    A=G ∨ A=insert (c-d) G ∨ A=insert (c-2*d) G := by
  let m := b-1
  let c := a-(m : ℤ)*d
  let G := Grid c d m
  change A=G ∨ A=insert (c-d) G ∨ A=insert (c-2*d) G
  have hm1 : 1≤m := by dsimp only [m]; omega
  have hsub : G⊆A := left_scaffold hA (by omega) hd hB hbB2 heq2
  have hGc : G.card=m := grid_card hd m
  have hlat := left_lattice hT hA hb hd hB hcard hbA2 hbB2 hbA3 heq2 heq3
  by_cases he : A=G
  · exact Or.inl he
  have hex : ∃ x∈A, x∉G := by
    by_contra hh
    push_neg at hh
    exact he (Finset.Subset.antisymm hh hsub)
  obtain ⟨x, hx, hxG⟩ := hex
  have hAeq : A=insert x G := one_extra_point hsub (by omega) hx hxG
  have haB : a∈T\A := by
    rw [hB]
    exact mem_grid.mpr ⟨0, by omega, by simp⟩
  have hxa : x<a := initial_before hA hx haB
  have hxlat : OnLattice c d x := hlat x hx
  have hxc : x<c := by
    by_contra hh
    apply hxG
    exact mem_grid_of_lattice hd (by omega) (by dsimp only [c]; omega) hxlat
  let z := c+((m : ℤ)-1)*d
  have hzG : z∈G := by
    apply mem_grid.mpr
    refine ⟨m-1, by omega, ?_⟩
    dsimp only [z]
    rw [Nat.cast_sub (by omega : 1≤m)]
    simp only [Nat.cast_one]
  have hxz : x<z := by
    have hzlo := grid_lower hd hzG
    omega
  have hlast := initial_pair_end (by decide : 2≤2) hA hbA2 heq2 hx (hsub hzG) hxz
  change x+2*(z-x)∈T at hlast
  have hlastBound : x+2*(z-x)≤a+((b : ℤ)-1)*d := by
    by_cases hzA : x+2*(z-x)∈A
    · have hbefore := initial_before hA hzA haB
      have hbR : 0≤(b : ℤ)-1 := by omega
      have hp := mul_nonneg hbR hd.le
      omega
    · have hzB : x+2*(z-x)∈Grid a d b := by
        rw [← hB]
        exact Finset.mem_sdiff.mpr ⟨hlast, hzA⟩
      exact grid_last hd hzB
  have hmR : (m : ℤ)=(b : ℤ)-1 := by
    have hh : (m : ℤ)+1=(b : ℤ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1≤b))
    omega
  have hxlower : c-2*d≤x := by
    dsimp only [z, c] at hlastBound ⊢
    rw [← hmR] at hlastBound
    nlinarith only [hlastBound]
  obtain ⟨i, hi⟩ := hxlat
  have hiLow : -2≤ i := by
    by_contra hh
    have hp := mul_lt_mul_of_pos_right (by omega : i< -2) hd
    omega
  have hiHi : i<0 := by
    by_contra hh
    have hp := mul_nonneg (by omega : 0≤ i) hd.le
    omega
  have hival : i= -1 ∨ i= -2 := by omega
  rcases hival with hi1 | hi2
  · have hxval : x=c-d := by rw [hi1] at hi; linarith only [hi]
    rw [hxval] at hAeq
    exact Or.inr (Or.inl hAeq)
  · have hxval : x=c-2*d := by rw [hi2] at hi; linarith only [hi]
    rw [hxval] at hAeq
    exact Or.inr (Or.inr hAeq)

#print axioms left_pattern
end
end JSP233.APLeftPattern86412
