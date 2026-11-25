module

public import Erdos272.Counting.N86412.APLeftFill86412

@[expose] public section

namespace JSP233.APLeftLattice86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open APSegments86412 OrderedFinite86412 APGridTools86412 APLeftFill86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem left_lattice {S T A : Finset ℤ} {a d : ℤ} {b : ℕ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hb : 2≤b) (hd : 0<d)
    (hB : T\A=Grid a d b) (hcard : A.card≤b)
    (hbA2 : BalancedTail T.card 2 A.card)
    (hbB2 : BalancedTail T.card 2 (T\A).card)
    (hbA3 : BalancedTail S.card 3 A.card)
    (heq2 : (Codes T 2).card=intervalMultiplicity T.card 2)
    (heq3 : (Codes S 3).card=intervalMultiplicity S.card 3) :
    ∀ x∈A, OnLattice (a-((b-1 : ℕ) : ℤ)*d) d x := by
  let m := b-1
  let c := a-(m : ℤ)*d
  let G := Grid c d m
  have hm1 : 1≤m := by dsimp only [m]; omega
  have hsub : G⊆A := left_scaffold hA (by omega) hd hB hbB2 heq2
  have hGc : G.card=m := grid_card hd m
  have hcG : c∈G := mem_grid.mpr ⟨0, by omega, by simp⟩
  have haB : a∈T\A := by
    rw [hB]
    exact mem_grid.mpr ⟨0, by omega, by simp⟩
  have haNext : a+d∈T := by
    have hh : a+d∈T\A := by
      rw [hB]
      exact mem_grid.mpr ⟨1, by omega, by simp⟩
    exact (Finset.mem_sdiff.mp hh).1
  intro x hx
  change OnLattice c d x
  by_cases hxG : x∈G
  · exact grid_lattice hxG
  have hAeq : A=insert x G := one_extra_point hsub (by omega) hx hxG
  have hxa : x<a := initial_before hA hx haB
  have hcoords : ∀ z∈T, z=x ∨ OnLattice c d z := by
    intro z hz
    by_cases hzA : z∈A
    · rw [hAeq] at hzA
      obtain hzX | hzG := Finset.mem_insert.mp hzA
      · exact Or.inl hzX
      · exact Or.inr (grid_lattice hzG)
    · have hzB : z∈Grid a d b := by
        rw [← hB]
        exact Finset.mem_sdiff.mpr ⟨hz, hzA⟩
      obtain ⟨i, hi, he⟩ := mem_grid.mp hzB
      apply Or.inr
      exact ⟨(m : ℤ)+(i : ℤ), by dsimp only [c]; rw [he]; ring⟩
  by_cases hxc : x<c
  · have hcx := initial_pair_end (by decide : 2≤2) hA hbA2 heq2 hx (hsub hcG) hxc
    change x+2*(c-x)∈T at hcx
    have hlat := (hcoords _ hcx).resolve_left (by omega)
    obtain ⟨j, hj⟩ := hlat
    exact ⟨-j, by linarith only [hj]⟩
  · have hxc0 : 0≤x-c := by omega
    let k := (x-c)/d
    let y := c+k*d
    have hk0 : 0≤k := Int.ediv_nonneg hxc0 hd.le
    have hdiv := Int.ediv_mul_add_emod (x-c) d
    have hmod0 := Int.emod_nonneg (x-c) (ne_of_gt hd)
    have hmodd := Int.emod_lt_of_pos (x-c) hd
    have hyx : y≤x := by dsimp only [y, k]; omega
    have hxy : x<y+d := by dsimp only [y, k]; omega
    have hyc : c≤y := by
      dsimp only [y]
      exact le_add_of_nonneg_right (mul_nonneg hk0 hd.le)
    have hyG : y∈G := by
      apply mem_grid_of_lattice hd hyc
      · dsimp only [c]
        omega
      · exact ⟨k, rfl⟩
    have hyxStrict : y<x := by
      by_contra hh
      have he : x=y := by omega
      exact hxG (he.symm ▸ hyG)
    have hya : y+d≤a := by
      have hh := grid_last hd hyG
      dsimp only [G, c] at hh
      linarith only [hh]
    have hyLat : OnLattice c d y := grid_lattice hyG
    have hcoordsY : ∀ z∈T, z=x ∨ OnLattice y d z := by
      intro z hz
      obtain he | hl := hcoords z hz
      · exact Or.inl he
      · exact Or.inr (lattice_translate hyLat hl)
    exact (no_interleaved_extra hT hA hd hbA2 hbA3 heq2 heq3 hx (hsub hyG)
      hyxStrict hxy hcoordsY haNext hya).elim

#print axioms left_lattice
end
end JSP233.APLeftLattice86412
