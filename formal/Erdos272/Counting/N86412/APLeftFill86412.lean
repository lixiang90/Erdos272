module

public import Erdos272.Counting.N86412.APGridTools86412
public import Erdos272.Counting.N86412.APSegments86412

@[expose] public section

namespace JSP233.APLeftFill86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open APSegments86412 OrderedFinite86412 APGridTools86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem left_scaffold {T A : Finset ℤ} {a d : ℤ} {b : ℕ}
    (hA : IsInitial T A) (hb : 1≤b) (hd : 0<d)
    (hB : T\A=Grid a d b)
    (hbal : BalancedTail T.card 2 (T\A).card)
    (heq : (Codes T 2).card=intervalMultiplicity T.card 2) :
    Grid (a-((b-1 : ℕ) : ℤ)*d) d (b-1) ⊆ A := by
  intro z hz
  obtain ⟨i, hi, rfl⟩ := mem_grid.mp hz
  let j := b-1-i
  have hji : j+i=b-1 := Nat.sub_add_cancel (by omega : i≤b-1)
  have hj0 : 0<j := by omega
  have hjb : j<b := by omega
  have hx : a∈T\A := by
    rw [hB]
    exact mem_grid.mpr ⟨0, by omega, by simp⟩
  have hy : a+(j : ℤ)*d∈T\A := by
    rw [hB]
    exact mem_grid.mpr ⟨j, hjb, rfl⟩
  have hxy : a<a+(j : ℤ)*d := by
    have hjR : 0<(j : ℤ) := by exact_mod_cast hj0
    nlinarith only [mul_pos hjR hd]
  have hzT := tail_pair_start (by decide : 2≤2) hA hbal heq hx hy hxy
  norm_num only [Nat.cast_ofNat] at hzT
  have hjR : (j : ℤ)=((b-1 : ℕ) : ℤ)-(i : ℤ) := by
    have hh : (j : ℤ)+(i : ℤ)=((b-1 : ℕ) : ℤ) := by exact_mod_cast hji
    omega
  have he : a+(j : ℤ)*d-(2 : ℤ)*((a+(j : ℤ)*d)-a)=
      a-((b-1 : ℕ) : ℤ)*d+(i : ℤ)*d := by rw [hjR]; ring
  rw [he] at hzT
  by_contra hzA
  have hzB : a-((b-1 : ℕ) : ℤ)*d+(i : ℤ)*d∈T\A :=
    Finset.mem_sdiff.mpr ⟨hzT, hzA⟩
  rw [hB] at hzB
  have hlo := grid_lower hd hzB
  have hiR : (i : ℤ)<((b-1 : ℕ) : ℤ) := by exact_mod_cast hi
  have hp := mul_lt_mul_of_pos_right hiR hd
  omega

theorem no_interleaved_extra {S T A : Finset ℤ} {a d x y : ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A) (hd : 0<d)
    (hb2 : BalancedTail T.card 2 A.card)
    (hb3 : BalancedTail S.card 3 A.card)
    (heq2 : (Codes T 2).card=intervalMultiplicity T.card 2)
    (heq3 : (Codes S 3).card=intervalMultiplicity S.card 3)
    (hx : x∈A) (hy : y∈A) (hyx : y<x) (hxy : x<y+d)
    (hcoords : ∀ z∈T, z=x ∨ OnLattice y d z)
    (hnext : a+d∈T) (hya : y+d≤a) : False := by
  have hz2 := initial_pair_end (by decide : 2≤2) hA hb2 heq2 hy hx hyx
  change y+2*(x-y)∈T at hz2
  have hz2lat : OnLattice y d (y+2*(x-y)) :=
    (hcoords _ hz2).resolve_left (by omega)
  have hz2eq := lattice_one_between hd hz2lat (by omega) (by omega)
  have hz3 := initial_pair_end (by decide : 2≤3) (initial_trans hT hA) hb3 heq3
    hy hx hyx
  change y+3*(x-y)∈S at hz3
  have hz3T : y+3*(x-y)∈T :=
    hT.2 _ hz3 _ hnext (by omega)
  have hz3lat : OnLattice y d (y+3*(x-y)) :=
    (hcoords _ hz3T).resolve_left (by omega)
  have hbase : OnLattice y d (y+d) := ⟨1, by ring⟩
  exact lattice_no_between hd (lattice_translate hbase hz3lat) (by omega) (by omega)

#print axioms left_scaffold
#print axioms no_interleaved_extra
end
end JSP233.APLeftFill86412
