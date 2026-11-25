module

public import Erdos272.Counting.N86412.APTemplateSets86412
public import Erdos272.Counting.N86412.APTemplateArithmetic86412
public import Erdos272.Counting.N86412.APReconstruction86412

@[expose] public section

namespace JSP233.APSingleHole86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APReconstruction86412
open OrderedFinite86412 APGridTools86412 APTemplatePrefix86412 APTemplateSets86412
open APTemplateArithmetic86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem left_hole_divides {S : Finset ℤ} {a d : ℤ} {n q : ℕ}
    (hd : 0<d) (hq : 3≤q) (hqn : q<n) (hcard : S.card=n)
    (hform : S=Template a d n 1 0)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) : q∣n := by
  by_contra hnot
  have hr : n%q≠0 := fun hh => hnot (Nat.dvd_of_mod_eq_zero hh)
  let D := n/q
  let A := TemplatePrefix a d 1 (D+1)
  have hf := quotient_frame hq hqn
  have hD : 1≤D := hf.1
  have hA : IsInitial S A := by
    rw [hform]
    exact prefix_initial hd (by omega) hf.2.1
  have hAc : A.card=D+1 := prefix_card hd (by omega)
  have hbal : BalancedTail S.card q A.card := by
    rw [hcard, hAc]
    exact Or.inr ⟨hr, rfl⟩
  have hx : a∈A := Finset.mem_insert_self a _
  have hy : a+((D+1 : ℕ) : ℤ)*d∈A := by
    have hh := prefix_last (a := a) (d := d) (l := 1) (by omega : 2≤D+1)
    simpa only [Nat.add_sub_cancel] using hh
  have hxy : a<a+((D+1 : ℕ) : ℤ)*d := by
    have hp := mul_pos (by omega : 0<((D+1 : ℕ) : ℤ)) hd
    omega
  have hz := initial_pair_end (by omega : 2≤q) hA hbal heq hx hy hxy
  have hze : a+(q : ℤ)*((a+((D+1 : ℕ) : ℤ)*d)-a)=
      a+((q*(D+1) : ℕ) : ℤ)*d := by push_cast; ring
  rw [hze, hform] at hz
  have hupper := template_upper hd (by omega : 2≤n) hz
  have hnn : n-1+1+0=n := by omega
  rw [hnn] at hupper
  have hrem : n%q+q*D=n := Nat.mod_add_div n q
  have hrq : n%q<q := Nat.mod_lt n (by omega)
  have hprod : q*(D+1)=q*D+q := by ring
  have hbig : n<q*(D+1) := by omega
  have hbigR : (n : ℤ)<((q*(D+1) : ℕ) : ℤ) := by exact_mod_cast hbig
  have hp := mul_lt_mul_of_pos_right hbigR hd
  omega

theorem right_hole_divides {S : Finset ℤ} {a d : ℤ} {n q : ℕ}
    (hd : 0<d) (hq : 3≤q) (hqn : q<n) (hcard : S.card=n)
    (hform : S=Template a d n 0 1)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) : q∣n := by
  by_contra hnot
  have hr : n%q≠0 := fun hh => hnot (Nat.dvd_of_mod_eq_zero hh)
  let D := n/q
  let m := n-(D+1)
  let A := TemplatePrefix a d 0 m
  have hf := quotient_frame hq hqn
  have hD : 1≤D := hf.1
  have hm1 : 1≤m := by dsimp only [m]; omega
  have hmn : m≤n-2 := by dsimp only [m]; omega
  have hA : IsInitial S A := by
    rw [hform]
    exact prefix_initial hd (by omega) (by omega)
  have hAc : A.card=m := prefix_card hd hm1
  have hdiff := Finset.card_sdiff_add_card_eq_card hA.1
  have htail : (S\A).card=D+1 := by dsimp only [m] at hAc; omega
  have hbal : BalancedTail S.card q (S\A).card := by
    rw [hcard, htail]
    exact Or.inr ⟨hr, rfl⟩
  have hcoord : 1+0+(m-1)=m := by omega
  have hxS : a+(m : ℤ)*d∈S := by
    rw [hform]
    apply Finset.mem_insert_of_mem
    apply Finset.mem_insert_of_mem
    apply mem_grid.mpr
    refine ⟨m-1, by omega, ?_⟩
    have hmR : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    rw [hmR]
    norm_num
    ring
  have hxA : a+(m : ℤ)*d∉A := by
    intro hh
    have hbad := (middle_mem_prefix (a := a) (d := d) (l := 0) (m := m)
      (i := m-1) hd).mp (by simpa only [hcoord] using hh)
    omega
  have hyS : a+(n : ℤ)*d∈S := by
    rw [hform]
    apply Finset.mem_insert_of_mem
    have hnn : n-1+0+1=n := by omega
    rw [hnn]
    exact Finset.mem_insert_self _ _
  have hyA : a+(n : ℤ)*d∉A := by
    intro hh
    rcases Finset.mem_insert.mp hh with he | hyG
    · have hp := mul_pos (by omega : 0<(n : ℤ)) hd
      omega
    · have hu := grid_upper hd hyG
      have hmnR : ((m-1 : ℕ) : ℤ)+1≤(n : ℤ) := by omega
      have hp := mul_le_mul_of_nonneg_right hmnR hd.le
      norm_num only at hu
      nlinarith only [hu, hp]
  have hxy : a+(m : ℤ)*d<a+(n : ℤ)*d := by
    have hp := mul_lt_mul_of_pos_right (by omega : (m : ℤ)<(n : ℤ)) hd
    omega
  have hz := tail_pair_start (by omega : 2≤q) hA hbal heq
    (Finset.mem_sdiff.mpr ⟨hxS, hxA⟩) (Finset.mem_sdiff.mpr ⟨hyS, hyA⟩) hxy
  rw [hform] at hz
  have hlo := template_lower hd hz
  have hrem : n%q+q*D=n := Nat.mod_add_div n q
  have hrq : n%q<q := Nat.mod_lt n (by omega)
  have hprod : q*(D+1)=q*D+q := by ring
  have hbig : n<q*(D+1) := by omega
  have hbigR : (n : ℤ)<((q*(D+1) : ℕ) : ℤ) := by exact_mod_cast hbig
  have hp := mul_lt_mul_of_pos_right hbigR hd
  have hnm : (n : ℤ)-(m : ℤ)=((D+1 : ℕ) : ℤ) := by dsimp only [m]; omega
  have he : (a+(n : ℤ)*d)-(q : ℤ)*((a+(n : ℤ)*d)-(a+(m : ℤ)*d))=
      a+((n : ℤ)-((q*(D+1) : ℕ) : ℤ))*d := by
    push_cast
    have hnmul := congrArg (fun z : ℤ => (q : ℤ)*z*d) hnm
    push_cast at hnmul
    nlinarith only [hnmul]
  rw [he] at hlo
  nlinarith only [hlo, hp]

#print axioms left_hole_divides
#print axioms right_hole_divides
end
end JSP233.APSingleHole86412
