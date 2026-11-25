module

public import Erdos272.Counting.N86412.APTemplateSets86412
public import Erdos272.Counting.N86412.APTemplateArithmetic86412
public import Erdos272.Counting.N86412.APSplit86412
public import Erdos272.Counting.N86412.APReconstruction86412

@[expose] public section

namespace JSP233.APDoubleHole86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412
open APReconstruction86412 OrderedFinite86412 APGridTools86412
open APTemplatePrefix86412 APTemplateSets86412 APTemplateArithmetic86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem no_double_hole {S : Finset ℤ} {a d : ℤ} {n q : ℕ}
    (hd : 0<d) (hq : 3≤q) (hqn : q<n) (hcard : S.card=n)
    (hform : S=Template a d n 1 1)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) : False := by
  let D := n/q
  have hf := quotient_frame hq hqn
  have hD : 1≤D := hf.1
  have hn : 4≤n := by omega
  have hrem : n%q+q*D=n := Nat.mod_add_div n q
  by_cases hr : n%q=0
  · have hD2 : 2≤D := by
      by_contra hh
      have hD1 : D=1 := by omega
      rw [hr, Nat.zero_add, hD1, Nat.mul_one] at hrem
      omega
    let A := TemplatePrefix a d 1 D
    have hA : IsInitial S A := by
      rw [hform]
      exact prefix_initial hd (by omega) (by omega)
    have hAc : A.card=D := prefix_card hd (by omega)
    have hbA : BalancedTail S.card q A.card := by
      rw [hcard, hAc]
      exact Or.inl rfl
    have hx : a∈A := Finset.mem_insert_self a _
    have hy : a+(D : ℤ)*d∈A := by
      have hh := prefix_last (a := a) (d := d) (l := 1) hD2
      have heD : D-1+1=D := by omega
      simpa only [heD] using hh
    have hxy : a<a+(D : ℤ)*d := by
      have hp := mul_pos (by omega : 0<(D : ℤ)) hd
      omega
    have hz := initial_pair_end (by omega : 2≤q) hA hbA heq hx hy hxy
    have hprod : q*D=n := by omega
    have hze : a+(q : ℤ)*((a+(D : ℤ)*d)-a)=a+(n : ℤ)*d := by
      rw [← hprod]
      push_cast
      ring
    rw [hze, hform] at hz
    exact double_missing hd hn hz
  · let t := n-D
    let k := t-(D+1)
    let T := TemplatePrefix a d 1 t
    let A := TemplatePrefix a d 1 k
    have ht : 3≤t := hf.2.2.1
    have hk : 1≤k := hf.2.2.2.1
    have htn : t≤n-1 := hf.2.2.2.2
    have hkt : k≤t := by dsimp only [k]; omega
    have hk1 : k+1=t-D := by dsimp only [k]; omega
    have hT : IsInitial S T := by
      rw [hform]
      exact prefix_initial hd (by omega) htn
    have hA : IsInitial T A := prefix_nested hd (by omega : 2≤n) hkt htn
    have hTc : T.card=t := prefix_card hd (by omega)
    have hAc : A.card=k := prefix_card hd hk
    have hCT := Finset.card_sdiff_add_card_eq_card hT.1
    have hBA := Finset.card_sdiff_add_card_eq_card hA.1
    have hCc : (S\T).card=D := by dsimp only [t] at hTc; omega
    have hBc : (T\A).card=D+1 := by dsimp only [k] at hAc; omega
    have hbC : BalancedTail S.card q (S\T).card := by
      rw [hcard, hCc]
      exact Or.inl rfl
    have hsplit := split_saturation (by omega : 2≤q) hT hbC heq
    have hoptT := hsplit.1
    have hbB : BalancedTail T.card (q-1) (T\A).card := by
      rw [hTc, hBc]
      exact nested_balanced_tail hq hqn hr
    let x := a+((t-D : ℕ) : ℤ)*d
    let y := a+(t : ℤ)*d
    have hxCoord : 1+1+(k-1)=t-D := by omega
    have hyCoord : 1+1+(t-2)=t := by omega
    have hxT : x∈T := by
      have hh := (middle_mem_prefix (a := a) (d := d) (l := 1) (m := t)
        (i := k-1) hd).2 (by dsimp only [k] at *; omega)
      simpa only [hxCoord] using hh
    have hxA : x∉A := by
      intro hh
      have hbad := (middle_mem_prefix (a := a) (d := d) (l := 1) (m := k)
        (i := k-1) hd).mp (by simpa only [hxCoord] using hh)
      omega
    have hyT : y∈T := by
      have hh := prefix_last (a := a) (d := d) (l := 1) (by omega : 2≤t)
      have he : t-1+1=t := by omega
      simpa only [he] using hh
    have hyA : y∉A := by
      intro hh
      have hbad := (middle_mem_prefix (a := a) (d := d) (l := 1) (m := k)
        (i := t-2) hd).mp (by simpa only [hyCoord] using hh)
      dsimp only [k] at *
      omega
    have hxy : x<y := by
      have hidx : ((t-D : ℕ) : ℤ)<(t : ℤ) := by omega
      have hp := mul_lt_mul_of_pos_right hidx hd
      dsimp only [x, y]
      linarith only [hp]
    have hp : (x,y)∈Codes T (q-1) :=
      (split_saturation (by omega : 2≤q-1) hA hbB hoptT).2.1 (x,y)
        (mem_orderedPairs.mpr ⟨Finset.mem_sdiff.mpr ⟨hxT, hxA⟩,
          Finset.mem_sdiff.mpr ⟨hyT, hyA⟩, hxy⟩)
    have hs := hsplit.2.2 (x,y) hp
    have hz := (mem_codes.mp hs).2.2.2 0 (by omega)
    simp only [Point, Suffix, Nat.cast_zero, zero_mul, sub_zero] at hz
    have hindex : 2*(t : ℤ)-((t-D : ℕ) : ℤ)=(n : ℤ) := by
      dsimp only [t]
      omega
    have hze : 2*y-x=a+(n : ℤ)*d := by
      dsimp only [x, y]
      have hh := congrArg (fun z : ℤ => z*d) hindex
      nlinarith only [hh]
    rw [hze, hform] at hz
    exact double_missing hd hn hz

#print axioms no_double_hole
end
end JSP233.APDoubleHole86412
