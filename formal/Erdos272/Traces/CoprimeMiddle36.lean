module

public import Erdos272.Core.LongCore34

@[expose] public section

/-! Finite middle coprime indices for the actual exterior-prefix geometry.
The physical condition is 6*t*J <= N, with no totient-supply premise. -/
namespace JSP233.CoprimeMiddle36
open scoped Classical BigOperators
noncomputable section

theorem totient_le_of_no_coprime_middle {m a h : ℕ}
    (hgap : ∀ j, a≤j → j≤h → ¬Nat.Coprime j m) :
    Nat.totient m≤2*a+(m-2*h) := by
  let D := (Finset.Icc 1 m).filter (fun j => Nat.Coprime m j)
  let A := Finset.range a
  let B := A.image (fun j => m-j)
  let C := Finset.Ioo h (m-h)
  have hs : D⊆A∪B∪C := by
    intro j hj
    obtain ⟨hjI,hcop⟩ := Finset.mem_filter.mp hj
    have hjm := (Finset.mem_Icc.mp hjI).2
    by_cases hja : j<a
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_range.mpr hja))
    by_cases hjh : j≤h
    · exact False.elim (hgap j (by omega) hjh hcop.symm)
    by_cases hmja : m-j<a
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨m-j,Finset.mem_range.mpr hmja,by omega⟩))
    by_cases hmjh : m-j≤h
    · have hh := (Nat.coprime_self_sub_left hjm).mpr hcop.symm
      exact False.elim (hgap (m-j) (by omega) hmjh hh)
    · exact Finset.mem_union_right _ (Finset.mem_Ioo.mpr ⟨by omega,by omega⟩)
  have hc : C.card≤m-2*h := by simp only [C,Nat.card_Ioo]; omega
  have hb : B.card≤a := by
    simpa only [A,B,Finset.card_range] using Finset.card_image_le (s:=A) (f:=fun j => m-j)
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A∪B) C
  have h3 := Finset.card_le_card hs
  have hA : A.card=a := Finset.card_range a
  have hD : D.card=Nat.totient m := by
    have he : Finset.Icc 1 m=Finset.Ico 1 (1+m) := by
      ext j
      simp only [Finset.mem_Icc,Finset.mem_Ico]
      omega
    dsimp [D]
    rw [he]
    exact Nat.filter_coprime_Ico_eq_totient m 1
  omega

theorem exists_coprime_middle_of_supply {m a h r : ℕ}
    (hr : m≤r*Nat.totient m) (hlarge : (2*a+(m-2*h))*r<m) :
    ∃ j, a≤j ∧ j≤h ∧ Nat.Coprime j m := by
  by_contra hh
  have hp := totient_le_of_no_coprime_middle (m:=m) (a:=a) (h:=h)
    (fun j hja hjh hc => hh ⟨j,hja,hjh,hc⟩)
  have hm := Nat.mul_le_mul_left r hp
  nlinarith

theorem exists_coprime_middle {m a h : ℕ}
    (hlarge : (2*a+(m-2*h))*(Nat.log 2 m+1)<m) :
    ∃ j, a≤j ∧ j≤h ∧ Nat.Coprime j m :=
  exists_coprime_middle_of_supply (LongCore34.actual_totient_log_bound m) hlarge

theorem exists_coprime_middle_omega {m a h : ℕ}
    (hlarge : (2*a+(m-2*h))*(m.primeFactors.card+1)<m) :
    ∃ j, a≤j ∧ j≤h ∧ Nat.Coprime j m :=
  exists_coprime_middle_of_supply (LongCore34.le_prime_factor_count_mul_totient m) hlarge

theorem thin_core_wide (N c L R : ℕ) (hcL : c<L) (_hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) : 2*L≤R+c := by
  have hsum : N+L=(L+N-R)+R := by omega
  have hsmall : 6*(L+N-R)≤N := by
    exact (Nat.le_mul_of_pos_right _ (by omega : 0<Nat.log 2 N+1)).trans hthin
  omega

theorem exists_coprime_in_prefix_core {N c L R d h m : ℕ}
    (hcL : c<L) (_hLR : L≤R) (hRN : R≤N) (hd : 0<d) (hdL : d≤L)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hmR : R<c+m*d) (hmN : c+m*d≤N)
    (hhalf : R+c<2*(c+h*d)) :
    ∃ j, L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m := by
  let t := L+N-R
  let a := (L-c)/d+1
  let q := 2*a+(m-2*h)
  let J := Nat.log 2 N+1
  have hLt : L≤t := by dsimp [t]; omega
  have hct : c≤t := by omega
  have hsum : N+L=t+R := by dsimp [t]; omega
  have hNR : N-R+R=N := Nat.sub_add_cancel hRN
  have hLc : L-c+c=L := Nat.sub_add_cancel hcL.le
  have hmN' : m≤N := by
    have hh := Nat.le_mul_of_pos_right m hd
    omega
  have ha : d*a≤L-c+d := by
    have hh := Nat.mul_div_le (L-c) d
    dsimp [a]
    nlinarith
  have hmid : d*(m-2*h)≤N-R := by
    by_cases hh : 2*h≤m
    · have he := Nat.sub_add_cancel hh
      nlinarith
    · have he : m-2*h=0 := by omega
      simp only [he,mul_zero,Nat.zero_le]
  have hq : d*q≤4*t := by dsimp [q]; nlinarith
  have hJ : 1≤J := by dsimp [J]; omega
  have hlog : Nat.log 2 m+1≤J := Nat.add_le_add_right (Nat.log_mono_right hmN') 1
  have hlarge : q*(Nat.log 2 m+1)<m := by
    by_contra hh
    have hm : m≤q*J := (by omega : m≤q*(Nat.log 2 m+1)).trans
      (Nat.mul_le_mul_left q hlog)
    have hbound : d*m≤4*t*J := by
      calc
        d*m≤d*(q*J) := Nat.mul_le_mul_left d hm
        _=(d*q)*J := by ring
        _≤(4*t)*J := Nat.mul_le_mul_right J hq
    have htJ : t≤t*J := by nlinarith
    change 6*t*J≤N at hthin
    nlinarith
  obtain ⟨j,haj,hjh,hcop⟩ := exists_coprime_middle hlarge
  have hj : (L-c)/d<j := by change (L-c)/d+1≤j at haj; omega
  have hjd : L-c<j*d := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j,by omega,hjh,hcop⟩

theorem exists_coprime_in_prefix_core256 {N c L R d h m : ℕ}
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d) (hdL : d≤L)
    (hthin : 256*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hmR : R<c+m*d) (hmN : c+m*d≤N)
    (hhalf : R+c<2*(c+h*d)) :
    ∃ j, L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m := by
  apply exists_coprime_in_prefix_core hcL hLR hRN hd hdL _ hmR hmN hhalf
  nlinarith

#print axioms totient_le_of_no_coprime_middle
#print axioms exists_coprime_middle_of_supply
#print axioms exists_coprime_middle
#print axioms exists_coprime_middle_omega
#print axioms thin_core_wide
#print axioms exists_coprime_in_prefix_core
#print axioms exists_coprime_in_prefix_core256
end
end JSP233.CoprimeMiddle36
