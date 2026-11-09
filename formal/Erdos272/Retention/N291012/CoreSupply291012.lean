module

public import Erdos272.Core.CoreSeven52
public import Erdos272.Arithmetic.PrimorialRatio39

@[expose] public section

namespace JSP233.CoreSupply291012
open StarCompletion APGeometry
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem totient_ratio {N m : ℕ} (hN : N < 2^50) (hm : m ≤ N) :
    10*m ≤ 69*Nat.totient m := by
  have hr := (PrimorialRatio39.uniform_q49 m (hm.trans_lt hN)).2.1 m le_rfl
  have hp : (0 : ℝ) ≤ Nat.totient m := Nat.cast_nonneg _
  have hh : 10*(m : ℝ) ≤ 69*Nat.totient m := by nlinarith only [hr, hp]
  exact_mod_cast hh

theorem coprime_middle {m a h : ℕ} (hr : 10*m ≤ 69*Nat.totient m)
    (hlarge : 69*(2*a+(m-2*h)) < 10*m) :
    ∃ j, a ≤ j ∧ j ≤ h ∧ Nat.Coprime j m := by
  by_contra hh
  have hphi := CoprimeMiddle36.totient_le_of_no_coprime_middle (m := m) (a := a) (h := h)
    (fun j hja hjh hcop => hh ⟨j, hja, hjh, hcop⟩)
  have hmul := Nat.mul_le_mul_left 69 hphi
  omega

theorem long_core_supply (N c L R d u : ℕ)
    (hN : N < 2^50) (hcL : c < L) (hLR : L ≤ R) (_hRN : R ≤ N) (hd : 0 < d)
    (hdt : d ≤ L+N-R) (hcore : 197*L+79*(L+N-R) ≤ 10*N)
    (hu : (R-c)/d < u) (huN : u ≤ N/d) :
    ((L-c)/d+1)+(c-1)/d+1 ≤ Nat.totient u := by
  let t := L+N-R
  let f := ((L-c)/d+1)+(c-1)/d+1
  have hsum : N+L = t+R := by dsimp only [t]; omega
  have hRc : R-c+c = R := by omega
  have hfloor1 := Nat.mul_div_le (L-c) d
  have hfloor2 := Nat.mul_div_le (c-1) d
  have hsubtract : (L-c)+(c-1) ≤ L := by omega
  have hdf : d*f ≤ L+2*d := by
    dsimp only [f]
    nlinarith only [hfloor1, hfloor2, hsubtract]
  have hratio := totient_ratio hN (huN.trans (Nat.div_le_self N d))
  have hdu : R-c < u*d := (Nat.div_lt_iff_lt_mul hd).mp hu
  by_contra hh
  have hphi : Nat.totient u+1 ≤ f := by dsimp only [f]; omega
  have hphid := Nat.mul_le_mul_left d hphi
  have hratiod := Nat.mul_le_mul_left d hratio
  change 197*L+79*t ≤ 10*N at hcore
  change d ≤ t at hdt
  nlinarith only [hdf, hphid, hratiod, hdu, hRc, hsum, hcore, hdt, hcL]

theorem normalized_cutoff (N c L R d : ℕ)
    (hcL : c < L) (hLR : L ≤ R) (_hRN : R ≤ N) (hd : 0 < d)
    (hdt : d ≤ L+N-R) (hcore : 197*L+79*(L+N-R) ≤ 10*N) :
    2 ≤ (R-c)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  omega

theorem prefix_core {N c L R d h m : ℕ}
    (hN : N < 2^50) (hcL : c < L) (_hLR : L ≤ R) (hRN : R ≤ N)
    (hd : 0 < d) (hdL : d ≤ L) (hthin : 197*L+79*(L+N-R) ≤ 10*N)
    (hmR : R < c+m*d) (hmN : c+m*d ≤ N) (hhalf : R+c < 2*(c+h*d)) :
    ∃ j, L ≤ c+j*d ∧ j ≤ h ∧ Nat.Coprime j m := by
  let t := L+N-R
  let a := (L-c)/d+1
  let q := 2*a+(m-2*h)
  have hsum : N+L = t+R := by dsimp only [t]; omega
  have hLc : L-c+c = L := Nat.sub_add_cancel hcL.le
  have hNR := Nat.sub_add_cancel hRN
  have hmN' : m ≤ N := by
    have hh := Nat.le_mul_of_pos_right m hd
    omega
  have ha : d*a ≤ L-c+d := by
    have hh := Nat.mul_div_le (L-c) d
    dsimp only [a]
    nlinarith only [hh]
  have hmid : d*(m-2*h) ≤ N-R := by
    by_cases hh : 2*h ≤ m
    · have he := congrArg (fun z => d*z) (Nat.sub_add_cancel hh)
      have hNR := Nat.sub_add_cancel hRN
      nlinarith only [he, hNR, hmN, hhalf]
    · have he : m-2*h = 0 := by omega
      simp only [he, mul_zero, Nat.zero_le]
  have hq : d*q+2*c ≤ 3*L+t := by
    dsimp only [q]
    nlinarith only [ha, hmid, hdL, hLc, hNR, hsum]
  have hratio := totient_ratio hN hmN'
  have hlarge : 69*q < 10*m := by
    by_contra hh
    have hscaled := Nat.mul_le_mul_left d (show 10*m ≤ 69*q by omega)
    change 197*L+79*t ≤ 10*N at hthin
    nlinarith only [hq, hscaled, hmR, hsum, hthin]
  obtain ⟨j, haj, hjh, hcop⟩ := coprime_middle hratio hlarge
  have hj : (L-c)/d < j := by change (L-c)/d+1 ≤ j at haj; omega
  have hjd : L-c < j*d := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j, by omega, hjh, hcop⟩

#print axioms totient_ratio
#print axioms coprime_middle
#print axioms long_core_supply
#print axioms normalized_cutoff
#print axioms prefix_core
end JSP233.CoreSupply291012
