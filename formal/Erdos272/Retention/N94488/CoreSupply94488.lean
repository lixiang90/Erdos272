module

public import Erdos272.Retention.N142758.CoreSupply142758

@[expose] public section

namespace JSP233.CoreSupply94488
open PrimorialRatio39
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Core (N L R : ℕ) : Prop :=
  19*L ≤ N ∧ 32*(L+N-R) ≤ 3*N ∧ N ≤ 100*L ∧ 160 ≤ N

theorem medium_totient_ratio {m : ℕ} (hm : m < 30030) :
    16*m ≤ 77*Nat.totient m := by
  have hcut : m < Primorial (5+1) := by
    norm_num [Primorial, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime]
    exact hm
  have hr := (uniform_omega_and_ratio m 5 hcut).2 m le_rfl
  norm_num [Ratio, Finset.prod_range_succ, prime_at_seed_nat, SeedPrime] at hr
  have hn : 16*(m : ℝ) ≤ 77*Nat.totient m := by nlinarith only [hr]
  exact_mod_cast hn

theorem wide {N c L R : ℕ} (hLR : L ≤ R) (hRN : R ≤ N)
    (hcore : Core N L R) : 2*L ≤ R+c := by
  rcases hcore with ⟨hL, hw, _, _⟩
  omega

theorem thin_of_small {N L R : ℕ} (hrect : 19*L ≤ N ∧ 32*(L+N-R) ≤ 3*N)
    (hsmall : 100*L < N) : 2811*L+1193*(L+N-R) ≤ 192*N := by
  omega

theorem long_core_supply (N c L R d u : ℕ)
    (hN : N < 120120) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d)
    (hdt : d ≤ L+N-R) (hcore : Core N L R)
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
  have hdu : R-c < u*d := (Nat.div_lt_iff_lt_mul hd).mp hu
  rcases hcore with ⟨hL, ht, hlarge, hlo⟩
  change 32*t ≤ 3*N at ht
  change d ≤ t at hdt
  by_contra hh
  have hphi : Nat.totient u+1 ≤ f := by dsimp only [f]; omega
  have hphid := Nat.mul_le_mul_left d hphi
  by_cases hdL : 2*d ≤ L
  · have hratio := CoreSupplyFinite3043.totient_ratio (by omega : N < 510510)
      (huN.trans (Nat.div_le_self N d))
    have hratiod := Nat.mul_le_mul_left d hratio
    nlinarith only [hdf, hphid, hratiod, hdu, hRc, hsum, hL, ht, hdL, hcL]
  · have huNd : u*d ≤ N := (Nat.le_div_iff_mul_le hd).mp huN
    have hu210 : u < 210 := by nlinarith only [huNd, hlarge, hdL, hd]
    have hratiod := Nat.mul_le_mul_left d (CoreSupply142758.small_totient_ratio hu210)
    nlinarith only [hdf, hphid, hratiod, hdu, hRc, hsum, hL, ht, hdt, hcL]

theorem normalized_cutoff (N c L R d : ℕ)
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d)
    (hdt : d ≤ L+N-R) (hcore : Core N L R) : 2 ≤ (R-c)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  rcases hcore with ⟨hL, hw, _, _⟩
  omega

theorem prefix_core {N c L R d h m : ℕ}
    (hN : N < 120120) (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hd : 0 < d) (hdL : d ≤ L) (hcore : Core N L R)
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
      nlinarith only [he, hNR, hmN, hhalf]
    · have he : m-2*h = 0 := by omega
      simp only [he, mul_zero, Nat.zero_le]
  have hq : d*q+2*c ≤ L+2*d+t := by
    dsimp only [q]
    nlinarith only [ha, hmid, hLc, hNR, hsum]
  rcases hcore with ⟨hL, ht, hlarge, hlo⟩
  change 32*t ≤ 3*N at ht
  have hphi : q < Nat.totient m := by
    by_cases hdtiny : d ≤ 3
    · have hratio := CoreSupplyFinite3043.totient_ratio (by omega : N < 510510) hmN'
      have hgate : 809*L+1193*t+6006 < 192*N := by
        nlinarith only [hL, ht, hlo]
      have hless : 1001*q < 192*m := by
        by_contra hh
        have hscaled := Nat.mul_le_mul_left d (show 192*m ≤ 1001*q by omega)
        nlinarith only [hq, hscaled, hmR, hsum, hgate, hdtiny]
      omega
    · by_cases hdhalf : 2*d ≤ L
      · have hm30030 : m < 30030 := by
          have hd4 : 4 ≤ d := by omega
          nlinarith only [hmN, hN, hd4]
        have hratio := medium_totient_ratio hm30030
        have hgate : 138*L+93*t ≤ 16*N := by omega
        have hless : 77*q < 16*m := by
          by_contra hh
          have hscaled := Nat.mul_le_mul_left d (show 16*m ≤ 77*q by omega)
          nlinarith only [hq, hscaled, hmR, hsum, hgate, hdhalf]
        omega
      · have hmNd : m*d ≤ N := by omega
        have hm210 : m < 210 := by nlinarith only [hmNd, hlarge, hdhalf, hd]
        have hratio := CoreSupply142758.small_totient_ratio hm210
        have hgate : 41*L+19*t ≤ 4*N := by omega
        have hless : 15*q < 4*m := by
          by_contra hh
          have hscaled := Nat.mul_le_mul_left d (show 4*m ≤ 15*q by omega)
          nlinarith only [hq, hscaled, hmR, hsum, hgate, hdL]
        omega
  have hmiddle : ∃ j, a ≤ j ∧ j ≤ h ∧ Nat.Coprime j m := by
    by_contra hh
    have hbound := CoprimeMiddle36.totient_le_of_no_coprime_middle
      (m := m) (a := a) (h := h) (fun j hja hjh hcop => hh ⟨j, hja, hjh, hcop⟩)
    change Nat.totient m ≤ q at hbound
    omega
  obtain ⟨j, haj, hjh, hcop⟩ := hmiddle
  have hj : (L-c)/d < j := by change (L-c)/d+1 ≤ j at haj; omega
  have hjd : L-c < j*d := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j, by omega, hjh, hcop⟩

#print axioms medium_totient_ratio
#print axioms wide
#print axioms thin_of_small
#print axioms long_core_supply
#print axioms normalized_cutoff
#print axioms prefix_core
end JSP233.CoreSupply94488
