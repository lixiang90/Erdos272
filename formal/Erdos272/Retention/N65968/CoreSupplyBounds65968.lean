module

public import Erdos272.Retention.N142758.CoreSupplyRatios142758

@[expose] public section

namespace JSP233.ActualSupply65968
open PrimorialRatio39
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Gates (N L R : ℕ) : Prop where
  prefix_low : 105*(809*L+1193*(L+N-R))≤19159*N
  prefix_mid : 11*L+19*(L+N-R)≤3*N
  prefix_high : 8*L+4*(L+N-R)≤N
  long_low : 210*(1001*L+192*(L+N-R))≤39319*N
  long_mid : 2*(15*L+4*(L+N-R))≤7*N
  long_high : 3*L+4*(L+N-R)≤N
  wide : L+(L+N-R)≤N
  cutoff : 3*(L+N-R)≤N

-- Consumers need the actual supply functions, without a lower bound on L/N.
structure Core (N L R : ℕ) : Prop where
  wide : L+(L+N-R)≤N
  cutoff : 3*(L+N-R)≤N
  long : ∀ c d u : ℕ, c<L → L≤R → R≤N → 0<d → d≤L+N-R →
    (R-c)/d<u → u≤N/d → ((L-c)/d+1)+(c-1)/d+1≤Nat.totient u
  prefix_supply : ∀ c d h m : ℕ, c<L → L≤R → R≤N → 0<d → d≤L →
    R<c+m*d → c+m*d≤N → R+c<2*(c+h*d) →
    ∃ j, L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m

theorem tiny_totient_ratio {m : ℕ} (hm : m<30) : m≤3*Nat.totient m := by
  have hp : Primorial 3=30 := by
    norm_num [Primorial,Finset.prod_range_succ,prime_at_seed_nat,SeedPrime]
  have hr : Ratio 2=(3 : ℝ) := by
    norm_num [Ratio,Finset.prod_range_succ,prime_at_seed_nat,SeedPrime]
  have hh := (uniform_omega_and_ratio m 2 (by simpa only [hp] using hm)).2 m le_rfl
  rw [hr] at hh
  exact_mod_cast hh

theorem actual_long {N c L R d u : ℕ}
    (hN : N<510510) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hd : 0<d) (hdt : d≤L+N-R) (hg : Gates N L R)
    (hu : (R-c)/d<u) (huN : u≤N/d) :
    ((L-c)/d+1)+(c-1)/d+1≤Nat.totient u := by
  let t:=L+N-R
  let f:=((L-c)/d+1)+(c-1)/d+1
  have hsum : N+L=t+R := by dsimp only [t];omega
  have hRc : R-c+c=R := by omega
  have hfloor1:=Nat.mul_div_le (L-c) d
  have hfloor2:=Nat.mul_div_le (c-1) d
  have hsubtract : (L-c)+(c-1)≤L := by omega
  have hdf : d*f≤L+2*d := by
    dsimp only [f]
    nlinarith only [hfloor1,hfloor2,hsubtract]
  have hdu : R-c<u*d := (Nat.div_lt_iff_lt_mul hd).mp hu
  have huNd : u*d≤N := (Nat.le_div_iff_mul_le hd).mp huN
  by_contra hh
  have hphi : Nat.totient u+1≤f := by dsimp only [f];omega
  have hphid:=Nat.mul_le_mul_left d hphi
  by_cases h210 : 210*d≤N
  · have hr:=Nat.mul_le_mul_left d (CoreSupplyFinite3043.totient_ratio hN
      (huN.trans (Nat.div_le_self N d)))
    have hgate : 210*(1001*L+192*t)≤39319*N := hg.long_low
    nlinarith only [hdf,hphid,hr,hdu,hRc,hsum,hgate,h210,hcL]
  by_cases h30 : 30*d≤N
  · have hu210 : u<210 := by nlinarith only [huNd,h210,hd]
    have hr:=Nat.mul_le_mul_left d (CoreSupply142758.small_totient_ratio hu210)
    have hgate : 2*(15*L+4*t)≤7*N := hg.long_mid
    nlinarith only [hdf,hphid,hr,hdu,hRc,hsum,hgate,h30,hcL]
  · have hu30 : u<30 := by nlinarith only [huNd,h30,hd]
    have hr:=Nat.mul_le_mul_left d (tiny_totient_ratio hu30)
    have hgate : 3*L+4*t≤N := hg.long_high
    change d≤t at hdt
    nlinarith only [hdf,hphid,hr,hdu,hRc,hsum,hgate,hdt,hcL]

theorem actual_prefix {N c L R d h m : ℕ}
    (hN : N<510510) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hd : 0<d) (hdL : d≤L) (hg : Gates N L R)
    (hmR : R<c+m*d) (hmN : c+m*d≤N) (hhalf : R+c<2*(c+h*d)) :
    ∃ j, L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m := by
  let t:=L+N-R
  let a:=(L-c)/d+1
  let q:=2*a+(m-2*h)
  have hsum : N+L=t+R := by dsimp only [t];omega
  have hLc : L-c+c=L := Nat.sub_add_cancel hcL.le
  have hNR:=Nat.sub_add_cancel hRN
  have hmN' : m≤N := by have hh:=Nat.le_mul_of_pos_right m hd;omega
  have hmNd : m*d≤N := by omega
  have ha : d*a≤L-c+d := by
    have hh:=Nat.mul_div_le (L-c) d
    dsimp only [a]
    nlinarith only [hh]
  have hmid : d*(m-2*h)≤N-R := by
    by_cases hh : 2*h≤m
    · have he:=congrArg (fun z=>d*z) (Nat.sub_add_cancel hh)
      nlinarith only [he,hNR,hmN,hhalf]
    · have he : m-2*h=0 := by omega
      simp only [he,mul_zero,Nat.zero_le]
  have hq : d*q+2*c≤L+2*d+t := by
    dsimp only [q]
    nlinarith only [ha,hmid,hLc,hNR,hsum]
  have hphi : q<Nat.totient m := by
    by_contra hh
    have hp : Nat.totient m≤q := by omega
    have hpd:=Nat.mul_le_mul_left d hp
    by_cases h210 : 210*d≤N
    · have hr:=Nat.mul_le_mul_left d (CoreSupplyFinite3043.totient_ratio hN hmN')
      have hgate : 105*(809*L+1193*t)≤19159*N := hg.prefix_low
      nlinarith only [hpd,hr,hq,hmR,hsum,hgate,h210]
    by_cases h30 : 30*d≤N
    · have hm210 : m<210 := by nlinarith only [hmNd,h210,hd]
      have hr:=Nat.mul_le_mul_left d (CoreSupply142758.small_totient_ratio hm210)
      have hgate : 11*L+19*t≤3*N := hg.prefix_mid
      nlinarith only [hpd,hr,hq,hmR,hsum,hgate,h30]
    · have hm30 : m<30 := by nlinarith only [hmNd,h30,hd]
      have hr:=Nat.mul_le_mul_left d (tiny_totient_ratio hm30)
      have hgate : 8*L+4*t≤N := hg.prefix_high
      nlinarith only [hpd,hr,hq,hmR,hsum,hgate,hdL]
  have hmiddle : ∃ j, a≤j ∧ j≤h ∧ Nat.Coprime j m := by
    by_contra hh
    have hb:=CoprimeMiddle36.totient_le_of_no_coprime_middle
      (m:=m) (a:=a) (h:=h) (fun j hja hjh hcop=>hh ⟨j,hja,hjh,hcop⟩)
    change Nat.totient m≤q at hb
    omega
  obtain ⟨j,haj,hjh,hcop⟩:=hmiddle
  have hj : (L-c)/d<j := by change (L-c)/d+1≤j at haj;omega
  have hjd : L-c<j*d := (Nat.div_lt_iff_lt_mul hd).mp hj
  exact ⟨j,by omega,hjh,hcop⟩

theorem of_gates {N L R : ℕ} (hN : N<510510) (hg : Gates N L R) : Core N L R := by
  refine ⟨hg.wide,hg.cutoff,?_,?_⟩
  · intro c d u hcL hLR hRN hd hdt hu huN
    exact actual_long hN hcL hLR hRN hd hdt hg hu huN
  · intro c d h m hcL hLR hRN hd hdL hmR hmN hhalf
    exact actual_prefix hN hcL hLR hRN hd hdL hg hmR hmN hhalf

theorem wide {N c L R : ℕ} (hLR : L≤R) (hRN : R≤N)
    (hcore : Core N L R) : 2*L≤R+c := by
  have hw:=hcore.wide
  omega

theorem normalized_cutoff (N c L R d : ℕ)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R) (hcore : Core N L R) : 2≤(R-c)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have hw:=hcore.cutoff
  omega

theorem long_core_supply (N c L R d u : ℕ)
    (hN : N<120120) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R) (hcore : Core N L R) (hu : (R-c)/d<u) (huN : u≤N/d) :
    ((L-c)/d+1)+(c-1)/d+1≤Nat.totient u := hcore.long c d u hcL hLR hRN hd hdt hu huN

theorem prefix_core {N c L R d h m : ℕ}
    (hN : N<120120) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdL : d≤L) (hcore : Core N L R)
    (hmR : R<c+m*d) (hmN : c+m*d≤N) (hhalf : R+c<2*(c+h*d)) :
    ∃ j, L≤c+j*d ∧ j≤h ∧ Nat.Coprime j m := hcore.prefix_supply c d h m hcL hLR hRN hd hdL hmR hmN hhalf

#print axioms tiny_totient_ratio
#print axioms actual_long
#print axioms actual_prefix
#print axioms of_gates
#print axioms wide
#print axioms normalized_cutoff
#print axioms long_core_supply
#print axioms prefix_core
end JSP233.ActualSupply65968
