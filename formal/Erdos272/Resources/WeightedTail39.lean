import Erdos272.Resources.WeightedFar38

/-! Finite ordinary-kernel payment for the exact linear dyadic tail.
The terminal budget is uniform in the number of actual size bands. -/
namespace JSP233.WeightedTail39
open StarCompletion WeightedFar38
open scoped Classical BigOperators
noncomputable section

theorem linear_dyadic_identity (b : ℝ) (n : ℕ) :
    (∑ j∈Finset.range n,(b+j)*(1/2:ℝ)^j)+
      (2*(b+n)+2)*(1/2:ℝ)^n=2*b+2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ,pow_succ,Nat.cast_add,Nat.cast_one]
    nlinarith only [ih]

theorem linear_dyadic_bound (a b : ℝ) (n : ℕ) (ha : 0≤a) (hb : 0≤b) :
    (∑ j∈Finset.range n,a*(b+j)*(1/2:ℝ)^j)≤a*(2*b+2) := by
  have hi := linear_dyadic_identity b n
  have hp : 0≤(2*(b+n)+2)*(1/2:ℝ)^n := by positivity
  have hs : (∑ j∈Finset.range n,(b+j)*(1/2:ℝ)^j)≤2*b+2 := by linarith
  calc
    (∑ j∈Finset.range n,a*(b+j)*(1/2:ℝ)^j)=
        a*(∑ j∈Finset.range n,(b+j)*(1/2:ℝ)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤a*(2*b+2) := mul_le_mul_of_nonneg_left hs ha

theorem finite_weighted_tail_bound (C : ℕ→ℝ) (n M : ℕ) (a b : ℝ)
    (hC : ∀ j,0≤C j) (ha : 0≤a) (hb : 0≤b)
    (htail : ∀ j,M≤j → C j≤a*(b+j)) :
    (∑ j∈Finset.range n,C j*(1/2:ℝ)^j)≤
      (∑ j∈Finset.range M,C j*(1/2:ℝ)^j)+a*(2*(b+M)+2)*(1/2:ℝ)^M := by
  by_cases hnm : n≤M
  · have hs : (∑ j∈Finset.range n,C j*(1/2:ℝ)^j)≤
        (∑ j∈Finset.range M,C j*(1/2:ℝ)^j) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm)
      intro j _ _
      exact mul_nonneg (hC j) (pow_nonneg (by norm_num) _)
    have hp : 0≤a*(2*(b+M)+2)*(1/2:ℝ)^M := by positivity
    linarith
  · have hMn : M≤n := by omega
    have hn : n=M+(n-M) := by omega
    have hs : (∑ j∈Finset.range (n-M),C (M+j)*(1/2:ℝ)^(M+j))≤
        (1/2:ℝ)^M*(∑ j∈Finset.range (n-M),a*((b+M)+j)*(1/2:ℝ)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hh := mul_le_mul_of_nonneg_right (htail (M+j) (by omega))
        (pow_nonneg (by norm_num : (0:ℝ)≤1/2) (M+j))
      simp only [Nat.cast_add,pow_add] at hh
      rw [pow_add]
      nlinarith only [hh]
    have hbM : 0≤b+(M:ℝ) := by positivity
    have hl := mul_le_mul_of_nonneg_left (linear_dyadic_bound a (b+M) (n-M) ha hbM)
      (pow_nonneg (by norm_num : (0:ℝ)≤1/2) M)
    rw [hn,Finset.sum_range_add]
    nlinarith only [hs,hl]

theorem max_linear_tail (a b L : ℝ) (M j : ℕ)
    (ha : 0≤a) (hM : L≤a*(b+M)) (hj : M≤j) :
    max (a*(b+j)) L≤a*(b+j) := by
  have hMj : (M:ℝ)≤j := by exact_mod_cast hj
  apply max_le le_rfl
  nlinarith

def TailSlope (ell v b : ℕ) : ℝ :=
  ((b+1:ℕ):ℝ)/((2*(b-(ell+3)*(v+1)):ℕ):ℝ)

def BandB (B0 B1 b j : ℕ) : ℕ :=
  if j=0 then B0 else if j=1 then B1 else 2^((j-2)/2)*b

theorem linear_dyadic_growth (ell k : ℕ) : ell+2+k≤2^(k/2)*(ell+3) := by
  have hg : ∀ h : ℕ,ell+3+2*h≤2^h*(ell+3) := by
    intro h
    induction h with
    | zero => simp
    | succ h ih =>
      have hp : 1≤(2:ℕ)^h := by
        have hh : 0<(2:ℕ)^h := by positivity
        omega
      rw [pow_succ]
      nlinarith
  have hmod := Nat.mod_add_div k 2
  have hlt := Nat.mod_lt k (by decide : 0<2)
  exact (show ell+2+k≤ell+3+2*(k/2) by omega).trans (hg (k/2))

theorem tail_band_conditions (K ell v b j : ℕ) (hj : 2≤j)
    (hbase : (ell+3)*(v+1)<b) (hsquare : b^2≤4*K) (hfinite : K≤2^ell) :
    (ell+j)*(v+1)<2^((j-2)/2)*b ∧
      (2^((j-2)/2)*b)^2≤2^j*K ∧ 2^j*K≤2^(ell+j) := by
  let k := j-2
  let s := (2:ℕ)^(k/2)
  have hs : 0<s := by dsimp [s]; positivity
  have hjk : j=2+k := by dsimp [k]; omega
  have hg : ell+j≤s*(ell+3) := by
    simpa only [hjk,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,s] using linear_dyadic_growth ell k
  have hm := Nat.mul_le_mul_right (v+1) hg
  have hb := Nat.mul_lt_mul_of_pos_left hbase hs
  have hshort : (ell+j)*(v+1)<s*b := by nlinarith only [hm,hb]
  have he : 2*(k/2)≤k := Nat.mul_div_le k 2
  have hp := Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) he
  have hs2 : s^2≤2^k := by
    calc
      s^2=2^(2*(k/2)) := by dsimp [s]; rw [Nat.mul_comm 2 (k/2),pow_mul]
      _≤2^k := hp
  have hsq1 := Nat.mul_le_mul_right (b^2) hs2
  have hsq2 := Nat.mul_le_mul_left (2^k) hsquare
  have hsquare' : (s*b)^2≤2^j*K := by
    rw [hjk,pow_add]
    norm_num
    nlinarith only [hsq1,hsq2]
  have hf := Nat.mul_le_mul_left (2^j) hfinite
  have hfinite' : 2^j*K≤2^(ell+j) := by
    rw [pow_add]
    nlinarith only [hf]
  exact ⟨hshort,hsquare',hfinite'⟩

theorem tail_slope_nonneg (ell v b : ℕ) : 0≤TailSlope ell v b := by
  unfold TailSlope
  positivity

theorem scaled_short_coefficient (ell e v b s : ℕ) (hs : 1≤s)
    (hbase : (ell+3)*(v+1)<b) (he : e≤s*(ell+3)) :
    ShortCoefficient e v (s*b)≤(e:ℝ)*TailSlope ell v b := by
  have hs0 : 0<s := by omega
  have hmul := Nat.mul_le_mul_right (v+1) he
  have hbaseS := Nat.mul_lt_mul_of_pos_left hbase hs0
  have hlocal : e*(v+1)<s*b := by nlinarith only [hmul,hbaseS]
  have hbaseR : (0:ℝ)<(b:ℝ)-(ell+3)*(v+1) := by
    have hh : ((ell:ℝ)+3)*(v+1)<b := by exact_mod_cast hbase
    linarith
  have hlocalR : (0:ℝ)<(s:ℝ)*b-e*(v+1) := by
    have hh : (e:ℝ)*(v+1)<(s:ℝ)*b := by exact_mod_cast hlocal
    linarith
  have hsR : (1:ℝ)≤s := by exact_mod_cast hs
  have heR : (e:ℝ)≤(s:ℝ)*(ell+3) := by exact_mod_cast he
  have hd : (s:ℝ)*((b:ℝ)-(ell+3)*(v+1))≤(s:ℝ)*b-e*(v+1) := by
    have hh := mul_le_mul_of_nonneg_right heR (show (0:ℝ)≤v+1 by positivity)
    nlinarith only [hh]
  have hn : (s:ℝ)*b+1≤(s:ℝ)*(b+1) := by nlinarith only [hsR]
  have hratio : ((s:ℝ)*b+1)/(2*((s:ℝ)*b-e*(v+1)))≤
      ((b:ℝ)+1)/(2*((b:ℝ)-(ell+3)*(v+1))) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh1 := mul_le_mul_of_nonneg_right hn (mul_nonneg (by norm_num : (0:ℝ)≤2) hbaseR.le)
    have hh2 := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤b+1 by positivity)
    nlinarith only [hh1,hh2]
  have hh := mul_le_mul_of_nonneg_left hratio (show (0:ℝ)≤e by positivity)
  simp only [ShortCoefficient,TailSlope,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
    Nat.cast_ofNat,Nat.cast_sub hbase.le,Nat.cast_sub hlocal.le]
  simpa only [mul_div_assoc] using hh

theorem band_schedule_conditions (K ell v B0 B1 b : ℕ)
    (hell : 4≤ell) (hfinite : K≤2^ell)
    (h0 : ell*(v+1)<B0) (h1 : (ell+1)*(v+1)<B1) (hb : (ell+3)*(v+1)<b)
    (hs0 : B0^2≤K) (hs1 : B1^2≤2*K) (hsb : b^2≤4*K) (j : ℕ) :
    4≤ell+j ∧ (ell+j)*(v+1)<BandB B0 B1 b j ∧
      (BandB B0 B1 b j)^2≤2^j*K ∧ 2^j*K≤2^(ell+j) := by
  have hellj : 4≤ell+j := by omega
  by_cases hj0 : j=0
  · subst j
    simpa [BandB] using
      (show 4≤ell ∧ ell*(v+1)<B0 ∧ B0^2≤K ∧ K≤2^ell from ⟨hell,h0,hs0,hfinite⟩)
  by_cases hj1 : j=1
  · subst j
    have hf1 : 2*K≤2^(ell+1) := by
      have hh := Nat.mul_le_mul_left 2 hfinite
      rw [pow_succ]
      nlinarith only [hh]
    simpa [BandB] using
      (show 4≤ell+1 ∧ (ell+1)*(v+1)<B1 ∧ B1^2≤2*K ∧ 2*K≤2^(ell+1) from
        ⟨hellj,h1,hs1,hf1⟩)
  have hj : 2≤j := by omega
  have ht := tail_band_conditions K ell v b j hj hb hsb hfinite
  simpa only [BandB,if_neg hj0,if_neg hj1] using ⟨hellj,ht⟩

def BandEnvelope (ell v B0 B1 b : ℕ) (R : ℝ) (j : ℕ) : ℝ :=
  if j=0 then max (ShortCoefficient ell v B0) (4*R)
  else if j=1 then max (ShortCoefficient (ell+1) v B1) (4*R)
  else max (TailSlope ell v b*(ell+j)) (4*R)

theorem band_envelope_nonneg (ell v B0 B1 b j : ℕ) (R : ℝ) :
    0≤BandEnvelope ell v B0 B1 b R j := by
  unfold BandEnvelope
  split_ifs
  · exact (short_coefficient_nonneg ell v B0).trans (le_max_left _ _)
  · exact (short_coefficient_nonneg (ell+1) v B1).trans (le_max_left _ _)
  · exact (mul_nonneg (tail_slope_nonneg ell v b) (by positivity)).trans (le_max_left _ _)

theorem actual_coefficient_le_envelope (ell v B0 B1 b j : ℕ) (R : ℝ)
    (hb : (ell+3)*(v+1)<b) :
    max (ShortCoefficient (ell+j) v (BandB B0 B1 b j)) (4*R)≤BandEnvelope ell v B0 B1 b R j := by
  by_cases hj0 : j=0
  · subst j
    simp [BandB,BandEnvelope]
  by_cases hj1 : j=1
  · subst j
    simp [BandB,BandEnvelope]
  have hj : 2≤j := by omega
  have hg : ell+j≤2^((j-2)/2)*(ell+3) := by
    have hh := linear_dyadic_growth ell (j-2)
    have he : ell+2+(j-2)=ell+j := by omega
    rwa [he] at hh
  have hp : 1≤(2:ℕ)^((j-2)/2) := by
    have hh : 0<(2:ℕ)^((j-2)/2) := by positivity
    omega
  have hs := scaled_short_coefficient ell (ell+j) v b (2^((j-2)/2)) hp hb hg
  simp only [BandB,BandEnvelope,if_neg hj0,if_neg hj1]
  apply max_le_max _ le_rfl
  simpa only [Nat.cast_add,mul_comm] using hs

theorem envelope_prefix_tail_bound (ell v B0 B1 b n M : ℕ) (R : ℝ)
    (hM : 2≤M) (hlinear : 4*R≤TailSlope ell v b*(ell+M)) :
    (∑ j∈Finset.range n,BandEnvelope ell v B0 B1 b R j*(1/2:ℝ)^j)≤
      (∑ j∈Finset.range M,BandEnvelope ell v B0 B1 b R j*(1/2:ℝ)^j)+
        TailSlope ell v b*(2*((ell:ℝ)+M)+2)*(1/2:ℝ)^M := by
  apply finite_weighted_tail_bound _ n M (TailSlope ell v b) ell
    (fun j=>band_envelope_nonneg ell v B0 B1 b j R) (tail_slope_nonneg ell v b) (by positivity)
  intro j hj
  have hj0 : j≠0 := by omega
  have hj1 : j≠1 := by omega
  simp only [BandEnvelope,if_neg hj0,if_neg hj1]
  exact max_linear_tail _ _ _ M j (tail_slope_nonneg ell v b) hlinear hj

theorem actual_large_schedule_budget (N K ell w v B0 B1 b : ℕ) (F : Finset (Finset ℤ)) (R : ℝ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hR0 : 0≤R)
    (homega : ∀ m≤N,m.primeFactors.card≤w) (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v) (hlong : 2*R*(2^w:ℕ)≤(K:ℝ))
    (hell : 4≤ell) (hfinite : K≤2^ell)
    (h0 : ell*(v+1)<B0) (h1 : (ell+1)*(v+1)<B1) (hb : (ell+3)*(v+1)<b)
    (hs0 : B0^2≤K) (hs1 : B1^2≤2*K) (hsb : b^2≤4*K) :
    (F.card:ℝ)*K≤(174/5+16*(∑ j∈Finset.range (N+1),
      BandEnvelope ell v B0 B1 b R j*(1/2:ℝ)^j))*(N:ℝ)^2 := by
  have hc := band_schedule_conditions K ell v B0 B1 b hell hfinite h0 h1 hb hs0 hs1 hsb
  have hh := actual_large_weighted_quadratic N K w v F R (fun j=>ell+j) (BandB B0 B1 b)
    hlegal hK hbad hlow hR0 homega hratio hproduct hlong
    (fun j _=>(hc j).1) (fun j _=>(hc j).2.1)
    (fun j _=>(hc j).2.2.1) (fun j _=>(hc j).2.2.2)
  have hs : (∑ j∈Finset.range (N+1),max (ShortCoefficient (ell+j) v (BandB B0 B1 b j)) (4*R)*(1/2:ℝ)^j)≤
      (∑ j∈Finset.range (N+1),BandEnvelope ell v B0 B1 b R j*(1/2:ℝ)^j) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (actual_coefficient_le_envelope ell v B0 B1 b j R hb)
      (pow_nonneg (by norm_num) _)
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (N:ℝ))
  nlinarith only [hh,hm]

theorem actual_large_prefix_tail_budget (N K ell w v B0 B1 b M : ℕ)
    (F : Finset (Finset ℤ)) (R : ℝ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hR0 : 0≤R)
    (homega : ∀ m≤N,m.primeFactors.card≤w) (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v) (hlong : 2*R*(2^w:ℕ)≤(K:ℝ))
    (hell : 4≤ell) (hfinite : K≤2^ell)
    (h0 : ell*(v+1)<B0) (h1 : (ell+1)*(v+1)<B1) (hb : (ell+3)*(v+1)<b)
    (hs0 : B0^2≤K) (hs1 : B1^2≤2*K) (hsb : b^2≤4*K)
    (hM : 2≤M) (hlinear : 4*R≤TailSlope ell v b*(ell+M)) :
    (F.card:ℝ)*K≤(174/5+16*((∑ j∈Finset.range M,
      BandEnvelope ell v B0 B1 b R j*(1/2:ℝ)^j)+
        TailSlope ell v b*(2*((ell:ℝ)+M)+2)*(1/2:ℝ)^M))*(N:ℝ)^2 := by
  have hh := actual_large_schedule_budget N K ell w v B0 B1 b F R hlegal hK hbad hlow
    hR0 homega hratio hproduct hlong hell hfinite h0 h1 hb hs0 hs1 hsb
  have hs := envelope_prefix_tail_bound ell v B0 B1 b (N+1) M R hM hlinear
  have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (N:ℝ))
  nlinarith only [hh,hm]

def Seed49Ratio : ℝ := 131710070791/19110297600
def Seed49Sigma : ℝ := 21985947800125637/153629805772800

theorem seed49_tail_gate : 4*Seed49Ratio≤TailSlope 18 21 861*((18:ℝ)+8) := by
  norm_num [Seed49Ratio,TailSlope]

theorem seed49_prefix_tail_exact :
    (∑ j∈Finset.range 8,BandEnvelope 18 21 430 608 861 Seed49Ratio j*(1/2:ℝ)^j)+
      TailSlope 18 21 861*(2*((18:ℝ)+8)+2)*(1/2:ℝ)^8=Seed49Sigma := by
  norm_num [Finset.sum_range_succ,BandEnvelope,ShortCoefficient,TailSlope,Seed49Ratio,Seed49Sigma]

theorem actual_seed49_large_budget (N K : ℕ) (F : Finset (Finset ℤ))
    (hlegal : Legal (Ground N) F) (hKl : 185363≤K) (hKu : K≤262144)
    (hbad : ∀ S∈F,¬IsAP S) (hlow : ∀ S∈F,16*K+1≤S.card)
    (homega : ∀ m≤N,m.primeFactors.card≤13)
    (hratio : ∀ m≤N,(m:ℝ)≤Seed49Ratio*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤21) :
    (F.card:ℝ)*K≤(174/5+16*Seed49Sigma)*(N:ℝ)^2 := by
  have hK : 0<K := by omega
  have hlong : 2*Seed49Ratio*(2^13:ℕ)≤(K:ℝ) := by
    have hh : 2*Seed49Ratio*(2^13:ℕ)≤(185363:ℝ) := by norm_num [Seed49Ratio]
    exact hh.trans (by exact_mod_cast hKl)
  have hh := actual_large_prefix_tail_budget N K 18 13 21 430 608 861 8 F Seed49Ratio
    hlegal hK hbad hlow (by norm_num [Seed49Ratio]) homega hratio hproduct hlong
    (by norm_num) (by norm_num; exact hKu) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num; omega) (by norm_num; omega) (by norm_num; omega)
    (by norm_num) seed49_tail_gate
  simp only [Nat.cast_ofNat] at hh
  rw [seed49_prefix_tail_exact] at hh
  exact hh

#print axioms linear_dyadic_identity
#print axioms linear_dyadic_bound
#print axioms finite_weighted_tail_bound
#print axioms max_linear_tail
#print axioms linear_dyadic_growth
#print axioms tail_band_conditions
#print axioms tail_slope_nonneg
#print axioms scaled_short_coefficient
#print axioms band_schedule_conditions
#print axioms band_envelope_nonneg
#print axioms actual_coefficient_le_envelope
#print axioms envelope_prefix_tail_bound
#print axioms actual_large_schedule_budget
#print axioms actual_large_prefix_tail_budget
#print axioms seed49_tail_gate
#print axioms seed49_prefix_tail_exact
#print axioms actual_seed49_large_budget
end
end JSP233.WeightedTail39
