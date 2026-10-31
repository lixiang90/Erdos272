import Erdos272.Resources.WeightedFar38

/-! Retain the actual half-interval error in each long-core band. -/
namespace JSP233.LongSharp42
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36
open DyadicTraceSupply36 NearAP36 FarCore37 FarAssembly37 Reflect37 FarWitness36 BandAggregation34
open WeightedFar38 TotientRatio38
open scoped Classical BigOperators
noncomputable section

def LongCoefficient (K w : ℕ) (R : ℝ) : ℝ :=
  2*R*(K:ℝ)/((K:ℝ)-R*(2^w:ℕ))

theorem long_coefficient_nonneg {K w : ℕ} {R : ℝ} (hR : 0≤R)
    (hK : R*(2^w:ℕ)<(K:ℝ)) : 0≤LongCoefficient K w R := by
  unfold LongCoefficient
  exact div_nonneg (by positivity) (by linarith)

theorem long_coefficient_ge_twice {K w : ℕ} {R : ℝ} (hR : 0≤R)
    (hK : R*(2^w:ℕ)<(K:ℝ)) : 2*R≤LongCoefficient K w R := by
  unfold LongCoefficient
  apply (le_div_iff₀ (by linarith : (0:ℝ)<(K:ℝ)-R*(2^w:ℕ))).mpr
  have hp : 0≤2*R*(R*(2^w:ℕ)) := by positivity
  nlinarith only [hp]

theorem long_coefficient_le_old {K w : ℕ} {R : ℝ} (hR : 0≤R)
    (hK : R*(2^w:ℕ)<(K:ℝ)) (hold : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    LongCoefficient K w R≤4*R := by
  unfold LongCoefficient
  apply (div_le_iff₀ (by linarith : (0:ℝ)<(K:ℝ)-R*(2^w:ℕ))).mpr
  have hm := mul_le_mul_of_nonneg_left hold (show 0≤2*R by positivity)
  nlinarith only [hm]

theorem long_coefficient_antitone {K L w : ℕ} {R : ℝ} (hR : 0≤R)
    (hK : R*(2^w:ℕ)<(K:ℝ)) (hKL : K≤L) :
    LongCoefficient L w R≤LongCoefficient K w R := by
  have hKLr : (K:ℝ)≤L := by exact_mod_cast hKL
  have hD : (0:ℝ)<(K:ℝ)-R*(2^w:ℕ) := by linarith
  have hD' : (0:ℝ)<(L:ℝ)-R*(2^w:ℕ) := by linarith
  unfold LongCoefficient
  apply (div_le_div_iff₀ hD' hD).mpr
  have hm := mul_nonneg (show 0≤2*R*(R*(2^w:ℕ)) by positivity) (sub_nonneg.mpr hKLr)
  nlinarith only [hm]

theorem actual_half_interval_sharp_supply (m K w : ℕ) (R : ℝ) (hm : 0<m)
    (hR : (m:ℝ)≤R*Nat.totient m) (hw : m.primeFactors.card≤w)
    (hK : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)≤LongCoefficient K w R*(SquarefreeSupply35.IntervalCoprime m (K/2) K).card := by
  have hr := actual_half_interval_real_lower m K R hm hR
  have hR0 := ratio_nonneg hm hR
  have he : ((2^m.primeFactors.card:ℕ):ℝ)≤(2^w:ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1≤2) hw
  have hh := mul_le_mul_of_nonneg_left he hR0
  have hs : (K:ℝ)-R*(2^w:ℕ)≤2*R*(SquarefreeSupply35.IntervalCoprime m (K/2) K).card := by
    nlinarith only [hr,hh]
  have hp := mul_le_mul_of_nonneg_left hs (show (0:ℝ)≤K by positivity)
  unfold LongCoefficient
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : (0:ℝ)<(K:ℝ)-R*(2^w:ℕ))).mpr
  nlinarith only [hp]

theorem actual_long_prefix_real_many {S : Finset ℤ} {c : ℤ} {K w : ℕ} (R : ℝ)
    (hR0 : 0≤R) (hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    ∃ U : Finset ℤ, U⊆S ∧ IsAP U ∧
      ((S\U).card:ℝ)*K≤LongCoefficient K w R*(StructuralPairs c S).card := by
  obtain ⟨d,hd,hprefix,hmin⟩ := actual_minimal_long_prefix_exists hex
  obtain ⟨U,hUS,hU,hPU,hcount⟩ := actual_long_prefix_codes hd hprefix hmin
  have hcU := hPU (prefix_zero_mem c d K)
  refine ⟨U,hUS,(isAP_iff_exists_APAt _).mpr ⟨d,c,hU,hcU⟩,?_⟩
  have hrow : ∀ z∈S\U,(K:ℝ)≤LongCoefficient K w R*
      (SquarefreeSupply35.IntervalCoprime (z-c).natAbs (K/2) K).card := by
    intro z hz
    obtain ⟨hzS,hzU⟩ := Finset.mem_sdiff.mp hz
    have hzc : z≠c := fun he=>hzU (he.symm ▸ hcU)
    exact actual_half_interval_sharp_supply (z-c).natAbs K w R
      (Int.natAbs_pos.mpr (by omega)) (hratio z hzS hzc) (homega z hzS hzc) hlong
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  have hc : (∑ z∈S\U,((SquarefreeSupply35.IntervalCoprime
      (z-c).natAbs (K/2) K).card:ℝ))≤(StructuralPairs c S).card := by
    exact_mod_cast hcount
  exact hs.trans (mul_le_mul_of_nonneg_left hc (long_coefficient_nonneg hR0 hlong))

theorem actual_far_long_real_bound {S : Finset ℤ} {c : ℤ} {K w : ℕ} (R : ℝ)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S) (hR0 : 0≤R)
    (hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤LongCoefficient K w R*(StructuralPairs c S).card := by
  obtain ⟨U,hUS,hAP,hh⟩ := actual_long_prefix_real_many R hR0 hex homega hratio hlong
  have hrem : (K:ℝ)≤(S\U).card := by
    exact_mod_cast non_near_actual_AP_remainder hlarge hfar U hUS hAP
  have hm := mul_le_mul_of_nonneg_right hrem (show (0:ℝ)≤K by positivity)
  nlinarith only [hh,hm]

theorem actual_far_right_weighted {S : Finset ℤ} {c : ℤ} {K ell w v B : ℕ} (R : ℝ)
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hell : 4≤ell) (hB : ell*(v+1)<B) (hBsquare : B^2≤K) (hfinite : K≤2^ell)
    (hR0 : 0≤R)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hproduct : ∀ p∈S,c<p → ∀ z∈S,p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  by_cases hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S
  · have hh := actual_far_long_real_bound R hlarge hfar hR0 hex homega hratio hlong
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hb : 0<B := by omega
    have hh := actual_no_long_right_prefix_weighted hc hK hright
      (fun d hd hpre=>hex ⟨d,hd,hpre⟩) hell hb hfinite hproduct hBsquare
    have hr := weighted_short_to_real hB hh
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem actual_far_weighted {S : Finset ℤ} {c : ℤ} {K ell w v B : ℕ} (R : ℝ)
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 4≤ell) (hB : ell*(v+1)<B) (hBsquare : B^2≤K) (hfinite : K≤2^ell)
    (hR0 : 0≤R)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hproduct : ∀ p∈S,p≠c → ∀ z∈S,z≠c →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  by_cases hright : 8*K≤(S.filter (fun x=>c<x)).card
  · exact actual_far_right_weighted R hc hK hlarge hfar hright hell hB hBsquare hfinite
      hR0 homega hratio
      (fun p hp hcp z hz hpz=>hproduct p hp (by omega) z hz (by omega)) hlong
  have hleft : 8*K≤(S.filter (fun x=>x<c)).card := by
    have hh := actual_side_card_partition hc
    omega
  have hc' : -c∈Reflect S := (mem_reflect S (-c)).mpr (by simpa using hc)
  have hlarge' : 16*K+1≤(Reflect S).card := by simpa only [reflect_card] using hlarge
  have hright' : 8*K≤((Reflect S).filter (fun x=> -c<x)).card := by
    simpa only [reflect_right_card] using hleft
  have hfar' := actual_non_near_reflect hlarge hfar
  have hω : ∀ z∈Reflect S,z≠ -c → (z-(-c)).natAbs.primeFactors.card≤w := by
    intro z hz hzc
    have hh := homega (-z) ((mem_reflect S z).mp hz) (by omega)
    have he : -z-c=-(z-(-c)) := by ring
    simpa only [he,Int.natAbs_neg] using hh
  have hρ : ∀ z∈Reflect S,z≠ -c →
      ((z-(-c)).natAbs:ℝ)≤R*Nat.totient (z-(-c)).natAbs := by
    intro z hz hzc
    have hh := hratio (-z) ((mem_reflect S z).mp hz) (by omega)
    have he : -z-c=-(z-(-c)) := by ring
    simpa only [he,Int.natAbs_neg] using hh
  have hv : ∀ p∈Reflect S,-c<p → ∀ z∈Reflect S,p≤z →
      ((p-(-c)).natAbs*(z-(-c)).natAbs).primeFactors.card≤v := by
    intro p hp hcp z hz hpz
    have hh := hproduct (-p) ((mem_reflect S p).mp hp) (by omega)
      (-z) ((mem_reflect S z).mp hz) (by omega)
    have he₁ : -p-c=-(p-(-c)) := by ring
    have he₂ : -z-c=-(z-(-c)) := by ring
    simpa only [he₁,he₂,Int.natAbs_neg] using hh
  have hh := actual_far_right_weighted R hc' hK hlarge' hfar' hright' hell hB hBsquare
    hfinite hR0 hω hρ hv hlong
  simpa only [structural_reflect_card] using hh

theorem actual_far_ground_weighted {N K ell w v B : ℕ} {S : Finset ℤ} {c : ℤ} (R : ℝ)
    (hS : S⊆Ground N) (hc : c∈S) (hK : 0<K)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 4≤ell) (hB : ell*(v+1)<B) (hBsquare : B^2≤K) (hfinite : K≤2^ell)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  apply actual_far_weighted R hc hK hlarge hfar hell hB hBsquare hfinite hR0 _ _ _ hlong
  · intro z hz _
    exact homega _ (actual_anchor_distance_le hS hc hz)
  · intro z hz _
    exact hratio _ (actual_anchor_distance_le hS hc hz)
  · intro p hp _ z hz _
    apply hproduct
    simpa only [pow_two] using Nat.mul_le_mul
      (actual_anchor_distance_le hS hc hp) (actual_anchor_distance_le hS hc hz)

theorem actual_one_band_weighted {N K ell w v B : ℕ} {F : Finset (Finset ℤ)} (R : ℝ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hhigh : ∀ S∈F,S.card≤32*K)
    (hell : 4≤ell) (hB : ell*(v+1)<B) (hBsquare : B^2≤K) (hfinite : K≤2^ell)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (F.card:ℝ)*(15*K)≤261*(N:ℝ)^2+
      480*max (ShortCoefficient ell v B) (LongCoefficient K w R)*N.choose 2 := by
  let C := max (ShortCoefficient ell v B) (LongCoefficient K w R)
  have hC : 0≤C := (short_coefficient_nonneg ell v B).trans (le_max_left _ _)
  have hf := actual_real_far_band_budget hC hlegal hK hlow hhigh (by
    intro S hSF hfar c hc
    exact actual_far_ground_weighted R (hlegal.1 S hSF) hc hK (hlow S hSF) hfar
      hell hB hBsquare hfinite hR0 homega hratio hproduct hlong)
  have hn := actual_near_members_band_budget hlegal hK hbad hlow
    (fun S hS=>(hhigh S hS).trans (by omega : 32*K≤64*K))
  have hnR : (15*(K:ℝ))*((NearMembers K F).card:ℝ)≤261*(N:ℝ)^2 := by exact_mod_cast hn
  have hp := Finset.card_filter_add_card_filter_not (s:=F) (HasNearAPCore K)
  change (NearMembers K F).card+(FarMembers K F).card=F.card at hp
  have hpR : ((NearMembers K F).card:ℝ)+((FarMembers K F).card:ℝ)=F.card := by exact_mod_cast hp
  change _≤261*(N:ℝ)^2+480*C*N.choose 2
  nlinarith only [hf,hnR,hpR]

theorem actual_large_from_weighted_arithmetic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (ell B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ))
    (hell : ∀ j<N+1,4≤ell j) (hB : ∀ j<N+1,ell j*(v+1)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤2^(ell j)) :
    15*(K:ℝ)*F.card≤522*(N:ℝ)^2+480*(N.choose 2:ℝ)*
      (∑ j∈Finset.range (N+1),max (ShortCoefficient (ell j) v (B j)) (LongCoefficient (2^j*K) w R)*(1/2:ℝ)^j) := by
  apply actual_large_weighted_sum N K F
    (fun j=>max (ShortCoefficient (ell j) v (B j)) (LongCoefficient (2^j*K) w R)) hK hlegal.1 hlow
  intro j hj
  let G := RankBand F Finset.card K j
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G :=
    ⟨fun S hS=>hlegal.1 S (hGF hS),fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩
  have hQK : K≤2^j*K := by
    have hp : 1≤(2:ℕ)^j := by
      have hh : 0<(2:ℕ)^j := by positivity
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right K hp
  have hlongj : R*(2^w:ℕ)<(2^j*K:ℕ) := hlong.trans_le (by exact_mod_cast hQK)
  have hh := actual_one_band_weighted R hLG (by positivity)
    (fun S hS=>hbad S (hGF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2)
    (hell j hj) (hB j hj) (hBsquare j hj) (hfinite j hj)
    hR0 homega hratio hproduct hlongj
  dsimp only [G] at hh
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  nlinarith only [hh]

theorem actual_large_weighted_quadratic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (ell B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ))
    (hell : ∀ j<N+1,4≤ell j) (hB : ∀ j<N+1,ell j*(v+1)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤2^(ell j)) :
    (F.card:ℝ)*K≤(174/5+16*(∑ j∈Finset.range (N+1),
      max (ShortCoefficient (ell j) v (B j)) (LongCoefficient (2^j*K) w R)*(1/2:ℝ)^j))*(N:ℝ)^2 := by
  have hh := actual_large_from_weighted_arithmetic N K w v F R ell B hlegal hK hbad hlow
    hR0 homega hratio hproduct hlong hell hB hBsquare hfinite
  apply weighted_quadratic_payment N K F.card _ _ hh
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg ((short_coefficient_nonneg (ell j) v (B j)).trans (le_max_left _ _))
    (pow_nonneg (by norm_num) _)

#print axioms long_coefficient_nonneg
#print axioms long_coefficient_ge_twice
#print axioms long_coefficient_le_old
#print axioms long_coefficient_antitone
#print axioms actual_half_interval_sharp_supply
#print axioms actual_long_prefix_real_many
#print axioms actual_far_long_real_bound
#print axioms actual_far_right_weighted
#print axioms actual_far_weighted
#print axioms actual_far_ground_weighted
#print axioms actual_one_band_weighted
#print axioms actual_large_from_weighted_arithmetic
#print axioms actual_large_weighted_quadratic
end
end JSP233.LongSharp42
