module

public import Erdos272.Resources.FarCore37
public import Erdos272.Resources.ShortPayment37
public import Erdos272.Core.FarAssembly37
public import Erdos272.Arithmetic.TotientRatio38
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! Actual short-prefix geometry with free-B payment. The original member
constructs all traces, cores and witness codes internally. -/
namespace JSP233.WeightedFar38
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36
open DyadicTraceSupply36 NearAP36 FarCore37 FarAssembly37 Reflect37 FarWitness36 BandAggregation34
open scoped Classical BigOperators
noncomputable section

theorem actual_short_prefix_weighted {S : Finset ℤ} {c p : ℤ} {K ell w B : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 2*K≤(S∩Finset.Icc c p).card)
    (htail : 4*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : (WitnessNeighbors S c p).card≤K)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤2^ell)
    (homega : ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w)
    (hsize : B^2≤K) :
    2*(B-ell*(w+1))*K^2≤ell*(B+1)*(StructuralPairs c S).card := by
  obtain ⟨k,hk⟩ := actual_minimal_trace_prefix_family (S:=S) hcp
  let J := MinimalTraceSteps S c p
  let R : ℕ→Finset ℤ := fun d=>Prefix c d (k d)
  have hshort : ∀ d∈J,k d<K := by
    intro d hd
    by_contra hn
    apply hno d (minimal_trace_step_data hd).1
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    apply (hk d hd).2.1
    exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega),rfl⟩
  have hsmall : ∀ d∈J,(R d).card≤K := by
    intro d hd
    exact (prefix_card_le c d (k d)).trans (by have := hshort d hd; omega)
  have htraceSub : J.biUnion (Segment c p)⊆J.biUnion R := by
    intro x hx
    obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨d,hd,(hk d hd).2.2.1 hxd⟩
  have hlarge : K≤(J.biUnion R).card := by
    have hh := actual_trace_card_cover hcp hc hp
    have htr := Finset.card_le_card htraceSub
    change (J.biUnion (Segment c p)).card≤_ at htr
    change (S∩Finset.Icc c p).card≤(J.biUnion (Segment c p)).card+_ at hh
    omega
  obtain ⟨I,hIJ,hIlow,hIhigh⟩ := actual_biUnion_subfamily_between J R hK hsmall hlarge
  let H := I.biUnion R
  let Z := (S.filter (fun z=>p≤z))\H
  have hZ : 2*K≤Z.card := by
    have hh := Finset.card_le_card_sdiff_add_card (s:=S.filter (fun z=>p≤z)) (t:=H)
    change (S.filter (fun z=>p≤z)).card≤Z.card+H.card at hh
    change H.card≤2*K at hIhigh
    omega
  have hdiv : ∀ d∈I,d∣(p-c).natAbs := fun d hd=>(minimal_trace_step_data (hIJ hd)).2.1
  have htrace : ∀ d∈I,Segment c p d⊆S := fun d hd=>(minimal_trace_step_data (hIJ hd)).2.2.1
  have hmin : ∀ d∈I,∀ e : ℕ, 0<e → e∣d → Segment c p e⊆S → d≤e :=
    fun d hd=>(minimal_trace_step_data (hIJ hd)).2.2.2
  have hend : ∀ d∈I,c+((p-c).natAbs:ℤ)∈Prefix c d (k d) := by
    intro d hd
    have he : c+((p-c).natAbs:ℤ)=p := by rw [Int.natAbs_of_nonneg (by omega : 0≤p-c)]; ring
    rw [he]
    apply (hk d (hIJ hd)).2.2.1
    exact (mem_segment _ _ _ _).mpr ⟨hcp.le,le_rfl,Int.natCast_dvd.mpr (hdiv d hd)⟩
  have hrow : ∀ z∈Z,(B-ell*(w+1))*K≤ell*(B+1)*
      (∑ d∈I,(PrimePrefix35.CoprimePrefix
        ((p-c).natAbs*(z-c).natAbs) (k d)).card) := by
    intro z hz
    obtain ⟨hzT,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    have hpabs : 0<(p-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hzabs : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    apply ShortPayment37.actual_minimal_trace_weighted c (p-c).natAbs
      ((p-c).natAbs*(z-c).natAbs) K ell w B I (fun d=>Segment c p d⊆S) k hpabs
      (Nat.mul_pos hpabs hzabs) hB hsize hdiv htrace hmin hend
      (fun d hd=>(hshort d (hIJ hd)).trans_le hfinite) (homega z hzS hpz) hIlow
  have hcode : (∑ z∈Z,∑ d∈I,(PrimePrefix35.CoprimePrefix
      ((p-c).natAbs*(z-c).natAbs) (k d)).card)≤(StructuralPairs c S).card := by
    apply actual_variable_anchor_codes I k (Int.natAbs_pos.mpr (by omega)) hdiv
      (fun d hd i hi hik=>Finset.mem_biUnion.mpr
        ⟨d,hd,Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩⟩)
      (Finset.disjoint_left.mpr (fun z hz hzH=>(Finset.mem_sdiff.mp hz).2 hzH))
    intro z hz d hd i hi hik hcop
    obtain ⟨hzT,hzH⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    apply (hk d (hIJ hd)).2.2.2 z hzS hpz _ i hi hik hcop
    exact fun hzR=>hzH (Finset.mem_biUnion.mpr ⟨d,hd,hzR⟩)
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  have hpay := Nat.mul_le_mul_left (ell*(B+1)) hcode
  have hp := Nat.mul_le_mul_right ((B-ell*(w+1))*K) hZ
  nlinarith only [hs,hpay,hp]

theorem actual_no_long_right_prefix_weighted {S : Finset ℤ} {c : ℤ} {K ell w B : ℕ}
    (hc : c∈S) (hK : 0<K) (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (hell : 4≤ell) (hB : 0<B) (hfinite : K≤2^ell)
    (homega : ∀ p∈S, c<p → ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w)
    (hsize : B^2≤K) :
    2*(B-ell*(w+1))*K^2≤ell*(B+1)*(StructuralPairs c S).card := by
  let T := S.filter (fun x=>c<x)
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_middle_block hright
  by_cases hsome : ∃ p∈M,(WitnessNeighbors S c p).card≤K
  · obtain ⟨p,hpM,hneigh⟩ := hsome
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 2*K≤(S∩Finset.Icc c p).card :=
      (hmiddle p hpM).1.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT,hxp⟩ := Finset.mem_filter.mp hx
        obtain ⟨hxS,hcx⟩ := Finset.mem_filter.mp hxT
        exact Finset.mem_inter.mpr ⟨hxS,Finset.mem_Icc.mpr ⟨hcx.le,hxp⟩⟩))
    have htail : 4*K≤(S.filter (fun x=>p≤x)).card :=
      (hmiddle p hpM).2.trans (Finset.card_le_card (by
        intro x hx
        obtain ⟨hxT,hpx⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxT).1,hpx⟩))
    exact actual_short_prefix_weighted hcp hc hpS hK hhead htail hneigh hno
      hB hfinite (homega p hpS hcp) hsize
  · have hneigh : ∀ p∈M,K≤(WitnessNeighbors S c p).card := by
      intro p hp
      by_contra hn
      exact hsome ⟨p,hp,by omega⟩
    have hlo := Finset.sum_le_sum hneigh
    simp only [Finset.sum_const,nsmul_eq_mul,hMcard] at hlo
    have hhi := actual_neighbors_double_count S M c
    have hsquare : K^2≤2*(StructuralPairs c S).card := by nlinarith only [hlo,hhi]
    have hsub : B-ell*(w+1)≤B := Nat.sub_le _ _
    have hcoef : 4*(B-ell*(w+1))≤ell*(B+1) := by nlinarith
    have hmul := Nat.mul_le_mul_left (2*(B-ell*(w+1))) hsquare
    have hpay := Nat.mul_le_mul_right (StructuralPairs c S).card hcoef
    nlinarith only [hmul,hpay]

def ShortCoefficient (ell w B : ℕ) : ℝ :=
  ((ell*(B+1):ℕ):ℝ)/((2*(B-ell*(w+1)):ℕ):ℝ)

theorem short_coefficient_nonneg (ell w B : ℕ) : 0≤ShortCoefficient ell w B := by
  exact div_nonneg (by positivity) (by positivity)

theorem short_coefficient_ge_two {ell w B : ℕ} (hell : 4≤ell) (hB : ell*(w+1)<B) :
    2≤ShortCoefficient ell w B := by
  have hD : 0<B-ell*(w+1) := Nat.sub_pos_of_lt hB
  have hDR : (0:ℝ)<((2*(B-ell*(w+1)):ℕ):ℝ) := by exact_mod_cast (by omega : 0<2*(B-ell*(w+1)))
  have hsub : B-ell*(w+1)≤B := Nat.sub_le _ _
  have hnum : 4*(B-ell*(w+1))≤ell*(B+1) := by nlinarith
  apply (le_div_iff₀ hDR).mpr
  have hh : (2:ℕ)*(2*(B-ell*(w+1)))≤ell*(B+1) := by omega
  exact_mod_cast hh

theorem weighted_short_to_real {K ell w B W : ℕ} (hB : ell*(w+1)<B)
    (h : 2*(B-ell*(w+1))*K^2≤ell*(B+1)*W) :
    (K:ℝ)^2≤ShortCoefficient ell w B*W := by
  have hD : (0:ℝ)<((2*(B-ell*(w+1)):ℕ):ℝ) := by
    exact_mod_cast (by omega : 0<2*(B-ell*(w+1)))
  unfold ShortCoefficient
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hD).mpr
  have hh : ((2*(B-ell*(w+1)):ℕ):ℝ)*(K:ℝ)^2≤((ell*(B+1):ℕ):ℝ)*W := by
    exact_mod_cast h
  nlinarith only [hh]

theorem actual_long_prefix_real_many {S : Finset ℤ} {c : ℤ} {K w : ℕ} (R : ℝ)
    (hR0 : 0≤R) (hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    ∃ U : Finset ℤ, U⊆S ∧ IsAP U ∧
      ((S\U).card:ℝ)*K≤4*R*(StructuralPairs c S).card := by
  obtain ⟨d,hd,hprefix,hmin⟩ := actual_minimal_long_prefix_exists hex
  obtain ⟨U,hUS,hU,hPU,hcount⟩ := actual_long_prefix_codes hd hprefix hmin
  have hcU := hPU (prefix_zero_mem c d K)
  refine ⟨U,hUS,(isAP_iff_exists_APAt _).mpr ⟨d,c,hU,hcU⟩,?_⟩
  have hrow : ∀ z∈S\U,(K:ℝ)≤4*R*
      (SquarefreeSupply35.IntervalCoprime (z-c).natAbs (K/2) K).card := by
    intro z hz
    obtain ⟨hzS,hzU⟩ := Finset.mem_sdiff.mp hz
    have hzc : z≠c := fun he=>hzU (he.symm ▸ hcU)
    exact TotientRatio38.actual_half_interval_real_supply (z-c).natAbs K w R
      (Int.natAbs_pos.mpr (by omega)) (hratio z hzS hzc) (homega z hzS hzc) hlong
  have hs := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
  have hc : (∑ z∈S\U,((SquarefreeSupply35.IntervalCoprime
      (z-c).natAbs (K/2) K).card:ℝ))≤(StructuralPairs c S).card := by
    exact_mod_cast hcount
  exact hs.trans (mul_le_mul_of_nonneg_left hc (by positivity))

theorem actual_far_long_real_bound {S : Finset ℤ} {c : ℤ} {K w : ℕ} (R : ℝ)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S) (hR0 : 0≤R)
    (hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (K:ℝ)^2≤4*R*(StructuralPairs c S).card := by
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
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (4*R)*(StructuralPairs c S).card := by
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
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (4*R)*(StructuralPairs c S).card := by
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

theorem actual_real_transversal_budget (N K : ℕ) (C : ℝ)
    (F : Finset (Finset ℤ)) (H : Finset ℤ) (hC : 0≤C)
    (hlegal : Legal (Ground N) F)
    (hcert : ∀ S∈F,∃ c : ℤ,c∈S ∧ c∈H ∧ (K:ℝ)^2≤C*(StructuralPairs c S).card) :
    (F.card:ℝ)*K^2≤C*H.card*N.choose 2 := by
  have hex : ∀ S : Finset ℤ,∃ c : ℤ,S∈F →
      c∈S ∧ c∈H ∧ (K:ℝ)^2≤C*(StructuralPairs c S).card := by
    intro S
    by_cases hS : S∈F
    · obtain ⟨c,hcS,hcH,hb⟩ := hcert S hS
      exact ⟨c,fun _=>⟨hcS,hcH,hb⟩⟩
    · exact ⟨0,fun hh=>False.elim (hS hh)⟩
  choose anchor ha using hex
  let A : ℤ→Finset (Finset ℤ) := fun c=>F.filter (fun S=>anchor S=c)
  have hAF : ∀ c,A c⊆F := fun c=>Finset.filter_subset _ _
  have hrow : ∀ c∈H,((A c).card:ℝ)*K^2≤C*N.choose 2 := by
    intro c _
    have hroot : Rooted (A c) c := by
      intro S hS
      have hh := (ha S (hAF c hS)).1
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    have hLC : Legal (Ground N) (A c) :=
      ⟨fun S hS=>hlegal.1 S (hAF c hS),
       fun S hS T hT he=>hlegal.2 S (hAF c hS) T (hAF c hT) he⟩
    have hlo : ∀ S∈A c,(K:ℝ)^2≤C*(StructuralPairs c S).card := by
      intro S hS
      have hh := (ha S (hAF c hS)).2.2
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    have hs := Finset.sum_le_sum hlo
    simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
    have hb := (actual_family_structural_budget hLC hroot).trans (pair_universe_ground_card_le N c)
    have hbR : (∑ S∈A c,((StructuralPairs c S).card:ℝ))≤N.choose 2 := by exact_mod_cast hb
    exact hs.trans (mul_le_mul_of_nonneg_left hbR hC)
  have hmaps : ∀ S∈F,anchor S∈H := fun S hS=>(ha S hS).2.1
  have hpart : F.card=∑ c∈H,(A c).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hp : (F.card:ℝ)=∑ c∈H,((A c).card:ℝ) := by exact_mod_cast hpart
  have hs := Finset.sum_le_sum hrow
  rw [←Finset.sum_mul] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  rw [←hp] at hs
  nlinarith only [hs]

theorem actual_real_far_band_budget {N K : ℕ} {C : ℝ} {F : Finset (Finset ℤ)}
    (hC : 0≤C) (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hhigh : ∀ S∈F,S.card≤32*K)
    (hW : ∀ S∈F,¬HasNearAPCore K S → ∀ c∈S,
      (K:ℝ)^2≤C*(StructuralPairs c S).card) :
    ((FarMembers K F).card:ℝ)*K≤32*C*N.choose 2 := by
  rcases F.eq_empty_or_nonempty with he|hne
  · simp [he,FarMembers]
    positivity
  obtain ⟨R,hR⟩ := hne
  have hRN : R.Nonempty := Finset.card_pos.mp (by have hh:=hlow R hR; omega)
  have hMF : FarMembers K F⊆F := Finset.filter_subset _ _
  have hLM : Legal (Ground N) (FarMembers K F) :=
    ⟨fun S hS=>hlegal.1 S (hMF hS),fun S hS T hT he=>hlegal.2 S (hMF hS) T (hMF hT) he⟩
  have hh := actual_real_transversal_budget N K C (FarMembers K F) R hC hLM (by
    intro S hS
    obtain ⟨c,hc⟩ := actual_member_hits_family hlegal hR hRN S (hMF hS)
    obtain ⟨hcS,hcR⟩ := Finset.mem_inter.mp hc
    exact ⟨c,hcS,hcR,hW S (hMF hS) (Finset.mem_filter.mp hS).2 c hcS⟩)
  have hRh : (R.card:ℝ)≤32*(K:ℝ) := by exact_mod_cast hhigh R hR
  have hm := mul_le_mul_of_nonneg_left hRh
    (show 0≤C*(N.choose 2:ℝ) by positivity)
  have hfinal : (((FarMembers K F).card:ℝ)*K)*(K:ℝ)≤(32*C*N.choose 2)*(K:ℝ) := by
    nlinarith only [hh,hm]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hK : (0:ℝ)<K)).mp hfinal

theorem actual_far_ground_weighted {N K ell w v B : ℕ} {S : Finset ℤ} {c : ℤ} (R : ℝ)
    (hS : S⊆Ground N) (hc : c∈S) (hK : 0<K)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 4≤ell) (hB : ell*(v+1)<B) (hBsquare : B^2≤K) (hfinite : K≤2^ell)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (K:ℝ)^2≤max (ShortCoefficient ell v B) (4*R)*(StructuralPairs c S).card := by
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
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ)) :
    (F.card:ℝ)*(15*K)≤261*(N:ℝ)^2+
      480*max (ShortCoefficient ell v B) (4*R)*N.choose 2 := by
  let C := max (ShortCoefficient ell v B) (4*R)
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

theorem actual_large_weighted_sum (N K : ℕ) (F : Finset (Finset ℤ)) (C : ℕ→ℝ)
    (hK : 0<K) (hground : ∀ S∈F,S⊆Ground N) (hlow : ∀ S∈F,16*K+1≤S.card)
    (hcap : ∀ j<N+1,((RankBand F Finset.card K j).card:ℝ)*(15*(2^j*K))≤
      261*(N:ℝ)^2+480*(N.choose 2:ℝ)*C j) :
    15*(K:ℝ)*F.card≤522*(N:ℝ)^2+
      480*(N.choose 2:ℝ)*(∑ j∈Finset.range (N+1),C j*(1/2:ℝ)^j) := by
  have hhigh : ∀ S∈F,S.card≤N := by
    intro S hS
    simpa only [ground_card] using Finset.card_le_card (hground S hS)
  have hc := actual_rank_band_cover F Finset.card N K hK hlow hhigh
  have hcard := (Finset.card_le_card hc).trans Finset.card_biUnion_le
  have hcardR : (F.card:ℝ)≤∑ j∈Finset.range (N+1),((RankBand F Finset.card K j).card:ℝ) := by
    exact_mod_cast hcard
  have hrow : ∀ j∈Finset.range (N+1),((RankBand F Finset.card K j).card:ℝ)*(15*K)≤
      261*(N:ℝ)^2*(1/2:ℝ)^j+480*(N.choose 2:ℝ)*(C j*(1/2:ℝ)^j) := by
    intro j hj
    have hh := hcap j (Finset.mem_range.mp hj)
    have hfactor : (15:ℝ)*((2:ℝ)^j*K)=(2:ℝ)^j*(15*K) := by ring
    rw [hfactor] at hh
    have hhR : ((RankBand F Finset.card K j).card:ℝ)*((2:ℝ)^j*(15*K))≤
        261*(N:ℝ)^2+480*(N.choose 2:ℝ)*C j := by
      exact hh
    have hp : 0<(2:ℝ)^j := pow_pos (by norm_num) _
    have hd := div_le_div_of_nonneg_right hhR hp.le
    have he : (((RankBand F Finset.card K j).card:ℝ)*((2:ℝ)^j*(15*K)))/(2:ℝ)^j=
        ((RankBand F Finset.card K j).card:ℝ)*(15*K) := by field_simp
    rw [he] at hd
    have hinv : (1/2:ℝ)^j=((2:ℝ)^j)⁻¹ := by
      rw [one_div,inv_pow]
    have hr : (261*(N:ℝ)^2+480*(N.choose 2:ℝ)*C j)/(2:ℝ)^j=
        261*(N:ℝ)^2*(1/2:ℝ)^j+480*(N.choose 2:ℝ)*(C j*(1/2:ℝ)^j) := by
      rw [hinv,div_eq_mul_inv]
      ring
    exact hd.trans_eq hr
  have hs := Finset.sum_le_sum hrow
  simp only [←Finset.sum_mul,Finset.sum_add_distrib,←Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (dyadic_sum_le_two (N+1))
    (show 0≤261*(N:ℝ)^2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hcardR (show (0:ℝ)≤15*K by positivity)
  nlinarith only [hs,ht,hm]

theorem actual_large_from_weighted_arithmetic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (ell B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ))
    (hell : ∀ j<N+1,4≤ell j) (hB : ∀ j<N+1,ell j*(v+1)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤2^(ell j)) :
    15*(K:ℝ)*F.card≤522*(N:ℝ)^2+480*(N.choose 2:ℝ)*
      (∑ j∈Finset.range (N+1),max (ShortCoefficient (ell j) v (B j)) (4*R)*(1/2:ℝ)^j) := by
  apply actual_large_weighted_sum N K F
    (fun j=>max (ShortCoefficient (ell j) v (B j)) (4*R)) hK hlegal.1 hlow
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
  have hlongj : 2*R*(2^w:ℕ)≤(2^j*K:ℕ) := hlong.trans (by exact_mod_cast hQK)
  have hh := actual_one_band_weighted R hLG (by positivity)
    (fun S hS=>hbad S (hGF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2)
    (hell j hj) (hB j hj) (hBsquare j hj) (hfinite j hj)
    hR0 homega hratio hproduct hlongj
  dsimp only [G] at hh
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  nlinarith only [hh]

theorem choose_two_real_le_quadratic (N : ℕ) : (N.choose 2:ℝ)≤(N:ℝ)^2/2 := by
  rw [Nat.cast_choose_two]
  have hN : (0:ℝ)≤N := by positivity
  nlinarith only [hN]

theorem weighted_quadratic_payment (N K m : ℕ) (Sigma : ℝ) (hSigma : 0≤Sigma)
    (h : 15*(K:ℝ)*m≤522*(N:ℝ)^2+480*(N.choose 2:ℝ)*Sigma) :
    (m:ℝ)*K≤(174/5+16*Sigma)*(N:ℝ)^2 := by
  have hm := mul_le_mul_of_nonneg_right (choose_two_real_le_quadratic N) hSigma
  nlinarith only [h,hm]

theorem actual_large_weighted_quadratic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (ell B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : 2*R*(2^w:ℕ)≤(K:ℝ))
    (hell : ∀ j<N+1,4≤ell j) (hB : ∀ j<N+1,ell j*(v+1)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤2^(ell j)) :
    (F.card:ℝ)*K≤(174/5+16*(∑ j∈Finset.range (N+1),
      max (ShortCoefficient (ell j) v (B j)) (4*R)*(1/2:ℝ)^j))*(N:ℝ)^2 := by
  have hh := actual_large_from_weighted_arithmetic N K w v F R ell B hlegal hK hbad hlow
    hR0 homega hratio hproduct hlong hell hB hBsquare hfinite
  apply weighted_quadratic_payment N K F.card _ _ hh
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg ((short_coefficient_nonneg (ell j) v (B j)).trans (le_max_left _ _))
    (pow_nonneg (by norm_num) _)

#print axioms actual_short_prefix_weighted
#print axioms actual_no_long_right_prefix_weighted
#print axioms short_coefficient_nonneg
#print axioms short_coefficient_ge_two
#print axioms weighted_short_to_real
#print axioms actual_long_prefix_real_many
#print axioms actual_far_long_real_bound
#print axioms actual_far_right_weighted
#print axioms actual_far_weighted
#print axioms actual_real_transversal_budget
#print axioms actual_real_far_band_budget
#print axioms actual_far_ground_weighted
#print axioms actual_one_band_weighted
#print axioms actual_large_weighted_sum
#print axioms actual_large_from_weighted_arithmetic
#print axioms choose_two_real_le_quadratic
#print axioms weighted_quadratic_payment
#print axioms actual_large_weighted_quadratic
end
end JSP233.WeightedFar38
