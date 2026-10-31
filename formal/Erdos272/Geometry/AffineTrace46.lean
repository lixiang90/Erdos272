import Erdos272.Arithmetic.PrimorialPrefix46
import Erdos272.Retention.LongSharp42
import Mathlib.Data.Finset.Lattice.Fold

/-! The finite primorial error is a constructed number, not a supplied actual
row bound. All actual minimal traces, exterior points and witness codes below
are constructed from the original member. -/
namespace JSP233.AffineTrace46
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36
open DyadicTraceSupply36 NearAP36 FarCore37 FarAssembly37 Reflect37 FarWitness36 BandAggregation34
open PrimorialPrefix46 LongSharp42 WeightedFar38
open scoped Classical BigOperators
noncomputable section

def AffineDefect (v U a : ℕ) : ℕ :=
  (Finset.range U).sup (fun k=>k-a*(PrimePrefix35.CoprimePrefix (Primorial v) k).card)

theorem primorial_affine_row (v U a k : ℕ) (hk : k<U) :
    k≤a*(PrimePrefix35.CoprimePrefix (Primorial v) k).card+AffineDefect v U a := by
  have hh := Finset.le_sup (f:=fun k=>k-a*(PrimePrefix35.CoprimePrefix (Primorial v) k).card)
    (Finset.mem_range.mpr hk)
  change k-a*(PrimePrefix35.CoprimePrefix (Primorial v) k).card≤AffineDefect v U a at hh
  omega

theorem actual_affine_row (m v U a k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤v) (hk : k<U) :
    k≤a*(PrimePrefix35.CoprimePrefix m k).card+AffineDefect v U a := by
  have hh := actual_primorial_prefix_compression m v k hm hw
  exact (primorial_affine_row v U a k hk).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left a hh) _)

theorem weighted_affine_payment (B a e K h C A : ℕ) (hB : 0<B)
    (hsquare : h^2≤C) (hcover : K≤C+h) (hK : B^2≤K)
    (hrow : C≤a*A+e*h) : (B-e)*K≤a*(B+1)*A := by
  have hp := PrimePrefix35.square_trace_payment B K h C (C+h)
    hB hsquare le_rfl hcover hK
  have hBK : B*K≤(B+1)*C := by nlinarith [Nat.mul_le_mul_left B hcover]
  by_cases hsmall : B≤e
  · simp [Nat.sub_eq_zero_of_le hsmall]
  have hsub : B-e+e=B := Nat.sub_add_cancel (by omega)
  have hrowB := Nat.mul_le_mul_left B hrow
  have hpay := Nat.mul_le_mul_left e hp.1
  have hCA : (B-e)*C≤a*B*A := by nlinarith only [hrowB,hpay,hsub]
  have hleft := Nat.mul_le_mul_left (B-e) hBK
  have hright := Nat.mul_le_mul_left (B+1) hCA
  have hfinal : B*((B-e)*K)≤B*(a*(B+1)*A) := by
    nlinarith only [hleft,hright]
  exact (mul_le_mul_iff_right₀ hB).mp hfinal

theorem actual_minimal_trace_affine (c : ℤ) (M m K v U a B : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hB : 0<B) (hK : B^2≤K)
    (hdiv : ∀ d∈I,d∣M) (htrace : ∀ d∈I,P d)
    (hminimal : ∀ d∈I,∀ e,0<e → e∣d → P e → d≤e)
    (hend : ∀ d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀ d∈I,k d<U) (homega : m.primeFactors.card≤v)
    (hunion : K≤(I.biUnion (fun d=>Prefix c d (k d))).card) :
    (B-AffineDefect v U a)*K≤a*(B+1)*
      (∑ d∈I,(PrimePrefix35.CoprimePrefix m (k d)).card) := by
  have hsquare := TraceAntichain35.minimal_trace_index_square hM I P k hdiv htrace hminimal
    (fun d hd=>endpoint_quotient_le (Nat.pos_of_dvd_of_pos (hdiv d hd) hM) (hend d hd))
  have hcover := hunion.trans (prefix_union_card c I k)
  have hs := Finset.sum_le_sum (fun d hd=>actual_affine_row m v U a (k d) hm homega (hfinite d hd))
  simp only [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hs
  apply weighted_affine_payment B a (AffineDefect v U a) K I.card (∑ d∈I,k d) _
    hB hsquare hcover hK
  nlinarith only [hs]


theorem actual_short_prefix_affine {S : Finset ℤ} {c p : ℤ} {K v U a B : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 2*K≤(S∩Finset.Icc c p).card)
    (htail : 4*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : (WitnessNeighbors S c p).card≤K)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤U)
    (homega : ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hsize : B^2≤K) :
    2*(B-AffineDefect v U a)*K^2≤a*(B+1)*(StructuralPairs c S).card := by
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
  have hrow : ∀ z∈Z,(B-AffineDefect v U a)*K≤a*(B+1)*
      (∑ d∈I,(PrimePrefix35.CoprimePrefix
        ((p-c).natAbs*(z-c).natAbs) (k d)).card) := by
    intro z hz
    obtain ⟨hzT,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    have hpabs : 0<(p-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hzabs : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    apply actual_minimal_trace_affine c (p-c).natAbs
      ((p-c).natAbs*(z-c).natAbs) K v U a B I (fun d=>Segment c p d⊆S) k hpabs
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
  have hpay := Nat.mul_le_mul_left (a*(B+1)) hcode
  have hp := Nat.mul_le_mul_right ((B-AffineDefect v U a)*K) hZ
  nlinarith only [hs,hpay,hp]

theorem actual_no_long_right_prefix_affine {S : Finset ℤ} {c : ℤ} {K v U a B : ℕ}
    (hc : c∈S) (hK : 0<K) (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hno : ∀ d : ℕ, 0<d → ¬Prefix c d K⊆S)
    (ha : 4≤a) (hB : 0<B) (hfinite : K≤U)
    (homega : ∀ p∈S, c<p → ∀ z∈S, p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hsize : B^2≤K) :
    2*(B-AffineDefect v U a)*K^2≤a*(B+1)*(StructuralPairs c S).card := by
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
    exact actual_short_prefix_affine hcp hc hpS hK hhead htail hneigh hno
      hB hfinite (homega p hpS hcp) hsize
  · have hneigh : ∀ p∈M,K≤(WitnessNeighbors S c p).card := by
      intro p hp
      by_contra hn
      exact hsome ⟨p,hp,by omega⟩
    have hlo := Finset.sum_le_sum hneigh
    simp only [Finset.sum_const,nsmul_eq_mul,hMcard] at hlo
    have hhi := actual_neighbors_double_count S M c
    have hsquare : K^2≤2*(StructuralPairs c S).card := by nlinarith only [hlo,hhi]
    have hsub : B-AffineDefect v U a≤B := Nat.sub_le _ _
    have hcoef : 4*(B-AffineDefect v U a)≤a*(B+1) := by nlinarith
    have hmul := Nat.mul_le_mul_left (2*(B-AffineDefect v U a)) hsquare
    have hpay := Nat.mul_le_mul_right (StructuralPairs c S).card hcoef
    nlinarith only [hmul,hpay]

def AffineCoefficient (v U a B : ℕ) : ℝ :=
  ((a*(B+1):ℕ):ℝ)/((2*(B-AffineDefect v U a):ℕ):ℝ)

theorem affine_coefficient_nonneg (v U a B : ℕ) : 0≤AffineCoefficient v U a B := by
  exact div_nonneg (by positivity) (by positivity)

theorem affine_payment_to_real {K v U a B W : ℕ} (hB : AffineDefect v U a<B)
    (h : 2*(B-AffineDefect v U a)*K^2≤a*(B+1)*W) :
    (K:ℝ)^2≤AffineCoefficient v U a B*W := by
  have hd : (0:ℝ)<((2*(B-AffineDefect v U a):ℕ):ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0<2) (Nat.sub_pos_of_lt hB)
  have hh : (((2*(B-AffineDefect v U a):ℕ):ℝ))*(K:ℝ)^2≤
      ((a*(B+1):ℕ):ℝ)*W := by exact_mod_cast h
  unfold AffineCoefficient
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hh]

theorem actual_far_right_affine {S : Finset ℤ} {c : ℤ} {K U a w v B : ℕ} (R : ℝ)
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (ha : 4≤a) (hB : AffineDefect v U a<B) (hBsquare : B^2≤K) (hfinite : K≤U)
    (hR0 : 0≤R)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hproduct : ∀ p∈S,c<p → ∀ z∈S,p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (AffineCoefficient v U a B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  by_cases hex : ∃ d : ℕ,0<d ∧ Prefix c d K⊆S
  · have hh := actual_far_long_real_bound R hlarge hfar hR0 hex homega hratio hlong
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have hb : 0<B := by omega
    have hh := actual_no_long_right_prefix_affine hc hK hright
      (fun d hd hpre=>hex ⟨d,hd,hpre⟩) ha hb hfinite hproduct hBsquare
    have hr := affine_payment_to_real hB hh
    exact hr.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

theorem actual_far_affine {S : Finset ℤ} {c : ℤ} {K U a w v B : ℕ} (R : ℝ)
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (ha : 4≤a) (hB : AffineDefect v U a<B) (hBsquare : B^2≤K) (hfinite : K≤U)
    (hR0 : 0≤R)
    (homega : ∀ z∈S,z≠c → (z-c).natAbs.primeFactors.card≤w)
    (hratio : ∀ z∈S,z≠c → ((z-c).natAbs:ℝ)≤R*Nat.totient (z-c).natAbs)
    (hproduct : ∀ p∈S,p≠c → ∀ z∈S,z≠c →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (AffineCoefficient v U a B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  by_cases hright : 8*K≤(S.filter (fun x=>c<x)).card
  · exact actual_far_right_affine R hc hK hlarge hfar hright ha hB hBsquare hfinite
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
  have hh := actual_far_right_affine R hc' hK hlarge' hfar' hright' ha hB hBsquare
    hfinite hR0 hω hρ hv hlong
  simpa only [structural_reflect_card] using hh

theorem actual_far_ground_affine {N K U a w v B : ℕ} {S : Finset ℤ} {c : ℤ} (R : ℝ)
    (hS : S⊆Ground N) (hc : c∈S) (hK : 0<K)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (ha : 4≤a) (hB : AffineDefect v U a<B) (hBsquare : B^2≤K) (hfinite : K≤U)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (K:ℝ)^2≤max (AffineCoefficient v U a B) (LongCoefficient K w R)*(StructuralPairs c S).card := by
  apply actual_far_affine R hc hK hlarge hfar ha hB hBsquare hfinite hR0 _ _ _ hlong
  · intro z hz _
    exact homega _ (actual_anchor_distance_le hS hc hz)
  · intro z hz _
    exact hratio _ (actual_anchor_distance_le hS hc hz)
  · intro p hp _ z hz _
    apply hproduct
    simpa only [pow_two] using Nat.mul_le_mul
      (actual_anchor_distance_le hS hc hp) (actual_anchor_distance_le hS hc hz)


theorem actual_one_band_affine {N K U a w v B : ℕ} {F : Finset (Finset ℤ)} (R : ℝ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hhigh : ∀ S∈F,S.card≤32*K)
    (ha : 4≤a) (hB : AffineDefect v U a<B) (hBsquare : B^2≤K) (hfinite : K≤U)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ)) :
    (F.card:ℝ)*(15*K)≤261*(N:ℝ)^2+
      480*max (AffineCoefficient v U a B) (LongCoefficient K w R)*N.choose 2 := by
  let C := max (AffineCoefficient v U a B) (LongCoefficient K w R)
  have hC : 0≤C := (affine_coefficient_nonneg v U a B).trans (le_max_left _ _)
  have hf := actual_real_far_band_budget hC hlegal hK hlow hhigh (by
    intro S hSF hfar c hc
    exact actual_far_ground_affine R (hlegal.1 S hSF) hc hK (hlow S hSF) hfar
      ha hB hBsquare hfinite hR0 homega hratio hproduct hlong)
  have hn := actual_near_members_band_budget hlegal hK hbad hlow
    (fun S hS=>(hhigh S hS).trans (by omega : 32*K≤64*K))
  have hnR : (15*(K:ℝ))*((NearMembers K F).card:ℝ)≤261*(N:ℝ)^2 := by exact_mod_cast hn
  have hp := Finset.card_filter_add_card_filter_not (s:=F) (HasNearAPCore K)
  change (NearMembers K F).card+(FarMembers K F).card=F.card at hp
  have hpR : ((NearMembers K F).card:ℝ)+((FarMembers K F).card:ℝ)=F.card := by exact_mod_cast hp
  change _≤261*(N:ℝ)^2+480*C*N.choose 2
  nlinarith only [hf,hnR,hpR]

theorem actual_large_from_affine_arithmetic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (U a B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ))
    (ha : ∀ j<N+1,4≤a j) (hB : ∀ j<N+1,AffineDefect v (U j) (a j)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤U j) :
    15*(K:ℝ)*F.card≤522*(N:ℝ)^2+480*(N.choose 2:ℝ)*
      (∑ j∈Finset.range (N+1),max (AffineCoefficient v (U j) (a j) (B j)) (LongCoefficient (2^j*K) w R)*(1/2:ℝ)^j) := by
  apply actual_large_weighted_sum N K F
    (fun j=>max (AffineCoefficient v (U j) (a j) (B j)) (LongCoefficient (2^j*K) w R)) hK hlegal.1 hlow
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
  have hh := actual_one_band_affine R hLG (by positivity)
    (fun S hS=>hbad S (hGF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2)
    (ha j hj) (hB j hj) (hBsquare j hj) (hfinite j hj)
    hR0 homega hratio hproduct hlongj
  dsimp only [G] at hh
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  nlinarith only [hh]

theorem actual_large_affine_quadratic (N K w v : ℕ) (F : Finset (Finset ℤ))
    (R : ℝ) (U a B : ℕ→ℕ)
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card)
    (hR0 : 0≤R) (homega : ∀ m≤N,m.primeFactors.card≤w)
    (hratio : ∀ m≤N,(m:ℝ)≤R*Nat.totient m)
    (hproduct : ∀ m≤N^2,m.primeFactors.card≤v)
    (hlong : R*(2^w:ℕ)<(K:ℝ))
    (ha : ∀ j<N+1,4≤a j) (hB : ∀ j<N+1,AffineDefect v (U j) (a j)<B j)
    (hBsquare : ∀ j<N+1,(B j)^2≤2^j*K) (hfinite : ∀ j<N+1,2^j*K≤U j) :
    (F.card:ℝ)*K≤(174/5+16*(∑ j∈Finset.range (N+1),
      max (AffineCoefficient v (U j) (a j) (B j)) (LongCoefficient (2^j*K) w R)*(1/2:ℝ)^j))*(N:ℝ)^2 := by
  have hh := actual_large_from_affine_arithmetic N K w v F R U a B hlegal hK hbad hlow
    hR0 homega hratio hproduct hlong ha hB hBsquare hfinite
  apply weighted_quadratic_payment N K F.card _ _ hh
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg ((affine_coefficient_nonneg v (U j) (a j) (B j)).trans (le_max_left _ _))
    (pow_nonneg (by norm_num) _)

#print axioms primorial_affine_row
#print axioms actual_affine_row
#print axioms weighted_affine_payment
#print axioms actual_minimal_trace_affine
#print axioms actual_short_prefix_affine
#print axioms actual_no_long_right_prefix_affine
#print axioms affine_coefficient_nonneg
#print axioms affine_payment_to_real
#print axioms actual_far_right_affine
#print axioms actual_far_affine
#print axioms actual_far_ground_affine
#print axioms actual_one_band_affine
#print axioms actual_large_from_affine_arithmetic
#print axioms actual_large_affine_quadratic
end
end JSP233.AffineTrace46
