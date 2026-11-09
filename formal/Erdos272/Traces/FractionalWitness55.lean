module

public import Erdos272.Certificates.FiniteSixteen54
public import Erdos272.Core.NearHelly54
public import Erdos272.Arithmetic.PrimorialRatio39
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace JSP233.FractionalWitness55
open StarCompletion APGeometry LongTerminal35 PrimePrefix35 PrimorialPrefix46
open PrimorialValue47 FiniteSeventeen52 TraceDefect54 FiniteSixteen54
open TraceAntichain35 DyadicTraceSupply36 TraceWitnessCodes36 FarCore37
open GraphDegree51 FarAssembly37 Reflect37 NearAP36 NearHelly54 BandAggregation34
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_short_prefix_with_outside16 {S : Finset ℤ} {c p : ℤ} {K U : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : (WitnessNeighbors S c p).card+K≤(S∩Finset.Icc c p).card)
    (htail : 2*K+U≤(S.filter (fun z=>p≤z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d K⊆S) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤16) :
    (K-2177)*U≤8*(StructuralPairs c S).card := by
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
  have hZ : U≤Z.card := by
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
  have hrow : ∀z∈Z,K-2177≤8*(∑d∈I,(CoprimePrefix
      ((p-c).natAbs*(z-c).natAbs) (k d)).card) := by
    intro z hz
    obtain ⟨hzT,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    have hpabs : 0<(p-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hzabs : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hh := actual_minimal_trace_joint16 c (p-c).natAbs
      ((p-c).natAbs*(z-c).natAbs) K I (fun d=>Segment c p d⊆S) k hpabs
      (Nat.mul_pos hpabs hzabs) hdiv htrace hmin hend
      (fun d hd=>(hshort d (hIJ hd)).trans_le hfinite) (homega z hzS hpz) hIlow
    omega
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
  have hpay := Nat.mul_le_mul_left 8 hcode
  have hp := Nat.mul_le_mul_right (K-2177) hZ
  nlinarith only [hs,hpay,hp]

theorem actual_fifteenth_middle_block {T : Finset ℤ} {k : ℕ} (hcard : 75*k≤T.card) :
    ∃M:Finset ℤ,M⊆T ∧ M.card=4*k ∧ ∀p∈M,
      23*k≤(T.filter (fun x=>x≤p)).card ∧ 48*k≤(T.filter (fun x=>p≤x)).card := by
  let f := T.orderEmbOfFin rfl
  let mid : Fin (4*k)→ℤ := fun i=>f ⟨23*k+i.val,by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hv := congrArg Fin.val (f.injective hij)
    apply Fin.ext
    change 23*k+i.val=23*k+j.val at hv
    omega
  refine ⟨Finset.univ.image mid,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (23*k)→ℤ := fun j=>f ⟨j.val,by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change a.val=b.val at hh
        exact hh
      have hmaps : Set.MapsTo lo ((Finset.univ:Finset (Fin (23*k))):Set (Fin (23*k))) (T.filter (fun x=>x≤mid i):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change j.val≤23*k+i.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (48*k)→ℤ := fun j=>f ⟨27*k+j.val,by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 27*k+a.val=27*k+b.val at hh
        omega
      have hmaps : Set.MapsTo hi ((Finset.univ:Finset (Fin (48*k))):Set (Fin (48*k))) (T.filter (fun x=>mid i≤x):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change 23*k+i.val≤27*k+j.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem actual_fifteenth_high_numerator {S M : Finset ℤ} {c : ℤ} {k : ℕ}
    (hcard : M.card=4*k) (hhigh : ∀p∈M,8*k<(WitnessNeighbors S c p).card) :
    24*k^2+6*k≤(StructuralPairs c S).card := by
  have hh := actual_high_neighbor_sum hhigh
  rw [hcard] at hh
  have hr : ((4*k:ℕ):ℝ)*((8*k:ℕ)+1)≤(StructuralPairs c S).card+((4*k).choose 2:ℝ) := by
    exact_mod_cast hh
  rw [Nat.cast_choose_two] at hr
  have hp : 24*(k:ℝ)^2+6*(k:ℝ)≤(StructuralPairs c S).card := by
    push_cast at hr ⊢
    nlinarith only [hr]
  exact_mod_cast hp

theorem actual_fifteenth_right_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hright : 75*k≤(S.filter (fun z=>c<z)).card) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      ∃p∈S,c<p ∧ 23*k≤(S∩Finset.Icc c p).card ∧
        48*k≤(S.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors S c p).card≤8*k := by
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_fifteenth_middle_block hright
  by_cases hex : ∃p∈M,(WitnessNeighbors S c p).card≤8*k
  · obtain ⟨p,hpM,hdegree⟩ := hex
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 23*k≤(S∩Finset.Icc c p).card := (hmiddle p hpM).1.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzS,hcz⟩ := Finset.mem_filter.mp hzT
        exact Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨hcz.le,hzp⟩⟩))
    have htail : 48*k≤(S.filter (fun z=>p≤z)).card := (hmiddle p hpM).2.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hpz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzT).1,hpz⟩))
    exact Or.inr ⟨p,hpS,hcp,hhead,htail,hdegree⟩
  · exact Or.inl (actual_fifteenth_high_numerator hMcard
      (fun p hp=>by by_contra hn;exact hex ⟨p,hp,by omega⟩))

theorem actual_fifteenth_member_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hsize : 150*k+1≤S.card) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      ∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃p∈T,r<p ∧ 23*k≤(T∩Finset.Icc r p).card ∧
          48*k≤(T.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors T r p).card≤8*k := by
  by_cases hright : 75*k≤(S.filter (fun z=>c<z)).card
  · rcases actual_fifteenth_right_dichotomy hright with hh|hlow
    · exact Or.inl hh
    · exact Or.inr ⟨S,c,Or.inl ⟨rfl,rfl⟩,hlow⟩
  · have hleft : 75*k≤(S.filter (fun z=>z<c)).card := by
      have hh := actual_side_card_partition hc
      omega
    have hright' : 75*k≤((Reflect S).filter (fun z=> -c<z)).card := by
      simpa only [reflect_right_card] using hleft
    rcases actual_fifteenth_right_dichotomy hright' with hh|hlow
    · exact Or.inl (by simpa only [structural_reflect_card] using hh)
    · exact Or.inr ⟨Reflect S,-c,Or.inr ⟨rfl,rfl⟩,hlow⟩

theorem actual_fifteenth_right_joint16 {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hk : 0<k) (hright : 75*k≤(S.filter (fun z=>c<z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (15*k)⊆S) (hfinite : 15*k≤2^19)
    (homega : ∀p∈S,c<p→∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤16) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  rcases actual_fifteenth_right_dichotomy hright with hhigh|hlow
  · exact Or.inl hhigh
  · obtain ⟨p,hp,hcp,hhead,htail,hdegree⟩ := hlow
    exact Or.inr (actual_short_prefix_with_outside16 (U:=18*k) hcp hc hp (by omega)
      (by omega) (by omega) hno hfinite (homega p hp hcp))

theorem actual_general_dyadic_near_budget {N K A b : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, (A+1)*(2^(level S)*K)+1≤S.card)
    (hhigh : ∀ S∈F, S.card≤b*(2^(level S)*K))
    (hnear : ∀ S∈F, HasNearAPCore (2^(level S)*K) S) :
    (A:ℝ)*K*F.card≤6*((b:ℝ)+1)*(N:ℝ)^2 := by
  let n := ∑ S∈F, (level S+1)
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀ j, family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀ S∈F, level S∈Finset.range n := by
    intro S hS
    have hh := Finset.single_le_sum (fun T (_hT:T∈F)=>Nat.zero_le (level T+1)) hS
    exact Finset.mem_range.mpr (by dsimp [n];omega)
  have hpart : F.card=∑ j∈Finset.range n, (family j).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hrow : ∀ j∈Finset.range n,
      (A:ℝ)*(K:ℝ)*(family j).card≤(3*((b:ℝ)+1))*(N:ℝ)^2*(1/2:ℝ)^j := by
    intro j _hj
    have hlegalj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := actual_nearAP_band_budget (A:=A) (b:=b) hlegalj
      (by positivity : 0<2^j*K) hA
      (fun S hS=>hbad S (hfamily j hS)) (by
        intro S hS
        have hs := hlow S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs) (by
        intro S hS
        have hs := hhigh S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs) (by
        intro S hS
        have hs := hnear S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs)
    have hhR : (A:ℝ)*((2:ℝ)^j*K)*(family j).card≤(3*((b:ℝ)+1))*(N:ℝ)^2 := by exact_mod_cast hh
    have hp : 0<(2:ℝ)^j := by positivity
    have hd := div_le_div_of_nonneg_right hhR hp.le
    have he : ((A:ℝ)*((2:ℝ)^j*K)*(family j).card)/(2:ℝ)^j=(A:ℝ)*K*(family j).card := by field_simp
    have hr : ((3*((b:ℝ)+1))*(N:ℝ)^2)/(2:ℝ)^j=(3*((b:ℝ)+1))*(N:ℝ)^2*(1/2:ℝ)^j := by
      rw [one_div,inv_pow,div_eq_mul_inv]
    rw [he,hr] at hd
    exact hd
  have hs := Finset.sum_le_sum hrow
  simp only [←Finset.mul_sum] at hs
  have hpartR : (F.card:ℝ)=∑ j∈Finset.range n, ((family j).card:ℝ) := by exact_mod_cast hpart
  rw [←hpartR] at hs
  have ht := mul_le_mul_of_nonneg_left (dyadic_sum_le_two n)
    (show (0:ℝ)≤(3*((b:ℝ)+1))*(N:ℝ)^2 by positivity)
  nlinarith only [hs,ht]

theorem actual_scaled_fifteenth_near_budget {N k : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hk : 0<k)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,150*(2^(level S)*k)+1≤S.card)
    (hhigh : ∀S∈F,S.card≤300*(2^(level S)*k))
    (hnear : ∀S∈F,HasNearAPCore (50*(2^(level S)*k)) S) :
    (F.card:ℝ)*(50*k)≤21*(N:ℝ)^2 := by
  have he : ∀j:ℕ,2^j*(50*k)=50*(2^j*k) := by intro j;ring
  have hh := actual_general_dyadic_near_budget (A:=2) (b:=6) (K:=50*k) level hlegal
    (by positivity) (by decide) hbad (by
      intro S hS
      have hs := hlow S hS
      simpa only [he,show 2+1=3 by norm_num,show 3*(50*(2^(level S)*k))=150*(2^(level S)*k) by ring] using hs) (by
      intro S hS
      have hs := hhigh S hS
      simpa only [he,show 6*(50*(2^(level S)*k))=300*(2^(level S)*k) by ring] using hs) (by
      intro S hS
      simpa only [he] using hnear S hS)
  push_cast at hh ⊢
  nlinarith only [hh]

theorem primorial_models_agree (v : ℕ) :
    PrimorialRatio39.Primorial v=PrimorialPrefix46.Primorial v := by
  unfold PrimorialRatio39.Primorial PrimorialRatio39.PrimeAt
  unfold PrimorialPrefix46.Primorial PrimorialPrefix46.FirstPrimes
  rw [Finset.prod_image]
  exact (Nat.nth_injective Nat.infinite_setOf_prime).injOn

theorem actual_product_omega16_below2pow35 {N u v : ℕ} (hN : N<2^35)
    (hu : 0<u) (hv : 0<v) (huN : u≤N) (hvN : v≤N) : (u*v).primeFactors.card≤16 := by
  apply PrimorialRatio39.actual_omega_of_lt_primorial (u*v) 16 (Nat.mul_pos hu hv)
  rw [primorial_models_agree,show 16+1=17 by norm_num,actual_primorial17]
  exact (Nat.mul_le_mul huN hvN).trans_lt ((Nat.mul_self_lt_mul_self hN).trans_le (by norm_num))

theorem actual_ground_distance_bound {N : ℕ} {S : Finset ℤ} (hS : S⊆Ground N)
    {x y : ℤ} (hx : x∈S) (hy : y∈S) : (y-x).natAbs≤N := by
  have hxG := hS hx
  have hyG := hS hy
  obtain ⟨i,hi,hix⟩ := Finset.mem_image.mp hxG
  obtain ⟨j,hj,hjy⟩ := Finset.mem_image.mp hyG
  have hiN := Finset.mem_range.mp hi
  have hjN := Finset.mem_range.mp hj
  have hab : |y-x|≤(N:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  have hc : ((y-x).natAbs:ℤ)≤N := by simpa only [Int.natCast_natAbs] using hab
  exact_mod_cast hc

theorem actual_reflected_span_bound {N : ℕ} {S : Finset ℤ}
    (hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N) :
    ∀x∈Reflect S,∀y∈Reflect S,(y-x).natAbs≤N := by
  intro x hx y hy
  have hh := hspan (-x) ((mem_reflect S x).mp hx) (-y) ((mem_reflect S y).mp hy)
  have he : -y- -x= -(y-x) := by ring
  simpa only [he,Int.natAbs_neg] using hh

theorem actual_span_fifteenth_right_joint {N k : ℕ} {S : Finset ℤ} {c : ℤ}
    (hN : N<2^35) (hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N)
    (hc : c∈S) (hk : 0<k) (hright : 75*k≤(S.filter (fun z=>c<z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (15*k)⊆S) (hfinite : 15*k≤2^19) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  apply actual_fifteenth_right_joint16 hc hk hright hno hfinite
  intro p hp hcp z hz hpz
  exact actual_product_omega16_below2pow35 hN
    (Int.natAbs_pos.mpr (by omega)) (Int.natAbs_pos.mpr (by omega))
    (hspan c hc p hp) (hspan c hc z hz)

theorem actual_ground_fifteenth_right_joint {N k : ℕ} {S : Finset ℤ} {c : ℤ}
    (hN : N<2^35) (hS : S⊆Ground N)
    (hc : c∈S) (hk : 0<k) (hright : 75*k≤(S.filter (fun z=>c<z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (15*k)⊆S) (hfinite : 15*k≤2^19) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  exact actual_span_fifteenth_right_joint hN (fun x hx y hy=>actual_ground_distance_bound hS hx hy)
    hc hk hright hno hfinite

theorem actual_ground_fifteenth_member_joint {N k : ℕ} {S : Finset ℤ} {c : ℤ}
    (hN : N<2^35) (hS : S⊆Ground N) (hc : c∈S) (hk : 0<k)
    (hsize : 150*k+1≤S.card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (15*k)⊆S)
    (hnoref : ∀d:ℕ,0<d→¬Prefix (-c) d (15*k)⊆Reflect S) (hfinite : 15*k≤2^19) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  by_cases hr : 75*k≤(S.filter (fun z=>c<z)).card
  · exact actual_ground_fifteenth_right_joint hN hS hc hk hr hno hfinite
  · have hl : 75*k≤(S.filter (fun z=>z<c)).card := by
      have hh := actual_side_card_partition hc
      omega
    have hr' : 75*k≤((Reflect S).filter (fun z=> -c<z)).card := by simpa only [reflect_right_card] using hl
    have hc' : -c∈Reflect S := by simpa only [mem_reflect,neg_neg] using hc
    have hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N := fun x hx y hy=>actual_ground_distance_bound hS hx hy
    have hh := actual_span_fifteenth_right_joint hN (actual_reflected_span_bound hspan) hc' hk hr' hnoref hfinite
    simpa only [structural_reflect_card] using hh

theorem actual_scaled_fifteenth_approximation_budget {N k : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hk : 0<k)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,150*(2^(level S)*k)+1≤S.card)
    (hhigh : ∀S∈F,S.card≤300*(2^(level S)*k))
    (happrox : ∀S∈F,∃U:Finset ℤ,U⊆S ∧ IsAP U ∧ (S\U).card<50*(2^(level S)*k)) :
    (F.card:ℝ)*(50*k)≤21*(N:ℝ)^2 := by
  apply actual_scaled_fifteenth_near_budget level hlegal hk hbad hlow hhigh
  intro S hS
  obtain ⟨U,hUS,hAP,hsmall⟩ := happrox S hS
  have hl : (2+1)*(50*(2^(level S)*k))+1≤S.card := by
    nlinarith only [hlow S hS]
  exact near_core_of_actual_approximation (by positivity) (by decide) hl hUS hAP hsmall

theorem actual_span_weak_head_short {N k : ℕ} {S : Finset ℤ} {c p : ℤ}
    (hN : N<2^35) (hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N)
    (hc : c∈S) (hp : p∈S) (hcp : c<p) (hk : 0<k)
    (hhead : 23*k≤(S∩Finset.Icc c p).card)
    (htail : 48*k≤(S.filter (fun z=>p≤z)).card)
    (hdegree : (WitnessNeighbors S c p).card≤8*k)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (15*k)⊆S) (hfinite : 15*k≤2^19) :
    (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  apply actual_short_prefix_with_outside16 (U:=18*k) hcp hc hp (by omega)
    (by omega) (by omega) hno hfinite
  intro z hz hpz
  exact actual_product_omega16_below2pow35 hN
    (Int.natAbs_pos.mpr (by omega)) (Int.natAbs_pos.mpr (by omega))
    (hspan c hc p hp) (hspan c hc z hz)

theorem actual_ground_member_long_or_private {N k : ℕ} {S : Finset ℤ} {c : ℤ}
    (hN : N<2^35) (hS : S⊆Ground N) (hc : c∈S) (hk : 0<k)
    (hsize : 150*k+1≤S.card) (hfinite : 15*k≤2^19) :
    (24*k^2+6*k≤(StructuralPairs c S).card) ∨
      (∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃d:ℕ,0<d ∧ Prefix r d (15*k)⊆T) ∨
      (15*k-2177)*(18*k)≤8*(StructuralPairs c S).card := by
  rcases actual_fifteenth_member_dichotomy hc hsize with hh|hlow
  · exact Or.inl hh
  · obtain ⟨T,r,hor,p,hp,hrp,hhead,htail,hdegree⟩ := hlow
    by_cases hlong : ∃d:ℕ,0<d ∧ Prefix r d (15*k)⊆T
    · exact Or.inr (Or.inl ⟨T,r,hor,hlong⟩)
    · have hno : ∀d:ℕ,0<d→¬Prefix r d (15*k)⊆T := by
        intro d hd hsub
        exact hlong ⟨d,hd,hsub⟩
      have hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N := fun x hx y hy=>actual_ground_distance_bound hS hx hy
      have hspanT : ∀x∈T,∀y∈T,(y-x).natAbs≤N := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hspan
        · exact actual_reflected_span_bound hspan
      have hroot : r∈T := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hc
        · simpa only [mem_reflect,neg_neg] using hc
      have hh := actual_span_weak_head_short hN hspanT hroot hp hrp hk hhead htail hdegree hno hfinite
      have hcard : (StructuralPairs r T).card=(StructuralPairs c S).card := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rfl
        · exact structural_reflect_card c S
      exact Or.inr (Or.inr (by simpa only [hcard] using hh))

theorem actual_thirtieth_middle_block {T : Finset ℤ} {k : ℕ} (hcard : 165*k≤T.card) :
    ∃M:Finset ℤ,M⊆T ∧ M.card=9*k ∧ ∀p∈M,
      48*k≤(T.filter (fun x=>x≤p)).card ∧ 108*k≤(T.filter (fun x=>p≤x)).card := by
  let f := T.orderEmbOfFin rfl
  let mid : Fin (9*k)→ℤ := fun i=>f ⟨48*k+i.val,by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hv := congrArg Fin.val (f.injective hij)
    apply Fin.ext
    change 48*k+i.val=48*k+j.val at hv
    omega
  refine ⟨Finset.univ.image mid,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (48*k)→ℤ := fun j=>f ⟨j.val,by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change a.val=b.val at hh
        exact hh
      have hmaps : Set.MapsTo lo ((Finset.univ:Finset (Fin (48*k))):Set (Fin (48*k))) (T.filter (fun x=>x≤mid i):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change j.val≤48*k+i.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (108*k)→ℤ := fun j=>f ⟨57*k+j.val,by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 57*k+a.val=57*k+b.val at hh
        omega
      have hmaps : Set.MapsTo hi ((Finset.univ:Finset (Fin (108*k))):Set (Fin (108*k))) (T.filter (fun x=>mid i≤x):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change 48*k+i.val≤57*k+j.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem actual_thirtieth_high_numerator {S M : Finset ℤ} {c : ℤ} {k : ℕ}
    (hcard : M.card=9*k) (hhigh : ∀p∈M,18*k<(WitnessNeighbors S c p).card) :
    243*k^2+27*k≤2*(StructuralPairs c S).card := by
  have hh := actual_high_neighbor_sum hhigh
  rw [hcard] at hh
  have hr : ((9*k:ℕ):ℝ)*((18*k:ℕ)+1)≤(StructuralPairs c S).card+((9*k).choose 2:ℝ) := by
    exact_mod_cast hh
  rw [Nat.cast_choose_two] at hr
  have hp : 243*(k:ℝ)^2+27*(k:ℝ)≤2*(StructuralPairs c S).card := by
    push_cast at hr ⊢
    nlinarith only [hr]
  exact_mod_cast hp

theorem actual_thirtieth_right_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hright : 165*k≤(S.filter (fun z=>c<z)).card) :
    (243*k^2+27*k≤2*(StructuralPairs c S).card) ∨
      ∃p∈S,c<p ∧ 48*k≤(S∩Finset.Icc c p).card ∧
        108*k≤(S.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors S c p).card≤18*k := by
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_thirtieth_middle_block hright
  by_cases hex : ∃p∈M,(WitnessNeighbors S c p).card≤18*k
  · obtain ⟨p,hpM,hdegree⟩ := hex
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 48*k≤(S∩Finset.Icc c p).card := (hmiddle p hpM).1.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzS,hcz⟩ := Finset.mem_filter.mp hzT
        exact Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨hcz.le,hzp⟩⟩))
    have htail : 108*k≤(S.filter (fun z=>p≤z)).card := (hmiddle p hpM).2.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hpz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzT).1,hpz⟩))
    exact Or.inr ⟨p,hpS,hcp,hhead,htail,hdegree⟩
  · exact Or.inl (actual_thirtieth_high_numerator hMcard
      (fun p hp=>by by_contra hn;exact hex ⟨p,hp,by omega⟩))

theorem actual_thirtieth_member_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hsize : 330*k+1≤S.card) :
    (243*k^2+27*k≤2*(StructuralPairs c S).card) ∨
      ∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃p∈T,r<p ∧ 48*k≤(T∩Finset.Icc r p).card ∧
          108*k≤(T.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors T r p).card≤18*k := by
  by_cases hright : 165*k≤(S.filter (fun z=>c<z)).card
  · rcases actual_thirtieth_right_dichotomy hright with hh|hlow
    · exact Or.inl hh
    · exact Or.inr ⟨S,c,Or.inl ⟨rfl,rfl⟩,hlow⟩
  · have hleft : 165*k≤(S.filter (fun z=>z<c)).card := by
      have hh := actual_side_card_partition hc
      omega
    have hright' : 165*k≤((Reflect S).filter (fun z=> -c<z)).card := by
      simpa only [reflect_right_card] using hleft
    rcases actual_thirtieth_right_dichotomy hright' with hh|hlow
    · exact Or.inl (by simpa only [structural_reflect_card] using hh)
    · exact Or.inr ⟨Reflect S,-c,Or.inr ⟨rfl,rfl⟩,hlow⟩

theorem actual_span_thirtieth_weak_head_short {N k : ℕ} {S : Finset ℤ} {c p : ℤ}
    (hN : N<2^35) (hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N)
    (hc : c∈S) (hp : p∈S) (hcp : c<p) (hk : 0<k)
    (hhead : 48*k≤(S∩Finset.Icc c p).card)
    (htail : 108*k≤(S.filter (fun z=>p≤z)).card)
    (hdegree : (WitnessNeighbors S c p).card≤18*k)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (30*k)⊆S) (hfinite : 30*k≤2^19) :
    (30*k-2177)*(48*k)≤8*(StructuralPairs c S).card := by
  apply actual_short_prefix_with_outside16 (U:=48*k) hcp hc hp (by omega)
    (by omega) (by omega) hno hfinite
  intro z hz hpz
  exact actual_product_omega16_below2pow35 hN
    (Int.natAbs_pos.mpr (by omega)) (Int.natAbs_pos.mpr (by omega))
    (hspan c hc p hp) (hspan c hc z hz)

theorem actual_ground_thirtieth_long_or_private {N k : ℕ} {S : Finset ℤ} {c : ℤ}
    (hN : N<2^35) (hS : S⊆Ground N) (hc : c∈S) (hk : 0<k)
    (hsize : 330*k+1≤S.card) (hfinite : 30*k≤2^19) :
    (243*k^2+27*k≤2*(StructuralPairs c S).card) ∨
      (∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃d:ℕ,0<d ∧ Prefix r d (30*k)⊆T) ∨
      (30*k-2177)*(48*k)≤8*(StructuralPairs c S).card := by
  rcases actual_thirtieth_member_dichotomy hc hsize with hh|hlow
  · exact Or.inl hh
  · obtain ⟨T,r,hor,p,hp,hrp,hhead,htail,hdegree⟩ := hlow
    by_cases hlong : ∃d:ℕ,0<d ∧ Prefix r d (30*k)⊆T
    · exact Or.inr (Or.inl ⟨T,r,hor,hlong⟩)
    · have hno : ∀d:ℕ,0<d→¬Prefix r d (30*k)⊆T := by
        intro d hd hsub
        exact hlong ⟨d,hd,hsub⟩
      have hspan : ∀x∈S,∀y∈S,(y-x).natAbs≤N := fun x hx y hy=>actual_ground_distance_bound hS hx hy
      have hspanT : ∀x∈T,∀y∈T,(y-x).natAbs≤N := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hspan
        · exact actual_reflected_span_bound hspan
      have hroot : r∈T := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hc
        · simpa only [mem_reflect,neg_neg] using hc
      have hh := actual_span_thirtieth_weak_head_short hN hspanT hroot hp hrp hk hhead htail hdegree hno hfinite
      have hcard : (StructuralPairs r T).card=(StructuralPairs c S).card := by
        rcases hor with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rfl
        · exact structural_reflect_card c S
      exact Or.inr (Or.inr (by simpa only [hcard] using hh))

theorem actual_scaled_thirtieth_near_budget {N k : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hk : 0<k)
    (hbad : ∀S∈F,¬IsAP S)
    (hlow : ∀S∈F,330*(2^(level S)*k)+1≤S.card)
    (hhigh : ∀S∈F,S.card≤660*(2^(level S)*k))
    (hnear : ∀S∈F,HasNearAPCore (110*(2^(level S)*k)) S) :
    (F.card:ℝ)*(110*k)≤21*(N:ℝ)^2 := by
  have he : ∀j:ℕ,2^j*(110*k)=110*(2^j*k) := by intro j;ring
  have hh := actual_general_dyadic_near_budget (A:=2) (b:=6) (K:=110*k) level hlegal
    (by positivity) (by decide) hbad (by
      intro S hS
      have hs := hlow S hS
      simpa only [he,show 2+1=3 by norm_num,show 3*(110*(2^(level S)*k))=330*(2^(level S)*k) by ring] using hs) (by
      intro S hS
      have hs := hhigh S hS
      simpa only [he,show 6*(110*(2^(level S)*k))=660*(2^(level S)*k) by ring] using hs) (by
      intro S hS
      simpa only [he] using hnear S hS)
  push_cast at hh ⊢
  nlinarith only [hh]

#print axioms actual_short_prefix_with_outside16
#print axioms actual_fifteenth_middle_block
#print axioms actual_fifteenth_high_numerator
#print axioms actual_fifteenth_right_dichotomy
#print axioms actual_fifteenth_member_dichotomy
#print axioms actual_fifteenth_right_joint16
#print axioms actual_general_dyadic_near_budget
#print axioms actual_scaled_fifteenth_near_budget
#print axioms primorial_models_agree
#print axioms actual_product_omega16_below2pow35
#print axioms actual_ground_distance_bound
#print axioms actual_reflected_span_bound
#print axioms actual_span_fifteenth_right_joint
#print axioms actual_ground_fifteenth_right_joint
#print axioms actual_ground_fifteenth_member_joint
#print axioms actual_scaled_fifteenth_approximation_budget
#print axioms actual_span_weak_head_short
#print axioms actual_ground_member_long_or_private
#print axioms actual_thirtieth_middle_block
#print axioms actual_thirtieth_high_numerator
#print axioms actual_thirtieth_right_dichotomy
#print axioms actual_thirtieth_member_dichotomy
#print axioms actual_span_thirtieth_weak_head_short
#print axioms actual_ground_thirtieth_long_or_private
#print axioms actual_scaled_thirtieth_near_budget
end
end JSP233.FractionalWitness55
