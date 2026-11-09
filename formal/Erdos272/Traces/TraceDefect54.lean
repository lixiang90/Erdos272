module

public import Erdos272.Certificates.FiniteSeventeen52
public import Erdos272.Counting.GraphDegree51
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual finite seventeen-prime tail layers, common-root prefix union,
quotient-antichain odd slots and joint minimal-trace resource payments. -/
namespace JSP233.TraceDefect54
open StarCompletion APGeometry LongTerminal35 PrimePrefix35 PrimorialPrefix46
open PrimorialValue47 AffineWitness47 AffinePayment47 FiniteSeventeen52
open TraceAntichain35 DyadicTraceSupply36 TraceWitnessCodes36 FarCore37
open GraphDegree51 FarAssembly37 Reflect37
open scoped Classical BigOperators
noncomputable section
set_option maxRecDepth 20000
set_option maxHeartbeats 0

def Layers : Finset (ℕ×ℕ) :=
  {(61,2),(67,4),(71,6),(73,2),(79,4),(83,2),(97,4),
   (101,6),(103,4),(107,4),(127,4),(131,2),(137,4),(149,4)}

def Envelope (k : ℕ) : ℕ := ∑u∈Layers,if k<u.1 then u.2 else 0

def Extra : Finset ℕ := {61,67,3721,4087,4331,4453,4489,4757}

theorem layers_data :
    (∀u∈Layers,u.1≤149 ∧ Odd u.1) ∧
      (∑u∈Layers,(u.1/2)*u.2)=2570 := by decide

theorem extra_data : Extra.card=8 ∧ ∀x∈Extra,
    1≤x ∧ x≤4757 ∧ Nat.Coprime x 1922760350154212639070 ∧
      ¬Nat.Coprime x 7858321551080267055879090 := by decide

theorem prefix17_eight_extra {k : ℕ} (hk : 4757≤k) :
    (CoprimePrefix (Primorial 19) k).card+8≤(CoprimePrefix (Primorial 17) k).card := by
  have hs : Extra∪CoprimePrefix (Primorial 19) k⊆CoprimePrefix (Primorial 17) k := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · obtain ⟨hx1,hxu,hcop,_⟩ := extra_data.2 x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hx1,hxu.trans hk⟩,by rwa [actual_primorial17]⟩
    · exact prefix19_subset17 k hx
  have hd : Disjoint Extra (CoprimePrefix (Primorial 19) k) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hh := (Finset.mem_filter.mp hy).2
    rw [actual_primorial19] at hh
    exact (extra_data.2 x hx).2.2.2 hh
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,extra_data.1] at hc
  omega

theorem prefix17_zero_after4757 {k : ℕ} (hk : k≤2^19) (hlo : 4757≤k) :
    k≤8*(CoprimePrefix (Primorial 17) k).card := by
  have hh := AffinePayment47.actual_primorial19_prefix k hk
  have he := prefix17_eight_extra hlo
  omega

theorem finite_small_profile : ∀k∈Finset.range 149,
    k≤8*(CoprimePrefix 1922760350154212639070 k).card+Envelope k := by decide

theorem prefix149_count : 19≤(CoprimePrefix 1922760350154212639070 149).card := by decide

theorem middle_block : BlockEstimate 1922760350154212639070 8 149 4608 611 3 :=
  estimate_of_valid _ _ _ _ _ [2, 8, 14, 18, 24, 30, 32, 42, 44, 48, 50, 62, 74, 78, 80, 84, 90, 92, 102, 108, 114, 120, 122, 128, 132, 134, 144, 158, 162, 164, 168, 182, 188, 198, 200, 204, 210, 218, 224, 230, 234, 240, 248, 252, 260, 270, 272, 282, 284, 290, 294, 300, 308, 312, 314, 318, 330, 338, 342, 350, 354, 360, 372, 374, 392, 398, 408, 414, 420, 422, 428, 438, 444, 450, 452, 458, 464, 468, 470, 482, 492, 494, 498, 504, 510, 512, 524, 528, 534, 542, 552, 560, 570, 578, 584, 590, 594, 602, 608, 612, 620, 624, 638, 648, 660, 662, 672, 674, 678, 680, 690, 704, 708, 710, 714, 728, 732, 734, 738, 758, 762, 770, 780, 788, 792, 798, 804, 818, 822, 828, 834, 842, 848, 860, 864, 870, 872, 882, 884, 890, 900, 902, 912, 914, 920, 938, 942, 944, 948, 954, 960, 968, 974, 980, 1002, 1004, 1014, 1022, 1032, 1038, 1044, 1052, 1064, 1068, 1074, 1080, 1082, 1088, 1100, 1110, 1128, 1130, 1134, 1140, 1142, 1148, 1152, 1154, 1158, 1170, 1172, 1178, 1212, 1218, 1224, 1232, 1250, 1260, 1274, 1278, 1280, 1284, 1290, 1298, 1302, 1304, 1310, 1322, 1332, 1334, 1338, 1340, 1344, 1350, 1362, 1374, 1382, 1394, 1400, 1404, 1410, 1418, 1422, 1430, 1434, 1448, 1452, 1458, 1460, 1464, 1470, 1472, 1478, 1488, 1508, 1514, 1518, 1520, 1544, 1548, 1550, 1560, 1572, 1574, 1584, 1592, 1598, 1604, 1610, 1628, 1634, 1638, 1640, 1652, 1662, 1674, 1682, 1698, 1712, 1718, 1722, 1724, 1728, 1730, 1740, 1752, 1758, 1764, 1782, 1784, 1800, 1802, 1824, 1830, 1838, 1844, 1848, 1850, 1854, 1862, 1868, 1878, 1880, 1890, 1904, 1914, 1920, 1932, 1934, 1938, 1940, 1950, 1962, 1964, 1980, 1982, 1988, 1992, 1994, 2004, 2012, 2030, 2054, 2058, 2064, 2072, 2088, 2090, 2094, 2102, 2118, 2120, 2124, 2132, 2138, 2144, 2148, 2160, 2162, 2184, 2190, 2192, 2198, 2202, 2208, 2222, 2228, 2232, 2234, 2240, 2244, 2250, 2262, 2268, 2274, 2288, 2292, 2298, 2310, 2318, 2324, 2328, 2354, 2372, 2382, 2390, 2394, 2400, 2402, 2408, 2430, 2442, 2444, 2460, 2468, 2472, 2484, 2498, 2508, 2510, 2514, 2522, 2528, 2534, 2538, 2540, 2544, 2550, 2558, 2562, 2564, 2570, 2580, 2582, 2592, 2600, 2604, 2618, 2628, 2640, 2642, 2648, 2652, 2654, 2670, 2684, 2688, 2694, 2702, 2708, 2712, 2730, 2738, 2748, 2754, 2760, 2768, 2778, 2790, 2804, 2808, 2814, 2820, 2822, 2850, 2852, 2862, 2870, 2874, 2888, 2892, 2900, 2912, 2918, 2930, 2934, 2940, 2960, 2970, 2972, 2988, 3014, 3018, 3020, 3032, 3038, 3042, 3054, 3060, 3068, 3072, 3080, 3102, 3104, 3108, 3110, 3122, 3150, 3152, 3158, 3164, 3170, 3174, 3180, 3182, 3194, 3198, 3210, 3212, 3222, 3224, 3240, 3242, 3258, 3264, 3284, 3300, 3308, 3312, 3314, 3318, 3320, 3342, 3350, 3362, 3368, 3378, 3380, 3384, 3390, 3392, 3398, 3408, 3410, 3422, 3432, 3434, 3444, 3458, 3464, 3468, 3474, 3482, 3488, 3494, 3510, 3522, 3524, 3528, 3542, 3548, 3552, 3560, 3570, 3572, 3578, 3584, 3590, 3612, 3618, 3620, 3630, 3644, 3648, 3654, 3672, 3674, 3684, 3698, 3702, 3704, 3714, 3728, 3732, 3740, 3758, 3762, 3768, 3770, 3774, 3780, 3782, 3794, 3798, 3818, 3840, 3852, 3854, 3858, 3864, 3870, 3872, 3878, 3900, 3902, 3908, 3924, 3930, 3938, 3942, 3944, 3950, 3962, 3978, 3980, 3984, 3990, 4004, 4008, 4010, 4028, 4052, 4062, 4068, 4070, 4080, 4082, 4092, 4094, 4104, 4110, 4112, 4122, 4124, 4134, 4140, 4148, 4178, 4182, 4188, 4190, 4200, 4208, 4214, 4224, 4242, 4248, 4260, 4272, 4274, 4292, 4298, 4302, 4304, 4308, 4314, 4332, 4334, 4340, 4344, 4358, 4364, 4368, 4370, 4374, 4398, 4400, 4412, 4418, 4434, 4442, 4448, 4454, 4472, 4488, 4490, 4494, 4500, 4502, 4508, 4514, 4524, 4530, 4542, 4554, 4572, 4574, 4580, 4584, 4602, 4608] (by decide)

theorem prefix17_zero_from149 {k : ℕ} (hlo : 149≤k) (hhi : k≤4757) :
    k≤8*(CoprimePrefix (Primorial 17) k).card := by
  have hh := middle_block.2 (k-149) (by omega)
  have hc := prefix149_count
  have he := block_count_add 1922760350154212639070 0 149 (k-149)
  simp only [Nat.zero_add,Nat.add_sub_of_le hlo,block_zero_prefix] at he
  rw [actual_primorial17]
  omega

theorem actual_primorial17_envelope (k : ℕ) (hk : k≤2^19) :
    k≤8*(CoprimePrefix (Primorial 17) k).card+Envelope k := by
  by_cases hlo:149≤k
  · by_cases hhi:k≤4757
    · exact (prefix17_zero_from149 hlo hhi).trans (Nat.le_add_right _ _)
    · exact (prefix17_zero_after4757 hk (by omega)).trans (Nat.le_add_right _ _)
  · have hh := finite_small_profile k (Finset.mem_range.mpr (by omega))
    rwa [←actual_primorial17] at hh

theorem actual_positive_modulus_envelope (m k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤17) (hk : k<2^19) :
    k≤8*(CoprimePrefix m k).card+Envelope k := by
  have hc := actual_primorial_prefix_compression m 17 k hm hw
  exact (actual_primorial17_envelope k hk.le).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hc) _)


theorem prefix_erase_root_card (c : ℤ) (d k : ℕ) : ((Prefix c d k).erase c).card≤k := by
  have hs : (Prefix c d k).erase c⊆(Finset.Icc 1 k).image (fun i:ℕ=>c+(i:ℤ)*(d:ℤ)) := by
    intro x hx
    obtain ⟨hxc,hxP⟩ := Finset.mem_erase.mp hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hxP
    refine Finset.mem_image.mpr ⟨i,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
    · by_contra hn
      have hi0:i=0 := by omega
      simp only [hi0,Nat.cast_zero,zero_mul,add_zero] at hxc
      exact hxc rfl
    · have hh:=Finset.mem_range.mp hi;omega
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (by simp))

theorem prefix_union_shared_root (c : ℤ) (I : Finset ℕ) (k : ℕ→ℕ) :
    (I.biUnion (fun d=>Prefix c d (k d))).card≤1+∑d∈I,k d := by
  let U := I.biUnion (fun d=>(Prefix c d (k d)).erase c)
  have hs : I.biUnion (fun d=>Prefix c d (k d))⊆insert c U := by
    intro x hx
    by_cases hxc:x=c
    · exact Finset.mem_insert.mpr (Or.inl hxc)
    · obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨d,hd,Finset.mem_erase.mpr ⟨hxc,hxd⟩⟩))
  have hb : U.card≤∑d∈I,k d := (Finset.card_biUnion_le).trans
    (Finset.sum_le_sum (fun d _=>prefix_erase_root_card c d (k d)))
  have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le c U)
  omega

theorem actual_odd_quotient_injective {M : ℕ} (hM : 0<M) (I : Finset ℕ)
    (hdiv : ∀d∈I,d∣M) (hanti : ∀a∈I,∀b∈I,a∣b→a=b) :
    Set.InjOn (fun d=>OddPart (M/d)) (I:Set ℕ) := by
  have hqa : ∀a∈I.image (fun d=>M/d),∀b∈I.image (fun d=>M/d),a∣b→a=b := by
    intro a ha b hb hab
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hb
    have heq := hanti e he d hd (quotient_dvd_reverse hM (hdiv d hd) (hdiv e he) hab)
    rw [heq]
  have ho := oddPart_injective_on_divisor_antichain (I.image (fun d=>M/d)) hqa
  have hq := quotient_injective_on_divisors hM I hdiv
  intro d hd e he hde
  apply hq hd he
  exact ho (Finset.mem_image.mpr ⟨d,hd,rfl⟩) (Finset.mem_image.mpr ⟨e,he,rfl⟩) hde

theorem actual_layer_slots {M : ℕ} (hM : 0<M) (I : Finset ℕ) (k : ℕ→ℕ)
    (hdiv : ∀d∈I,d∣M) (hanti : ∀a∈I,∀b∈I,a∣b→a=b)
    (hindex : ∀d∈I,M/d≤k d) (t : ℕ) :
    (I.filter (fun d=>k d<t)).card≤t/2 := by
  let A := I.filter (fun d=>k d<t)
  have hsub:A⊆I := Finset.filter_subset _ _
  have hop : ∀d∈I,Odd (OddPart (M/d)) := by
    intro d hd
    apply oddPart_odd
    exact Nat.div_pos (Nat.le_of_dvd hM (hdiv d hd)) (Nat.pos_of_dvd_of_pos (hdiv d hd) hM)
  have hm : Set.MapsTo (fun d=>OddPart (M/d)/2) (A:Set ℕ) (Finset.range (t/2):Set ℕ) := by
    intro d hd
    have ho:=Nat.odd_iff.mp (hop d (hsub hd))
    have hlt := (oddPart_le (M/d)).trans (hindex d (hsub hd))
    have hh := (Finset.mem_filter.mp hd).2
    apply Finset.mem_range.mpr
    change OddPart (M/d)/2<t/2
    omega
  have hi : Set.InjOn (fun d=>OddPart (M/d)/2) (A:Set ℕ) := by
    intro d hd e he hde
    have hdo:=Nat.odd_iff.mp (hop d (hsub hd))
    have heo:=Nat.odd_iff.mp (hop e (hsub he))
    apply actual_odd_quotient_injective hM I hdiv hanti (hsub hd) (hsub he)
    change OddPart (M/d)/2=OddPart (M/e)/2 at hde
    change OddPart (M/d)=OddPart (M/e)
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hm hi

theorem actual_envelope_sum2570 {M : ℕ} (hM : 0<M) (I : Finset ℕ) (k : ℕ→ℕ)
    (hdiv : ∀d∈I,d∣M) (hanti : ∀a∈I,∀b∈I,a∣b→a=b)
    (hindex : ∀d∈I,M/d≤k d) : (∑d∈I,Envelope (k d))≤2570 := by
  have he : (∑d∈I,Envelope (k d))=∑u∈Layers,(I.filter (fun d=>k d<u.1)).card*u.2 := by
    unfold Envelope
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
  rw [he]
  calc
    _≤∑u∈Layers,(u.1/2)*u.2 := Finset.sum_le_sum (fun u _hu=>Nat.mul_le_mul_right _
      (actual_layer_slots hM I k hdiv hanti hindex u.1))
    _=2570 := layers_data.2

theorem actual_minimal_trace_joint (c : ℤ) (M m K : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hdiv : ∀d∈I,d∣M) (htrace : ∀d∈I,P d)
    (hminimal : ∀d∈I,∀e,0<e→e∣d→P e→d≤e)
    (hend : ∀d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀d∈I,k d<2^19) (homega : m.primeFactors.card≤17)
    (hunion : K≤(I.biUnion (fun d=>Prefix c d (k d))).card) :
    K≤8*(∑d∈I,(CoprimePrefix m (k d)).card)+2571 := by
  have hanti : ∀a∈I,∀b∈I,a∣b→a=b := by
    intro a ha b hb hab
    exact Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos (hdiv b hb) hM) hab)
      (hminimal b hb a (Nat.pos_of_dvd_of_pos (hdiv a ha) hM) hab (htrace a ha))
  have hindex : ∀d∈I,M/d≤k d := fun d hd=>endpoint_quotient_le
    (Nat.pos_of_dvd_of_pos (hdiv d hd) hM) (hend d hd)
  have he := actual_envelope_sum2570 hM I k hdiv hanti hindex
  have hc := hunion.trans (prefix_union_shared_root c I k)
  have hr := Finset.sum_le_sum (fun d hd=>actual_positive_modulus_envelope m (k d) hm homega (hfinite d hd))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hr
  omega

theorem actual_short_prefix_joint {S : Finset ℤ} {c p : ℤ} {K : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : (WitnessNeighbors S c p).card+K≤(S∩Finset.Icc c p).card)
    (htail : 3*K≤(S.filter (fun z=>p≤z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d K⊆S) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤17) :
    (K-2571)*K≤8*(StructuralPairs c S).card := by
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
  have hZ : K≤Z.card := by
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
  have hrow : ∀z∈Z,K-2571≤8*(∑d∈I,(CoprimePrefix
      ((p-c).natAbs*(z-c).natAbs) (k d)).card) := by
    intro z hz
    obtain ⟨hzT,_⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzS,hpz⟩ := Finset.mem_filter.mp hzT
    have hpabs : 0<(p-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hzabs : 0<(z-c).natAbs := Int.natAbs_pos.mpr (by omega)
    have hh := actual_minimal_trace_joint c (p-c).natAbs
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
  have hp := Nat.mul_le_mul_right (K-2571) hZ
  nlinarith only [hs,hpay,hp]

theorem actual_fractional_short_prefix_joint {S : Finset ℤ} {c p : ℤ} {K : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 7*K≤5*(S∩Finset.Icc c p).card)
    (htail : 3*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : 5*(WitnessNeighbors S c p).card≤2*K)
    (hno : ∀d:ℕ,0<d→¬Prefix c d K⊆S) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤17) :
    (K-2571)*K≤8*(StructuralPairs c S).card := by
  exact actual_short_prefix_joint hcp hc hp hK (by omega) htail hno hfinite homega

theorem actual_tenth_middle_block {T : Finset ℤ} {k : ℕ} (hcard : 47*k≤T.card) :
    ∃M:Finset ℤ,M⊆T ∧ M.card=3*k ∧ ∀p∈M,
      14*k≤(T.filter (fun x=>x≤p)).card ∧ 30*k≤(T.filter (fun x=>p≤x)).card := by
  let f := T.orderEmbOfFin rfl
  let mid : Fin (3*k)→ℤ := fun i=>f ⟨14*k+i.val,by omega⟩
  have hinj : Function.Injective mid := by
    intro i j hij
    have hv := congrArg Fin.val (f.injective hij)
    apply Fin.ext
    change 14*k+i.val=14*k+j.val at hv
    omega
  refine ⟨Finset.univ.image mid,?_,?_,?_⟩
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    exact T.orderEmbOfFin_mem rfl _
  · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    constructor
    · let lo : Fin (14*k)→ℤ := fun j=>f ⟨j.val,by omega⟩
      have hlo : Function.Injective lo := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change a.val=b.val at hh
        exact hh
      have hmaps : Set.MapsTo lo ((Finset.univ:Finset (Fin (14*k))):Set (Fin (14*k))) (T.filter (fun x=>x≤mid i):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change j.val≤14*k+i.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn lo hmaps hlo.injOn
    · let hi : Fin (30*k)→ℤ := fun j=>f ⟨17*k+j.val,by omega⟩
      have hhi : Function.Injective hi := by
        intro a b hab
        have hh := congrArg Fin.val (f.injective hab)
        apply Fin.ext
        change 17*k+a.val=17*k+b.val at hh
        omega
      have hmaps : Set.MapsTo hi ((Finset.univ:Finset (Fin (30*k))):Set (Fin (30*k))) (T.filter (fun x=>mid i≤x):Set ℤ) := by
        intro j _
        refine Finset.mem_filter.mpr ⟨T.orderEmbOfFin_mem rfl _,?_⟩
        apply f.monotone
        change 14*k+i.val≤17*k+j.val
        omega
      simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card_of_injOn hi hmaps hhi.injOn

theorem actual_tenth_high_numerator {S M : Finset ℤ} {c : ℤ} {k : ℕ}
    (hcard : M.card=3*k) (hhigh : ∀p∈M,4*k<(WitnessNeighbors S c p).card) :
    3*(10*k)^2+18*(10*k)≤40*(StructuralPairs c S).card := by
  have hh := actual_high_neighbor_sum hhigh
  rw [hcard] at hh
  have hr : ((3*k:ℕ):ℝ)*((4*k:ℕ)+1)≤(StructuralPairs c S).card+((3*k).choose 2:ℝ) := by
    exact_mod_cast hh
  rw [Nat.cast_choose_two] at hr
  have hp : 3*((10*k:ℕ):ℝ)^2+18*((10*k:ℕ):ℝ)≤40*(StructuralPairs c S).card := by
    push_cast at hr ⊢
    nlinarith only [hr]
  exact_mod_cast hp

theorem actual_tenth_right_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hright : 47*k≤(S.filter (fun z=>c<z)).card) :
    (3*(10*k)^2+18*(10*k)≤40*(StructuralPairs c S).card) ∨
      ∃p∈S,c<p ∧ 14*k≤(S∩Finset.Icc c p).card ∧
        30*k≤(S.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors S c p).card≤4*k := by
  obtain ⟨M,hMT,hMcard,hmiddle⟩ := actual_tenth_middle_block hright
  by_cases hex : ∃p∈M,(WitnessNeighbors S c p).card≤4*k
  · obtain ⟨p,hpM,hdegree⟩ := hex
    obtain ⟨hpS,hcp⟩ := Finset.mem_filter.mp (hMT hpM)
    have hhead : 14*k≤(S∩Finset.Icc c p).card := (hmiddle p hpM).1.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hzp⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzS,hcz⟩ := Finset.mem_filter.mp hzT
        exact Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨hcz.le,hzp⟩⟩))
    have htail : 30*k≤(S.filter (fun z=>p≤z)).card := (hmiddle p hpM).2.trans
      (Finset.card_le_card (by
        intro z hz
        obtain ⟨hzT,hpz⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hzT).1,hpz⟩))
    exact Or.inr ⟨p,hpS,hcp,hhead,htail,hdegree⟩
  · exact Or.inl (actual_tenth_high_numerator hMcard
      (fun p hp=>by by_contra hn;exact hex ⟨p,hp,by omega⟩))

theorem actual_tenth_member_dichotomy {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hsize : 94*k+1≤S.card) :
    (3*(10*k)^2+18*(10*k)≤40*(StructuralPairs c S).card) ∨
      ∃T:Finset ℤ,∃r:ℤ,((T=S ∧ r=c) ∨ (T=Reflect S ∧ r= -c)) ∧
        ∃p∈T,r<p ∧ 14*k≤(T∩Finset.Icc r p).card ∧
          30*k≤(T.filter (fun z=>p≤z)).card ∧ (WitnessNeighbors T r p).card≤4*k := by
  by_cases hright : 47*k≤(S.filter (fun z=>c<z)).card
  · rcases actual_tenth_right_dichotomy hright with hh|hlow
    · exact Or.inl hh
    · exact Or.inr ⟨S,c,Or.inl ⟨rfl,rfl⟩,hlow⟩
  · have hleft : 47*k≤(S.filter (fun z=>z<c)).card := by
      have hh := actual_side_card_partition hc
      omega
    have hright' : 47*k≤((Reflect S).filter (fun z=> -c<z)).card := by
      simpa only [reflect_right_card] using hleft
    rcases actual_tenth_right_dichotomy hright' with hh|hlow
    · exact Or.inl (by simpa only [structural_reflect_card] using hh)
    · exact Or.inr ⟨Reflect S,-c,Or.inr ⟨rfl,rfl⟩,hlow⟩

theorem actual_tenth_right_short_joint {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hk : 0<k) (hright : 47*k≤(S.filter (fun z=>c<z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (10*k)⊆S) (hfinite : 10*k≤2^19)
    (homega : ∀p∈S,c<p→∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤17) :
    (3*(10*k)^2+18*(10*k)≤40*(StructuralPairs c S).card) ∨
      (10*k-2571)*(10*k)≤8*(StructuralPairs c S).card := by
  rcases actual_tenth_right_dichotomy hright with hhigh|hlow
  · exact Or.inl hhigh
  · obtain ⟨p,hp,hcp,hhead,htail,hdegree⟩ := hlow
    exact Or.inr (actual_fractional_short_prefix_joint hcp hc hp (by omega)
      (by omega) (by omega) (by omega) hno hfinite (homega p hp hcp))

#print axioms layers_data
#print axioms extra_data
#print axioms prefix17_eight_extra
#print axioms prefix17_zero_after4757
#print axioms finite_small_profile
#print axioms prefix149_count
#print axioms middle_block
#print axioms prefix17_zero_from149
#print axioms actual_primorial17_envelope
#print axioms actual_positive_modulus_envelope
#print axioms prefix_erase_root_card
#print axioms prefix_union_shared_root
#print axioms actual_odd_quotient_injective
#print axioms actual_layer_slots
#print axioms actual_envelope_sum2570
#print axioms actual_minimal_trace_joint
#print axioms actual_short_prefix_joint
#print axioms actual_fractional_short_prefix_joint
#print axioms actual_tenth_middle_block
#print axioms actual_tenth_high_numerator
#print axioms actual_tenth_right_dichotomy
#print axioms actual_tenth_member_dichotomy
#print axioms actual_tenth_right_short_joint
end
end JSP233.TraceDefect54
