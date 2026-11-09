module

public import Erdos272.Traces.TraceDefect54
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace JSP233.FiniteSixteen54
open PrimePrefix35 PrimorialPrefix46 PrimorialValue47 FiniteSeventeen52 TraceDefect54
open StarCompletion APGeometry LongTerminal35 TraceWitnessCodes36 DyadicTraceSupply36 FarCore37 TraceAntichain35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Primes16 : Finset ℕ := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53}

theorem primes16_finite_data : Primes16.card=16 ∧
    (∀p∈Primes16,p.Prime ∧ p≤53) ∧
    (∀q∈Finset.range 54,q.Prime → q∈Primes16) := by decide

theorem actual_first_primes16 : FirstPrimes 16=Primes16 := by
  have hi : ∀p∈Primes16,∀q,q.Prime → q∉Primes16 → p≤q := by
    intro p hp q hq hqn
    have hp53 := (primes16_finite_data.2.1 p hp).2
    have hq53 : 53<q := by
      by_contra hn
      exact hqn (primes16_finite_data.2.2 q (Finset.mem_range.mpr (by omega)) hq)
    omega
  have hs : Primes16⊆FirstPrimes 16 := by
    intro p hp
    by_contra hpn
    have hn : ¬FirstPrimes 16⊆Primes16 := by
      intro hsub
      have heq := Finset.eq_of_subset_of_card_le hsub
        (by rw [first_primes_card,primes16_finite_data.1])
      exact hpn (by rw [heq];exact hp)
    obtain ⟨q,hq,hqn⟩ := Finset.not_subset.mp hn
    have hpq := hi p hp q (first_primes_prime 16 q hq) hqn
    have hqp := first_primes_initial 16 q p hq (primes16_finite_data.2.1 p hp).1 hpn
    exact hqn ((Nat.le_antisymm hpq hqp) ▸ hp)
  exact (Finset.eq_of_subset_of_card_le hs
    (by rw [first_primes_card,primes16_finite_data.1])).symm

theorem actual_primorial16 : Primorial 16=32589158477190044730 := by
  unfold Primorial
  rw [actual_first_primes16]
  norm_num [Primes16]

def Layers16 : Finset (ℕ×ℕ) := {(59,6),(61,2),(67,4),(71,6),(73,2),(79,4),(83,2),
  (97,4),(101,6),(103,4),(107,4),(127,4),(131,2)}

def Envelope16 (k : ℕ) : ℕ := ∑u∈Layers16,if k<u.1 then u.2 else 0

theorem layers16_data : (∑u∈Layers16,(u.1/2)*u.2)=2176 := by decide

theorem primorial16_dvd17 : Primorial 16∣Primorial 17 := by
  rw [actual_primorial16,actual_primorial17]
  exact ⟨59,by decide⟩

theorem prefix17_subset16 (k : ℕ) :
    CoprimePrefix (Primorial 17) k⊆CoprimePrefix (Primorial 16) k := by
  intro x hx
  obtain ⟨hi,hcop⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hi,hcop.of_dvd_right primorial16_dvd17⟩

theorem finite_small_profile16 : ∀k∈Finset.range 149,
    k≤8*(CoprimePrefix 32589158477190044730 k).card+Envelope16 k := by decide

theorem actual_primorial16_envelope (k : ℕ) (hk : k≤2^19) :
    k≤8*(CoprimePrefix (Primorial 16) k).card+Envelope16 k := by
  by_cases hlo:149≤k
  · have hh : k≤8*(CoprimePrefix (Primorial 17) k).card := by
      by_cases hhi:k≤4757
      · exact prefix17_zero_from149 hlo hhi
      · exact prefix17_zero_after4757 hk (by omega)
    exact (hh.trans (Nat.mul_le_mul_left 8 (Finset.card_le_card (prefix17_subset16 k)))).trans (Nat.le_add_right _ _)
  · have hh := finite_small_profile16 k (Finset.mem_range.mpr (by omega))
    rwa [←actual_primorial16] at hh

theorem actual_positive_modulus_envelope16 (m k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤16) (hk : k<2^19) :
    k≤8*(CoprimePrefix m k).card+Envelope16 k := by
  have hc := actual_primorial_prefix_compression m 16 k hm hw
  exact (actual_primorial16_envelope k hk.le).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hc) _)

theorem actual_envelope16_sum2176 {M : ℕ} (hM : 0<M) (I : Finset ℕ) (k : ℕ→ℕ)
    (hdiv : ∀d∈I,d∣M) (hanti : ∀a∈I,∀b∈I,a∣b→a=b)
    (hindex : ∀d∈I,M/d≤k d) : (∑d∈I,Envelope16 (k d))≤2176 := by
  have he : (∑d∈I,Envelope16 (k d))=∑u∈Layers16,(I.filter (fun d=>k d<u.1)).card*u.2 := by
    unfold Envelope16
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
  rw [he]
  calc
    _≤∑u∈Layers16,(u.1/2)*u.2 := Finset.sum_le_sum (fun u _hu=>Nat.mul_le_mul_right _
      (actual_layer_slots hM I k hdiv hanti hindex u.1))
    _=2176 := layers16_data

theorem actual_minimal_trace_joint16 (c : ℤ) (M m K : ℕ)
    (I : Finset ℕ) (P : ℕ→Prop) (k : ℕ→ℕ)
    (hM : 0<M) (hm : 0<m) (hdiv : ∀d∈I,d∣M) (htrace : ∀d∈I,P d)
    (hminimal : ∀d∈I,∀e,0<e→e∣d→P e→d≤e)
    (hend : ∀d∈I,c+(M:ℤ)∈Prefix c d (k d))
    (hfinite : ∀d∈I,k d<2^19) (homega : m.primeFactors.card≤16)
    (hunion : K≤(I.biUnion (fun d=>Prefix c d (k d))).card) :
    K≤8*(∑d∈I,(CoprimePrefix m (k d)).card)+2177 := by
  have hanti : ∀a∈I,∀b∈I,a∣b→a=b := by
    intro a ha b hb hab
    exact Nat.le_antisymm (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos (hdiv b hb) hM) hab)
      (hminimal b hb a (Nat.pos_of_dvd_of_pos (hdiv a ha) hM) hab (htrace a ha))
  have hindex : ∀d∈I,M/d≤k d := fun d hd=>endpoint_quotient_le
    (Nat.pos_of_dvd_of_pos (hdiv d hd) hM) (hend d hd)
  have he := actual_envelope16_sum2176 hM I k hdiv hanti hindex
  have hc := hunion.trans (prefix_union_shared_root c I k)
  have hr := Finset.sum_le_sum (fun d hd=>actual_positive_modulus_envelope16 m (k d) hm homega (hfinite d hd))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hr
  omega

theorem actual_short_prefix_joint16 {S : Finset ℤ} {c p : ℤ} {K : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : (WitnessNeighbors S c p).card+K≤(S∩Finset.Icc c p).card)
    (htail : 3*K≤(S.filter (fun z=>p≤z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d K⊆S) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤16) :
    (K-2177)*K≤8*(StructuralPairs c S).card := by
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

theorem actual_fractional_short_prefix_joint16 {S : Finset ℤ} {c p : ℤ} {K : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 7*K≤5*(S∩Finset.Icc c p).card)
    (htail : 3*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : 5*(WitnessNeighbors S c p).card≤2*K)
    (hno : ∀d:ℕ,0<d→¬Prefix c d K⊆S) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤16) :
    (K-2177)*K≤8*(StructuralPairs c S).card := by
  exact actual_short_prefix_joint16 hcp hc hp hK (by omega) htail hno hfinite homega

theorem actual_tenth_right_short_joint16 {S : Finset ℤ} {c : ℤ} {k : ℕ}
    (hc : c∈S) (hk : 0<k) (hright : 47*k≤(S.filter (fun z=>c<z)).card)
    (hno : ∀d:ℕ,0<d→¬Prefix c d (10*k)⊆S) (hfinite : 10*k≤2^19)
    (homega : ∀p∈S,c<p→∀z∈S,p≤z→((p-c).natAbs*(z-c).natAbs).primeFactors.card≤16) :
    (3*(10*k)^2+18*(10*k)≤40*(StructuralPairs c S).card) ∨
      (10*k-2177)*(10*k)≤8*(StructuralPairs c S).card := by
  rcases actual_tenth_right_dichotomy hright with hhigh|hlow
  · exact Or.inl hhigh
  · obtain ⟨p,hp,hcp,hhead,htail,hdegree⟩ := hlow
    exact Or.inr (actual_fractional_short_prefix_joint16 hcp hc hp (by omega)
      (by omega) (by omega) (by omega) hno hfinite (homega p hp hcp))

#print axioms primes16_finite_data
#print axioms actual_first_primes16
#print axioms actual_primorial16
#print axioms layers16_data
#print axioms primorial16_dvd17
#print axioms prefix17_subset16
#print axioms finite_small_profile16
#print axioms actual_primorial16_envelope
#print axioms actual_positive_modulus_envelope16
#print axioms actual_envelope16_sum2176
#print axioms actual_minimal_trace_joint16
#print axioms actual_short_prefix_joint16
#print axioms actual_fractional_short_prefix_joint16
#print axioms actual_tenth_right_short_joint16
end
end JSP233.FiniteSixteen54
