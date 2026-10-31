import Erdos272.Resources.FarCore37
import Erdos272.Geometry.Reflect37
import Erdos272.Resources.FarWitness36

/-! Complete actual far witness geometry at an arbitrary anchor and its
integration into the true near/far band and dyadic large-family budgets.
The public endpoints take arithmetic omega/length conditions, not structural
witness counts or an assumed band budget. -/
namespace JSP233.FarAssembly37
open StarCompletion LongTerminal35 TraceWitnessCodes36 NearAP36
open FarCore37 Reflect37 FarWitness36 BandAggregation34
open scoped Classical BigOperators
noncomputable section

theorem actual_side_card_partition {S : Finset ℤ} {c : ℤ} (hc : c∈S) :
    (S.filter (fun x=>x<c)).card+(S.filter (fun x=>c<x)).card+1=S.card := by
  have hu : S.filter (fun x=>x<c)∪S.filter (fun x=>c<x)=S.erase c := by
    ext x
    simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_erase]
    constructor
    · rintro (⟨hx,hxc⟩|⟨hx,hcx⟩)
      · exact ⟨by omega,hx⟩
      · exact ⟨by omega,hx⟩
    · rintro ⟨hne,hx⟩
      by_cases hxc : x<c
      · exact Or.inl ⟨hx,hxc⟩
      · exact Or.inr ⟨hx,by omega⟩
  have hd : Disjoint (S.filter (fun x=>x<c)) (S.filter (fun x=>c<x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hh := (Finset.mem_filter.mp hx).2
    have ht := (Finset.mem_filter.mp hy).2
    omega
  have hh := Finset.card_union_of_disjoint hd
  rw [hu,Finset.card_erase_of_mem hc] at hh
  have hp := Finset.card_pos.mpr (show S.Nonempty from ⟨c,hc⟩)
  omega

theorem actual_non_near_reflect {S : Finset ℤ} {K : ℕ}
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S) :
    ¬HasNearAPCore K (Reflect S) := by
  have hrem := far_reflect (non_near_actual_AP_remainder hlarge hfar)
  rintro ⟨P,hPS,_,hsmall⟩
  have hh := hrem P hPS.1 hPS.2.1
  omega

theorem actual_far_witness_bound {S : Finset ℤ} {c : ℤ} {K ell w₁ w₂ : ℕ}
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 1≤ell) (hfinite : K≤2^ell)
    (homega₁ : ∀ z∈S, z≠c → (z-c).natAbs.primeFactors.card≤w₁)
    (homega₂ : ∀ p∈S, p≠c → ∀ z∈S, z≠c →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*ell*(w₂+1))^2≤K) :
    K^2≤max (4*(w₁+1)) (2*ell)*(StructuralPairs c S).card := by
  by_cases hright : 8*K≤(S.filter (fun x=>c<x)).card
  · exact actual_far_right_witness_bound hc hK hlarge hfar hright hell hfinite homega₁
      (fun p hp hcp z hz hpz=>homega₂ p hp (by omega) z hz (by omega)) hlong hshort
  have hleft : 8*K≤(S.filter (fun x=>x<c)).card := by
    have hh := actual_side_card_partition hc
    omega
  have hc' : -c∈Reflect S := (mem_reflect S (-c)).mpr (by simpa using hc)
  have hlarge' : 16*K+1≤(Reflect S).card := by simpa only [reflect_card] using hlarge
  have hright' : 8*K≤((Reflect S).filter (fun x=> -c<x)).card := by
    simpa only [reflect_right_card] using hleft
  have hfar' := actual_non_near_reflect hlarge hfar
  have hω₁ : ∀ z∈Reflect S,z≠ -c → (z-(-c)).natAbs.primeFactors.card≤w₁ := by
    intro z hz hzc
    have hzs := (mem_reflect S z).mp hz
    have hh := homega₁ (-z) hzs (by omega)
    have he : -z-c=-(z-(-c)) := by ring
    simpa only [he,Int.natAbs_neg] using hh
  have hω₂ : ∀ p∈Reflect S,-c<p → ∀ z∈Reflect S,p≤z →
      ((p-(-c)).natAbs*(z-(-c)).natAbs).primeFactors.card≤w₂ := by
    intro p hp hcp z hz hpz
    have hh := homega₂ (-p) ((mem_reflect S p).mp hp) (by omega)
      (-z) ((mem_reflect S z).mp hz) (by omega)
    have he₁ : -p-c=-(p-(-c)) := by ring
    have he₂ : -z-c=-(z-(-c)) := by ring
    simpa only [he₁,he₂,Int.natAbs_neg] using hh
  have hh := actual_far_right_witness_bound hc' hK hlarge' hfar' hright' hell hfinite
    hω₁ hω₂ hlong hshort
  simpa only [structural_reflect_card] using hh

theorem actual_far_witness_bound_four_J {S : Finset ℤ} {c : ℤ} {K J ell w₁ w₂ : ℕ}
    (hc : c∈S) (hK : 0<K) (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 1≤ell) (hfinite : K≤2^ell) (hellJ : ell≤2*J) (hwJ : w₁+1≤J)
    (homega₁ : ∀ z∈S, z≠c → (z-c).natAbs.primeFactors.card≤w₁)
    (homega₂ : ∀ p∈S, p≠c → ∀ z∈S, z≠c →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*ell*(w₂+1))^2≤K) :
    K^2≤4*J*(StructuralPairs c S).card := by
  have hh := actual_far_witness_bound hc hK hlarge hfar hell hfinite homega₁ homega₂ hlong hshort
  have hcoef : max (4*(w₁+1)) (2*ell)≤4*J := max_le (by omega) (by omega)
  exact hh.trans (Nat.mul_le_mul_right _ hcoef)

theorem actual_anchor_distance_le {N : ℕ} {S : Finset ℤ} {c z : ℤ}
    (hS : S⊆Ground N) (hc : c∈S) (hz : z∈S) : (z-c).natAbs≤N := by
  obtain ⟨hc1,hcN⟩ := (mem_ground N c).mp (hS hc)
  obtain ⟨hz1,hzN⟩ := (mem_ground N z).mp (hS hz)
  have hh : |z-c|≤(N:ℤ) := abs_le.mpr ⟨by omega,by omega⟩
  exact_mod_cast (show ((z-c).natAbs:ℤ)≤N by simpa only [Int.natCast_natAbs] using hh)

theorem actual_far_ground_witness_bound {N K J ell w₁ w₂ : ℕ} {S : Finset ℤ} {c : ℤ}
    (hS : S⊆Ground N) (hc : c∈S) (hK : 0<K)
    (hlarge : 16*K+1≤S.card) (hfar : ¬HasNearAPCore K S)
    (hell : 1≤ell) (hfinite : K≤2^ell) (hellJ : ell≤2*J) (hwJ : w₁+1≤J)
    (homega₁ : ∀ m≤N,m.primeFactors.card≤w₁)
    (homega₂ : ∀ m≤N^2,m.primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*ell*(w₂+1))^2≤K) :
    K^2≤4*J*(StructuralPairs c S).card := by
  apply actual_far_witness_bound_four_J hc hK hlarge hfar hell hfinite hellJ hwJ _ _ hlong hshort
  · intro z hz _
    exact homega₁ _ (actual_anchor_distance_le hS hc hz)
  · intro p hp _ z hz _
    apply homega₂
    simpa only [pow_two] using Nat.mul_le_mul
      (actual_anchor_distance_le hS hc hp) (actual_anchor_distance_le hS hc hz)

theorem actual_one_band_from_arithmetic {N K J ell w₁ w₂ : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hhigh : ∀ S∈F,S.card≤32*K)
    (hell : 1≤ell) (hfinite : K≤2^ell) (hellJ : ell≤2*J) (hwJ : w₁+1≤J)
    (homega₁ : ∀ m≤N,m.primeFactors.card≤w₁)
    (homega₂ : ∀ m≤N^2,m.primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*ell*(w₂+1))^2≤K) :
    F.card*(15*K)≤261*N^2+1920*J*N.choose 2 := by
  apply actual_one_band_from_local_witnesses hlegal hK hbad hlow hhigh
  intro S hSF hfar c hc
  exact actual_far_ground_witness_bound (hlegal.1 S hSF) hc hK (hlow S hSF) hfar
    hell hfinite hellJ hwJ homega₁ homega₂ hlong hshort

theorem actual_large_from_arithmetic (N K J w₁ w₂ : ℕ) (F : Finset (Finset ℤ))
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F,¬IsAP S)
    (hlow : ∀ S∈F,16*K+1≤S.card) (hJ : 1≤J) (hN : N<2^J) (hwJ : w₁+1≤J)
    (homega₁ : ∀ m≤N,m.primeFactors.card≤w₁)
    (homega₂ : ∀ m≤N^2,m.primeFactors.card≤w₂)
    (hlong : 4*(w₁+1)*2^w₁≤K) (hshort : (2*J*(w₂+1))^2≤K) :
    15*K*F.card≤522*N^2+3840*J*N.choose 2 := by
  apply actual_large_from_local_far_witnesses N K J F hlegal hK hbad hlow
  intro j _ S hS hfar c hc
  have hSF := (Finset.mem_filter.mp hS).1
  have hband := (Finset.mem_filter.mp hS).2
  have hQK : K≤2^j*K := by
    have hp : 1≤(2:ℕ)^j := by
      have hh : 0<(2:ℕ)^j := by positivity
      omega
    simpa only [one_mul] using Nat.mul_le_mul_right K hp
  have hcard := (Finset.card_le_card (hlegal.1 S hSF)).trans_eq (ground_card N)
  have hfinite : 2^j*K≤2^J := by omega
  exact actual_far_ground_witness_bound (hlegal.1 S hSF) hc (by positivity)
    hband.1 hfar hJ hfinite (by omega) hwJ homega₁ homega₂
    (hlong.trans hQK) (hshort.trans hQK)

#print axioms actual_side_card_partition
#print axioms actual_non_near_reflect
#print axioms actual_far_witness_bound
#print axioms actual_far_witness_bound_four_J
#print axioms actual_anchor_distance_le
#print axioms actual_far_ground_witness_bound
#print axioms actual_one_band_from_arithmetic
#print axioms actual_large_from_arithmetic
end
end JSP233.FarAssembly37
