module

public import Erdos272.Counting.N67702.LowAPStep67702
public import Erdos272.Counting.EndpointDensity54

@[expose] public section

namespace JSP233.LowAPCount67702
open StarCompletion APGeometry APCount41 HarmonicAbel29 LowAPStep67702
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_AP_low_count {N L : ℕ} {F : Finset (Finset ℤ)}
    (hL : 1≤L) (hhalf : 2*L≤N) (hF : Legal (Ground N) F)
    (hAP : ∀ S∈F,IsAP S) (hlow : ∀ S∈F,Low S≤(L : ℤ)) :
    (F.card : ℝ)≤(329/200 : ℝ)*((L : ℝ)-1)*((N : ℝ)-L)+
      ((N : ℝ)-1)*Harmonic N+1 := by
  let A := F.filter (fun S=>2≤S.card)
  let B := F.filter (fun S=>¬2≤S.card)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hBF : B⊆F := Finset.filter_subset _ _
  have hAtwo : ∀ S∈A,2≤S.card := fun S hS=>(Finset.mem_filter.mp hS).2
  have hmaps : Set.MapsTo Step (A : Set (Finset ℤ)) (Finset.Icc 1 N) := by
    intro S hS
    exact Finset.mem_Icc.mpr
      ⟨(actual_step (hAP S (hAF hS))).1,actual_step_bound (hF.1 S (hAF hS))
        (hAP S (hAF hS)) (hAtwo S hS)⟩
  have hpart : (A.card : ℝ)=∑ d∈Finset.Icc 1 N,((A.filter (fun S=>Step S=d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  let q : ℝ := ((L : ℝ)-1)*((N : ℝ)-L)
  have hclass : ∀ d∈Finset.Icc 1 N,((A.filter (fun S=>Step S=d)).card : ℝ)≤
      q/(d : ℝ)^2+((N : ℝ)-1)/d := by
    intro d hd
    let C := A.filter (fun S=>Step S=d)
    have hCA : C⊆A := Finset.filter_subset _ _
    have hCF : C⊆F := hCA.trans hAF
    apply actual_same_step_low hL hhalf (Finset.mem_Icc.mp hd).1
      (show Legal (Ground N) C from
        ⟨fun S hS=>hF.1 S (hCF hS),fun S hS T hT hne=>hF.2 S (hCF hS) T (hCF hT) hne⟩)
      (fun S hS=>hAtwo S (hCA hS))
    · intro S hS
      obtain ⟨hSA,hSd⟩ := Finset.mem_filter.mp hS
      obtain ⟨_,p,hp⟩ := actual_step (hAP S (hAF hSA))
      exact ⟨p,by simpa only [hSd] using hp⟩
    · exact fun S hS=>hlow S (hCF hS)
  have heq : (∑ d∈Finset.Icc 1 N,(q/(d : ℝ)^2+((N : ℝ)-1)/d))=
      q*(∑ d∈Finset.Icc 1 N,(1 : ℝ)/(d : ℝ)^2)+((N : ℝ)-1)*Harmonic N := by
    have he1 (d : ℕ) : q/(d : ℝ)^2=q*((1 : ℝ)/(d : ℝ)^2) := by ring
    have he2 (d : ℕ) : ((N : ℝ)-1)/d=((N : ℝ)-1)*((1 : ℝ)/(d : ℝ)) := by ring
    simp_rw [he1,he2]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    rfl
  have hsq : (∑ d∈Finset.Icc 1 N,(1 : ℝ)/(d : ℝ)^2)≤329/200 := by
    simpa only [CoprimeDensity52.reciprocalSquareSum,one_div] using
      EndpointDensity54.reciprocal_square_upper N
  have hl0 : (0 : ℝ)≤(L : ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast hL)
  have hnl : (0 : ℝ)≤(N : ℝ)-L :=
    sub_nonneg.mpr (by exact_mod_cast (show L≤N by omega))
  have hpay := mul_le_mul_of_nonneg_left hsq (show 0≤q from mul_nonneg hl0 hnl)
  have hs := Finset.sum_le_sum hclass
  rw [heq,←hpart] at hs
  have hBlegal : Legal (Ground N) B :=
    ⟨fun S hS=>hF.1 S (hBF hS),fun S hS T hT hne=>hF.2 S (hBF hS) T (hBF hT) hne⟩
  have hb := actual_singleton_family_count hBlegal (fun S hS=>by
    have hh := (Finset.mem_filter.mp hS).2
    omega)
  have hbR : (B.card : ℝ)≤1 := by exact_mod_cast hb
  have hp : (A.card : ℝ)+B.card=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=F) (fun S=>2≤S.card)
  dsimp only [q] at hs hpay
  nlinarith only [hs,hpay,hbR,hp]

theorem actual_AP_low_weak {N L : ℕ} {F : Finset (Finset ℤ)}
    (hL : 1≤L) (hhalf : 2*L≤N) (hF : Legal (Ground N) F)
    (hAP : ∀ S∈F,IsAP S) (hlow : ∀ S∈F,Low S≤(L : ℤ)) :
    (F.card : ℝ)≤(329/200 : ℝ)*L*((N : ℝ)-L)+(N : ℝ)*Harmonic N+1 := by
  have hh := actual_AP_low_count hL hhalf hF hAP hlow
  have hH := harmonic_nonneg N
  have hnl : (0 : ℝ)≤(N : ℝ)-L :=
    sub_nonneg.mpr (by exact_mod_cast (show L≤N by omega))
  nlinarith only [hh,hH,hnl]

#print axioms actual_AP_low_count
#print axioms actual_AP_low_weak
end
end JSP233.LowAPCount67702
