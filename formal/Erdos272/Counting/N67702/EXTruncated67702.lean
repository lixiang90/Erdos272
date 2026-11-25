module

public import Erdos272.Geometry.N67702.EXGeometry67702

@[expose] public section

namespace JSP233.EXTruncated67702
open StarCompletion APGeometry APCount41 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem reciprocal_two_sum {M : ℕ} (hM : 1≤M) :
    (∑ d∈Finset.Icc 2 M,(1 : ℝ)/(d : ℝ))=Harmonic M-1 := by
  have he : Finset.Icc 1 M=insert 1 (Finset.Icc 2 M) := by
    ext d
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  unfold Harmonic
  rw [he,Finset.sum_insert (by simp)]
  norm_num

theorem actual_truncated_count {N L R M : ℕ} {F : Finset (Finset ℤ)} {J : Finset ℕ}
    (hRN : R≤N) (hM : 1≤M) (hMD : M≤(N-1)/3)
    (hF : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S)
    (hfour : ∀ S∈F,4≤S.card) (hlarge : ∀ S∈F,2≤Step S)
    (hends : ∀ S∈F,Low S≤(L : ℤ) ∧ (R : ℤ)≤High S)
    (hJ : J⊆Finset.Icc (M+1) ((N-1)/3))
    (hempty : ∀ d∈J,F.filter (fun S=>Step S=d)=∅)
    (hcap : ∀ d∈Finset.Icc 2 ((N-1)/3),M<d → (F.filter (fun S=>Step S=d)).card≤1) :
    (F.card : ℝ)≤(129/200 : ℝ)*L*((N : ℝ)-R)+
      ((L : ℝ)+((N : ℝ)-R))*(Harmonic M-1)+((N-1)/3 : ℕ)-1-(J.card : ℝ) := by
  let D := (N-1)/3
  let I := Finset.Icc 2 D
  let A := Finset.Icc 2 M
  let k : ℝ := (N : ℝ)-R
  let w : ℝ := (L : ℝ)+k
  have hRNr : (R : ℝ)≤N := by exact_mod_cast hRN
  have hk : 0≤k := sub_nonneg.mpr hRNr
  have hmaps := EXGeometry67702.actual_four_step_maps hF.1 hAP hfour hlarge
  have hpart : (F.card : ℝ)=∑ d∈I,((F.filter (fun S=>Step S=d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hAI : A⊆I := by
    intro d hd
    obtain ⟨hd2,hdM⟩ := Finset.mem_Icc.mp hd
    exact Finset.mem_Icc.mpr ⟨hd2,hdM.trans hMD⟩
  have hJI : J⊆I := by
    intro d hd
    obtain ⟨hMd,hdD⟩ := Finset.mem_Icc.mp (hJ hd)
    exact Finset.mem_Icc.mpr ⟨by omega,hdD⟩
  have hbound (d : ℕ) : ((F.filter (fun S=>Step S=d)).card : ℝ)≤
      (L : ℝ)*k/(d : ℝ)^2+w/d+1 := by
    let B := F.filter (fun S=>Step S=d)
    have hBF : B⊆F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) B :=
      ⟨fun S hS=>hF.1 S (hBF hS),fun S hS T hT hne=>hF.2 S (hBF hS) T (hBF hT) hne⟩
    apply ActualExterior208.actual_same_step_endpoint_width hRN hlegal
      (fun S hS=>isAP_nonempty (hAP S (hBF hS)))
    · intro S hS
      obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
      obtain ⟨_,p,hp⟩ := actual_step (hAP S hSF)
      exact ⟨p,by simpa only [hSd] using hp⟩
    · exact fun S hS=>hends S (hBF hS)
  have hpoint : ∀ d∈I,((F.filter (fun S=>Step S=d)).card : ℝ)≤
      (if d∈A then (L : ℝ)*k/(d : ℝ)^2+w/d else 0)+1-(if d∈J then 1 else 0) := by
    intro d hd
    by_cases hdJ : d∈J
    · have hMd := (Finset.mem_Icc.mp (hJ hdJ)).1
      have hdA : d∉A := by
        intro hh
        have hhM := (Finset.mem_Icc.mp hh).2
        omega
      simp only [hdJ,hdA,if_pos,if_neg,hempty d hdJ,Finset.card_empty,Nat.cast_zero]
      norm_num
    · by_cases hdA : d∈A
      · simpa only [if_pos hdA,if_neg hdJ,sub_zero] using hbound d
      · have hMd : M<d := by
          have hd2 := (Finset.mem_Icc.mp hd).1
          by_contra hn
          exact hdA (Finset.mem_Icc.mpr ⟨hd2,by omega⟩)
        have hh : ((F.filter (fun S=>Step S=d)).card : ℝ)≤1 := by exact_mod_cast hcap d hd hMd
        simpa only [if_neg hdA,if_neg hdJ,zero_add,sub_zero] using hh
  have hIA : I.filter (fun d=>d∈A)=A := by
    ext d
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hd=>hAI hd)
  have hIJ : I.filter (fun d=>d∈J)=J := by
    ext d
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hd=>hJI hd)
  have hsumA : (∑ d∈I,if d∈A then (L : ℝ)*k/(d : ℝ)^2+w/d else 0)=
      ∑ d∈A,((L : ℝ)*k/(d : ℝ)^2+w/d) := by
    rw [←Finset.sum_filter,hIA]
  have hsumJ : (∑ d∈I,if d∈J then (1 : ℝ) else 0)=(J.card : ℝ) := by
    rw [←Finset.sum_filter,hIJ]
    simp
  have hIcard : (I.card : ℝ)=(D : ℝ)-1 := by
    have hc : I.card=D-1 := by dsimp only [I];rw [Nat.card_Icc];omega
    rw [hc,Nat.cast_sub (show 1≤D by omega),Nat.cast_one]
  have heq : (∑ d∈A,((L : ℝ)*k/(d : ℝ)^2+w/d))=
      (L : ℝ)*k*(∑ d∈Finset.Icc 2 M,(1 : ℝ)/(d : ℝ)^2)+w*(Harmonic M-1) := by
    have he1 (d : ℕ) : (L : ℝ)*k/(d : ℝ)^2=(L : ℝ)*k*((1 : ℝ)/(d : ℝ)^2) := by ring
    have he2 (d : ℕ) : w/d=w*((1 : ℝ)/(d : ℝ)) := by ring
    simp_rw [he1,he2]
    rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
    change _=(L : ℝ)*k*(∑ d∈Finset.Icc 2 M,(1 : ℝ)/(d : ℝ)^2)+w*(Harmonic M-1)
    rw [reciprocal_two_sum hM]
  have ht := mul_le_mul_of_nonneg_left (EndpointExterior55.reciprocal_square_tail_two M)
    (show (0 : ℝ)≤(L : ℝ)*k by positivity)
  have hs := Finset.sum_le_sum hpoint
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,hsumA,hsumJ] at hs
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
  rw [heq,hIcard] at hs
  dsimp only [k,w,D] at hs ht
  linarith only [hpart,hs,ht]

#print axioms reciprocal_two_sum
#print axioms actual_truncated_count
end
end JSP233.EXTruncated67702
