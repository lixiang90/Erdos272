import Erdos272.Counting.PhaseCodes208
import Erdos272.Geometry.PhaseOverlap208
import Erdos272.Counting.SpanBudget208
import Erdos272.Geometry.BlockAP119

/-! The complete 10/11 span bound for the same actual AP traces.
Repeated phase labels remain indexed by their original members. -/
namespace JSP233.ActualPhase208
open StarCompletion APGeometry BlockAP119 ConflictBudget208 PhaseCodes208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

variable {α : Type*} [DecidableEq α]

theorem actual_span_phase_sum (C : Finset α) (T : α→Finset ℤ)
    (d : α→ℕ) (a : α→ℤ) (y L R : ℤ) (hLR : L≤R)
    (hAP : ∀i∈C,APAt (d i : ℤ) (a i) (T i))
    (hd : ∀i∈C,2≤d i ∧ d i≤11)
    (hsub : ∀i∈C,T i⊆Finset.Icc L R) (hne : ∀i∈C,(T i).Nonempty)
    (hoff : ∀i∈C,¬(d i : ℤ)∣y-a i)
    (hpair : ∀i∈C,∀j∈C,i≠j → ((T i)∩T j).card≤1) :
    (∑i∈C,(((T i).card : ℝ)-1))≤
      (10/11 : ℝ)*((R : ℝ)-L+1)+10*(C.card : ℝ)*((C.card : ℝ)-1) := by
  let lo := fun i => if h : i∈C then (T i).min' (hne i h) else 0
  let hi := fun i => if h : i∈C then (T i).max' (hne i h) else 0
  let code := fun i => Code (d i) (a i) y
  let rel := Compatible code
  let w := fun i => 1/(d i : ℝ)
  have hlo : ∀i∈C,lo i∈T i := by
    intro i hiC
    simp only [lo,dif_pos hiC]
    exact Finset.min'_mem _ (hne i hiC)
  have hhi : ∀i∈C,hi i∈T i := by
    intro i hiC
    simp only [hi,dif_pos hiC]
    exact Finset.max'_mem _ (hne i hiC)
  have hspan : ∀i∈C,L≤lo i ∧ lo i≤hi i ∧ hi i≤R := by
    intro i hiC
    have hl := Finset.mem_Icc.mp (hsub i hiC (hlo i hiC))
    have hh := Finset.mem_Icc.mp (hsub i hiC (hhi i hiC))
    have hmid : lo i≤hi i := by
      simp only [lo,dif_pos hiC]
      exact Finset.min'_le _ _ (hhi i hiC)
    exact ⟨hl.1,hmid,hh.2⟩
  have hcode : ∀i∈C,code i∈PhaseDensity208.Codes := by
    intro i hiC
    have hb := actual_off_code_bounds (by have hh := (hd i hiC).1;omega : 0<d i)
      (by have hh := (hd i hiC).2;omega : d i≤12) (hoff i hiC)
    apply PhaseDensity208.mem_codes.mpr
    exact ⟨(hd i hiC).1,(hd i hiC).2,hb.2.2.1,hb.2.2.2⟩
  have hlocal : ∀z∈Finset.Ico L R,(∑i∈SpanBudget208.Active C lo hi z,w i)≤
      (10/11 : ℝ)+PairCost rel w (SpanBudget208.Active C lo hi z)/2 := by
    intro z hz
    exact phase_conflict_bound code (SpanBudget208.Active C lo hi z)
      (fun i hiC => hcode i (Finset.mem_filter.mp hiC).1)
  have hover : ∀i∈C,∀j∈C,i≠j → Cost rel w i j*
      (((Finset.Ico (lo i) (hi i))∩Finset.Ico (lo j) (hi j)).card : ℝ)≤20 := by
    intro i hiC j hjC hij
    by_cases hc : rel i j
    · have hcost : Cost rel w i j=min (1/(d i : ℝ)) (1/(d j : ℝ)) := by
        simp only [Cost,if_neg hij,if_pos hc,w]
      obtain ⟨z,hzi,hzj⟩ := hc
      have hdi : 0<d i := by have hh := (hd i hiC).1;omega
      have hdj : 0<d j := by have hh := (hd j hjC).1;omega
      have hzi' : (d i : ℤ)∣(y+(z : ℤ))-a i := (code_residue_iff hdi (a i) y z).mpr hzi
      have hzj' : (d j : ℤ)∣(y+(z : ℤ))-a j := (code_residue_iff hdj (a j) y z).mpr hzj
      have hh := PhaseOverlap208.actual_overlap_weight (hd i hiC).1 (hd i hiC).2
        (hd j hjC).1 (hd j hjC).2 (hAP i hiC) (hAP j hjC)
        (hlo i hiC) (hhi i hiC) (hlo j hjC) (hhi j hjC)
        (hpair i hiC j hjC hij) ⟨y+(z : ℤ),hzi',hzj'⟩
      rw [hcost]
      exact hh
    · simp only [Cost,if_neg hij,if_neg hc,zero_mul]
      norm_num
  have hb := SpanBudget208.span_budget rel C lo hi L R w (10/11) 20 hLR hspan hlocal hover
  have hlen : ∀i∈C,w i*((hi i : ℝ)-lo i)=((T i).card : ℝ)-1 := by
    intro i hiC
    have hs := apAt_span_eq (hAP i hiC) (hne i hiC)
    have hsR : (hi i : ℝ)-(lo i : ℝ)=(d i : ℝ)*((T i).card-1) := by
      have hs' : hi i-lo i=(d i : ℤ)*((T i).card-1) := by
        simpa only [hi,lo,dif_pos hiC] using hs
      exact_mod_cast hs'
    have hdR : (0 : ℝ)<d i := by exact_mod_cast (show 0<d i by have hh := (hd i hiC).1;omega)
    rw [hsR]
    dsimp only [w]
    field_simp
  rw [Finset.sum_congr rfl hlen] at hb
  simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hb ⊢
  nlinarith only [hb]

#print axioms actual_span_phase_sum
end
end JSP233.ActualPhase208
