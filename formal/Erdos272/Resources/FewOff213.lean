module

public import Erdos272.Resources.FewOff212
public import Erdos272.Resources.FewOffGeometry213
public import Erdos272.Arithmetic.FewOffGates213
public import Erdos272.Resources.AlignedPlans213
public import Erdos272.Resources.ActualGrid213
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.FewOff213
open StarCompletion APGeometry DenseDeletion40
open ActualGrid212 FewOffGeometry212 FewOffGates212 OffResidue44 AlignedPlans212
open FewOff212 (Few source_count_lower)
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem actual_few_bucket {N L R k : ℕ} {F : Finset (Finset ℤ)}
    (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ) (y : ℤ)
    (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11)
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S : ℤ) (a S) (S∩Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀S∈F,(N : ℝ)<(k : ℝ)*S.card)
    (hwidth : (L : ℝ)+(N-R)<(N : ℝ)/(2951/100)) :
    (OffPoint (Few N F (fun S => (d S : ℤ)) a) (fun S => (d S : ℤ)) a y).card≤SourceCount k-1 := by
  let E := Few N F (fun S => (d S : ℤ)) a
  let B := OffPoint E (fun S => (d S : ℤ)) a y
  have hEF : E⊆F := Finset.filter_subset _ _
  have hBF : B⊆F := (Finset.filter_subset _ _).trans hEF
  by_contra hbig
  have hn := source_count_lower hk2 hk11
  obtain ⟨C,hCB,hCc⟩ := Finset.exists_subset_card_eq
    (show SourceCount k≤B.card by change ¬B.card≤SourceCount k-1 at hbig;omega)
  let T := fun S : Finset ℤ => S∩Finset.Icc (L : ℤ) (R : ℤ)
  have hCF : C⊆F := hCB.trans hBF
  have hfew : ∀S∈C,0<(ActualOffPoints S (d S) (a S)).card ∧
      ((ActualOffPoints S (d S) (a S)).card : ℝ)≤(3/5000 : ℝ)*N := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (hCB hS)).1).2
  have hsteps : ∀S∈C,2≤d S ∧ d S≤11 := by
    intro S hS
    have hdpos : 0<d S := by exact_mod_cast (htrace S (hCF hS)).1
    exact FewOffGeometry213.actual_few_step_domain (by omega : 640000≤N) (hF.1 S (hCF hS)) hdpos hk11
      (hdense S (hCF hS)) (hfew S hS).2 (hfew S hS).1
  have hlower : ∀S∈C,(N : ℝ)/k-(3/5000 : ℝ)*N-((L : ℝ)+(N-R))/2-3<(T S).card-1 := by
    intro S hS
    exact actual_few_trace_lower hL hLR hRN (hsteps S hS).1 (by omega : 0<k)
      (hF.1 S (hCF hS)) (htrace S (hCF hS)) (hdense S (hCF hS)) (hfew S hS).2
  have hbase : (0 : ℝ)≤(N : ℝ)/k-(3/5000 : ℝ)*N-((L : ℝ)+(N-R))/2-3 := by
    have hnR : (646000 : ℝ)≤N := by exact_mod_cast hN
    have hkR : (k : ℝ)≤11 := by exact_mod_cast hk11
    have hkp : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
    have hdiv := div_le_div_of_nonneg_left (Nat.cast_nonneg N : (0 : ℝ)≤N) hkp hkR
    norm_num at hwidth
    nlinarith only [hnR,hdiv,hwidth]
  have hne : ∀S∈C,(T S).Nonempty := by
    intro S hS
    have hh := hlower S hS
    apply Finset.card_pos.mp
    have hhR : (0 : ℝ)<(T S).card := by linarith only [hh,hbase]
    exact_mod_cast hhR
  have hoff : ∀S∈C,¬(d S : ℤ)∣y-a S := by
    intro S hS
    exact (Finset.mem_filter.mp (hCB hS)).2.2
  have hpair : ∀S∈C,∀U∈C,S≠U → ((T S)∩T U).card≤1 := by
    intro S hS U hU hSU
    obtain ⟨hSE,hyS,hoffS⟩ := Finset.mem_filter.mp (hCB hS)
    obtain ⟨hUE,hyU,hoffU⟩ := Finset.mem_filter.mp (hCB hU)
    exact off_point_trace_inter_card (htrace S (hCF hS))
      (hF.2 S (hCF hS) U (hCF hU) hSU) hyS hyU hoffS
  have hs := ActualPhase208.actual_span_phase_sum C T d a y (L : ℤ) (R : ℤ)
    (by exact_mod_cast hLR) (fun S hS => htrace S (hCF hS)) hsteps
    (fun S hS => Finset.inter_subset_right) hne hoff hpair
  have hCne : C.Nonempty := Finset.card_pos.mp (by omega : 0<C.card)
  obtain ⟨S,hSC⟩ := hCne
  have hl := Finset.sum_lt_sum (fun S hS => (hlower S hS).le) ⟨S,hSC,hlower S hSC⟩
  simp only [Finset.sum_const,nsmul_eq_mul,hCc] at hl
  rw [hCc] at hs
  have hg := FewOffGates213.full_phase_gate hN hk2 hk11 hwidth
  push_cast at hs
  nlinarith only [hs,hl,hg]


#print axioms actual_few_bucket
end
end JSP233.FewOff213
