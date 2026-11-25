module

public import Erdos272.Geometry.N82427.PhaseIncrement82427
public import Erdos272.Counting.N158375.ClassCount158375

@[expose] public section

namespace JSP233.PhaseRamp82427
open LightPhases208 (Indices)
open PhaseDefs82427 ClassCount158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem old_caps_ramp {N d T E B V : ℕ}
    (hd : 0 < d) (hET : E ≤ T)
    (hlo : T-E+1 ≤ N/d) (hhi : N/d+E ≤ V) :
    (∑ j ∈ Indices N d (T-E) B, Cap N d E B V j)+1 ≤
      ∑ j ∈ Indices N d (T-E) B, Cap (N+1) d E B V j := by
  let i : ℕ × ℕ := (0,N%d+1)
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  have hq : 1 ≤ N/d := by omega
  have hx : N%d+1 ∈ Finset.Icc 1 d := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hi : i ∈ Indices N d (T-E) B := by
    change (0,N%d+1) ∈ Indices N d (T-E) B
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),hx⟩,?_⟩
    change N%d+1+(T-E+0*B)*d ≤ N
    have hh := Nat.mul_le_mul_right d hlo
    simp only [Nat.add_mul,Nat.one_mul] at hh
    nlinarith
  have hcap : Cap N d E B V i+1=Cap (N+1) d E B V i := by
    have hdiv : (N-(N%d+1))/d=N/d-1 := by
      rw [PhaseClosed82427.phase_div hd hx,if_neg (by omega)]
    have hs : N+1-(N%d+1)=N/d*d := by omega
    have hdiv' : (N+1-(N%d+1))/d=N/d := by rw [hs,Nat.mul_div_cancel _ hd]
    change min V ((N-(N%d+1))/d-0*B+E)+1=min V ((N+1-(N%d+1))/d-0*B+E)
    rw [hdiv,hdiv']
    simp only [Nat.zero_mul,Nat.sub_zero]
    rw [min_eq_right (by omega : N/d-1+E ≤ V),min_eq_right hhi]
    omega
  have hpoint : ∀ j ∈ Indices N d (T-E) B,
      Cap N d E B V j+(if j=i then 1 else 0) ≤ Cap (N+1) d E B V j := by
    intro j hj
    by_cases he : j=i
    · simpa [he] using hcap.le
    · simpa only [if_neg he,Nat.add_zero] using
        PhaseIncrement82427.cap_mono (N:=N) (H:=N+1) (d:=d) (E:=E) (B:=B) (V:=V) (by omega) j
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  simpa only [Finset.sum_ite_eq',if_pos hi] using hsum

theorem price_ramp_increment {N d T E B V : ℕ}
    (hd : 0 < d) (hET : E ≤ T)
    (hlo : T-E+1 ≤ N/d) (hhi : N/d+E ≤ V) :
    Price N d T E B V+1 ≤ Price (N+1) d T E B V := by
  have hpay := old_caps_ramp (B:=B) hd hET hlo hhi
  have hmore := Finset.sum_le_sum_of_subset_of_nonneg
    (f:=fun j => Cap (N+1) d E B V j)
    (PhaseIncrement82427.indices_mono (N:=N) (H:=N+1) (d:=d) (A:=T-E) (B:=B) (by omega))
    (by intros; exact Nat.zero_le _)
  exact hpay.trans hmore

theorem price_joint_increment {N d T E B V r : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E ≤ T) (hTV : T ≤ V)
    (hq : T-E+r*B=N/d) (hlo : T-E+1 ≤ N/d) (hhi : N/d+E ≤ V) :
    Price N d T E B V+T+1 ≤ Price (N+1) d T E B V := by
  let i : ℕ × ℕ := (r,N%d+1)
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  have hrB : r ≤ r*B := by nlinarith [show 1 ≤ B by omega]
  have hrN : r < N+2 := by have hh := Nat.div_le_self N d; omega
  have hnew : i ∈ Indices (N+1) d (T-E) B := by
    change (r,N%d+1) ∈ Indices (N+1) d (T-E) B
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hrN,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩,?_⟩
    change N%d+1+(T-E+r*B)*d ≤ N+1
    rw [hq]
    omega
  have hnot : i ∉ Indices N d (T-E) B := by
    intro hi
    have ha := (Finset.mem_filter.mp hi).2
    change N%d+1+(T-E+r*B)*d ≤ N at ha
    rw [hq] at ha
    omega
  have hcap : Cap (N+1) d E B V i=T := by
    have hs : N+1-(N%d+1)=N/d*d := by omega
    change min V ((N+1-(N%d+1))/d-r*B+E)=T
    rw [hs,Nat.mul_div_cancel _ hd]
    have he : N/d-r*B+E=T := by omega
    rw [he,min_eq_right hTV]
  have hsub : insert i (Indices N d (T-E) B) ⊆ Indices (N+1) d (T-E) B :=
    Finset.insert_subset_iff.mpr ⟨hnew,PhaseIncrement82427.indices_mono (by omega)⟩
  have hpay := old_caps_ramp (B:=B) hd hET hlo hhi
  have hmore := Finset.sum_le_sum_of_subset_of_nonneg
    (f:=fun j => Cap (N+1) d E B V j) hsub (by intros; exact Nat.zero_le _)
  rw [Finset.sum_insert hnot,hcap] at hmore
  unfold Price
  omega

def Steps (N A C p : ℕ) : Finset ℕ :=
  (Finset.Icc (N/C+1) (N/A)).filter (fun d => StepClass208.PrimeGate d=p)

theorem interval_length {N low A C : ℕ} (hA : 0 < A) (hAC : A ≤ C) (hlo : low ≤ N) :
    N/C+low*(C-A)/(A*C) ≤ N/A := by
  have hC : 0 < C := lt_of_lt_of_le hA hAC
  have hcsub : C-A+A=C := Nat.sub_add_cancel hAC
  have hnum := Nat.div_mul_le_self (low*(C-A)) (A*C)
  have hscale : low*(C-A) ≤ N*(C-A) := Nat.mul_le_mul_right (C-A) hlo
  have hbase := Nat.div_mul_le_self N C
  apply (Nat.le_div_iff_mul_le hA).mpr
  by_contra hh
  have hbad : N+1 ≤ (N/C+low*(C-A)/(A*C))*A := by omega
  have hmul := Nat.mul_le_mul_right C hbad
  have hbase' := Nat.mul_le_mul_right A hbase
  nlinarith

theorem physical_count {N low A C p b : ℕ}
    (hA : 0 < A) (hAC : A ≤ C) (hlo : low ≤ N)
    (h : Certificate p (low*(C-A)/(A*C)) b) : b ≤ (Steps N A C p).card := by
  have hb := certificate_lower h (N/C)
  rw [window_count_eq_card] at hb
  have hl := interval_length hA hAC hlo
  apply hb.trans (Finset.card_le_card ?_)
  intro d hd
  obtain ⟨hd,hgate⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hl⟩,hgate⟩

theorem mem_steps {N A C p d : ℕ} (hA : 0 < A) (hAC : A ≤ C) (hd : d ∈ Steps N A C p) :
    0 < d ∧ A ≤ N/d ∧ N/d < C ∧ StepClass208.PrimeGate d=p := by
  change d ∈ (Finset.Icc (N/C+1) (N/A)).filter (fun d => StepClass208.PrimeGate d=p) at hd
  obtain ⟨hd,hgate⟩ := Finset.mem_filter.mp hd
  obtain ⟨hl,hr⟩ := Finset.mem_Icc.mp hd
  have hdpos : 0 < d := (Nat.succ_pos _).trans_le hl
  have hmul : d*A ≤ N := (Nat.le_div_iff_mul_le hA).mp hr
  have hC : 0 < C := lt_of_lt_of_le hA hAC
  have htop : N < d*C := (Nat.div_lt_iff_lt_mul hC).mp (by omega)
  refine ⟨hdpos,(Nat.le_div_iff_mul_le hdpos).mpr (by nlinarith),?_,hgate⟩
  exact (Nat.div_lt_iff_lt_mul hdpos).mpr (by nlinarith)

#print axioms old_caps_ramp
#print axioms price_ramp_increment
#print axioms price_joint_increment
#print axioms interval_length
#print axioms physical_count
#print axioms mem_steps
end
end JSP233.PhaseRamp82427
