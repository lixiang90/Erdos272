module

public import Erdos272.Retention.CrossBad116
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual short-trace rectangles with the weaker dense117 missing-point
ratio.  Sources remain legal on Ground N; the core interval is only a trace
set.  The p13 crossing-AP step and original physical exterior are preserved. -/
namespace JSP233.CrossBad120
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33 CrossBad116
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_bad_rectangles_disjoint {N L R b : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 325≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hmiss : ∀S∈E,((Ground N\Finset.Icc (L:ℤ) (R:ℤ))\S).card≤b)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1)
    (hshape : 16*b≤7*(L+N-R)) (hlarge : 90<L+N-R) :
    ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩Finset.Icc (1:ℤ) ((L:ℤ)-1)).product (S∩Finset.Icc ((R:ℤ)+1) N))
        ((T∩Finset.Icc (1:ℤ) ((L:ℤ)-1)).product (T∩Finset.Icc ((R:ℤ)+1) N)) := by
  let O := Ground N\Finset.Icc (L:ℤ) (R:ℤ)
  let A := Finset.Icc (1:ℤ) ((L:ℤ)-1)
  let B := Finset.Icc ((R:ℤ)+1) N
  have hO : O=A∪B := by
    ext x
    simp only [O,A,B,Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_union,mem_ground]
    omega
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have ha := Finset.mem_Icc.mp hx
    have hb := Finset.mem_Icc.mp hy
    omega
  have hOc : O.card+1=L+N-R := by
    have he := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
      (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
    dsimp only [O]
    omega
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨haS,hbS⟩ := Finset.mem_product.mp hzS
  obtain ⟨haT,hbT⟩ := Finset.mem_product.mp hzT
  have hu : z.1∈S∩T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp haS).1,(Finset.mem_inter.mp haT).1⟩
  have hv : z.2∈S∩T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbS).1,(Finset.mem_inter.mp hbT).1⟩
  have hlu := (Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2).2
  have hrv := (Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2).1
  obtain ⟨d,p,hAP,_hp⟩ := (isAP_iff_exists_APAt _).mp (hlegal.2 S (hEF hS) T (hEF hT) hne)
  have hd := crossing_small_trace_step_ge13 hLR hM hAP hu hv (by omega) (by omega)
    Finset.inter_subset_left (hshort S hS)
  have ha := arm_card_upper13 (a:=(1:ℤ)) (z:=(L:ℤ)-1) hAP hd
  have hb := arm_card_upper13 (a:=(R:ℤ)+1) (z:=(N:ℤ)) hAP hd
  have hc := BadFringe115.common_arm_card (O:=O) (A:=O) (Finset.Subset.refl O) (hmiss S hS) (hmiss T hT)
  have hcup : (S∩T)∩O=((S∩T)∩A)∪((S∩T)∩B) := by rw [hO,Finset.inter_union_distrib_left]
  have hupp := Finset.card_union_le ((S∩T)∩A) ((S∩T)∩B)
  have hOc' : O.card=A.card+B.card := by rw [hO,Finset.card_union_of_disjoint hAB]
  have hup : 13*((S∩T)∩O).card≤O.card+24 := by
    rw [hcup]
    change 13*((S∩T)∩A).card≤A.card+12 at ha
    change 13*((S∩T)∩B).card≤B.card+12 at hb
    omega
  omega

theorem actual_bad13_shape {N L R m : ℕ}
    (hLR : L≤R) (hRN : R≤N) (hm : N<11*m)
    (hpay : 900*(L+N-R)≤23*N) :
    16*((L+N-R)+(R-L+1)/13-m)≤7*(L+N-R) := by
  let w := L+N-R
  let M := R-L+1
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 13
  by_cases hs : w+M/13<m
  · have hb : w+M/13-m=0 := by omega
    change 16*(w+M/13-m)≤7*w
    rw [hb]
    omega
  · have hsub := Nat.sub_add_cancel (show m≤w+M/13 by omega)
    have hd : 143*(w+M/13-m)+2*N+2≤132*w := by nlinarith only [hsub,hdiv,hMw,hm]
    change 900*w≤23*N at hpay
    change 16*(w+M/13-m)≤7*w
    omega

#print axioms actual_bad_rectangles_disjoint
#print axioms actual_bad13_shape
end
end JSP233.CrossBad120
