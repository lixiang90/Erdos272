module

public import Erdos272.Resources.CovarianceFinite213
public import Erdos272.Resources.LocalizedResource208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual resource sums, with each physical e_d independently chosen.
No geometry or family-cardinality hypothesis is introduced here. -/
namespace JSP233.CovarianceResource213
open CoprimeDensity52 MiddleJoint51 ResourceSymmetry56 LocalizedMiddle208
open GcdResource208 FrontierGrid208 FrontierDensity208 CovarianceFinite213
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem actual_central_resource {N c L R : ℕ}
    (hc : 1≤c) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (hphase : (L : ℝ)-c≤CovarianceScalar213.Alpha*c)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hFu : ∀t≤N,TotientRows208.TotientMass t≤(76/125 : ℝ)*t+579/1000)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
      (R : ℝ)^2/2-CovarianceScalar213.K*L^2+
        (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L) := by
  let base := fun d : ℕ=>((coprimeRectangle (c/d) ((R-c)/d)).card : ℝ)+
    (UpperTriangle 0 ((R-c)/d)).card
  let term := fun d : ℕ=>-((c/d : ℕ) : ℝ)*(((L-c)/d : ℕ) : ℝ)+
    ((1-Rho)*(c : ℝ)/d+Zeta c d)^2/(2*Rho)+TotientRows208.RowError (c/d)
  have hcN : c≤N := hcL.trans (hLR.trans hRN)
  have hterm : ∀d∈Finset.Icc 1 N,
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℝ)≤
        base d+(if d≤c then term d else 0) := by
    intro d hd
    by_cases hdc : d≤c
    · rw [if_pos hdc]
      have hr:=resource_frontier_identity (C:=c/d) (he d hd).1 (he d hd).2
      have hrow:=TotientRows208.rectangle_row_lower (c/d) (e d)
      have ht:=hU (e d) ((he d hd).2.trans
        ((Nat.div_le_self _ _).trans ((Nat.sub_le R c).trans hRN)))
      have hh:=TotientCovariance212.row_unconstrained
        (C:=((c/d : ℕ) : ℝ)) (A:=(((L-c)/d : ℕ) : ℝ))
        CovarianceScalar213.rho_pos hrow ht
      rw [centred_row_identity c d] at hh
      rw [←actual_triangle_totient ((R-c)/d)] at hr
      dsimp only [base,term]
      linarith only [hr,hh]
    · rw [if_neg hdc,add_zero]
      have hc0 : c/d=0 := Nat.div_eq_of_lt (by omega)
      have hh:=LocalizedResource208.resource_zero_left (he d hd).1 (he d hd).2
      have hz : coprimeRectangle 0 ((R-c)/d)=∅ := by
        ext p
        simp only [Finset.notMem_empty,iff_false,mem_rectangle]
        omega
      rw [hc0]
      dsimp only [base]
      rw [hc0,hz]
      simpa only [Finset.card_empty,Nat.cast_zero,zero_add] using hh
  have hs:=Finset.sum_le_sum hterm
  have hcut : (∑d∈Finset.Icc 1 N,if d≤c then term d else 0)=
      ∑d∈Finset.Icc 1 c,term d := by
    rw [←Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have hb : (∑d∈Finset.Icc 1 N,base d)=
      (R : ℝ)^2/2-(c : ℝ)^2/2-((R : ℝ)-c)/2 := by
    simpa only [base,Nat.cast_sum,Nat.cast_add] using physical_base_identity (hcL.trans hLR) hRN
  rw [Finset.sum_add_distrib,hcut,hb] at hs
  have hexpand : (∑d∈Finset.Icc 1 c,term d)=
      -(∑d∈Finset.Icc 1 c,(c/d : ℕ)*(((L-c)/d : ℕ) : ℝ))+
      (1-Rho)^2*c^2/(2*Rho)*reciprocalSquareSum c+
      CovarianceScalar213.Alpha*c*(∑d∈Finset.Icc 1 c,Zeta c d/(d : ℝ))+
      (∑d∈Finset.Icc 1 c,(Zeta c d)^2/(2*Rho))+
      ∑d∈Finset.Icc 1 c,TotientRows208.RowError (c/d) := by
    have ht : ∀d∈Finset.Icc 1 c,term d=
        -(c/d : ℕ)*(((L-c)/d : ℕ) : ℝ)+
        (1-Rho)^2*c^2/(2*Rho)*((d : ℝ)^2)⁻¹+
        CovarianceScalar213.Alpha*c*(Zeta c d/(d : ℝ))+
        (Zeta c d)^2/(2*Rho)+TotientRows208.RowError (c/d) := by
      intro d hd
      have hdR : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      dsimp only [term,CovarianceScalar213.Alpha,Rho]
      field_simp [hdR.ne']
      ring
    rw [Finset.sum_congr rfl ht]
    simp only [Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.mul_sum,
      reciprocalSquareSum,neg_mul]
  rw [hexpand] at hs
  have hCA : (c : ℝ)*((L : ℝ)-c)≤
      ∑d∈Finset.Icc 1 c,(c/d : ℕ)*(((L-c)/d : ℕ) : ℝ) := by
    have hh:=Finset.single_le_sum (s:=Finset.Icc 1 c)
      (f:=fun d : ℕ=>(c/d : ℕ)*(((L-c)/d : ℕ) : ℝ))
      (fun d hd=>by positivity) (Finset.mem_Icc.mpr ⟨by omega,hc⟩ : 1∈Finset.Icc 1 c)
    simpa only [Nat.div_one,Nat.cast_sub hcL] using hh
  have hZ : Rho*reciprocalSquareSum c≤1 := by
    have hh:=mul_le_mul_of_nonneg_left (actual_square_upper (hcN.trans hN))
      CovarianceScalar213.rho_pos.le
    have he : Rho*(1/Rho)=(1 : ℝ) := by norm_num [Rho]
    rwa [he] at hh
  have hcen:=CovarianceScalar213.central_total
    (Nat.cast_nonneg (α:=ℝ) c)
    (sub_nonneg.mpr (show (c : ℝ)≤L by exact_mod_cast hcL))
    (Real.log_nonneg (show (1 : ℝ)≤c by exact_mod_cast hc)) hphase hZ
    (weighted_zeta (hcN.trans hN)) (HarmonicAbel29.harmonic_le_one_add_log c)
    (square_zeta hc hcN (hcN.trans hN) hF hFu) (row_error_sum hc)
  have hpoly:=CovarianceScalar213.centre_polynomial_le
    (Real.log_nonneg (show (1 : ℝ)≤c by exact_mod_cast hc))
  have hpolyM:=mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg (α:=ℝ) c)
  have hscale:=CovarianceScalar213.scaled_polynomial_mono
    (show (1 : ℝ)≤c by exact_mod_cast hc) (show (c : ℝ)≤L by exact_mod_cast hcL)
  have hRc : (0 : ℝ)≤(R : ℝ)-c := sub_nonneg.mpr (by exact_mod_cast (hcL.trans hLR))
  push_cast
  have hca : (c : ℝ)+((L : ℝ)-c)=(L : ℝ) := by ring
  rw [hca] at hcen
  linarith only [hs,hCA,hcen,hpolyM,hscale,hRc]

/- The original floor/tail proof is retained before its coarse density
relaxation.  This is needed in the low-c phase; the c-truncated square
bound alone would lose the large negative triangle contribution. -/
theorem actual_old_strong_main {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
      (R : ℝ)^2/2-(c : ℝ)^2/2+FrontierMain Rho c ((L : ℝ)-c)/Rho+
        (L : ℝ)*FrontierSum208.Polynomial (Real.log L) := by
  let base := fun d : ℕ=>((coprimeRectangle (c/d) ((R-c)/d)).card : ℝ)+
    (UpperTriangle 0 ((R-c)/d)).card
  let fee := fun d : ℕ=>FrontierMain Rho c ((L : ℝ)-c)/(d : ℝ)^2+FrontierSum208.Error L d
  have hLN : L≤N := hLR.trans hRN
  have hterms : ∀d∈Finset.Icc 1 N,
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℝ)≤
        base d+(if d≤L then fee d else 0) := by
    intro d hd
    by_cases hdL : d≤L
    · rw [if_pos hdL]
      have hh:=LocalizedResource208.resource_physical_local rho_bounds.1 rho_bounds.2 hcL hLR hRN
        (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,hdL⟩)
        (he d hd).1 (he d hd).2
        (hF (c/d) ((Nat.div_le_self _ _).trans (hcL.trans hLN)))
        (hU (e d) ((he d hd).2.trans ((Nat.div_le_self _ _).trans ((Nat.sub_le R c).trans hRN))))
      dsimp only [base,fee]
      linarith only [hh]
    · rw [if_neg hdL,add_zero]
      have hc0 : c/d=0 := Nat.div_eq_of_lt (by omega)
      rw [hc0]
      have hh:=LocalizedResource208.resource_zero_left (he d hd).1 (he d hd).2
      dsimp only [base]
      rw [hc0]
      have hz : coprimeRectangle 0 ((R-c)/d)=∅ := by
        ext p
        simp only [Finset.notMem_empty,iff_false,mem_rectangle]
        omega
      simpa only [hz,Finset.card_empty,Nat.cast_zero,zero_add] using hh
  have hs:=Finset.sum_le_sum hterms
  have hcut : (∑d∈Finset.Icc 1 N,if d≤L then fee d else 0)=∑d∈Finset.Icc 1 L,fee d := by
    rw [←Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have hb : (∑d∈Finset.Icc 1 N,base d)=
      (R : ℝ)^2/2-(c : ℝ)^2/2-((R : ℝ)-c)/2 := by
    simpa only [base,Nat.cast_sum,Nat.cast_add] using physical_base_identity (hcL.trans hLR) hRN
  rw [Finset.sum_add_distrib,hcut,hb] at hs
  have hlocal : (∑d∈Finset.Icc 1 L,fee d)=
      FrontierMain Rho c ((L : ℝ)-c)*reciprocalSquareSum L+
        ∑d∈Finset.Icc 1 L,FrontierSum208.Error L d := by
    simp only [fee,Finset.sum_add_distrib,div_eq_mul_inv,←Finset.mul_sum,reciprocalSquareSum]
  rw [hlocal] at hs
  have hCA : (c : ℝ)+((L : ℝ)-c)=L := by ring
  have hA : (0 : ℝ)≤(L : ℝ)-c := sub_nonneg.mpr (by exact_mod_cast hcL)
  have htail:=truncated_main_tail CovarianceScalar213.rho_pos rho_bounds.2
    (Nat.cast_nonneg c) hA (by exact_mod_cast (show 0<L by omega)) hCA
    (actual_square_upper (hLN.trans hN)) (actual_square_lower hL)
  have herr:=FrontierSum208.complete_error_bound hL
  have hRc : (0 : ℝ)≤(R : ℝ)-c := sub_nonneg.mpr (by exact_mod_cast (hcL.trans hLR))
  push_cast
  linarith only [hs,htail,herr,hRc]

theorem low_main_identity {c a : ℝ} (hphase : CovarianceScalar213.Alpha*c≤a) :
    -c^2/2+FrontierMain Rho c a/Rho=-(c+a)^2/2 := by
  dsimp only [FrontierMain,CovarianceScalar213.Alpha] at hphase ⊢
  rw [max_eq_left hphase]
  dsimp only [Rho]
  ring

theorem actual_low_resource {N c L R : ℕ}
    (hL : 64≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (hphase : CovarianceScalar213.Alpha*c≤(L : ℝ)-c)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
      (R : ℝ)^2/2-CovarianceScalar213.K*L^2+
        (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L) := by
  have hh:=actual_old_strong_main (by omega : 1≤L) hcL hLR hRN hN e he hF hU
  have hm:=low_main_identity hphase
  have hca : (c : ℝ)+((L : ℝ)-c)=(L : ℝ) := by ring
  rw [hca] at hm
  have ha:=CovarianceScalar213.low_phase_absorption (show (64 : ℝ)≤L by exact_mod_cast hL)
  linarith only [hh,hm,ha]

theorem actual_resource_sum_slack {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hFu : ∀t≤N,TotientRows208.TotientMass t≤(76/125 : ℝ)*t+579/1000)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)+3≤
      (R : ℝ)^2/2-CovarianceScalar213.K*L^2+
        (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850 := by
  by_cases hsmall : L≤63
  · have hh:=LocalizedResource208.actual_resource_sum_local rho_bounds.1 rho_bounds.2
      hL hcL hLR hRN e he hF hU
      (actual_square_upper ((hLR.trans hRN).trans hN)) (actual_square_lower hL)
    have ha:=CovarianceScalar213.small_phase_absorption hL hsmall
    dsimp only [CovarianceScalar213.K]
    linarith only [hh,ha]
  · have hlarge : 64≤L := by omega
    by_cases hphase : (L : ℝ)-c≤CovarianceScalar213.Alpha*c
    · have hc : 1≤c := by
        by_contra h
        have hz : c=0 := by omega
        rw [hz,Nat.cast_zero,mul_zero,sub_zero] at hphase
        have hL0 : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
        linarith only [hphase,hL0]
      have hh:=actual_central_resource hc hcL hLR hRN hN hphase e he hF hFu hU
      linarith only [hh]
    · have hh:=actual_low_resource hlarge hcL hLR hRN hN (le_of_not_ge hphase) e he hF hU
      linarith only [hh]

theorem actual_resource_sum {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hFu : ∀t≤N,TotientRows208.TotientMass t≤(76/125 : ℝ)*t+579/1000)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
      (R : ℝ)^2/2-CovarianceScalar213.K*L^2+
        (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850 := by
  have hh:=actual_resource_sum_slack hL hcL hLR hRN hN e he hF hFu hU
  linarith only [hh]

theorem actual_middle_profile {N c L R : ℕ}
    (hL : 1≤L) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hN : N≤1670000)
    (e : ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧e d≤(R-c)/d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientRows208.TotientMass t)
    (hFu : ∀t≤N,TotientRows208.TotientMass t≤(76/125 : ℝ)*t+579/1000)
    (hU : ∀t≤N,Rho*(t : ℝ)^2/2-(61/200)*t≤TotientTriangle t) :
    ((R : ℝ)+(129/200)*L)*(N-R)+
      ((∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) : ℕ) : ℝ)≤
        (N : ℝ)^2/2-RawEndpoint115.ProfileDeficit L (N-R)+
          (L : ℝ)*CovarianceScalar213.Polynomial (Real.log L)+850 := by
  have hh:=actual_resource_sum hL hcL hLR hRN hN e he hF hFu hU
  dsimp only [RawEndpoint115.ProfileDeficit,CovarianceScalar213.K] at hh ⊢
  nlinarith only [hh]

#print axioms actual_central_resource
#print axioms actual_old_strong_main
#print axioms low_main_identity
#print axioms actual_low_resource
#print axioms actual_resource_sum_slack
#print axioms actual_resource_sum
#print axioms actual_middle_profile
end
end JSP233.CovarianceResource213
