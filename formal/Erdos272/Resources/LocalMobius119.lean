import Erdos272.Resources.RawEndpoint115
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Physical middle rows use their actual finite Mobius cutoff N/d.
All rows return to the same finite density rho_N before being summed. -/
namespace JSP233.LocalMobius119
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem moebius_truncation_upper {T N : ℕ} (hT : 1≤T) (hTN : T≤N) :
    moebiusSquareSum T-moebiusSquareSum N≤1/(T:ℝ) := by
  have hi : Finset.Icc 1 N=Finset.Icc 1 T∪Finset.Ioc T N := by
    ext k;simp only [Finset.mem_Icc,Finset.mem_Ioc,Finset.mem_union];omega
  have hd : Disjoint (Finset.Icc 1 T) (Finset.Ioc T N) := by
    apply Finset.disjoint_left.mpr
    intro k hk hl
    have hh := Finset.mem_Icc.mp hk
    have hg := Finset.mem_Ioc.mp hl
    omega
  have he : moebiusSquareSum N=moebiusSquareSum T+
      ∑k∈Finset.Ioc T N,(ArithmeticFunction.moebius k:ℝ)/(k:ℝ)^2 := by
    unfold moebiusSquareSum
    rw [hi,Finset.sum_union hd]
  have hs : -(∑k∈Finset.Ioc T N,(ArithmeticFunction.moebius k:ℝ)/(k:ℝ)^2)≤
      ∑k∈Finset.Ioc T N,((k:ℝ)^2)⁻¹ := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro k _hk
    have hmu : |(ArithmeticFunction.moebius k:ℝ)|≤1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=k)
    have hl : -(ArithmeticFunction.moebius k:ℝ)≤1 := by linarith only [(abs_le.mp hmu).1]
    have hh := div_le_div_of_nonneg_right hl (sq_nonneg (k:ℝ))
    simpa only [neg_div,one_div] using hh
  have ht := sum_Ioc_inv_sq_le_sub (α:=ℝ) (k:=T) (by omega : T≠0) hTN
  have hn : (0:ℝ)≤(N:ℝ)⁻¹ := by positivity
  simp only [one_div]
  linarith only [he,hs,ht,hn]

theorem actual_resource_local_density {N T C A M e : ℕ}
    (hT : 1≤T) (hTN : T≤N) (hCM : C+M≤T) (hAe : A≤e) (heM : e≤M) :
    (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*
      (((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2)+
      4*((C:ℝ)+M)*Harmonic T+((C:ℝ)+M)+Harmonic N*((C:ℝ)+M)^2/N := by
  have hN : 1≤N := hT.trans hTN
  have hr := ResourceBudget56.actual_resource_moebius_bound (N:=T) (by omega : C≤T) hAe heM (by omega : M≤T)
  rw [reciprocalSum_eq_Harmonic] at hr
  have hdiff := moebius_truncation_upper hT hTN
  have hden := (abs_le.mp (moebiusSquareSum_density_error hN)).2
  rw [reciprocalSum_eq_Harmonic] at hden
  let area : ℝ := ((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2
  have he : (e:ℝ)≤M := by exact_mod_cast heM
  have hCMR : (C:ℝ)+M≤T := by exact_mod_cast hCM
  have hTpos : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hH0 := harmonic_nonneg N
  have hHT := harmonic_nonneg T
  have harea0 : 0≤area := by
    have hh := mul_nonneg (show (0:ℝ)≤(M:ℝ)-e by linarith only [he])
      (show (0:ℝ)≤(C:ℝ)+M-((M:ℝ)-e)/2 by linarith only [Nat.cast_nonneg (α:=ℝ) C,Nat.cast_nonneg (α:=ℝ) M,Nat.cast_nonneg (α:=ℝ) e])
    dsimp only [area];nlinarith only [hh]
  have hareaSq : 2*area≤((C:ℝ)+M)^2 := by
    dsimp only [area]
    nlinarith only [sq_nonneg ((C:ℝ)+e)]
  have hareaT : area≤(T:ℝ)*((C:ℝ)+M) := by
    have hh := mul_le_mul_of_nonneg_right hCMR (show (0:ℝ)≤(C:ℝ)+M by positivity)
    nlinarith only [hareaSq,hh]
  have htail : area/(T:ℝ)≤(C:ℝ)+M := (div_le_iff₀ hTpos).mpr (by nlinarith only [hareaT])
  have hnorm : (2*Harmonic N/N)*area≤Harmonic N*((C:ℝ)+M)^2/N := by
    have hh := mul_le_mul_of_nonneg_left hareaSq (show (0:ℝ)≤Harmonic N/N by positivity)
    calc
      _=(Harmonic N/N)*(2*area) := by ring
      _≤(Harmonic N/N)*((C:ℝ)+M)^2 := hh
      _=Harmonic N*((C:ℝ)+M)^2/N := by ring
  have hm := mul_le_mul_of_nonneg_right (show moebiusSquareSum T-finiteCoprimeDensity N≤
      1/(T:ℝ)+2*Harmonic N/N by linarith only [hdiff,hden]) harea0
  have hlinear := mul_le_mul_of_nonneg_right (show (2*C+2*M+2*e:ℝ)≤4*((C:ℝ)+M) by
    linarith only [he,Nat.cast_nonneg (α:=ℝ) C]) hHT
  change (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*area+4*((C:ℝ)+M)*Harmonic T+((C:ℝ)+M)+Harmonic N*((C:ℝ)+M)^2/N
  change (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+moebiusSquareSum T*area+_ at hr
  simp only [div_eq_mul_inv] at hr hm htail hnorm hlinear ⊢
  nlinarith only [hr,hm,htail,hnorm,hlinear]

theorem actual_middle_resource_physical {N c L R d e : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d) (hdN : d≤N)
    (hAe : (L-c)/d≤e) (heM : e≤(R-c)/d) :
    ∃s:ℝ,0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) e:ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*Harmonic (N/d)+3)*N/d+Harmonic N*N/(d:ℝ)^2 := by
  let C := c/d
  let M := (R-c)/d
  let T := N/d
  have hT : 1≤T := by dsimp only [T];exact Nat.div_pos hdN hd
  have hTN : T≤N := Nat.div_le_self _ _
  have hCMd : (C+M)*d≤N := by
    have hc := Nat.div_mul_le_self c d
    have hr := Nat.div_mul_le_self (R-c) d
    dsimp only [C,M]
    have hsub := Nat.sub_add_cancel (hcL.trans hLR)
    nlinarith only [hc,hr,hsub,hRN]
  have hCM : C+M≤T := (Nat.le_div_iff_mul_le hd).mpr hCMd
  have hr := actual_resource_local_density hT hTN hCM hAe heM
  let E : ℝ := ((C:ℝ)+M)+Harmonic N*((C:ℝ)+M)^2/N
  have hK : (ResourceCount C ((L-c)/d) M e:ℝ)-E≤(C:ℝ)*((e:ℝ)-((L-c)/d:ℕ))+
      finiteCoprimeDensity N*((((M:ℝ)-e)*((C:ℝ)+M)-((M:ℝ)-e)^2/2))+
        4*((C:ℝ)+M)*Harmonic T := by dsimp only [E];linarith only [hr]
  have hb := ResourceBudget56.middle_nat_grid_bounds hcL hLR hd
  obtain ⟨s,hs,hsr,hgrid⟩ := ResourceBudget56.middle_grid_scaling (K:=(ResourceCount C ((L-c)/d) M e:ℝ)-E)
    (Nat.cast_nonneg N) (Nat.cast_nonneg c) (by exact_mod_cast (hcL.trans (hLR.trans hRN)))
    (sub_nonneg.mpr (by exact_mod_cast hLR)) (Nat.cast_nonneg R) (by exact_mod_cast hRN)
    (Nat.cast_pos.mpr hd) (Nat.cast_nonneg C) (Nat.cast_nonneg ((L-c)/d))
    (by exact_mod_cast hAe) (by exact_mod_cast heM) hb.1 hb.2.1 hb.2.2
    (finiteCoprimeDensity_bounds hN).1.le (finiteCoprimeDensity_bounds hN).2 (harmonic_nonneg T) hK
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hdpos : (0:ℝ)<d := Nat.cast_pos.mpr hd
  have hwidth : (C:ℝ)+M≤(N:ℝ)/d := (le_div_iff₀ hdpos).mpr (by exact_mod_cast hCMd)
  have hsq : ((C:ℝ)+M)^2≤((N:ℝ)/d)^2 := by gcongr
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤Harmonic N/N by have hh := harmonic_nonneg N;positivity)
  have hE : E≤(N:ℝ)/d+Harmonic N*N/(d:ℝ)^2 := by
    dsimp only [E]
    have he : Harmonic N/N*((N:ℝ)/d)^2=Harmonic N*N/(d:ℝ)^2 := by field_simp
    rw [he] at hmul
    simp only [div_eq_mul_inv] at hwidth hmul ⊢
    nlinarith only [hwidth,hmul]
  refine ⟨s,hs,hsr,?_⟩
  change (ResourceCount C ((L-c)/d) M e:ℝ)≤_
  change (ResourceCount C ((L-c)/d) M e:ℝ)-E≤_ at hgrid
  dsimp only [T] at hgrid
  simp only [div_eq_mul_inv] at hgrid hE ⊢
  nlinarith only [hgrid,hE]

theorem actual_harmonic_div_sum {N : ℕ} (hN : 1≤N) :
    (∑d∈Finset.Icc 1 N,Harmonic (N/d)/(d:ℝ))≤
      (Real.log N)^2/2+Real.log N+Harmonic N := by
  have hs : (∑d∈Finset.Icc 1 N,Harmonic (N/d)/(d:ℝ))≤
      ∑d∈Finset.Icc 1 N,(SimplexMoment57.LogKernel (N:ℝ) 1 d+1/(d:ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hh := Finset.mem_Icc.mp hd
    have hT : 1≤N/d := Nat.div_pos hh.2 hh.1
    have hb : Harmonic (N/d)≤1+Real.log ((N/d:ℕ):ℝ) := by
      exact HarmonicAbel29.harmonic_le_one_add_log (N/d)
    have hdpos : (0:ℝ)<d := by exact_mod_cast hh.1
    have hfloor : ((N/d:ℕ):ℝ)≤(N:ℝ)/d := by
      exact Nat.cast_div_le (α:=ℝ)
    have hl := Real.log_le_log (by exact_mod_cast (show 0<N/d by omega)) hfloor
    rw [Real.log_div (by exact_mod_cast (show N≠0 by omega)) hdpos.ne'] at hl
    have hb' : Harmonic (N/d)≤1+Real.log N-Real.log d := by linarith only [hb,hl]
    have hbound := div_le_div_of_nonneg_right hb' hdpos.le
    dsimp only [SimplexMoment57.LogKernel]
    norm_num only [pow_one]
    simp only [div_eq_mul_inv] at hbound ⊢
    linarith only [hbound]
  rw [Finset.sum_add_distrib] at hs
  have hk := SimplexMoment57.actual_log_kernel_sum hN 1
  norm_num only [pow_one,Nat.reduceAdd,Nat.cast_ofNat] at hk
  change (∑d∈Finset.Icc 1 N,Harmonic (N/d)/(d:ℝ))≤_
  change _≤_+Harmonic N at hs
  linarith only [hs,hk]

#print axioms moebius_truncation_upper
#print axioms actual_resource_local_density
#print axioms actual_middle_resource_physical
#print axioms actual_harmonic_div_sum
end
end JSP233.LocalMobius119
