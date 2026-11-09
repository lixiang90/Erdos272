module

public import Erdos272.Resources.LocalMobius120

@[expose] public section
namespace JSP233.LocalMobius121
/-! Half of the actual area pays the local reciprocal cutoff loss.
The finite cubic comparison retains the same physical density rho_N. -/
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem area_div_cutoff_half {T : ℕ} {u q : ℝ}
    (hT : 1≤T) (hu : 0≤u) (huT : u≤T) (harea : 2*q≤u^2) :
    q/(T:ℝ)≤u/2 := by
  have hTpos : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hh := mul_le_mul_of_nonneg_right huT hu
  apply (div_le_iff₀ hTpos).mpr
  nlinarith only [harea,hh]

theorem actual_resource_local_density {N T C A M e : ℕ}
    (hT : 1≤T) (hTN : T≤N) (hCM : C+M≤T) (hAe : A≤e) (heM : e≤M) :
    (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*
      (((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2)+
      4*((C:ℝ)+M)*Harmonic T+((C:ℝ)+M)/2+3*((C:ℝ)+M)^2/(N:ℝ)^2 := by
  have hN : 1≤N := hT.trans hTN
  have hr := ResourceBudget56.actual_resource_moebius_bound (N:=T) (by omega : C≤T) hAe heM (by omega : M≤T)
  rw [reciprocalSum_eq_Harmonic] at hr
  have hden := LocalMobius120.local_density_upper_cubic hT hTN
  let area : ℝ := ((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2
  have he : (e:ℝ)≤M := by exact_mod_cast heM
  have hCMR : (C:ℝ)+M≤T := by exact_mod_cast hCM
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHT := harmonic_nonneg T
  have harea0 : 0≤area := by
    have hh := mul_nonneg (show (0:ℝ)≤(M:ℝ)-e by linarith only [he])
      (show (0:ℝ)≤(C:ℝ)+M-((M:ℝ)-e)/2 by linarith only [Nat.cast_nonneg (α:=ℝ) C,Nat.cast_nonneg (α:=ℝ) M,Nat.cast_nonneg (α:=ℝ) e])
    dsimp only [area];nlinarith only [hh]
  have hareaSq : 2*area≤((C:ℝ)+M)^2 := by
    dsimp only [area]
    nlinarith only [sq_nonneg ((C:ℝ)+e)]
  have htail : area/(T:ℝ)≤((C:ℝ)+M)/2 :=
    area_div_cutoff_half hT (by positivity) hCMR hareaSq
  have hnorm : (6/(N:ℝ)^2)*area≤3*((C:ℝ)+M)^2/(N:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hareaSq (show (0:ℝ)≤3/(N:ℝ)^2 by positivity)
    calc
      _=(3/(N:ℝ)^2)*(2*area) := by ring
      _≤(3/(N:ℝ)^2)*((C:ℝ)+M)^2 := hh
      _=3*((C:ℝ)+M)^2/(N:ℝ)^2 := by ring
  have hm := mul_le_mul_of_nonneg_right (show moebiusSquareSum T-finiteCoprimeDensity N≤
      1/(T:ℝ)+6/(N:ℝ)^2 by exact hden) harea0
  have hlinear := mul_le_mul_of_nonneg_right (show (2*C+2*M+2*e:ℝ)≤4*((C:ℝ)+M) by
    linarith only [he,Nat.cast_nonneg (α:=ℝ) C]) hHT
  change (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*area+4*((C:ℝ)+M)*Harmonic T+((C:ℝ)+M)/2+3*((C:ℝ)+M)^2/(N:ℝ)^2
  change (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+moebiusSquareSum T*area+_ at hr
  simp only [div_eq_mul_inv] at hr hm htail hnorm hlinear ⊢
  nlinarith only [hr,hm,htail,hnorm,hlinear]

theorem actual_middle_resource_physical {N c L R d e : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d) (hdN : d≤N)
    (hAe : (L-c)/d≤e) (heM : e≤(R-c)/d) :
    ∃s:ℝ,0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) e:ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*Harmonic (N/d)+5/2)*N/d+3/(d:ℝ)^2 := by
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
  let E : ℝ := ((C:ℝ)+M)/2+3*((C:ℝ)+M)^2/(N:ℝ)^2
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
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤3/(N:ℝ)^2 by positivity)
  have hE : E≤(N:ℝ)/d/2+3/(d:ℝ)^2 := by
    dsimp only [E]
    have he : 3/(N:ℝ)^2*((N:ℝ)/d)^2=3/(d:ℝ)^2 := by field_simp
    rw [he] at hmul
    simp only [div_eq_mul_inv] at hwidth hmul ⊢
    nlinarith only [hwidth,hmul]
  refine ⟨s,hs,hsr,?_⟩
  change (ResourceCount C ((L-c)/d) M e:ℝ)≤_
  change (ResourceCount C ((L-c)/d) M e:ℝ)-E≤_ at hgrid
  dsimp only [T] at hgrid
  simp only [div_eq_mul_inv] at hgrid hE ⊢
  nlinarith only [hgrid,hE]

#print axioms area_div_cutoff_half
#print axioms actual_resource_local_density
#print axioms actual_middle_resource_physical
end
end JSP233.LocalMobius121
