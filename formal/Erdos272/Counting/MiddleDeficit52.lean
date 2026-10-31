import Erdos272.Arithmetic.CoprimeDensity52
import Erdos272.Retention.EndpointDeficit44

/-! Physical scaling and actual-family endpoint102 from the finite coprime
resource pools. The scaling proof is adapted from the fixed Erdos272 source;
the weighted endpoint uses the stronger local EndpointDeficit44 raw102. -/
namespace JSP233.MiddleDeficit52
open CoprimeDensity52 MiddleJoint51
open StarCompletion APGeometry PreparedClasses50 APPrepare49 PreparedWitness48
open MiddleCoordinates51 DenseDeletion40 FamilyReflect43 RestrictedWitness44
open LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2500000

theorem middle_grid_scaling {n c r R d C A M e ρ H K : ℝ}
    (_hn : 0 ≤ n) (hc : 0 ≤ c) (hcN : c ≤ n) (hr : 0 ≤ r) (hR : 0 ≤ R) (hRN : R ≤ n)
    (hd : 0 < d) (_hC : 0 ≤ C) (_hA : 0 ≤ A) (hAe : A ≤ e) (heM : e ≤ M)
    (hCd : C*d ≤ c) (hCMd : (C+M)*d ≤ R) (hwidth : (M-A)*d ≤ r+d)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hH : 0 ≤ H)
    (hK : K ≤ C*(e-A)+ρ*((M-e)*(C+M)-(M-e)^2/2)+40*(C+M)*H) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧
      K ≤ (c*(r-s)+ρ*(s*R-s^2/2))/d^2+(40*H+2)*n/d := by
  let u := (M-e)*d
  let s := min r u
  have hu : 0 ≤ u := mul_nonneg (sub_nonneg.mpr heM) hd.le
  have hs : 0 ≤ s := le_min hr hu
  have hsr : s ≤ r := min_le_left _ _
  have hsu : s ≤ u := min_le_right _ _
  have huwidth : u ≤ r+d := by dsimp only [u]; nlinarith only [hwidth,hAe,hd]
  have hdelta : u-s ≤ d := by
    dsimp only [s]
    rcases le_total r u with hru | hur
    · rw [min_eq_left hru]; linarith only [huwidth]
    · rw [min_eq_right hur]; linarith only [hd]
  have hstart0 : 0 ≤ (e-A)*d := mul_nonneg (sub_nonneg.mpr hAe) hd.le
  have hstart : (e-A)*d ≤ r-s+d := by
    have hsum : (e-A)*d+u = (M-A)*d := by dsimp only [u]; ring
    linarith only [hwidth,hsum,hsu]
  have hfirst : (C*d)*((e-A)*d) ≤ c*(r-s+d) := by
    exact (mul_le_mul_of_nonneg_right hCd hstart0).trans
      (mul_le_mul_of_nonneg_left hstart hc)
  have hright : u*((C+M)*d) ≤ u*R := mul_le_mul_of_nonneg_left hCMd hu
  have htail₁ : ρ*(u*((C+M)*d)-u^2/2) ≤ ρ*(u*R-u^2/2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hright]) hρ
  have hdeltaR := mul_le_mul_of_nonneg_right hdelta hR
  have hdeltaSum : 0 ≤ (u-s)*(u+s) := mul_nonneg (sub_nonneg.mpr hsu) (add_nonneg hu hs)
  have htail₂ : u*R-u^2/2 ≤ s*R-s^2/2+d*R := by
    nlinarith only [hdeltaR,hdeltaSum]
  have hρdR := mul_le_mul_of_nonneg_right hρ1 (mul_nonneg hd.le hR)
  have htail₃ : ρ*(u*R-u^2/2) ≤ ρ*(s*R-s^2/2)+d*R := by
    have hh := mul_le_mul_of_nonneg_left htail₂ hρ
    nlinarith only [hh,hρdR]
  have hgrid : (C*(e-A)+ρ*((M-e)*(C+M)-(M-e)^2/2))*d^2 ≤
      c*(r-s)+ρ*(s*R-s^2/2)+d*(c+R) := by
    dsimp only [u] at htail₁ htail₃
    nlinarith only [hfirst,htail₁,htail₃]
  have hCMN : (C+M)*d ≤ n := hCMd.trans hRN
  have herr := mul_le_mul_of_nonneg_right hCMN (show 0 ≤ 40*H*d by positivity)
  have hends := mul_le_mul_of_nonneg_left (add_le_add hcN hRN) hd.le
  have hKd := mul_le_mul_of_nonneg_right hK (sq_nonneg d)
  have hscaled : K*d^2 ≤ c*(r-s)+ρ*(s*R-s^2/2)+(40*H+2)*n*d := by
    nlinarith only [hKd,hgrid,herr,hends]
  refine ⟨s,hs,hsr,?_⟩
  have hid : ((c*(r-s)+ρ*(s*R-s^2/2))/d^2+(40*H+2)*n/d)*d^2 =
      c*(r-s)+ρ*(s*R-s^2/2)+(40*H+2)*n*d := by
    field_simp
  exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hd)).mp (by
    rw [hid]
    exact hscaled)

theorem middle_nat_grid_bounds {c L R d : ℕ} (hcL : c ≤ L) (hLR : L ≤ R)
    (hd : 0 < d) :
    ((c/d : ℕ) : ℝ)*d ≤ c ∧
      (((c/d : ℕ) : ℝ)+( (R-c)/d : ℕ))*d ≤ R ∧
      ((( (R-c)/d : ℕ) : ℝ)-((L-c)/d : ℕ))*d ≤ ((R : ℝ)-L)+d := by
  have hcR : c ≤ R := hcL.trans hLR
  have hcdiv := Nat.div_mul_le_self c d
  have hRdiv := Nat.div_mul_le_self (R-c) d
  have hLmod := Nat.mod_lt (L-c) hd
  have hLquot := Nat.mod_add_div (L-c) d
  have hLdiv : L-c ≤ ((L-c)/d+1)*d := by nlinarith only [hLmod,hLquot]
  have hcdivR : ((c/d : ℕ) : ℝ)*d ≤ c := by exact_mod_cast hcdiv
  have hRdivR : (((R-c)/d : ℕ) : ℝ)*d ≤ (R : ℝ)-c := by
    exact_mod_cast hRdiv
  have hLdivR : (L : ℝ)-c ≤ (((L-c)/d : ℕ)+1 : ℝ)*d := by
    exact_mod_cast hLdiv
  exact ⟨hcdivR,by nlinarith only [hcdivR,hRdivR],by nlinarith only [hRdivR,hLdivR]⟩

theorem middle_nat_grid_scale {N c L R d e : ℕ} {K : ℝ}
    (hN : 1 ≤ N) (hcL : c ≤ L) (hLR : L ≤ R) (hRN : R ≤ N) (hd : 0 < d)
    (hAe : (L-c)/d ≤ e) (heM : e ≤ (R-c)/d)
    (hK : K ≤ ((c/d : ℕ) : ℝ)*((e : ℝ)-((L-c)/d : ℕ))+
      finiteCoprimeDensity N*((((R-c)/d : ℕ)-(e : ℝ))*((c/d : ℕ)+((R-c)/d : ℕ) : ℝ)-
        (((R-c)/d : ℕ)-(e : ℝ))^2/2)+
      40*((c/d : ℕ)+((R-c)/d : ℕ) : ℝ)*reciprocalSum N) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ (R : ℝ)-L ∧
      K ≤ ((c : ℝ)*((R : ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/((d : ℝ)^2)+
        (40*reciprocalSum N+2)*N/d := by
  have hcN : c ≤ N := hcL.trans (hLR.trans hRN)
  have hb := middle_nat_grid_bounds hcL hLR hd
  apply middle_grid_scaling (Nat.cast_nonneg N) (Nat.cast_nonneg c)
    (by exact_mod_cast hcN) (sub_nonneg.mpr (by exact_mod_cast hLR))
    (Nat.cast_nonneg R) (by exact_mod_cast hRN) (Nat.cast_pos.mpr hd)
    (Nat.cast_nonneg (c/d)) (Nat.cast_nonneg ((L-c)/d))
    (by exact_mod_cast hAe) (by exact_mod_cast heM) hb.1 hb.2.1 hb.2.2
    (finiteCoprimeDensity_bounds hN).1.le (finiteCoprimeDensity_bounds hN).2
    (Finset.sum_nonneg (fun d _hd => by positivity)) hK


theorem actual_weighted_endpoint102 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (_hLR : L≤R) (hRN : R≤N)
    (s : ℕ→ℝ) (hs : ∀d∈Finset.Icc 1 N,0≤s d ∧ s d≤(R:ℝ)-L) :
    ((R:ℝ)+(2/3)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102 := by
  let outer := ((R:ℝ)+(2/3)*L)*(N-R)
  let bound := (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102
  let w := fun d:ℕ=>finiteCoprimeDensity N/(d:ℝ)^2
  let f := fun d:ℕ=>((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2
  have hrho := (finiteCoprimeDensity_bounds hN).1.le
  have hden : 1≤(5/3:ℝ)*finiteCoprimeDensity N := by
    have hh := finiteCoprimeDensity_lower hN
    linarith only [hh]
  have hterms : ∀d∈Finset.Icc 1 N,w d*outer+f d≤w d*bound := by
    intro d hd
    have hh := EndpointDeficit44.weighted_middle_endpoint_deficit
      (N:=(N:ℝ)) (c:=(c:ℝ)) (L:=(L:ℝ)) (R:=(R:ℝ))
      (rho:=finiteCoprimeDensity N) (s:=s d)
      (Nat.cast_nonneg c) (by exact_mod_cast hcL) (by exact_mod_cast hRN) (hs d hd).2 hrho hden
    have hraw : finiteCoprimeDensity N*outer+(c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2)≤finiteCoprimeDensity N*bound := by
      dsimp only [outer,bound]
      convert hh using 1; ring
    calc
      w d*outer+f d=(finiteCoprimeDensity N*outer+(c:ℝ)*((R:ℝ)-L-s d)+
          finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2 := by dsimp only [w,f];ring
      _≤(finiteCoprimeDensity N*bound)/(d:ℝ)^2 :=
        div_le_div_of_nonneg_right hraw (sq_nonneg _)
      _=w d*bound := by dsimp only [w];ring
  have hsum := Finset.sum_le_sum hterms
  have hw : (∑d∈Finset.Icc 1 N,w d)=1 := finiteCoprimeDensity_weights_sum hN
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Finset.sum_mul,hw,one_mul,one_mul] at hsum
  exact hsum

theorem actual_middle_resource_physical {N c L R d e : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hAe : (L-c)/d≤e) (heM : e≤(R-c)/d) :
    ∃s:ℝ,0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) e:ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (40*HarmonicAbel29.Harmonic N+2)*N/d := by
  have hcN := hcL.trans (hLR.trans hRN)
  have hC : c/d≤N := (Nat.div_le_self c d).trans hcN
  have hM : (R-c)/d≤N := (Nat.div_le_self (R-c) d).trans ((Nat.sub_le R c).trans hRN)
  have hbound := actual_resource_density hN hC hAe heM hM
  rw [←reciprocalSum_eq_Harmonic] at hbound
  obtain ⟨s,hs,hsr,hcount⟩ := middle_nat_grid_scale hN hcL hLR hRN hd hAe heM hbound
  exact ⟨s,hs,hsr,by simpa only [reciprocalSum_eq_Harmonic] using hcount⟩

theorem actual_middle_resource_sum102 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(2/3)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102+
          (40*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
  have hx : ∀d:ℕ,∃s:ℝ,d∈Finset.Icc 1 N→0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (40*HarmonicAbel29.Harmonic N+2)*N/d := by
    intro d
    by_cases hd:d∈Finset.Icc 1 N
    · obtain ⟨s,hs⟩ := actual_middle_resource_physical hN hcL hLR hRN
        (by have hh := (Finset.mem_Icc.mp hd).1;omega) (he d hd).1 (he d hd).2
      exact ⟨s,fun _=>hs⟩
    · exact ⟨0,fun hh=>False.elim (hd hh)⟩
  choose s hs using hx
  have hc := Finset.sum_le_sum (fun d hd=>(hs d hd).2.2)
  have herr : (∑d∈Finset.Icc 1 N,(40*HarmonicAbel29.Harmonic N+2)*N/(d:ℝ))=
      (40*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
    simp only [HarmonicAbel29.Harmonic,div_eq_mul_inv,←Finset.mul_sum,one_mul]
  rw [Finset.sum_add_distrib,herr] at hc
  have ht := actual_weighted_endpoint102 hN hcL hLR hRN s (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  push_cast
  linarith only [hc,ht]

theorem actual_prepared_CM_EM_endpoint102 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 1≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(2/3)*L)*(N-R)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102+
        (40*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_sum102 hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_original_prepared_endpoint102 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃c∈Finset.Icc 1 N,∃L R:ℕ,c<L ∧ L≤R ∧ R≤N ∧
        (∀S∈Retained N 28 H,¬IsAP S→(c:ℤ)∈S) ∧
        (∃P∈Avoiders (Retained N 28 H) c,∀z∈P,(L:ℤ)≤z) ∧
        (∃T∈Avoiders (Retained N 28 H) c,∀z∈T,z≤(R:ℤ)) ∧
        (∀S∈Avoiders (Retained N 28 H) c,
          (∃a∈S,a≤(L:ℤ) ∧ ∀z∈S,a≤z) ∧ ∃b∈S,(R:ℤ)≤b ∧ ∀z∈S,z≤b) ∧
        (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102+
          (Deleted N 28 F).card+(WitnessException (Ground N) c:ℝ)+
          40*N*(HarmonicAbel29.Harmonic N)^2+6*N*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    actual_original_middle_reduction28 hN hF hcounter
  obtain ⟨P,hPG,hLP⟩ := hP
  have hPF := (Finset.mem_filter.mp hPG).1
  have hn : 1≤N := by
    have hh : 1≤2^49 := by norm_num
    exact hh.trans hN
  have hb := actual_prepared_CM_EM_endpoint102 x p hn (actual_retained_legal (r:=28) hLH)
    (by omega) hLR hRN hroot hPF hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,⟨P,hPG,hLP⟩,hT,henv,?_⟩
  nlinarith only [hb,hcount]

#print axioms middle_grid_scaling
#print axioms middle_nat_grid_bounds
#print axioms middle_nat_grid_scale
#print axioms actual_weighted_endpoint102
#print axioms actual_middle_resource_physical
#print axioms actual_middle_resource_sum102
#print axioms actual_prepared_CM_EM_endpoint102
#print axioms actual_original_prepared_endpoint102
end
end JSP233.MiddleDeficit52
