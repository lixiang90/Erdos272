module

public import Erdos272.Resources.ResourceSymmetry56
public import Erdos272.Arithmetic.HarmonicLog55
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! Recombine the actual finite coprime pools before converting their common
Moebius density to the same finite rho_N. This lowers the real error coefficient
from40 to4 and transports it through all physical steps and the same original
family endpoint67. The sharper log-simplex exception moment remains separate. -/
namespace JSP233.ResourceBudget56
open CoprimeDensity52 MiddleJoint51 MiddleDeficit52 EndpointExterior55
open StarCompletion APGeometry PreparedClasses50 APPrepare49 PreparedWitness48
open MiddleCoordinates51 DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicLog55 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2500000

theorem actual_resource_moebius_bound {N C A M e : ℕ}
    (hCN : C≤N) (hAe : A≤e) (heM : e≤M) (hMN : M≤N) :
    (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+moebiusSquareSum N*
      (((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2)+
      (2*C+2*M+2*e)*reciprocalSum N := by
  have hcm := abs_le.mp (coprimeRectangle_moebius_error (B:=M) hCN)
  have hce := abs_le.mp (coprimeRectangle_moebius_error (B:=e) hCN)
  have hmm := abs_le.mp (coprimeRectangle_moebius_error (B:=M) hMN)
  have hee := abs_le.mp (coprimeRectangle_moebius_error (B:=e) (heM.trans hMN))
  have hbox := coprimeBox_card_identity (Nat.zero_le C) heM
  have hboxR : ((CoprimeBox 0 C e M).card:ℝ)+(coprimeRectangle C e).card=
      (coprimeRectangle C M).card := by
    simpa only [coprimeBox,coprimeRectangle,Finset.Icc_eq_empty_of_lt (by omega : 0<1),
      Finset.product_eq_sprod,Finset.empty_product,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,zero_add,add_zero]
      using (show ((coprimeBox 0 C e M).card:ℝ)+(coprimeRectangle 0 M).card+
        (coprimeRectangle C e).card=(coprimeRectangle C M).card+(coprimeRectangle 0 e).card by
        exact_mod_cast hbox)
  have hs := ResourceSymmetry56.actual_square_tail_identity heM
  have hsR : 2*(((CoprimeBox 0 e e M).card:ℝ)+(UpperTriangle e M).card)+
      (coprimeRectangle e e).card≤(coprimeRectangle M M).card := by
    have hh : 2*(((CoprimeBox 0 e e M).card:ℝ)+(UpperTriangle e M).card)+
        (coprimeRectangle e e).card+((if e=0∧0<M then 1 else 0:ℕ):ℝ)=
          (coprimeRectangle M M).card := by exact_mod_cast hs
    have hdelta : (0:ℝ)≤((if e=0∧0<M then 1 else 0:ℕ):ℝ) := Nat.cast_nonneg _
    linarith only [hh,hdelta]
  simp only [ResourceCount,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hAe]
  nlinarith only [hcm.2,hce.1,hmm.2,hee.1,hboxR,hsR]

theorem actual_resource_density_four {N C A M e : ℕ} (hN : 1≤N)
    (hCN : C≤N) (hAe : A≤e) (heM : e≤M) (hMN : M≤N) :
    (ResourceCount C A M e:ℝ)≤(C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*
      (((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2)+
      4*((C:ℝ)+M)*Harmonic N := by
  have hb := actual_resource_moebius_bound hCN hAe heM hMN
  have herr := (abs_le.mp (moebiusSquareSum_density_error hN)).2
  have hC : (C:ℝ)≤N := by exact_mod_cast hCN
  have hM : (M:ℝ)≤N := by exact_mod_cast hMN
  have he : (e:ℝ)≤M := by exact_mod_cast heM
  have hNpos : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hH : 0≤reciprocalSum N := Finset.sum_nonneg (fun d _=>by positivity)
  let h : ℝ := (M:ℝ)-e
  let area : ℝ := h*(C+M)-h^2/2
  have hh : 0≤h := sub_nonneg.mpr he
  have hhM : h≤M := by dsimp only [h];linarith only [Nat.cast_nonneg (α:=ℝ) e]
  have harea0 : 0≤area := by
    have hpos := mul_nonneg hh (show 0≤(C:ℝ)+M-h/2 by
      linarith only [hhM,Nat.cast_nonneg (α:=ℝ) C,Nat.cast_nonneg (α:=ℝ) M])
    dsimp only [area];nlinarith only [hpos]
  have ha : area≤N*((C:ℝ)+h) := by
    have h1 := mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) (show 0≤(N:ℝ)-h by linarith only [hhM,hM])
    have h2 := mul_nonneg hh (sub_nonneg.mpr hM)
    dsimp only [area];nlinarith only [h1,h2,sq_nonneg h]
  have hdiv : (2*reciprocalSum N/N)*area≤2*((C:ℝ)+h)*reciprocalSum N := by
    have hh := mul_le_mul_of_nonneg_left ha (show 0≤2*reciprocalSum N/N by positivity)
    have hid : (2*reciprocalSum N/N)*(N*((C:ℝ)+h))=2*((C:ℝ)+h)*reciprocalSum N := by field_simp
    exact hh.trans_eq hid
  have hearea := mul_le_mul_of_nonneg_right herr harea0
  change _≤_+finiteCoprimeDensity N*area+_
  change _≤_+moebiusSquareSum N*area+_ at hb
  rw [←reciprocalSum_eq_Harmonic]
  dsimp only [h] at hdiv
  nlinarith only [hb,hearea,hdiv]

theorem middle_grid_scaling {n c r R d C A M e ρ H K : ℝ}
    (_hn : 0 ≤ n) (hc : 0 ≤ c) (hcN : c ≤ n) (hr : 0 ≤ r) (hR : 0 ≤ R) (hRN : R ≤ n)
    (hd : 0 < d) (_hC : 0 ≤ C) (_hA : 0 ≤ A) (hAe : A ≤ e) (heM : e ≤ M)
    (hCd : C*d ≤ c) (hCMd : (C+M)*d ≤ R) (hwidth : (M-A)*d ≤ r+d)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hH : 0 ≤ H)
    (hK : K ≤ C*(e-A)+ρ*((M-e)*(C+M)-(M-e)^2/2)+4*(C+M)*H) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ r ∧
      K ≤ (c*(r-s)+ρ*(s*R-s^2/2))/d^2+(4*H+2)*n/d := by
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
  have herr := mul_le_mul_of_nonneg_right hCMN (show 0 ≤ 4*H*d by positivity)
  have hends := mul_le_mul_of_nonneg_left (add_le_add hcN hRN) hd.le
  have hKd := mul_le_mul_of_nonneg_right hK (sq_nonneg d)
  have hscaled : K*d^2 ≤ c*(r-s)+ρ*(s*R-s^2/2)+(4*H+2)*n*d := by
    nlinarith only [hKd,hgrid,herr,hends]
  refine ⟨s,hs,hsr,?_⟩
  have hid : ((c*(r-s)+ρ*(s*R-s^2/2))/d^2+(4*H+2)*n/d)*d^2 =
      c*(r-s)+ρ*(s*R-s^2/2)+(4*H+2)*n*d := by
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
      4*((c/d : ℕ)+((R-c)/d : ℕ) : ℝ)*reciprocalSum N) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ (R : ℝ)-L ∧
      K ≤ ((c : ℝ)*((R : ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/((d : ℝ)^2)+
        (4*reciprocalSum N+2)*N/d := by
  have hcN : c ≤ N := hcL.trans (hLR.trans hRN)
  have hb := middle_nat_grid_bounds hcL hLR hd
  apply middle_grid_scaling (Nat.cast_nonneg N) (Nat.cast_nonneg c)
    (by exact_mod_cast hcN) (sub_nonneg.mpr (by exact_mod_cast hLR))
    (Nat.cast_nonneg R) (by exact_mod_cast hRN) (Nat.cast_pos.mpr hd)
    (Nat.cast_nonneg (c/d)) (Nat.cast_nonneg ((L-c)/d))
    (by exact_mod_cast hAe) (by exact_mod_cast heM) hb.1 hb.2.1 hb.2.2
    (finiteCoprimeDensity_bounds hN).1.le (finiteCoprimeDensity_bounds hN).2
    (Finset.sum_nonneg (fun d _hd => by positivity)) hK


theorem actual_middle_resource_physical {N c L R d e : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hAe : (L-c)/d≤e) (heM : e≤(R-c)/d) :
    ∃s:ℝ,0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) e:ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*HarmonicAbel29.Harmonic N+2)*N/d := by
  have hcN := hcL.trans (hLR.trans hRN)
  have hC : c/d≤N := (Nat.div_le_self c d).trans hcN
  have hM : (R-c)/d≤N := (Nat.div_le_self (R-c) d).trans ((Nat.sub_le R c).trans hRN)
  have hbound := actual_resource_density_four hN hC hAe heM hM
  rw [←reciprocalSum_eq_Harmonic] at hbound
  obtain ⟨s,hs,hsr,hcount⟩ := middle_nat_grid_scale hN hcL hLR hRN hd hAe heM hbound
  exact ⟨s,hs,hsr,by simpa only [reciprocalSum_eq_Harmonic] using hcount⟩


theorem actual_middle_resource_sum67 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+
          (4*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
  have hx : ∀d:ℕ,∃s:ℝ,d∈Finset.Icc 1 N→0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*HarmonicAbel29.Harmonic N+2)*N/d := by
    intro d
    by_cases hd:d∈Finset.Icc 1 N
    · obtain ⟨s,hs⟩ := actual_middle_resource_physical hN hcL hLR hRN
        (by have hh := (Finset.mem_Icc.mp hd).1;omega) (he d hd).1 (he d hd).2
      exact ⟨s,fun _=>hs⟩
    · exact ⟨0,fun hh=>False.elim (hd hh)⟩
  choose s hs using hx
  have hc := Finset.sum_le_sum (fun d hd=>(hs d hd).2.2)
  have herr : (∑d∈Finset.Icc 1 N,(4*HarmonicAbel29.Harmonic N+2)*N/(d:ℝ))=
      (4*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
    simp only [HarmonicAbel29.Harmonic,div_eq_mul_inv,←Finset.mul_sum,one_mul]
  rw [Finset.sum_add_distrib,herr] at hc
  have ht := actual_weighted_endpoint67 hN hcL hLR hRN s (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  push_cast
  linarith only [hc,ht]

theorem actual_prepared_CM_EM_endpoint67 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 1≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+
        (4*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_sum67 hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_original_prepared_endpoint67 {N : ℕ} {F : Finset (Finset ℤ)}
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
        (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+
          (Deleted N 28 F).card+(WitnessException (Ground N) c:ℝ)+
          4*N*(HarmonicAbel29.Harmonic N)^2+6*N*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    EndpointExterior55.actual_original_middle_reduction28 hN hF hcounter
  obtain ⟨P,hPG,hLP⟩ := hP
  have hPF := (Finset.mem_filter.mp hPG).1
  have hn : 1≤N := by
    have hh : 1≤2^49 := by norm_num
    exact hh.trans hN
  have hb := actual_prepared_CM_EM_endpoint67 x p hn (actual_retained_legal (r:=28) hLH)
    (by omega) hLR hRN hroot hPF hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,⟨P,hPG,hLP⟩,hT,henv,?_⟩
  nlinarith only [hb,hcount]


def NativeTailPolynomialFour67 (J hi D : ℕ) : ℝ :=
  67*(6*(HarmonicUpper J hi)^3+4*(HarmonicUpper J hi)^2+6*HarmonicUpper J hi+28+D+1)

theorem actual_original_refined_endpoint67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+(Deleted N 28 F).card+
        6*N*(HarmonicUpper J hi)^3+4*N*(HarmonicUpper J hi)^2+
          6*N*HarmonicUpper J hi+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hraw⟩ :=
    actual_original_prepared_endpoint67 hN hF hcounter
  have h63 : 63≤N := by norm_num at hN;omega
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by
    have hh:=Finset.mem_Icc.mp hc
    omega)
  have hW := actual_exception_refined_harmonic (J:=J) h63 hhi hcG
  have hh := actual_refined_harmonic_upper (J:=J) h63 hhi
  have h0 := harmonic_nonneg N
  have herror : 4*(N:ℝ)*(Harmonic N)^2+6*N*Harmonic N≤
      4*N*(HarmonicUpper J hi)^2+6*N*HarmonicUpper J hi := by gcongr
  refine ⟨H,c,L,R,⟨hHF,hLH,hcard,hD,hG,hc,hLc,hLR,hRN,hroot,hP,hT,henv⟩,?_⟩
  linarith only [hraw,hW,herror]

theorem actual_original_refined_tail67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (((L+N-R:ℕ):ℝ)^2≤NativeTailPolynomialFour67 J hi 3137*N) := by
  obtain ⟨H,c,L,R,hcontext,hraw⟩ := actual_original_refined_endpoint67 (J:=J) hN hhi hF hcounter
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hkeep := hcontext
  obtain ⟨_hHF,_hLH,_hcard,_hD,_hG,_hc,hcL,hLR,hRN,_hroot,_hP,_hT,_henv⟩ := hcontext
  have hD : (Deleted N 28 F).card≤3137*N := by
    apply DenseSharper41.actual_deleted_sharp (by decide : 0<28) (by norm_num;norm_num at hN;omega) hF
  have hDR : ((Deleted N 28 F).card:ℝ)≤3137*(N:ℝ) := by exact_mod_cast hD
  have hdiff : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter;omega
  have hchooseR : ((N.choose 2):ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hchooseR
  have ht : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-R := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
  refine ⟨H,c,L,R,hkeep,?_⟩
  dsimp only [NativeTailPolynomialFour67]
  norm_num only [Nat.cast_ofNat]
  rw [ht]
  nlinarith only [hraw,hDR,hdiff,hchooseR,hn]


#print axioms actual_resource_moebius_bound
#print axioms actual_resource_density_four
#print axioms middle_grid_scaling
#print axioms middle_nat_grid_bounds
#print axioms middle_nat_grid_scale
#print axioms actual_middle_resource_physical
#print axioms actual_middle_resource_sum67
#print axioms actual_prepared_CM_EM_endpoint67
#print axioms actual_original_prepared_endpoint67
#print axioms actual_original_refined_endpoint67
#print axioms actual_original_refined_tail67
end
end JSP233.ResourceBudget56
