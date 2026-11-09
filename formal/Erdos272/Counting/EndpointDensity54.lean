module

public import Erdos272.Counting.MiddleDeficit52
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Sharper actual finite coprime density and the full prepared-family
endpoint81 chain. No resource row or family count is supplied. -/
namespace JSP233.EndpointDensity54
open CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open StarCompletion APGeometry PreparedClasses50 APPrepare49 PreparedWitness48
open MiddleCoordinates51 DenseDeletion40 FamilyReflect43 RestrictedWitness44
open LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 5000

theorem reciprocal_square_128 : reciprocalSquareSum 128+(1/128:ℝ)≤329/200 := by
  norm_num [reciprocalSquareSum,Finset.sum_Icc_succ_top]

theorem reciprocal_square_upper (N : ℕ) : reciprocalSquareSum N≤329/200 := by
  have hf := reciprocal_square_128
  by_cases hN : N≤128
  · have hs : reciprocalSquareSum N≤reciprocalSquareSum 128 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,(Finset.mem_Icc.mp hd).2.trans hN⟩
      · intro d _hd _hnot
        positivity
    linarith only [hf,hs]
  · have he : Finset.Icc 1 N=Finset.Icc 1 128∪Finset.Ioc 128 N := by
      ext d
      simp only [Finset.mem_union,Finset.mem_Icc,Finset.mem_Ioc]
      omega
    have hd : Disjoint (Finset.Icc 1 128) (Finset.Ioc 128 N) := by
      exact Finset.disjoint_left.mpr (fun d h1 h2=>by
        have ha:=Finset.mem_Icc.mp h1
        have hb:=Finset.mem_Ioc.mp h2
        omega)
    have ht := sum_Ioc_inv_sq_le_sub (α:=ℝ) (k:=128) (by decide : (128:ℕ)≠0) (by omega : 128≤N)
    have hn : (0:ℝ)≤(N:ℝ)⁻¹ := by positivity
    have hh : reciprocalSquareSum N=reciprocalSquareSum 128+
        ∑d∈Finset.Ioc 128 N,((d:ℝ)^2)⁻¹ := by
      rw [reciprocalSquareSum,he,Finset.sum_union hd]
      rfl
    norm_num only [Nat.cast_ofNat] at ht
    linarith only [hf,ht,hn,hh]

theorem actual_coprime_density_lower {N : ℕ} (hN : 1≤N) :
    (200/329:ℝ)≤finiteCoprimeDensity N := by
  have hp : 0<reciprocalSquareSum N := by
    have hh := (reciprocalSquareSum_bounds hN).1
    linarith only [hh]
  change (200/329:ℝ)≤(reciprocalSquareSum N)⁻¹
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hp).mpr
  linarith only [reciprocal_square_upper N]

theorem retained_endpoint_deficit81 {n q c a x s : ℝ}
    (hq : 0≤q) (hc : 0≤c) (hx : 0≤x) (hsa : s≤a) (hn : n=q+c+a+x) :
    (5/3:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2≤
      n^2/2-((q+c)+x)^2/81 := by
  let L := q+c
  let y := a-s
  let w := x+y
  have hL : 0≤L := add_nonneg hq hc
  have hy : 0≤y := sub_nonneg.mpr hsa
  have hw : 0≤w := add_nonneg hx hy
  have hxw : x≤w := by dsimp [w];linarith only [hy]
  have he : n^2/2-((5/3:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2)-
      (L+w)^2/81=
      (y-w/2+(13/1200:ℝ)*L)^2+(77/324:ℝ)*(w-(22049/15400:ℝ)*L)^2+
        (20249/55440000:ℝ)*L^2+(329/200:ℝ)*q*y := by
    rw [hn]
    dsimp only [L,y,w]
    ring
  have hnon : 0≤n^2/2-((5/3:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2)-
      (L+w)^2/81 := by
    rw [he]
    positivity
  have hs : (L+x)^2≤(L+w)^2 :=
    (sq_le_sq₀ (add_nonneg hL hx) (add_nonneg hL hw)).mpr (by linarith only [hxw])
  change _≤n^2/2-(L+x)^2/81
  linarith only [hnon,hs]

theorem weighted_middle_endpoint_deficit81 {N c L R rho s : ℝ}
    (hc : 0≤c) (hcL : c≤L) (hRN : R≤N) (hs : s≤R-L)
    (hrho : 0≤rho) (hdensity : 1≤(329/200:ℝ)*rho) :
    rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*(N^2/2-(L+(N-R))^2/81) := by
  have hh := retained_endpoint_deficit81 (n:=N) (q:=L-c) (c:=c) (a:=R-L)
    (x:=N-R) (s:=s) (sub_nonneg.mpr hcL) hc (sub_nonneg.mpr hRN) hs (by ring)
  have hh' : (5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+
      s*R-s^2/2≤N^2/2-(L+(N-R))^2/81 := by
    convert hh using 1 <;> ring
  have hraw : rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2)≤
      rho*((5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2) := by
    apply sub_nonneg.mp
    have he : rho*((5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2)-
        (rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2))=
        ((329/200:ℝ)*rho-1)*(c*(R-L-s)) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hdensity) (mul_nonneg hc (sub_nonneg.mpr hs))
  exact hraw.trans (mul_le_mul_of_nonneg_left hh' hrho)

theorem actual_weighted_endpoint81 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (_hLR : L≤R) (hRN : R≤N)
    (s : ℕ→ℝ) (hs : ∀d∈Finset.Icc 1 N,0≤s d ∧ s d≤(R:ℝ)-L) :
    ((R:ℝ)+(2/3)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81 := by
  let outer := ((R:ℝ)+(2/3)*L)*(N-R)
  let bound := (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81
  let w := fun d:ℕ=>finiteCoprimeDensity N/(d:ℝ)^2
  let f := fun d:ℕ=>((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2
  have hrho := (finiteCoprimeDensity_bounds hN).1.le
  have hden : 1≤(329/200:ℝ)*finiteCoprimeDensity N := by
    have hh := actual_coprime_density_lower hN
    linarith only [hh]
  have hterms : ∀d∈Finset.Icc 1 N,w d*outer+f d≤w d*bound := by
    intro d hd
    have hh := weighted_middle_endpoint_deficit81
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

theorem actual_middle_resource_sum81 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(2/3)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81+
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
  have ht := actual_weighted_endpoint81 hN hcL hLR hRN s (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  push_cast
  linarith only [hc,ht]

theorem actual_prepared_CM_EM_endpoint81 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 1≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(2/3)*L)*(N-R)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81+
        (40*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_sum81 hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_original_prepared_endpoint81 {N : ℕ} {F : Finset (Finset ℤ)}
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
        (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81+
          (Deleted N 28 F).card+(WitnessException (Ground N) c:ℝ)+
          40*N*(HarmonicAbel29.Harmonic N)^2+6*N*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    actual_original_middle_reduction28 hN hF hcounter
  obtain ⟨P,hPG,hLP⟩ := hP
  have hPF := (Finset.mem_filter.mp hPG).1
  have hn : 1≤N := by
    have hh : 1≤2^49 := by norm_num
    exact hh.trans hN
  have hb := actual_prepared_CM_EM_endpoint81 x p hn (actual_retained_legal (r:=28) hLH)
    (by omega) hLR hRN hroot hPF hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,⟨P,hPG,hLP⟩,hT,henv,?_⟩
  nlinarith only [hb,hcount]

#print axioms reciprocal_square_128
#print axioms reciprocal_square_upper
#print axioms actual_coprime_density_lower
#print axioms retained_endpoint_deficit81
#print axioms weighted_middle_endpoint_deficit81
#print axioms actual_weighted_endpoint81
#print axioms actual_middle_resource_sum81
#print axioms actual_prepared_CM_EM_endpoint81
#print axioms actual_original_prepared_endpoint81
end
end JSP233.EndpointDensity54
