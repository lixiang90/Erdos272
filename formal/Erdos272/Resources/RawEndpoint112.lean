import Erdos272.Resources.ResourceBudget56
import Erdos272.Arithmetic.TwoSidedMoment62

/-!
The direct endpoint-width square completion, transported through the actual
finite-density physical resource pools and same-family prepared classes.
No fixed-rank large-N original-family wrapper is used.  The last endpoints
retain the actual root, actual retained family, two actual omitters, and the
same exterior envelope as explicit geometric inputs.
-/
namespace JSP233.RawEndpoint112
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def DeficitCoeff : ℝ := 3359/114959

def RawPolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*(x^3/6+11*x^2/2+19*x+527)

theorem deficit_identity (q c a x s : ℝ) :
    (q+c+a+x)^2/2-
      ((329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2)-
      DeficitCoeff*((q+c)+x)^2=
      (1/2:ℝ)*(a-s-(129/200:ℝ)*(q+c))^2+
      (329*x-(49159/200:ℝ)*(q+c))^2/(2*114959)+
      (329/200:ℝ)*q*(a-s) := by
  dsimp only [DeficitCoeff]
  ring

theorem retained_endpoint_deficit {n q c a x s : ℝ}
    (hq : 0≤q) (_hc : 0≤c) (_hx : 0≤x) (hsa : s≤a) (hn : n=q+c+a+x) :
    (329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2≤
      n^2/2-DeficitCoeff*((q+c)+x)^2 := by
  have hnon : 0≤(1/2:ℝ)*(a-s-(129/200:ℝ)*(q+c))^2+
      (329*x-(49159/200:ℝ)*(q+c))^2/(2*114959)+
      (329/200:ℝ)*q*(a-s) := by
    have hy : 0≤a-s := sub_nonneg.mpr hsa
    positivity
  have he := deficit_identity q c a x s
  rw [←hn] at he
  linarith only [he,hnon]

theorem weighted_middle_endpoint_deficit {N c L R rho s : ℝ}
    (hc : 0≤c) (hcL : c≤L) (hRN : R≤N) (hs : s≤R-L)
    (hrho : 0≤rho) (hdensity : 1≤(329/200:ℝ)*rho) :
    rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*(N^2/2-DeficitCoeff*(L+(N-R))^2) := by
  have hh := retained_endpoint_deficit (n:=N) (q:=L-c) (c:=c) (a:=R-L)
    (x:=N-R) (s:=s) (sub_nonneg.mpr hcL) hc (sub_nonneg.mpr hRN) hs (by ring)
  have hh' : (329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+
      s*R-s^2/2≤N^2/2-DeficitCoeff*(L+(N-R))^2 := by
    convert hh using 1 <;> ring
  have hraw : rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2)≤
      rho*((329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2) := by
    apply sub_nonneg.mp
    have he : rho*((329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2)-
        (rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2))=
        ((329/200:ℝ)*rho-1)*(c*(R-L-s)) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hdensity) (mul_nonneg hc (sub_nonneg.mpr hs))
  exact hraw.trans (mul_le_mul_of_nonneg_left hh' hrho)

theorem actual_weighted_endpoint {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (_hLR : L≤R) (hRN : R≤N)
    (s : ℕ→ℝ) (hs : ∀d∈Finset.Icc 1 N,0≤s d ∧ s d≤(R:ℝ)-L) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)≤
      (N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2 := by
  let outer := ((R:ℝ)+(129/200)*L)*(N-R)
  let bound := (N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2
  let w := fun d:ℕ=>finiteCoprimeDensity N/(d:ℝ)^2
  let f := fun d:ℕ=>((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2
  have hrho := (finiteCoprimeDensity_bounds hN).1.le
  have hden : 1≤(329/200:ℝ)*finiteCoprimeDensity N := by
    have hh := EndpointDensity54.actual_coprime_density_lower hN
    linarith only [hh]
  have hterms : ∀d∈Finset.Icc 1 N,w d*outer+f d≤w d*bound := by
    intro d hd
    have hh := weighted_middle_endpoint_deficit
      (N:=(N:ℝ)) (c:=(c:ℝ)) (L:=(L:ℝ)) (R:=(R:ℝ))
      (rho:=finiteCoprimeDensity N) (s:=s d)
      (Nat.cast_nonneg c) (by exact_mod_cast hcL) (by exact_mod_cast hRN) (hs d hd).2 hrho hden
    have hraw : finiteCoprimeDensity N*outer+(c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2)≤finiteCoprimeDensity N*bound := by
      dsimp only [outer,bound]
      convert hh using 1
      ring
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

theorem actual_middle_resource_sum {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2+
          (4*Harmonic N+2)*N*Harmonic N := by
  have hx : ∀d:ℕ,∃s:ℝ,d∈Finset.Icc 1 N→0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*Harmonic N+2)*N/d := by
    intro d
    by_cases hd:d∈Finset.Icc 1 N
    · obtain ⟨s,hs⟩ := ResourceBudget56.actual_middle_resource_physical hN hcL hLR hRN
        (Finset.mem_Icc.mp hd).1 (he d hd).1 (he d hd).2
      exact ⟨s,fun _=>hs⟩
    · exact ⟨0,fun hh=>False.elim (hd hh)⟩
  choose s hs using hx
  have hc := Finset.sum_le_sum (fun d hd=>(hs d hd).2.2)
  have herr : (∑d∈Finset.Icc 1 N,(4*Harmonic N+2)*N/(d:ℝ))=
      (4*Harmonic N+2)*N*Harmonic N := by
    simp only [Harmonic,div_eq_mul_inv,←Finset.mul_sum,one_mul]
  rw [Finset.sum_add_distrib,herr] at hc
  have ht := actual_weighted_endpoint hN hcL hLR hRN s (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  push_cast
  linarith only [hc,ht]

theorem actual_prepared_CM_EM_endpoint {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 1≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)≤
      (N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2+
        (4*Harmonic N+2)*N*Harmonic N := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_sum hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_prepared_family_raw {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 1≤N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2+
      (WitnessException (Ground N) c:ℝ)+4*N*(Harmonic N)^2+
        6*N*Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c:ℤ)≤L) (by exact_mod_cast hLR : (L:ℤ)≤R) hT hcT hTR
  have hp := actual_joint_preparation_loss hG hroot hP hcP hLP
  have hm := EndpointExterior55.actual_prepared_middle_reduction x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hr := actual_prepared_CM_EM_endpoint x p hN hG hcL.le hLR hRN hroot hP hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  nlinarith only [hp,hm,hr]

theorem actual_prepared_family_raw_half {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c:ℤ)∈Ground N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+4*N*(Harmonic N)^2+
        6*N*Harmonic N+24*N+(L-c:ℕ)+3 := by
  have hground := (mem_ground N (c:ℤ)).mp hc
  have hN : 1≤N := by omega
  have hr := actual_prepared_family_raw hN hG hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have hw := TwoSidedMoment62.actual_simplex_exception_half hc
  linarith only [hr,hw]

theorem actual_retained11_raw_half {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hNr : 10185≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (F.card:ℝ)≤(N:ℝ)^2/2-DeficitCoeff*((L:ℝ)+(N-R))^2+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+4*N*(Harmonic N)^2+
        6*N*Harmonic N+509*N+(L-c:ℕ)+3 := by
  have hr := actual_prepared_family_raw_half hc (actual_retained_legal hF)
    hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have hd := DenseSharper41.actual_retained_sharp_lower (r:=11) (by decide : 0<11)
    (by norm_num;exact hNr) hF
  have hdR : (F.card:ℝ)≤(Retained N 11 F).card+485*N := by exact_mod_cast hd
  linarith only [hr,hdR]

theorem actual_retained11_width {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hNr : 10185≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*RawPolynomial (Real.log N) := by
  have hr := actual_retained11_raw_half hNr hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hdiff : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hcB : N.choose 2≤F.card := by unfold B at hcard;omega
  have hcR : (N.choose 2:ℝ)≤F.card := by exact_mod_cast hcB
  rw [Nat.cast_choose_two] at hcR
  have hcost : DeficitCoeff*((L:ℝ)+(N-R))^2≤
      (N:ℝ)*(SimplexPolynomial (Real.log N) (Harmonic N)/2+
        4*(Harmonic N)^2+6*Harmonic N+514) := by
    nlinarith only [hr,hdiff,hcR,hn]
  have hh := HarmonicLog55.actual_harmonic_log_586 (N:=N) (by omega : 63≤N)
  have hh1 : Harmonic N≤Real.log (N:ℝ)+1 := by linarith only [hh]
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg hn
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+1)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+
      4*(Harmonic N)^2+6*Harmonic N+514≤
      (Real.log N)^3/6+11*(Real.log N)^2/2+19*Real.log N+527 := by
    dsimp only [SimplexPolynomial]
    nlinarith only [hh1,hhsq]
  have htotal := hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))
  dsimp only [DeficitCoeff] at htotal
  dsimp only [RawPolynomial]
  nlinarith only [htotal]

#print axioms deficit_identity
#print axioms retained_endpoint_deficit
#print axioms weighted_middle_endpoint_deficit
#print axioms actual_weighted_endpoint
#print axioms actual_middle_resource_sum
#print axioms actual_prepared_CM_EM_endpoint
#print axioms actual_prepared_family_raw
#print axioms actual_prepared_family_raw_half
#print axioms actual_retained11_raw_half
#print axioms actual_retained11_width
end
end JSP233.RawEndpoint112
