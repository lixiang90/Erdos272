module

public import Erdos272.Resources.RawEndpoint114
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Keep the actual left/right quadratic profile before taking its worst ray.
The only extra readded-family loss is the actual deleted-avoider fringe.
Its original 165*w <=4*N gate suffices; no 42*w <=N bootstrap is assumed here.
No balanced/Bad-family dichotomy or original-family startup is asserted. -/
namespace JSP233.RawEndpoint115
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def ProfileDeficit (L x : ℝ) : ℝ :=
  (23359/80000:ℝ)*L^2-(129/200:ℝ)*L*x+x^2/2

def CorePolynomial (x : ℝ) : ℝ :=
  x^3/6+11*x^2/2+(1961/125:ℝ)*x+2042599/62500

def RefinedPolynomial (x : ℝ) : ℝ := (114959/3359:ℝ)*CorePolynomial x

theorem profile_square_identity (L x : ℝ) :
    ProfileDeficit L x=DeficitCoeff*(L+x)^2+
      (329*x-(49159/200:ℝ)*L)^2/(2*114959) := by
  dsimp only [ProfileDeficit,DeficitCoeff]
  ring

theorem retained_endpoint_profile {n q c a x s : ℝ}
    (hq : 0≤q) (hsa : s≤a) (hn : n=q+c+a+x) :
    (329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2≤
      n^2/2-ProfileDeficit (q+c) x := by
  have he := RawEndpoint112.deficit_identity q c a x s
  have hp := profile_square_identity (q+c) x
  have hnon : 0≤(1/2:ℝ)*(a-s-(129/200:ℝ)*(q+c))^2+
      (329/200:ℝ)*q*(a-s) := by
    have hh : 0≤a-s := sub_nonneg.mpr hsa
    positivity
  rw [←hn] at he
  linarith only [he,hp,hnon]

theorem weighted_middle_endpoint_profile {N c L R rho s : ℝ}
    (hc : 0≤c) (hcL : c≤L) (_hRN : R≤N) (hs : s≤R-L)
    (hrho : 0≤rho) (hdensity : 1≤(329/200:ℝ)*rho) :
    rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*(N^2/2-ProfileDeficit L (N-R)) := by
  have hh := retained_endpoint_profile (n:=N) (q:=L-c) (c:=c) (a:=R-L)
    (x:=N-R) (s:=s) (sub_nonneg.mpr hcL) hs (by ring)
  have hleft : L-c+c=L := by ring
  have hright : L+(R-L)=R := by ring
  rw [hleft,hright] at hh
  have hh' : (329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+
      s*R-s^2/2≤N^2/2-ProfileDeficit L (N-R) := hh
  have hraw : rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2)≤
      rho*((329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2) := by
    apply sub_nonneg.mp
    have he : rho*((329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+s*R-s^2/2)-
        (rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+rho*(s*R-s^2/2))=
        ((329/200:ℝ)*rho-1)*(c*(R-L-s)) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hdensity) (mul_nonneg hc (sub_nonneg.mpr hs))
  exact hraw.trans (mul_le_mul_of_nonneg_left hh' hrho)

theorem actual_weighted_endpoint_profile {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (_hLR : L≤R) (hRN : R≤N)
    (s : ℕ→ℝ) (hs : ∀d∈Finset.Icc 1 N,0≤s d ∧ s d≤(R:ℝ)-L) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)≤
      (N:ℝ)^2/2-ProfileDeficit L (N-R) := by
  let outer := ((R:ℝ)+(129/200)*L)*(N-R)
  let bound := (N:ℝ)^2/2-ProfileDeficit L (N-R)
  let w := fun d:ℕ=>finiteCoprimeDensity N/(d:ℝ)^2
  let f := fun d:ℕ=>((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2
  have hrho := (finiteCoprimeDensity_bounds hN).1.le
  have hden : 1≤(329/200:ℝ)*finiteCoprimeDensity N := by
    have hh := EndpointDensity54.actual_coprime_density_lower hN
    linarith only [hh]
  have hterms : ∀d∈Finset.Icc 1 N,w d*outer+f d≤w d*bound := by
    intro d hd
    have hh := weighted_middle_endpoint_profile
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

theorem actual_middle_resource_profile {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-ProfileDeficit L (N-R)+(4*Harmonic N+2)*N*Harmonic N := by
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
  have ht := actual_weighted_endpoint_profile hN hcL hLR hRN s (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  push_cast
  linarith only [hc,ht]

theorem actual_prepared_CM_EM_profile {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 1≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)≤
      (N:ℝ)^2/2-ProfileDeficit L (N-R)+(4*Harmonic N+2)*N*Harmonic N := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_profile hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_prepared_family_raw_profile {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c:ℤ)∈Ground N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+4*N*(Harmonic N)^2+
      6*N*Harmonic N+24*N+(L-c:ℕ)+3 := by
  have hground := (mem_ground N (c:ℤ)).mp hc
  have hN : 1≤N := by omega
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c:ℤ)≤L) (by exact_mod_cast hLR : (L:ℤ)≤R) hT hcT hTR
  have hp := actual_joint_preparation_loss hG hroot hP hcP hLP
  have hm := EndpointExterior55.actual_prepared_middle_reduction x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hr := actual_prepared_CM_EM_profile x p hN hG hcL.le hLR hRN hroot hP hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hw := TwoSidedMoment62.actual_simplex_exception_half hc
  nlinarith only [hp,hm,hr,hw]

theorem actual_readded11_raw_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (F.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+4*N*(Harmonic N)^2+
      6*N*Harmonic N+24*N+(L-c:ℕ)+3+
      (TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  let G := RawEndpoint114.Readded N F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hGF : G⊆F := Finset.sdiff_subset
  have hGlegal : Legal (Ground N) G := ⟨fun S hS=>hF.1 S (hGF hS),
    fun S hS U hU he=>hF.2 S (hGF hS) U (hGF hU) he⟩
  have hsub := RawEndpoint114.actual_retained_subset_readded N F (c:ℤ)
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c:ℤ)
  have hout : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    have hv : S∈Avoiders G (c:ℤ) := Finset.mem_filter.mpr ⟨hS,hcS⟩
    change Avoiders G (c:ℤ)=_ at ha
    rw [ha] at hv
    exact houtside S (Finset.mem_filter.mp hv).1 hcS
  have hr := actual_prepared_family_raw_profile hc hGlegal hcL hLR hRN
    (RawEndpoint114.actual_readded_root hroot) (hsub hP) hcP hLP (hsub hT) hcT hTR hout
  have hcard := Finset.card_sdiff_add_card_eq_card hEF
  have hcardR : (G.card:ℝ)+E.card=F.card := by exact_mod_cast hcard
  dsimp only [E] at hcardR
  linarith only [hr,hcardR]

theorem actual_deleted_avoider_count55 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 225≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgeometry : 165*(L+N-R)≤4*N) (hlarge : 90<L+N-R) :
    (TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card≤55*(L+N-R) := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀S∈E,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hdense : ∀S∈E,N<11*S.card := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  obtain ⟨H,hHG,hHAP,hKH⟩ := RestoreTerminal35.actual_interval_core_member N c L R
    (Retained N 11 F) hLR hne hi
  have hHF : H∈F := (Finset.mem_sdiff.mp hHG).1
  have hcN := (mem_ground N (c:ℤ)).mp hc
  have hL : 1≤L := by omega
  have hb := CeilFringe113.actual_dense_fringe_bound55 hN hL hLR hRN hlarge
    hF hEF hbad hdense ⟨H,hHF,hHAP,hKH⟩ hgeometry
  have hext := ThinFringe33.ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hextle : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card≤L+N-R := by omega
  exact hb.trans (Nat.mul_le_mul_left 55 hextle)

theorem core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x+293/500)/2+4*(x+293/500)^2+
      6*(x+293/500)+1281/50=CorePolynomial x := by
  dsimp only [SimplexPolynomial,CorePolynomial]
  ring

theorem actual_readded11_profile_width {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 3000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgeometry : 165*(L+N-R)≤4*N) (hlarge : 90<L+N-R) :
    ProfileDeficit L (N-R)≤(N:ℝ)*CorePolynomial (Real.log N) := by
  have hr := actual_readded11_raw_profile hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩⟩
  have hcount := actual_deleted_avoider_count55 (by omega : 225≤N)
    hc hF hcL hLR hRN hne hi hgeometry hlarge
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card:ℝ)≤
      55*((L+N-R:ℕ):ℝ) := by exact_mod_cast hcount
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast hN
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add];ring
  rw [he] at hcountR
  have ht : (165:ℝ)*((L:ℝ)+(N-R))≤4*N := by
    have hh : (165:ℝ)*((L+N-R:ℕ):ℝ)≤4*N := by exact_mod_cast hgeometry
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : ProfileDeficit L (N-R)≤(N:ℝ)*
      (SimplexPolynomial (Real.log N) (Harmonic N)/2+4*(Harmonic N)^2+
        6*Harmonic N+1281/50) := by
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  have hh := actual_harmonic_log_586 (N:=N) (by omega : 63≤N)
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+293/500)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+4*(Harmonic N)^2+
      6*Harmonic N+1281/50≤CorePolynomial (Real.log N) := by
    rw [←core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh,hhsq]
  exact hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))

theorem profile_ge_three_fiftieths_of_unbalanced {L x : ℝ}
    (hL : 0≤L) (hx : 0≤x) (hu : 3*x≤L ∨ 3*L≤x) :
    (3/50:ℝ)*(L+x)^2≤ProfileDeficit L x := by
  rcases hu with h | h
  · have he : ProfileDeficit L x-(3/50:ℝ)*(L+x)^2=
        (18631/80000:ℝ)*x^2+(25077/40000:ℝ)*x*(L-3*x)+(18559/80000:ℝ)*(L-3*x)^2 := by
      dsimp only [ProfileDeficit];ring
    have hn : 0≤(18631/80000:ℝ)*x^2+(25077/40000:ℝ)*x*(L-3*x)+(18559/80000:ℝ)*(L-3*x)^2 := by
      have hd : 0≤L-3*x := sub_nonneg.mpr h
      positivity
    linarith only [he,hn]
  · have he : ProfileDeficit L x-(3/50:ℝ)*(L+x)^2=
        (151759/80000:ℝ)*L^2+(15/8:ℝ)*L*(x-3*L)+(11/25:ℝ)*(x-3*L)^2 := by
      dsimp only [ProfileDeficit];ring
    have hn : 0≤(151759/80000:ℝ)*L^2+(15/8:ℝ)*L*(x-3*L)+(11/25:ℝ)*(x-3*L)^2 := by
      have hd : 0≤x-3*L := sub_nonneg.mpr h
      positivity
    linarith only [he,hn]

theorem profile_ge_double_deficit_of_unbalanced {L x : ℝ}
    (hL : 0≤L) (hx : 0≤x) (hu : 3*x≤L ∨ 3*L≤x) :
    2*DeficitCoeff*(L+x)^2≤ProfileDeficit L x := by
  have hh := profile_ge_three_fiftieths_of_unbalanced hL hx hu
  have hc : 2*DeficitCoeff≤(3/50:ℝ) := by norm_num [DeficitCoeff]
  exact (mul_le_mul_of_nonneg_right hc (sq_nonneg (L+x))).trans hh

theorem profile_width_payment_of_unbalanced {N L x : ℝ}
    (_hN : 0≤N) (hL : 0≤L) (hx : 0≤x) (hu : 3*x≤L ∨ 3*L≤x)
    (hprofile : ProfileDeficit L x≤N*CorePolynomial (Real.log N)) :
    (L+x)^2≤N*RefinedPolynomial (Real.log N)/2 := by
  have hh := (profile_ge_double_deficit_of_unbalanced hL hx hu).trans hprofile
  dsimp only [DeficitCoeff] at hh
  dsimp only [RefinedPolynomial]
  nlinarith only [hh]

theorem actual_readded11_width {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 3000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgeometry : 165*(L+N-R)≤4*N) (hlarge : 90<L+N-R) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*RefinedPolynomial (Real.log N) := by
  have hp := actual_readded11_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hgeometry hlarge
  have he := profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [RefinedPolynomial]
  nlinarith only [hp,he,hs]

theorem actual_readded11_width_side {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 3000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hgeometry : 165*(L+N-R)≤4*N) (hlarge : 90<L+N-R)
    (hside : 4*L≤L+N-R ∨ 4*(N-R)≤L+N-R) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*RefinedPolynomial (Real.log N)/2 := by
  have hp := actual_readded11_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hgeometry hlarge
  have hcast : ((N-R:ℕ):ℝ)=(N:ℝ)-R := Nat.cast_sub hRN
  have huN : 3*(N-R)≤L ∨ 3*L≤N-R := by omega
  have hu : 3*((N-R:ℕ):ℝ)≤L ∨ 3*(L:ℝ)≤((N-R:ℕ):ℝ) := by exact_mod_cast huN
  have hp' : ProfileDeficit L ((N-R:ℕ):ℝ)≤(N:ℝ)*CorePolynomial (Real.log N) := by
    simpa only [hcast] using hp
  have hh := profile_width_payment_of_unbalanced (Nat.cast_nonneg N) (Nat.cast_nonneg L)
    (Nat.cast_nonneg (N-R)) hu hp'
  simpa only [hcast] using hh

#print axioms profile_square_identity
#print axioms retained_endpoint_profile
#print axioms weighted_middle_endpoint_profile
#print axioms actual_weighted_endpoint_profile
#print axioms actual_middle_resource_profile
#print axioms actual_prepared_CM_EM_profile
#print axioms actual_prepared_family_raw_profile
#print axioms actual_readded11_raw_profile
#print axioms actual_deleted_avoider_count55
#print axioms core_harmonic_identity
#print axioms actual_readded11_profile_width
#print axioms profile_ge_three_fiftieths_of_unbalanced
#print axioms profile_ge_double_deficit_of_unbalanced
#print axioms profile_width_payment_of_unbalanced
#print axioms actual_readded11_width
#print axioms actual_readded11_width_side
end
end JSP233.RawEndpoint115
