module

public import Erdos272.Counting.EndpointDensity54
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual EX129/200 endpoint rectangles and the complete same-family raw67
resource chain. No exterior-family capacity or middle resource row is supplied. -/
namespace JSP233.EndpointExterior55
open CoprimeDensity52 MiddleJoint51 MiddleDeficit52 EndpointDensity54
open StarCompletion APGeometry APCount41 APExterior50 PreparedClasses50 APPrepare49 PreparedWitness48
open MiddleCoordinates51 DenseDeletion40 FamilyReflect43 RestrictedWitness44
open LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 5000

theorem reciprocal_square_tail_two (N : ℕ) :
    (∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)≤129/200 := by
  simp only [one_div]
  by_cases hN : 1≤N
  · have hsplit : Finset.Icc 1 N=insert 1 (Finset.Icc 2 N) := by
      ext d
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    have hh := reciprocal_square_upper N
    dsimp only [reciprocalSquareSum] at hh
    rw [hsplit,Finset.sum_insert (by simp)] at hh
    norm_num only [Nat.cast_one,one_pow,inv_one] at hh
    linarith only [hh]
  · have hz : N=0 := by omega
    norm_num [hz]

theorem actual_large_step_endpoint_count {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hLN : L≤N) (hRN : R≤N) (hF : Legal (Ground N) F)
    (hAP : ∀ S∈F,IsAP S) (htwo : ∀ S∈F,2≤S.card)
    (hlarge : ∀ S∈F,2≤Step S) (hends : ∀ S∈F,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    (F.card:ℝ)≤(129/200)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hmaps : Set.MapsTo Step (F:Set (Finset ℤ)) (Finset.Icc 2 N) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨hlarge S hS,actual_step_bound (hF.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card:ℝ)=∑ d∈Finset.Icc 2 N,((F.filter (fun S=>Step S=d)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ d∈Finset.Icc 2 N,((F.filter (fun S=>Step S=d)).card:ℝ)≤
      (L:ℝ)*(N-R)/(d:ℝ)^2+2*N/d+1 := by
    intro d hd
    have hAF : F.filter (fun S=>Step S=d)⊆F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) (F.filter (fun S=>Step S=d)) :=
      ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
    apply actual_same_step_endpoint_real hLN hRN (by have hh:=Finset.mem_Icc.mp hd;omega) hlegal
      (fun S hS=>isAP_nonempty (hAP S (hAF hS)))
    · intro S hS
      obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
      obtain ⟨_,p,hp⟩ := actual_step (hAP S hSF)
      exact ⟨p,by simpa only [hSd] using hp⟩
    · exact fun S hS=>hends S (hAF hS)
  have hinv : (∑ d∈Finset.Icc 2 N,(d:ℝ)⁻¹)≤HarmonicAbel29.Harmonic N := by
    simp only [HarmonicAbel29.Harmonic,one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hd,hdN⟩ := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega,hdN⟩
    · intro d _ _
      positivity
  have hcardI : ((Finset.Icc 2 N).card:ℝ)≤N := by
    exact_mod_cast (show (Finset.Icc 2 N).card≤N by rw [Nat.card_Icc];omega)
  have hsum : (F.card:ℝ)≤(L:ℝ)*(N-R)*(∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)+
      2*N*(∑ d∈Finset.Icc 2 N,(d:ℝ)⁻¹)+(Finset.Icc 2 N).card := by
    calc
      _≤∑ d∈Finset.Icc 2 N,((L:ℝ)*(N-R)/(d:ℝ)^2+2*N/d+1) := by
        rw [hpart]
        exact Finset.sum_le_sum hbound
      _=_ := by simp only [div_eq_mul_inv,one_mul,Finset.sum_add_distrib,←Finset.mul_sum,
        Finset.sum_const,nsmul_eq_mul,mul_one]
  have hRN' : (R:ℝ)≤N := by exact_mod_cast hRN
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail_two N)
    (show (0:ℝ)≤(L:ℝ)*(N-R) by positivity)
  have hharm := mul_le_mul_of_nonneg_left hinv (show (0:ℝ)≤2*N by positivity)
  linarith only [hsum,hquad,hharm,hcardI]

theorem actual_exterior_AP_count {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hLN : L≤N) (hRN : R≤N) :
    ((ExteriorAP F L R).card:ℝ)≤(129/200)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hEF : ExteriorAP F L R⊆F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (ExteriorAP F L R) :=
    ⟨fun S hS=>hF.1 S (hEF hS),fun S hS T hT hne=>hF.2 S (hEF hS) T (hEF hT) hne⟩
  apply actual_large_step_endpoint_count hLN hRN hlegal
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.2.2

theorem actual_selected_exterior_count {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hLN : L≤N) (hRN : R≤N) (hEF : E⊆F)
    (hAP : ∀ S∈E,IsAP S) (htwo : ∀ S∈E,2≤S.card)
    (hlarge : ∀ S∈E,2≤Step S) (hends : ∀ S∈E,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    (E.card:ℝ)≤(129/200)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hs : E⊆ExteriorAP F L R := by
    intro S hS
    exact Finset.mem_filter.mpr ⟨hEF hS,hAP S hS,htwo S hS,hlarge S hS,hends S hS⟩
  have hh : (E.card:ℝ)≤(ExteriorAP F L R).card := by exact_mod_cast Finset.card_le_card hs
  exact hh.trans (actual_exterior_AP_count hF hLN hRN)
theorem actual_prepared_EX_count {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hP : P∈G) (hLP : ∀z∈P,(L:ℤ)≤z)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    ((EX (PreparedAP G c L) R).card:ℝ)≤
      (129/200)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hmember := fun S hS=>actual_EX_endpoints hG hcL hP hLP houtside (S:=S) hS
  apply actual_selected_exterior_count hG (by omega) hRN
    (fun S hS=>(hmember S hS).1)
    (fun S hS=>(hmember S hS).2.1)
  · intro S hS
    have hh := (hmember S hS).2.2.1
    omega
  · exact fun S hS=>(hmember S hS).2.2.2.1
  · exact fun S hS=>(hmember S hS).2.2.2.2

theorem actual_prepared_middle_reduction {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (x p : Finset ℤ→ℤ) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hP : P∈G) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hW : ∀S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S} ∧ x S≤(R:ℤ) ∧ x S≠(L:ℤ) ∧
      ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) :
    ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)+2*N*HarmonicAbel29.Harmonic N+3*N+(L-c:ℕ) := by
  have hcorner := actual_prepared_corner_reduction x p hG hcL hLR hP hLP hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.1,(hW S hS).2.2.1⟩)
  have hright := actual_prepared_right_joint x p hG hcL hLR hRN hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.2.2⟩)
  have hEB := actual_EB_count (by omega : c<R) houtside
  have hEX := actual_prepared_EX_count hG hcL hLR hRN hP hLP houtside
  have hcombined : (PreparedCrooked G c L).card+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+R*(N-R)+2*N+(L-c) := by
    have hpoly : c*(N-R)+(R-L)*(N-R)+(L-c)*(N-R)=R*(N-R) := by
      rw [←Nat.add_mul,←Nat.add_mul]
      congr 1
      omega
    omega
  have hreal : ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+(R:ℝ)*(N-R)+2*N+(L-c:ℕ) := by
    have hh : ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
        (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
        (EX (PreparedAP G c L) R).card+(R*(N-R):ℕ)+(2*N:ℕ)+(L-c:ℕ) := by exact_mod_cast hcombined
    simpa only [Nat.cast_mul,Nat.cast_sub hRN,Nat.cast_ofNat] using hh
  nlinarith only [hreal,hEX]

theorem actual_original_middle_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
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
        ∃x p:Finset ℤ→ℤ,
          (∀S∈PreparedCrooked (Retained N 28 H) c L,
            IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤(R:ℤ) ∧ (L:ℤ)<p S ∧ x S≠(L:ℤ) ∧
            ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
              S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) ∧
          ((F.card:ℝ)≤(CM (PreparedCrooked (Retained N 28 H) c L) p R).card+
            (EM (PreparedAP (Retained N 28 H) c L) c R).card+
            ((R:ℝ)+(129/200)*L)*(N-R)+(Deleted N 28 F).card+
            (WitnessException (Ground N) c:ℝ)+4*(N:ℝ)*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3) := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    actual_original_corner_reduction28 hN hF hcounter
  obtain ⟨P,hP,hLP⟩ := hP
  obtain ⟨hPF,hcP⟩ := Finset.mem_filter.mp hP
  have hlegal := actual_retained_legal (r:=28) hLH
  have houtside : ∀S∈Retained N 28 H,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    obtain ⟨⟨a,ha,haL,_⟩,b,hb,hRb,_⟩ := henv S (Finset.mem_filter.mpr ⟨hS,hcS⟩)
    exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
  have hright := actual_prepared_right_joint x p hlegal hLc hLR hRN hroot houtside
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.2.2.2⟩)
  have hEX := actual_prepared_EX_count hlegal hLc hLR hRN hPF hLP houtside
  have hEB := actual_EB_count (by omega : c<R) houtside
  have hrightR : ((CQ (PreparedCrooked (Retained N 28 H) c L) x p c L R).card:ℝ)+
      (EP (PreparedAP (Retained N 28 H) c L) c R).card≤
      ((L-c)*(N-R):ℕ)+(2*N:ℕ) := by exact_mod_cast hright
  have hEBR : ((EB (PreparedAP (Retained N 28 H) c L) c R).card:ℝ)≤(L-c:ℕ) := by
    exact_mod_cast hEB
  have hpoly : c*(N-R)+(R-L)*(N-R)+(L-c)*(N-R)=R*(N-R) := by
    rw [←Nat.add_mul,←Nat.add_mul]
    congr 1
    omega
  have hpolyR : ((c*(N-R)+(R-L)*(N-R):ℕ):ℝ)+((L-c)*(N-R):ℕ)=(R:ℝ)*(N-R) := by
    rw [←Nat.cast_add,hpoly,Nat.cast_mul,Nat.cast_sub hRN]
  dsimp only [Residual] at hcount
  simp only [Nat.cast_add] at hcount
  simp only [Nat.cast_add] at hpolyR
  have htwoN : ((2*N:ℕ):ℝ)=2*(N:ℝ) := by norm_num
  have hfinal : (F.card:ℝ)≤(CM (PreparedCrooked (Retained N 28 H) c L) p R).card+
      (EM (PreparedAP (Retained N 28 H) c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)+(Deleted N 28 F).card+
      (WitnessException (Ground N) c:ℝ)+4*(N:ℝ)*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
    nlinarith only [hcount,hrightR,hEX,hEBR,hpolyR,htwoN]
  exact ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,
    ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩,hLP⟩,hT,henv,x,p,hx,hfinal⟩
theorem retained_endpoint_deficit67 {n q c a x s : ℝ}
    (hq : 0≤q) (hc : 0≤c) (hx : 0≤x) (hsa : s≤a) (hn : n=q+c+a+x) :
    (329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2≤
      n^2/2-((q+c)+x)^2/67 := by
  let L := q+c
  let y := a-s
  let w := x+y
  have hL : 0≤L := add_nonneg hq hc
  have hy : 0≤y := sub_nonneg.mpr hsa
  have hw : 0≤w := add_nonneg hx hy
  have hxw : x≤w := by dsimp [w];linarith only [hy]
  have he : n^2/2-((329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2)-
      (L+w)^2/67=
      (x-y)^2/4+(63/268:ℝ)*(w-(9043/6300:ℝ)*L)^2+
        (1853/2520000:ℝ)*L^2+(329/200:ℝ)*q*y := by
    rw [hn]
    dsimp only [L,y,w]
    ring
  have hnon : 0≤n^2/2-((329/200:ℝ)*x*(q+c)+a*x+(329/200:ℝ)*c*(a-s)+s*(q+c+a)-s^2/2)-
      (L+w)^2/67 := by
    rw [he]
    positivity
  have hs : (L+x)^2≤(L+w)^2 :=
    (sq_le_sq₀ (add_nonneg hL hx) (add_nonneg hL hw)).mpr (by linarith only [hxw])
  change _≤n^2/2-(L+x)^2/67
  linarith only [hnon,hs]

theorem weighted_middle_endpoint_deficit67 {N c L R rho s : ℝ}
    (hc : 0≤c) (hcL : c≤L) (hRN : R≤N) (hs : s≤R-L)
    (hrho : 0≤rho) (hdensity : 1≤(329/200:ℝ)*rho) :
    rho*((329/200:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*(N^2/2-(L+(N-R))^2/67) := by
  have hh := retained_endpoint_deficit67 (n:=N) (q:=L-c) (c:=c) (a:=R-L)
    (x:=N-R) (s:=s) (sub_nonneg.mpr hcL) hc (sub_nonneg.mpr hRN) hs (by ring)
  have hh' : (329/200:ℝ)*(N-R)*L+(R-L)*(N-R)+(329/200:ℝ)*c*(R-L-s)+
      s*R-s^2/2≤N^2/2-(L+(N-R))^2/67 := by
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

theorem actual_weighted_endpoint67 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (_hLR : L≤R) (hRN : R≤N)
    (s : ℕ→ℝ) (hs : ∀d∈Finset.Icc 1 N,0≤s d ∧ s d≤(R:ℝ)-L) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+
        finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)≤
      (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67 := by
  let outer := ((R:ℝ)+(129/200)*L)*(N-R)
  let bound := (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67
  let w := fun d:ℕ=>finiteCoprimeDensity N/(d:ℝ)^2
  let f := fun d:ℕ=>((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2
  have hrho := (finiteCoprimeDensity_bounds hN).1.le
  have hden : 1≤(329/200:ℝ)*finiteCoprimeDensity N := by
    have hh := actual_coprime_density_lower hN
    linarith only [hh]
  have hterms : ∀d∈Finset.Icc 1 N,w d*outer+f d≤w d*bound := by
    intro d hd
    have hh := weighted_middle_endpoint_deficit67
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

theorem actual_middle_resource_sum67 {N c L R : ℕ}
    (hN : 1≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+
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
        (40*HarmonicAbel29.Harmonic N+2)*N*HarmonicAbel29.Harmonic N := by
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
          40*N*(HarmonicAbel29.Harmonic N)^2+6*N*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    actual_original_middle_reduction28 hN hF hcounter
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

#print axioms reciprocal_square_tail_two
#print axioms actual_large_step_endpoint_count
#print axioms actual_exterior_AP_count
#print axioms actual_selected_exterior_count
#print axioms actual_prepared_EX_count
#print axioms actual_prepared_middle_reduction
#print axioms actual_original_middle_reduction28
#print axioms retained_endpoint_deficit67
#print axioms weighted_middle_endpoint_deficit67
#print axioms actual_weighted_endpoint67
#print axioms actual_middle_resource_sum67
#print axioms actual_prepared_CM_EM_endpoint67
#print axioms actual_original_prepared_endpoint67
end
end JSP233.EndpointExterior55
