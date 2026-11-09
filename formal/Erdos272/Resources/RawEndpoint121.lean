module

public import Erdos272.Resources.LocalMobius121
public import Erdos272.Arithmetic.HarmonicDiv121
public import Erdos272.Resources.RawEndpoint118
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Sum actual local-cutoff middle rows at their common physical density.
The reciprocal cutoff loss is paid by half of its true local area. A finite cubic cutoff leaves only an absolute square-sum loss. The full
same-family raw profile and independent68-class bootstrap are retained before any new restoration count is used. -/
namespace JSP233.RawEndpoint121
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def BootstrapCorePolynomial (x : ℝ) : ℝ :=
  x^3/6+7*x^2/2+(817/50)*x+148579/4000

def BootstrapPolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*BootstrapCorePolynomial x

theorem actual_middle_resource_profile {N c L R : ℕ}
    (hN : 16≤N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (e:ℕ→ℕ) (he : ∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) :
    ((R:ℝ)+(129/200)*L)*(N-R)+
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)≤
        (N:ℝ)^2/2-ProfileDeficit L (N-R)+2*N*(Real.log N)^2+
          (61/25)*N*Real.log N+(49/10)*N*Harmonic N+(86/25)*N+987/200 := by
  have hx : ∀d:ℕ,∃s:ℝ,d∈Finset.Icc 1 N→0≤s ∧ s≤(R:ℝ)-L ∧
      (ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℝ)≤
        ((c:ℝ)*((R:ℝ)-L-s)+finiteCoprimeDensity N*(s*R-s^2/2))/(d:ℝ)^2+
          (4*Harmonic (N/d)+5/2)*N/d+3/(d:ℝ)^2 := by
    intro d
    by_cases hd:d∈Finset.Icc 1 N
    · obtain ⟨s,hs⟩ := LocalMobius121.actual_middle_resource_physical (by omega : 1≤N) hcL hLR hRN
        (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 (he d hd).1 (he d hd).2
      exact ⟨s,fun _=>hs⟩
    · exact ⟨0,fun hh=>False.elim (hd hh)⟩
  choose s hs using hx
  have hc := Finset.sum_le_sum (fun d hd=>(hs d hd).2.2)
  have herr : (∑d∈Finset.Icc 1 N,((4*Harmonic (N/d)+5/2)*N/d+3/(d:ℝ)^2))=
      4*N*(∑d∈Finset.Icc 1 N,Harmonic (N/d)/(d:ℝ))+
        (5/2)*N*Harmonic N+3*reciprocalSquareSum N := by
    calc
      _=∑d∈Finset.Icc 1 N,(4*(N:ℝ)*(Harmonic (N/d)/(d:ℝ))+
          (5/2)*N*(1/(d:ℝ))+3*((d:ℝ)^2)⁻¹) := by
        apply Finset.sum_congr rfl
        intro d _hd
        ring
      _=_ := by
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]
        rfl
  have hsum := HarmonicDiv121.actual_harmonic_div_sum61 hN
  have hpoly := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤4*N by positivity)
  have hden := mul_le_mul_of_nonneg_left (EndpointDensity54.reciprocal_square_upper N)
    (by norm_num : (0:ℝ)≤3)
  have herror : (∑d∈Finset.Icc 1 N,((4*Harmonic (N/d)+5/2)*N/d+3/(d:ℝ)^2))≤
      2*N*(Real.log N)^2+(61/25)*N*Real.log N+(49/10)*N*Harmonic N+(86/25)*N+987/200 := by
    rw [herr]
    nlinarith only [hpoly,hden]
  have ht := RawEndpoint115.actual_weighted_endpoint_profile (by omega : 1≤N) hcL hLR hRN s
    (fun d hd=>⟨(hs d hd).1,(hs d hd).2.1⟩)
  have hc' : (∑d∈Finset.Icc 1 N,(ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℝ))≤
      (∑d∈Finset.Icc 1 N,((c:ℝ)*((R:ℝ)-L-s d)+finiteCoprimeDensity N*(s d*R-(s d)^2/2))/(d:ℝ)^2)+
        ∑d∈Finset.Icc 1 N,((4*Harmonic (N/d)+5/2)*N/d+3/(d:ℝ)^2) := by
    simpa only [add_assoc,Finset.sum_add_distrib] using hc
  push_cast
  linarith only [hc',ht,herror]

theorem actual_prepared_CM_EM_profile {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 16≤N)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card+
      ((R:ℝ)+(129/200)*L)*(N-R)≤
      (N:ℝ)^2/2-ProfileDeficit L (N-R)+2*N*(Real.log N)^2+(61/25)*N*Real.log N+(49/10)*N*Harmonic N+(86/25)*N+987/200 := by
  obtain ⟨e,he,hcount⟩ := actual_prepared_middle_resource_sum x p hF hcL hLR hRN hroot hP hLP hW
  have hb := actual_middle_resource_profile hN hcL hLR hRN e he
  have hc : ((CM (PreparedCrooked F c L) p R).card:ℝ)+(EM (PreparedAP F c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hcount
  linarith only [hb,hc]

theorem actual_prepared_family_raw_profile {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN16 : 16≤N) (hc : (c:ℤ)∈Ground N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200 := by
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c:ℤ)≤L) (by exact_mod_cast hLR : (L:ℤ)≤R) hT hcT hTR
  have hp := actual_joint_preparation_loss hG hroot hP hcP hLP
  have hm := EndpointExterior55.actual_prepared_middle_reduction x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hr := actual_prepared_CM_EM_profile x p hN16 hG hcL.le hLR hRN hroot hP hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hw := TwoSidedMoment62.actual_simplex_exception_half hc
  nlinarith only [hp,hm,hr,hw]

theorem actual_readded11_raw_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN16 : 16≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (F.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      N*SimplexPolynomial (Real.log N) (Harmonic N)/2+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200+
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
  have hr := actual_prepared_family_raw_profile hN16 hc hGlegal hcL hLR hRN
    (RawEndpoint114.actual_readded_root hroot) (hsub hP) hcP hLP (hsub hT) hcT hTR hout
  have hcard := Finset.card_sdiff_add_card_eq_card hEF
  have hcardR : (G.card:ℝ)+E.card=F.card := by exact_mod_cast hcard
  dsimp only [E] at hcardR
  linarith only [hr,hcardR]


theorem bootstrap_core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x+231/400)/2+2*x^2+(61/25)*x+
      (89/10)*(x+231/400)+597/20=BootstrapCorePolynomial x := by
  dsimp only [SimplexPolynomial,BootstrapCorePolynomial]
  ring

theorem actual_readded11_bootstrap_profile_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N) :
    RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*BootstrapCorePolynomial (Real.log N) := by
  have hr := actual_readded11_raw_profile (by omega : 16≤N) hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩⟩
  have hcount := RawEndpoint116.actual_deleted_avoider_count68 (by omega : 4913≤N) hc hF hcL hLR hRN hne hi hthin
  have hcount' := hcount.trans (Nat.mul_le_mul_left 68 (Nat.sub_le (L+N-R) 1))
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card:ℝ)≤
      68*((L+N-R:ℕ):ℝ) := by exact_mod_cast hcount'
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast (show 3000≤N by omega)
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add];ring
  rw [he] at hcountR
  have ht : (32:ℝ)*((L:ℝ)+(N-R))≤N := by
    have hh : (32:ℝ)*((L+N-R:ℕ):ℝ)≤N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*
      (SimplexPolynomial (Real.log N) (Harmonic N)/2+2*(Real.log N)^2+
        (61/25)*Real.log N+(89/10)*Harmonic N+597/20) := by
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+231/400)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+597/20≤BootstrapCorePolynomial (Real.log N) := by
    rw [←bootstrap_core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh]
  exact hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))

theorem actual_readded11_bootstrap_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*BootstrapPolynomial (Real.log N) := by
  have hp := actual_readded11_bootstrap_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hthin
  have he := RawEndpoint115.profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [BootstrapPolynomial]
  nlinarith only [hp,he,hs]

#print axioms actual_middle_resource_profile
#print axioms actual_prepared_CM_EM_profile
#print axioms actual_prepared_family_raw_profile
#print axioms actual_readded11_raw_profile
#print axioms bootstrap_core_harmonic_identity
#print axioms actual_readded11_bootstrap_profile_width
#print axioms actual_readded11_bootstrap_width
end
end JSP233.RawEndpoint121
