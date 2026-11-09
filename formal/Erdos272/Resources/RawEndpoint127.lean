module

public import Erdos272.Resources.RawEndpoint121
public import Erdos272.Arithmetic.WitnessSingle127

@[expose] public section

/-! The full actual single-prefix complete2+3 tangent saving is paid at the physical root exception.
The merged physical prefix and its single absolute tangent fee remain in the same original
family profile; the fixed fee is carried to the all-real-N gate. -/
namespace JSP233.RawEndpoint127
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 FamilyReflect43 RestrictedWitness44 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def BootstrapCorePolynomial (x : ℝ) : ℝ :=
  x^3/6+(291/100)*x^2+(151581/10000)*x-912499/4000

def BootstrapPolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*BootstrapCorePolynomial x

theorem actual_prepared_family_raw_profile {N c L R : ℕ} {G : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN16 : 16≤N) (hc : (c:ℤ)∈Ground N) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈G) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (G.card:ℝ)≤(N:ℝ)^2/2-ProfileDeficit L (N-R)+
      N*(DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200+WitnessSingle127.FullFee := by
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hG hroot
    (by exact_mod_cast hcL.le : (c:ℤ)≤L) (by exact_mod_cast hLR : (L:ℤ)≤R) hT hcT hTR
  have hp := actual_joint_preparation_loss hG hroot hP hcP hLP
  have hm := EndpointExterior55.actual_prepared_middle_reduction x p hG hcL hLR hRN hP hLP hroot
    houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,
      (hx S hS).2.2.2.2.1,(hx S hS).2.2.2.2.2⟩)
  have hr := RawEndpoint121.actual_prepared_CM_EM_profile x p hN16 hG hcL.le hLR hRN hroot hP hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hw := WitnessSingle127.actual_exception_prefix127 hc
  dsimp only [SingleTangent127.Slope,LogAnchor127.AnchorSlope] at hw
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
      N*(DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*N*(Real.log N)^2+
      (61/25)*N*Real.log N+(89/10)*N*Harmonic N+24*N+(86/25)*N+(L-c:ℕ)+3+987/200+WitnessSingle127.FullFee+
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
    (DivisorMoment122.Q3 x+2*(x+231/400)-53107/200)+2*x^2+(61/25)*x+
      (89/10)*(x+231/400)+597/20=BootstrapCorePolynomial x := by
  dsimp only [DivisorMoment122.Q3,BootstrapCorePolynomial]
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
    RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*BootstrapCorePolynomial (Real.log N)+WitnessSingle127.FullFee := by
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
      ((DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*(Real.log N)^2+
        (61/25)*Real.log N+(89/10)*Harmonic N+597/20)+WitnessSingle127.FullFee := by
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hp : (DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+597/20≤BootstrapCorePolynomial (Real.log N) := by
    rw [←bootstrap_core_harmonic_identity]
    dsimp only [DivisorMoment122.Q3]
    nlinarith only [hh]
  have hcp := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)
  linarith only [hcost,hcp]

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
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*BootstrapPolynomial (Real.log N)+(114959/3359:ℝ)*WitnessSingle127.FullFee := by
  have hp := actual_readded11_bootstrap_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hthin
  have he := RawEndpoint115.profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [BootstrapPolynomial]
  nlinarith only [hp,he,hs]

#print axioms actual_prepared_family_raw_profile
#print axioms actual_readded11_raw_profile
#print axioms bootstrap_core_harmonic_identity
#print axioms actual_readded11_bootstrap_profile_width
#print axioms actual_readded11_bootstrap_width
end
end JSP233.RawEndpoint127
