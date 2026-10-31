import Erdos272.Resources.HalfRecovery133
import Erdos272.Resources.BootstrapFringe139
namespace JSP233.HalfBootstrap139
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 DenseSharper41 FamilyReflect43 RestrictedWitness44 LongTerminal35
open LinearOmitters43 OutsideEnvelope43 OneSided47 Straddling47 APCount41
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115 PairRecovery131 HalfRecovery133
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
theorem actual_readded11_bootstrap_profile_width24 {N c L R : ℕ} {C : ℝ}
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
    (hthin : 24*(L+N-R)≤N)
    (hbudget : (HalfBad133.HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*(C+2) := by
  have hr := HalfRecovery133.actual_readded11_raw_profile hN hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩⟩
  have hcount := BootstrapFringe139.actual_deleted_avoider_count90 (by omega : 9261≤N) hc hF hcL hLR hRN hne hi hthin
  have hcount' := hcount.trans (Nat.mul_le_mul_left 90 (Nat.sub_le (L+N-R) 1))
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card:ℝ)≤
      90*((L+N-R:ℕ):ℝ) := by exact_mod_cast hcount'
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast (show 3000≤N by omega)
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add];ring
  rw [he] at hcountR
  have ht : (24:ℝ)*((L:ℝ)+(N-R))≤N := by
    have hh : (24:ℝ)*((L+N-R:ℕ):ℝ)≤N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : RawEndpoint115.ProfileDeficit L (N-R)≤
      (HalfBad133.HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N+2*N := by
    dsimp only [Extra]
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  nlinarith only [hcost,hbudget]

theorem actual_readded11_bootstrap_width24 {N c L R : ℕ} {C : ℝ}
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
    (hthin : 24*(L+N-R)≤N)
    (hbudget : (HalfBad133.HalfWitnessException (Ground N) (c:ℤ):ℝ)+(N:ℝ)*Extra N≤(N:ℝ)*C) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*(Rho*(C+2)) := by
  have hp := actual_readded11_bootstrap_profile_width24 hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hthin hbudget
  have he := RawEndpoint115.profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [Rho]
  nlinarith only [hp,he,hs]


#print axioms actual_readded11_bootstrap_profile_width24
#print axioms actual_readded11_bootstrap_width24
end
end JSP233.HalfBootstrap139
