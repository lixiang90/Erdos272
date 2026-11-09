module

public import Erdos272.Core.TerminalSeven52
public import Erdos272.Counting.MiddleDeficit52
public import Erdos272.Counting.NonIntervalAP47
public import Erdos272.Arithmetic.DivisorMoment45
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.NonInterval53
open StarCompletion PrivatePairExistence LongTerminal35 WitnessInterval43 RestrictedWitness44
open APGeometry APCount41 APLinearCount49 APExterior50 APPrepare49 NonIntervalAP47
open MeetingPool46 DivisorMoment45 KKRetention32 ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

theorem actual_noninterval_card {N : ℕ} {P : Finset ℤ}
    (hsub : P⊆Ground N) (hAP : IsAP P) (hno : ¬IsInterval P) :
    (P.card:ℝ)≤(N:ℝ)/2+1 := by
  obtain ⟨_,a,hstep⟩ := actual_step hAP
  have hd := actual_noninterval_step_two hAP hno
  have hne := isAP_nonempty hAP
  have hg : P⊆Finset.Icc 1 (N:ℤ) := fun x hx=>Finset.mem_Icc.mpr ((mem_ground N x).mp (hsub hx))
  have hs := apAt_card_span hstep hne hg
  have hp : (1:ℤ)≤P.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hdZ : (2:ℤ)≤Step P := by exact_mod_cast hd
  have hmul := mul_le_mul_of_nonneg_right hdZ (show (0:ℤ)≤(P.card:ℤ)-1 by omega)
  have hh : (2:ℤ)*P.card≤(N:ℤ)+2 := by nlinarith only [hs,hmul]
  have hhR : (2:ℝ)*P.card≤(N:ℝ)+2 := by exact_mod_cast hh
  linarith only [hhR]

theorem actual_meeting_half_card {N : ℕ} {P : Finset ℤ}
    (hP : P⊆Ground N) (hsize : (P.card:ℝ)≤(N:ℝ)/2+1) :
    ((((Ground N).powersetCard 2).filter (fun Q=>¬Disjoint Q P)).card:ℝ)≤3*(N:ℝ)^2/8+N := by
  have hh := actual_meeting_pairs_card_real hP
  rw [ground_card] at hh
  have hp0 : (0:ℝ)≤P.card := Nat.cast_nonneg _
  have hn0 : (0:ℝ)≤N := Nat.cast_nonneg _
  by_cases hp : (P.card:ℝ)≤(N:ℝ)/2
  · have hs := mul_nonneg (sub_nonneg.mpr hp)
      (show (0:ℝ)≤3*(N:ℝ)/2-P.card by linarith only [hp,hn0])
    nlinarith only [hh,hs,hp0,hn0]
  · have hs := mul_le_mul_of_nonneg_right
      (show (P.card:ℝ)-(N:ℝ)/2≤1 by linarith only [hsize]) hn0
    nlinarith only [hh,hs,sq_nonneg ((P.card:ℝ)-(N:ℝ)/2),hp0,hn0]

theorem actual_crooked_half_avoider {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {P : Finset ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hsize : (P.card:ℝ)≤(N:ℝ)/2+1) :
    ((CrookedMembers F).card:ℝ)≤3*(N:ℝ)^2/8+N+(WitnessException (Ground N) c:ℝ) := by
  let Pool := ((Ground N).powersetCard 2).filter (fun Q=>¬Disjoint Q P)
  have hg : (MeetingCrooked F c P).card≤Pool.card := by
    have hh := private_pairs_and_intervals_card_le (C:=MeetingCrooked F c P) (E:=∅) (Pool:=Pool)
      hF (Finset.filter_subset _ _) (Finset.empty_subset _)
      (fun S hS=>(Finset.mem_filter.mp hS).2.1)
      (fun S hS=>(Finset.mem_filter.mp hS).2.2.1) (by
        intro S hS
        obtain ⟨hSF,_hc,_hbad,Q,hQ,hQP⟩ := Finset.mem_filter.mp hS
        exact ⟨Q,hQ,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨hQ.2.2.1.trans (hF.1 S hSF),hQ.1⟩,hQP⟩⟩)
      (by intro S hS;simp only [Finset.notMem_empty] at hS)
    simpa only [Finset.card_empty,Nat.add_zero] using hh
  have hb := actual_restricted_bad_family_bound c P hF
  have hp := actual_crooked_good_bad_partition F c P hroot
    (fun S hS hbad=>actual_avoider_meets_erase hF hS hP (hroot S hS hbad) hcP)
  have hpool := actual_meeting_half_card (hF.1 P hP) hsize
  have hgR : ((MeetingCrooked F c P).card:ℝ)≤Pool.card := by exact_mod_cast hg
  have hbR : ((BadMembers F c P).card:ℝ)≤WitnessException (Ground N) c := by exact_mod_cast hb
  have hpR : ((MeetingCrooked F c P).card:ℝ)+(BadMembers F c P).card=(CrookedMembers F).card := by exact_mod_cast hp
  dsimp only [Pool] at hgR
  linarith only [hgR,hbR,hpR,hpool]

theorem actual_large_AP_low_count {N L : ℕ} {F : Finset (Finset ℤ)}
    (hLN : L≤N) (hF : Legal (Ground N) F) (hAP : ∀S∈F,IsAP S)
    (hcard : ∀S∈F,2≤S.card) (hlow : ∀S∈F,Low S≤(L:ℤ)) :
    (F.card:ℝ)≤(5/3)*(L:ℝ)*N+2*N*HarmonicAbel29.Harmonic N+N := by
  have hmaps : ∀S∈F,Step S∈Finset.Icc 1 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(actual_step (hAP S hS)).1,actual_step_bound (hF.1 S hS) (hAP S hS) (hcard S hS)⟩
  have hpart := Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀d∈Finset.Icc 1 N,
      ((F.filter (fun S=>Step S=d)).card:ℝ)≤(L:ℝ)*N/(d:ℝ)^2+2*N/d+1 := by
    intro d hd
    let D := F.filter (fun S=>Step S=d)
    have hDF : D⊆F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) D := ⟨fun S hS=>hF.1 S (hDF hS),fun S hS T hT hn=>hF.2 S (hDF hS) T (hDF hT) hn⟩
    have he := actual_same_step_endpoint_real (L:=L) (R:=0) hLN (Nat.zero_le N)
      (Finset.mem_Icc.mp hd).1 hlegal (fun S hS=>isAP_nonempty (hAP S (hDF hS))) (by
        intro S hS
        obtain ⟨_,a,ha⟩ := actual_step (hAP S (hDF hS))
        exact ⟨a,by rwa [(Finset.mem_filter.mp hS).2] at ha⟩) (by
        intro S hS
        refine ⟨hlow S (hDF hS),?_⟩
        have hn := isAP_nonempty (hAP S (hDF hS))
        have hh := (mem_ground N (High S)).mp (hF.1 S (hDF hS) (high_spec hn).1)
        omega)
    simpa only [Nat.cast_zero,sub_zero] using he
  have hsum := Finset.sum_le_sum hclass
  have hs : (∑d∈Finset.Icc 1 N,((L:ℝ)*N/(d:ℝ)^2+2*N/d+1))=
      (L:ℝ)*N*SquareReciprocal N+2*N*HarmonicAbel29.Harmonic N+N := by
    simp only [SquareReciprocal,HarmonicAbel29.Harmonic,div_eq_mul_inv,Finset.sum_add_distrib,
      ←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one,one_mul,Nat.card_Icc,Nat.add_sub_cancel]
  rw [hs] at hsum
  have hp : (F.card:ℝ)=∑d∈Finset.Icc 1 N,((F.filter (fun S=>Step S=d)).card:ℝ) := by exact_mod_cast hpart
  rw [←hp] at hsum
  have hsq := mul_le_mul_of_nonneg_left (square_reciprocal_bound N) (show (0:ℝ)≤(L:ℝ)*N by positivity)
  nlinarith only [hsum,hsq]

theorem actual_AP_low_count {N L : ℕ} {F : Finset (Finset ℤ)}
    (hLN : L≤N) (hF : Legal (Ground N) F) (hAP : ∀S∈F,IsAP S)
    (hlow : ∀S∈F,Low S≤(L:ℤ)) :
    (F.card:ℝ)≤(5/3)*(L:ℝ)*N+2*N*HarmonicAbel29.Harmonic N+19*N+3 := by
  let A := F.filter (fun S=>4≤S.card)
  let B := F.filter (fun S=>¬4≤S.card)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hBF : B⊆F := Finset.filter_subset _ _
  have ha := actual_large_AP_low_count hLN
    (show Legal (Ground N) A from ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hn=>hF.2 S (hAF hS) T (hAF hT) hn⟩)
    (fun S hS=>hAP S (hAF hS)) (fun S hS=>by have hh:=(Finset.mem_filter.mp hS).2;omega)
    (fun S hS=>hlow S (hAF hS))
  have hb := actual_small_AP_family_count
    (show Legal (Ground N) B from ⟨fun S hS=>hF.1 S (hBF hS),fun S hS T hT hn=>hF.2 S (hBF hS) T (hBF hT) hn⟩)
    (fun S hS=>hAP S (hBF hS)) (fun S hS=>by have hh:=(Finset.mem_filter.mp hS).2;omega)
  have hbR : (B.card:ℝ)≤18*N+3 := by exact_mod_cast hb
  have hp : (A.card:ℝ)+B.card=F.card := by exact_mod_cast Finset.card_filter_add_card_filter_not (s:=F) (fun S=>4≤S.card)
  linarith only [ha,hbR,hp]

theorem actual_noninterval_family_count {N c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hno : ¬IsInterval P) :
    (G.card:ℝ)≤3*(N:ℝ)^2/8+(5/3)*(L:ℝ)*N+2*N*HarmonicAbel29.Harmonic N+
      20*N+3+(WitnessException (Ground N) c:ℝ) := by
  have hAP : IsAP P := by by_contra hh;exact hcP (hroot P hP hh)
  have hC := actual_crooked_half_avoider hF hroot hP hcP (actual_noninterval_card (hF.1 P hP) hAP hno)
  let E := G.filter IsAP
  have hEF : E⊆G := Finset.filter_subset _ _
  have hEAP : ∀S∈E,IsAP S := fun S hS=>(Finset.mem_filter.mp hS).2
  have he := actual_AP_low_count hLN
    (show Legal (Ground N) E from ⟨fun S hS=>hF.1 S (hEF hS),fun S hS T hT hn=>hF.2 S (hEF hS) T (hEF hT) hn⟩)
    hEAP (by
      intro S hS
      have hn := isAP_nonempty (hEAP S hS)
      by_cases hcS:(c:ℤ)∈S
      · exact ((low_spec hn).2 c hcS).trans (by exact_mod_cast hcL)
      · obtain ⟨a,ha,haL⟩ := hlow S (Finset.mem_filter.mpr ⟨hEF hS,hcS⟩)
        exact ((low_spec hn).2 a ha).trans haL)
  have hp : (E.card:ℝ)+(CrookedMembers G).card=G.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=G) IsAP
  linarith only [hC,he,hp]

theorem actual_noninterval_family_gap {N J c L : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hP : P∈G) (hcP : (c:ℤ)∉P) (hno : ¬IsInterval P)
    (hscale : 32*L≤N) (hJcube : 16384*J^3≤N) :
    (G.card:ℝ)≤11*(N:ℝ)^2/24 := by
  have hJ : 2≤J := by
    by_contra hn
    have hh:J≤1 := by omega
    interval_cases J <;>norm_num at hNJ <;>omega
  have hJR : (2:ℝ)≤J := by exact_mod_cast hJ
  have hNN : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hH := HarmonicSharp39.actual_harmonic_tight N J hNJ
  have hH0 := HarmonicAbel29.harmonic_nonneg N
  have hHJ : HarmonicAbel29.Harmonic N≤(J:ℝ) := by linarith only [hH,hJR]
  have hH3 : HarmonicAbel29.Harmonic N^3≤(J:ℝ)^3 := by gcongr
  have hJJ : (J:ℝ)≤(J:ℝ)^3 := by
    have hh := mul_nonneg (show (0:ℝ)≤(J:ℝ)-1 by linarith only [hJR])
      (show (0:ℝ)≤(J:ℝ)^2+J by positivity)
    nlinarith only [hh]
  have h1J : (1:ℝ)≤(J:ℝ)^3 := by linarith only [hJR,hJJ]
  have hW := actual_exception_harmonic hcN
  have hb := actual_noninterval_family_count hF hroot hcL hLN hlow hP hcP hno
  have hlin := mul_le_mul_of_nonneg_left hHJ (show (0:ℝ)≤2*N by positivity)
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0:ℝ)≤6*N by positivity)
  have hlin3 := mul_le_mul_of_nonneg_left hJJ (Nat.cast_nonneg (α:=ℝ) N)
  have hone := mul_le_mul_of_nonneg_left h1J (Nat.cast_nonneg (α:=ℝ) N)
  have hs : (32:ℝ)*L≤N := by exact_mod_cast hscale
  have hsc := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg (α:=ℝ) N)
  have ht : (16384:ℝ)*(J:ℝ)^3≤N := by exact_mod_cast hJcube
  have htc := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [hb,hW,hlin,hcube,hlin3,hone,hsc,htc,hNN,sq_nonneg (N:ℝ)]

theorem actual_avoiders_are_intervals {N J c L δ : ℕ} {G : Finset (Finset ℤ)}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c≤L) (hLN : L≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hscale : 32*L≤N) (hJcube : 16384*J^3≤N) (hdelta : 24*δ<N)
    (hfull : (N:ℝ)^2/2≤G.card+(δ:ℝ)*N) :
    ∀S∈Avoiders G (c:ℤ),IsInterval S := by
  intro S hS
  by_contra hn
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have hb := actual_noninterval_family_gap hN hNJ hcN hF hroot hcL hLN hlow hSG hcS hn hscale hJcube
  have hd : (24:ℝ)*δ<N := by exact_mod_cast hdelta
  have hpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hdn := mul_lt_mul_of_pos_right hd hpos
  nlinarith only [hb,hfull,hdn]

theorem actual_avoiders_intervals {N J c L R δ : ℕ} {G : Finset (Finset ℤ)}
    (hN : 6≤N) (hNJ : N<2^J) (hcN : (c:ℤ)∈Ground N)
    (hF : Legal (Ground N) G) (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hlow : ∀S∈Avoiders G (c:ℤ),∃a∈S,a≤(L:ℤ))
    (hright : ∀S∈Avoiders G (c:ℤ),∃b∈S,(R:ℤ)≤b)
    (hscale : 32*L≤N) (hJcube : 16384*J^3≤N) (hdelta : 24*δ<N)
    (hfull : (N:ℝ)^2/2≤G.card+(δ:ℝ)*N) :
    ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b) := by
  have hi := actual_avoiders_are_intervals hN hNJ hcN hF hroot hcL.le (hLR.trans hRN)
    hlow hscale hJcube hdelta hfull
  intro S hS
  obtain ⟨a,b,hrep⟩ := hi S hS
  obtain ⟨u,hu,huL⟩ := hlow S hS
  obtain ⟨v,hv,hRv⟩ := hright S hS
  obtain ⟨hSG,hcS⟩ := Finset.mem_filter.mp hS
  have huI : a≤u ∧ u≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hvI : a≤v ∧ v≤b := Finset.mem_Icc.mp (by rwa [←hrep])
  have hab : a≤b := huI.1.trans huI.2
  have haS : a∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨le_rfl,hab⟩
  have hbS : b∈S := by rw [hrep];exact Finset.mem_Icc.mpr ⟨hab,le_rfl⟩
  have haN := (mem_ground N a).mp (hF.1 S hSG haS)
  have hbN := (mem_ground N b).mp (hF.1 S hSG hbS)
  have hca : (c:ℤ)<a := by
    by_contra hn
    apply hcS
    rw [hrep]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have ha : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hb : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  refine ⟨a.toNat,b.toNat,by omega,by omega,by omega,by omega,?_⟩
  simpa only [Interval,ha,hb] using hrep

#print axioms actual_noninterval_card
#print axioms actual_meeting_half_card
#print axioms actual_crooked_half_avoider
#print axioms actual_large_AP_low_count
#print axioms actual_AP_low_count
#print axioms actual_noninterval_family_count
#print axioms actual_noninterval_family_gap
#print axioms actual_avoiders_are_intervals
#print axioms actual_avoiders_intervals
end
end JSP233.NonInterval53
