module

public import Erdos272.Retention.RestoreDense118
public import Erdos272.Retention.DenseFringe120
public import Erdos272.Retention.CrossBad120
public import Erdos272.Resources.ProfileArms120
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Restore the same original family at width900/23. Every density leaf
uses the complete actual Bad/Good partition; the true smallest omitted
member is selected once and retained in every deficit payment. -/
namespace JSP233.RestoreDense120
open StarCompletion APGeometry LongTerminal35 DenseDeletion40 JointFringe44
open QuarterRestore54 RankTwenty58 KKRetention32 Restore33 ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_bad_good_count {N L R m r : ℕ} {F E : Finset (Finset ℤ)}
    (hsize : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hdense : ∀S∈E,N<r*S.card)
    (hpay : 900*(L+N-R)≤23*N) (hlarge : 90<L+N-R)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2) :
    E.card+((DenseAligned117.DenseShortKeys r).card+11)≤
      ((DenseAligned117.DenseShortKeys r).card+11)*(L+N-R)+25 := by
  let K := (DenseAligned117.DenseShortKeys r).card+11
  let w := L+N-R
  let M := R-L+1
  let b := w+M/13-m
  let O := Ground N\Finset.Icc (L:ℤ) (R:ℤ)
  let A := Finset.Icc (1:ℤ) ((L:ℤ)-1)
  let B := Finset.Icc ((R:ℤ)+1) N
  let D := E.filter (fun S=>(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/13+1)
  let G := E.filter (fun S=>¬(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/13+1)
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hM : 1801800≤M := by change 900*w≤23*N at hpay;omega
  have hO : O=A∪B := by
    ext x
    simp only [O,A,B,Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_union,mem_ground]
    omega
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have ha := Finset.mem_Icc.mp hx
    have hb := Finset.mem_Icc.mp hy
    omega
  have hAc : A.card=L-1 := by dsimp only [A];simp only [Int.card_Icc];omega
  have hBc : B.card=N-R := by dsimp only [B];simp only [Int.card_Icc];omega
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hOc : O.card+1=w := by dsimp only [O,w];omega
  have hshape : 16*b≤7*w := CrossBad120.actual_bad13_shape hLR hRN hm hpay
  have hmiss : ∀S∈D,(O\S).card≤b := by
    intro S hS
    exact CrossBad116.actual_bad13_missing hL hLR hRN
      (hlegal.1 S (hEF (Finset.mem_filter.mp hS).1))
      (hminimum S (Finset.mem_filter.mp hS).1) (Finset.mem_filter.mp hS).2
  have hd : D.card≤25 := by
    by_cases hne : D.Nonempty
    · have harms := ProfileArms120.actual_bad13_nonempty_arm_margins
        (by omega : 5000≤N) hL hLR hRN hlegal ((Finset.filter_subset _ _).trans hEF) hne
        (fun S hS=>hminimum S (Finset.mem_filter.mp hS).1) hm
        (fun S hS=>(Finset.mem_filter.mp hS).2) hprofile
      have hrect := CrossBad120.actual_bad_rectangles_disjoint hL hLR hRN
        (by omega : 325≤R-L+1) hlegal ((Finset.filter_subset _ _).trans hEF)
        hmiss (fun S hS=>(Finset.mem_filter.mp hS).2) hshape hlarge
      exact RectSlack117.actual_rectangles_card_le25 (b:=b) (w:=w) (A:=A) (B:=B) (E:=D)
        (by omega : 0<w) hAB (by omega : A.card+B.card+1=w)
        (by rw [hAc];exact harms.1) (by rw [hBc];exact harms.2)
        (by intro S hS;simpa only [←hO] using hmiss S hS) hrect
    · have he : D=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [he,Finset.card_empty]
      omega
  have hg : G.card≤K*O.card := DenseFringe120.actual_long_trace_fringe_bound
    hL hLR hRN hM hlegal ((Finset.filter_subset _ _).trans hEF)
    (fun S hS=>hbad S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hdense S (Finset.mem_filter.mp hS).1)
    hcore (fun S hS=>by have hh := (Finset.mem_filter.mp hS).2;omega)
  have hc := Finset.card_filter_add_card_filter_not (s:=E)
    (fun S=>(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤M/13+1)
  change D.card+G.card=E.card at hc
  have hK : K*O.card+K=K*w := by rw [←hOc];ring
  change E.card+K≤K*w+25
  omega

theorem actual_bad_good_count44 {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hsize : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hdense : ∀S∈E,N<11*S.card)
    (hpay : 900*(L+N-R)≤23*N) (hlarge : 90<L+N-R)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2) :
    E.card+19≤44*(L+N-R) := by
  have h := actual_bad_good_count hsize hL hLR hRN hlegal hEF hbad hcore hminimum hm hdense hpay hlarge hprofile
  simp only [DenseAligned117.dense_short_keys_card11,Nat.reduceAdd] at h
  omega

theorem actual_bad_good_count43 {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hsize : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hdense : ∀S∈E,N<10*S.card)
    (hpay : 900*(L+N-R)≤23*N) (hlarge : 90<L+N-R)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2) :
    E.card+18≤43*(L+N-R) := by
  have h := actual_bad_good_count hsize hL hLR hRN hlegal hEF hbad hcore hminimum hm hdense hpay hlarge hprofile
  simp only [Dense10Aligned117.dense_short_keys_card10,Nat.reduceAdd] at h
  omega

theorem actual_bad_good_count42 {N L R m : ℕ} {F E : Finset (Finset ℤ)}
    (hsize : 2000000≤N) (hL : 1≤L) (hLR : L≤R) (hRN : R≤N)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F) (hbad : ∀S∈E,¬IsAP S)
    (hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H)
    (hminimum : ∀S∈E,m≤S.card) (hm : N<11*m)
    (hdense : ∀S∈E,N<9*S.card)
    (hpay : 900*(L+N-R)≤23*N) (hlarge : 90<L+N-R)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2) :
    E.card+17≤42*(L+N-R) := by
  have h := actual_bad_good_count hsize hL hLR hRN hlegal hEF hbad hcore hminimum hm hdense hpay hlarge hprofile
  simp only [DenseAligned117.dense_short_keys_card9,Nat.reduceAdd] at h
  omega

theorem actual_adaptive_restore11_profile900
    (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 2000000≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 900*(L+N-R)≤23*N)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2)
    (hlarge : 90<L+N-R)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<11*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have hthin : 29*(L+N-R)≤N := by omega
  have hGlegal := RestoreTerminal35.retained_legal hG hlegal
  have ht := Terminal29Native117.actual_native_interval_terminal N c L R G hN hc hcL hLR hRN
    hthin hGlegal hne hi
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    obtain ⟨H,hHG,hHAP,hKH⟩ := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
    have hcore : ∃H∈F,IsAP H ∧ Finset.Icc (L:ℤ) (R:ℤ)⊆H :=
      ⟨H,hGF hHG,hHAP,hKH⟩
    have hL : 1≤L := by omega
    have hM : 1801800≤R-L+1 := by omega
    have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
      (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
    have hout : (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card≤L+N-R := by omega
    have hd := Terminal29Native117.actual_native_terminal_deficit N c L R F G P hN hc hcL hLR hRN
      hthin hlegal hGF (hEF hPE) (havoid P hPE) hi
    by_cases hm10 : 10*P.card≤N
    · have he44 := actual_bad_good_count44 hsize hL hLR hRN hlegal hEF hbad hcore
        hmin (hdense P hPE) hdense hpay hlarge hprofile
      have hquarter : 4*P.card+180*(L+N-R)≤5*N+76 := by nlinarith only [hm10,hpay]
      exact card_le_B_of_four_card (by nlinarith only [hd,he44,hcard,hquarter])
    · have hd10 : ∀S∈E,N<10*S.card := by
        intro S hS
        have hh := Nat.mul_le_mul_left 10 (hmin S hS)
        omega
      by_cases hm9 : 9*P.card≤N
      · have he43 := actual_bad_good_count43 hsize hL hLR hRN hlegal hEF hbad hcore
          hmin (hdense P hPE) hd10 hpay hlarge hprofile
        have hquarter : 4*P.card+176*(L+N-R)≤5*N+72 := by nlinarith only [hm9,hpay]
        exact card_le_B_of_four_card (by nlinarith only [hd,he43,hcard,hquarter])
      · have hd9 : ∀S∈E,N<9*S.card := by
          intro S hS
          have hh := Nat.mul_le_mul_left 9 (hmin S hS)
          omega
        by_cases hm8 : 8*P.card≤N
        · have he42 := actual_bad_good_count42 hsize hL hLR hRN hlegal hEF hbad hcore
            hmin (hdense P hPE) hd9 hpay hlarge hprofile
          have hquarter : 4*P.card+172*(L+N-R)≤5*N+68 := by nlinarith only [hm8,hpay]
          exact card_le_B_of_four_card (by nlinarith only [hd,he42,hcard,hquarter])
        · have hd8 : ∀S∈E,N<8*S.card := by
            intro S hS
            have hh := Nat.mul_le_mul_left 8 (hmin S hS)
            omega
          have h37 : 37*(L+N-R)≤N := by omega
          have hrows := RestoreDense118.lower_rank_ratio_table
          have hp : ∀k∈Finset.Icc 2 8,k<Restore11Ratio112.RankWidth11 k ∧
              3≤Restore11Ratio112.RankWidth11 k := fun k hk=>⟨(hrows k hk).1,(hrows k hk).2.1⟩
          have hcube : ∀k∈Finset.Icc 2 8,(Restore11Ratio112.RankWidth11 k)^3≤N := by
            intro k hk
            exact (Nat.pow_le_pow_left (hrows k hk).2.2.1 3).trans (by norm_num;omega)
          have hgeom : ∀k∈Finset.Icc 2 8,
              k*Restore11Ratio112.RankWidth11 k*(L+N-R)≤(Restore11Ratio112.RankWidth11 k-k)*N := by
            intro k hk
            have hh := (hrows k hk).2.2.2.1
            simp only [one_mul] at hh
            calc
              _≤(Restore11Ratio112.RankWidth11 k-k)*37*(L+N-R) := Nat.mul_le_mul_right _ hh
              _=(Restore11Ratio112.RankWidth11 k-k)*(37*(L+N-R)) := by ring
              _≤_ := Nat.mul_le_mul_left _ h37
          have hquarter : ∀k∈Finset.Icc 2 8,
              4*(k-1)*(JointCount (Restore11Ratio112.RankWidth11 k)+1)*(L+N-R)≤(5*k-9)*N := by
            intro k hk
            have hh := (hrows k hk).2.2.2.2
            simp only [one_mul] at hh
            calc
              _≤(5*k-9)*37*(L+N-R) := Nat.mul_le_mul_right _ hh
              _=(5*k-9)*(37*(L+N-R)) := by ring
              _≤_ := Nat.mul_le_mul_left _ h37
          exact RestoreDense117.actual_adaptive_restore_rank_table29 8 Restore11Ratio112.RankWidth11 N c L R F G E
            hN (by decide) hp hcube hc hcL hLR hRN hthin hgeom hquarter
            hG hEF hlegal hbad hd8 havoid hne hi
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

theorem actual_deleted_avoider_restore11_profile900
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 2000000≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 900*(L+N-R)≤23*N)
    (hprofile : RawEndpoint115.ProfileDeficit (L:ℝ) ((N-R:ℕ):ℝ)≤
      RawEndpoint112.DeficitCoeff/(900/23)^2*(N:ℝ)^2)
    (hlarge : 90<L+N-R)
    (hlegal : Legal (Ground N) F)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have ha := TerminalDeficit51.actual_avoider_readdition N 11 F (c:ℤ)
  apply actual_adaptive_restore11_profile900 N c L R F (F\E) E hN hsize
    hc hcL hLR hRN hpay hprofile hlarge rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi



#print axioms actual_bad_good_count
#print axioms actual_bad_good_count44
#print axioms actual_bad_good_count43
#print axioms actual_bad_good_count42
#print axioms actual_adaptive_restore11_profile900
#print axioms actual_deleted_avoider_restore11_profile900
end
end JSP233.RestoreDense120
