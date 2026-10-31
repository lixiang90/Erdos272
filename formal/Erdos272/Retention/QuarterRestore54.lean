import Erdos272.Core.TerminalSeven52

/-! Actual reciprocal restoration retaining the integer quarter in B(N).
The low branch obtains its deficit from the actual minimum omitted member;
the original deleted-avoider endpoint constructs that omitted family itself. -/
namespace JSP233.QuarterRestore54
open StarCompletion LongTerminal35 DenseDeletion40 JointFringe44
open KKRetention32 Restore33 TerminalDeficit51 TerminalSeven52
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

theorem quarter_floor_reserve (N : ℕ) : N/4≤1+(N-1)/4 := by omega

theorem card_le_B_of_four_card {N f : ℕ} (hfour : 4*f≤4*N.choose 2+N) : f≤B N := by
  have hf : f≤N.choose 2+N/4 := by omega
  have hq := quarter_floor_reserve N
  unfold B
  omega

theorem reciprocal_quarter_payment {N C m t j s f g e : ℕ}
    (hs : 0<s) (hm : s*m≤N) (hd : g+N≤C+m+t)
    (he : e≤j*t) (hcard : f=g+e)
    (hpay : 4*s*(j+1)*t≤(5*s-4)*N) : 4*f≤4*C+N := by
  have hd' := Nat.mul_le_mul_left (4*s) hd
  have he' := Nat.mul_le_mul_left (4*s) he
  have hm' := Nat.mul_le_mul_left 4 hm
  have hcard' := congrArg (fun n:ℕ=>4*s*n) hcard
  have hco : (5*s-4)*N+4*N=5*s*N := by
    have hh : 5*s-4+4=5*s := Nat.sub_add_cancel (by omega)
    nlinarith only [congrArg (fun n:ℕ=>n*N) hh]
  have hb : s*(4*f)≤s*(4*C+N) := by
    nlinarith only [hd',he',hm',hcard',hpay,hco]
  by_contra hn
  have hh := Nat.mul_le_mul_left s (show 4*C+N+1≤4*f by omega)
  nlinarith only [hh,hb,hs]

theorem actual_low_omitter_four_card
    (r p s N c L R : ℕ) (F G E : Finset (Finset ℤ)) (P : Finset ℤ)
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hs : 0<s) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hsmallpay : 4*s*(JointCount p+1)*(L+N-R)≤(5*s-4)*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (hPE : P∈E) (hcP : (c:ℤ)∉P) (hm : s*P.card≤N)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) :
    4*F.card≤4*N.choose 2+N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have hd := TerminalSeven52.actual_native_terminal_deficit N c L R F G P hN hc hcL hLR hRN hthin
    hlegal hGF (hEF hPE) hcP hi
  have hb := TerminalDeficit51.actual_interval_fringe_count r p N c L R F G E hr hp hp3 hsize
    hc hcL hLR hRN hgeometry hGF hEF hlegal hbad hdense hne hi
  have he : E.card≤JointCount p*(L+N-R) := hb.trans
    (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  exact reciprocal_quarter_payment hs hm hd he hcard hsmallpay

theorem actual_adaptive_restore_reciprocal_quarter
    (r p s p0 N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hs : 1<s) (hp0 : s<p0) (hp03 : 3≤p0) (hsize0 : p0^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hsmallpay : 4*s*(JointCount p+1)*(L+N-R)≤(5*s-4)*N)
    (hgeometry0 : s*p0*(L+N-R)≤(p0-s)*N)
    (hquarter0 : 4*JointCount p0*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  have hGF : G⊆F := by rw [hG];exact Finset.sdiff_subset
  have ht := TerminalSeven52.actual_native_interval_terminal N c L R G hN hc hcL hLR hRN hthin
    (RestoreTerminal35.retained_legal hG hlegal) hne hi
  have hcard := deletion_card_exact F E hEF
  rw [←hG] at hcard
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    by_cases hm : s*P.card≤N
    · exact card_le_B_of_four_card (actual_low_omitter_four_card r p s N c L R F G E P
        hN hr hp hp3 hsize (by omega) hc hcL hLR hRN hthin hgeometry hsmallpay
        hG hEF hlegal hbad hdense hPE (havoid P hPE) hm hne hi)
    · have hd0 : ∀S∈E,N<s*S.card := by
        intro S hS
        have hh := Nat.mul_le_mul_left s (hmin S hS)
        omega
      have hb := TerminalDeficit51.actual_interval_fringe_count s p0 N c L R F G E (by omega) hp0 hp03 hsize0
        hc hcL hLR hRN hgeometry0 hGF hEF hlegal hbad hd0 hne hi
      have hpay := quarter_payment (JointCount p0) N (L+N-R) (by omega) hquarter0
      unfold B
      omega
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [hE,Finset.card_empty,add_zero] at hcard
    unfold B
    omega

theorem actual_deleted_avoider_restore_reciprocal_quarter
    (r p s p0 N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 0<r) (hp : r<p) (hp3 : 3≤p) (hsize : p^3≤N)
    (hs : 1<s) (hp0 : s<p0) (hp03 : 3≤p0) (hsize0 : p0^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : r*p*(L+N-R)≤(p-r)*N)
    (hsmallpay : 4*s*(JointCount p+1)*(L+N-R)≤(5*s-4)*N)
    (hgeometry0 : s*p0*(L+N-R)≤(p0-s)*N)
    (hquarter0 : 4*JointCount p0*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := OmittedAvoiders N r F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N r F)
  have ha := actual_avoider_readdition N r F (c:ℤ)
  apply actual_adaptive_restore_reciprocal_quarter r p s p0 N c L R F (F\E) E
    hN hr hp hp3 hsize hs hp0 hp03 hsize0 hc hcL hLR hRN hthin
    hgeometry hsmallpay hgeometry0 hquarter0 rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

theorem actual_minimal_dense_rank {N r : ℕ} {P : Finset ℤ}
    (hr : 2≤r) (hP : P⊆Ground N) (hdense : N<r*P.card) :
    ∃k∈Finset.Icc 2 r,N<k*P.card ∧ (k-1)*P.card≤N := by
  have hm : P.card≤N := (Finset.card_le_card hP).trans_eq (ground_card N)
  let K := (Finset.Icc 2 r).filter (fun k=>N<k*P.card)
  have hK : K.Nonempty := ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr,le_rfl⟩,hdense⟩⟩
  obtain ⟨k,hk,hmin⟩ := Finset.exists_min_image K id hK
  have hkI := (Finset.mem_filter.mp hk).1
  have hkd := (Finset.mem_filter.mp hk).2
  have hkB := Finset.mem_Icc.mp hkI
  have hprevious : (k-1)*P.card≤N := by
    by_cases hk2 : k=2
    · subst k
      simpa using hm
    · by_contra hn
      have hj : k-1∈K := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
      have hh := hmin (k-1) hj
      change k≤k-1 at hh
      omega
  exact ⟨k,hkI,hkd,hprevious⟩

theorem actual_adaptive_restore_rank_table
    (r : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r)
    (hp : ∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k)
    (hsize : ∀k∈Finset.Icc 2 r,(p k)^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : ∀k∈Finset.Icc 2 r,k*p k*(L+N-R)≤(p k-k)*N)
    (hsmallpay : ∀k∈Finset.Icc 2 r,
      4*(k-1)*(JointCount (p k)+1)*(L+N-R)≤(5*k-9)*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  by_cases he : E.Nonempty
  · obtain ⟨P,hPE,hmin⟩ := Finset.exists_min_image E Finset.card he
    obtain ⟨k,hk,hkP,hm⟩ := actual_minimal_dense_rank hr (hlegal.1 P (hEF hPE)) (hdense P hPE)
    have hkb := Finset.mem_Icc.mp hk
    have hdk : ∀S∈E,N<k*S.card := by
      intro S hS
      have hh := Nat.mul_le_mul_left k (hmin S hS)
      omega
    have hcoef : 5*(k-1)-4=5*k-9 := by omega
    have hpay : 4*(k-1)*(JointCount (p k)+1)*(L+N-R)≤(5*(k-1)-4)*N := by
      simpa only [hcoef] using hsmallpay k hk
    exact card_le_B_of_four_card (actual_low_omitter_four_card k (p k) (k-1) N c L R F G E P
      hN (by omega) (hp k hk).1 (hp k hk).2 (hsize k hk) (by omega)
      hc hcL hLR hRN hthin (hgeometry k hk) hpay hG hEF hlegal hbad hdk
      hPE (havoid P hPE) hm hne hi)
  · have hE : E=∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have hGF : G=F := by simpa only [hE,Finset.sdiff_empty] using hG
    have ht := TerminalSeven52.actual_native_interval_terminal N c L R G hN hc hcL hLR hRN hthin
      (hGF.symm ▸ hlegal) hne hi
    unfold B
    rw [hGF] at ht
    omega

theorem actual_deleted_avoider_restore_rank_table
    (r : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r)
    (hp : ∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k)
    (hsize : ∀k∈Finset.Icc 2 r,(p k)^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 42*(L+N-R)≤N)
    (hgeometry : ∀k∈Finset.Icc 2 r,k*p k*(L+N-R)≤(p k-k)*N)
    (hsmallpay : ∀k∈Finset.Icc 2 r,
      4*(k-1)*(JointCount (p k)+1)*(L+N-R)≤(5*k-9)*N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  let E := OmittedAvoiders N r F (c:ℤ)
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N r F)
  have ha := actual_avoider_readdition N r F (c:ℤ)
  apply actual_adaptive_restore_rank_table r p N c L R F (F\E) E
    hN hr hp hsize hc hcL hLR hRN hthin hgeometry hsmallpay rfl hEF hlegal
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  · intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · simpa only [E,ha] using hne
  · simpa only [E,ha] using hi

def RankWidth14 : ℕ→ℕ
  | 2=>3 | 3=>4 | 4=>5 | 5=>6 | 6=>7 | 7=>8 | 8=>10
  | 9=>11 | 10=>12 | 11=>14 | 12=>15 | 13=>17 | 14=>18 | _=>18

theorem rank_width14_payments (k : ℕ) (hk : k∈Finset.Icc 2 14) :
    k<RankWidth14 k ∧ 3≤RankWidth14 k ∧ RankWidth14 k≤18 ∧
      k*RankWidth14 k≤(RankWidth14 k-k)*65 ∧
      4*(k-1)*(JointCount (RankWidth14 k)+1)≤(5*k-9)*65 := by
  obtain ⟨h2,h14⟩ := Finset.mem_Icc.mp hk
  interval_cases k <;> decide

theorem actual_deleted_avoider_restore14
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 18^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 65*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N 14 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 14 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  apply actual_deleted_avoider_restore_rank_table 14 RankWidth14 N c L R F hN (by decide)
    (fun k hk=>⟨(rank_width14_payments k hk).1,(rank_width14_payments k hk).2.1⟩)
    (fun k hk=>(Nat.pow_le_pow_left (rank_width14_payments k hk).2.2.1 3).trans hsize)
    hc hcL hLR hRN (by omega) ?_ ?_ hlegal hne hi
  · intro k hk
    calc
      k*RankWidth14 k*(L+N-R)≤(RankWidth14 k-k)*65*(L+N-R) :=
        Nat.mul_le_mul_right _ (rank_width14_payments k hk).2.2.2.1
      _=(RankWidth14 k-k)*(65*(L+N-R)) := by ring
      _≤(RankWidth14 k-k)*N := Nat.mul_le_mul_left _ hpay
  · intro k hk
    calc
      4*(k-1)*(JointCount (RankWidth14 k)+1)*(L+N-R)≤(5*k-9)*65*(L+N-R) :=
        Nat.mul_le_mul_right _ (rank_width14_payments k hk).2.2.2.2
      _=(5*k-9)*(65*(L+N-R)) := by ring
      _≤(5*k-9)*N := Nat.mul_le_mul_left _ hpay

#print axioms quarter_floor_reserve
#print axioms card_le_B_of_four_card
#print axioms reciprocal_quarter_payment
#print axioms actual_low_omitter_four_card
#print axioms actual_adaptive_restore_reciprocal_quarter
#print axioms actual_deleted_avoider_restore_reciprocal_quarter
#print axioms actual_minimal_dense_rank
#print axioms actual_adaptive_restore_rank_table
#print axioms actual_deleted_avoider_restore_rank_table
#print axioms rank_width14_payments
#print axioms actual_deleted_avoider_restore14
end
end JSP233.QuarterRestore54
