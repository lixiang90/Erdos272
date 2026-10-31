import Erdos272.Retention.QuarterRestore54

/-! Uniform physical payment for the actual minimum dense rank, followed by
the complete r20/T98 table from the written cross-band startup argument.
The minimum omitted member, its rank, and rooted readdition remain internal. -/
namespace JSP233.RankTwenty58
open QuarterRestore54 StarCompletion LongTerminal35 DenseDeletion40 JointFringe44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def RankTable (r T Pmax : ℕ) (p : ℕ→ℕ) : Prop :=
  ∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k ∧ p k≤Pmax ∧
    k*p k≤(p k-k)*T ∧
    4*(k-1)*(JointCount (p k)+1)≤(5*k-9)*T

theorem uniform_rank_physical_payments
    {r T Pmax N t : ℕ} {p : ℕ→ℕ}
    (hrows : RankTable r T Pmax p) (hT : 42≤T)
    (hsize : Pmax^3≤N) (hpay : T*t≤N) :
    42*t≤N ∧
      (∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k) ∧
      (∀k∈Finset.Icc 2 r,(p k)^3≤N) ∧
      (∀k∈Finset.Icc 2 r,k*p k*t≤(p k-k)*N) ∧
      (∀k∈Finset.Icc 2 r,4*(k-1)*(JointCount (p k)+1)*t≤(5*k-9)*N) := by
  refine ⟨(Nat.mul_le_mul_right t hT).trans hpay,?_,?_,?_,?_⟩
  · intro k hk
    exact ⟨(hrows k hk).1,(hrows k hk).2.1⟩
  · intro k hk
    exact (Nat.pow_le_pow_left (hrows k hk).2.2.1 3).trans hsize
  · intro k hk
    calc
      k*p k*t≤(p k-k)*T*t := Nat.mul_le_mul_right t (hrows k hk).2.2.2.1
      _=(p k-k)*(T*t) := by ring
      _≤(p k-k)*N := Nat.mul_le_mul_left _ hpay
  · intro k hk
    calc
      4*(k-1)*(JointCount (p k)+1)*t≤(5*k-9)*T*t :=
        Nat.mul_le_mul_right t (hrows k hk).2.2.2.2
      _=(5*k-9)*(T*t) := by ring
      _≤(5*k-9)*N := Nat.mul_le_mul_left _ hpay

theorem actual_adaptive_restore_uniform
    (r T Pmax : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r) (hT : 42≤T)
    (hrows : RankTable r T Pmax p) (hsize : Pmax^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : T*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  obtain ⟨hthin,hp,hcube,hgeometry,hquarter⟩ :=
    uniform_rank_physical_payments hrows hT hsize hpay
  exact actual_adaptive_restore_rank_table r p N c L R F G E hN hr hp hcube
    hc hcL hLR hRN hthin hgeometry hquarter hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore_uniform
    (r T Pmax : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r) (hT : 42≤T)
    (hrows : RankTable r T Pmax p) (hsize : Pmax^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : T*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  obtain ⟨hthin,hp,hcube,hgeometry,hquarter⟩ :=
    uniform_rank_physical_payments hrows hT hsize hpay
  exact actual_deleted_avoider_restore_rank_table r p N c L R F hN hr hp hcube
    hc hcL hLR hRN hthin hgeometry hquarter hlegal hne hi

def RankWidth20 : ℕ→ℕ
  | 2=>3 | 3=>4 | 4=>5 | 5=>6 | 6=>7 | 7=>8 | 8=>9
  | 9=>10 | 10=>12 | 11=>13 | 12=>14 | 13=>15 | 14=>17
  | 15=>18 | 16=>20 | 17=>21 | 18=>23 | 19=>24 | 20=>26 | _=>26

theorem rank_width20_payments : RankTable 20 98 26 RankWidth20 := by
  intro k hk
  obtain ⟨h2,h20⟩ := Finset.mem_Icc.mp hk
  interval_cases k <;> decide

theorem actual_adaptive_restore20
    (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 98*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<20*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_adaptive_restore_uniform 20 98 26 RankWidth20 N c L R F G E hN
    (by decide) (by decide) rank_width20_payments hsize hc hcL hLR hRN hpay
    hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore20
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 98*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N 20 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 20 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_deleted_avoider_restore_uniform 20 98 26 RankWidth20 N c L R F hN
    (by decide) (by decide) rank_width20_payments hsize hc hcL hLR hRN hpay hlegal hne hi

def RatioRankTable (r num den Pmax : ℕ) (p : ℕ→ℕ) : Prop :=
  ∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k ∧ p k≤Pmax ∧
    den*(k*p k)≤(p k-k)*num ∧
    den*(4*(k-1)*(JointCount (p k)+1))≤(5*k-9)*num

theorem ratio_rank_physical_payments
    {r num den Pmax N t : ℕ} {p : ℕ→ℕ}
    (hrows : RatioRankTable r num den Pmax p) (hden : 0<den)
    (hnum : 42*den≤num) (hsize : Pmax^3≤N) (hpay : num*t≤den*N) :
    42*t≤N ∧
      (∀k∈Finset.Icc 2 r,k<p k ∧ 3≤p k) ∧
      (∀k∈Finset.Icc 2 r,(p k)^3≤N) ∧
      (∀k∈Finset.Icc 2 r,k*p k*t≤(p k-k)*N) ∧
      (∀k∈Finset.Icc 2 r,4*(k-1)*(JointCount (p k)+1)*t≤(5*k-9)*N) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · have hh : den*(42*t)≤den*N := by
      calc
        den*(42*t)=(42*den)*t := by ring
        _≤num*t := Nat.mul_le_mul_right t hnum
        _≤den*N := hpay
    exact le_of_mul_le_mul_left hh hden
  · intro k hk
    exact ⟨(hrows k hk).1,(hrows k hk).2.1⟩
  · intro k hk
    exact (Nat.pow_le_pow_left (hrows k hk).2.2.1 3).trans hsize
  · intro k hk
    have hh : den*(k*p k*t)≤den*((p k-k)*N) := by
      calc
        den*(k*p k*t)=(den*(k*p k))*t := by ring
        _≤((p k-k)*num)*t := Nat.mul_le_mul_right t (hrows k hk).2.2.2.1
        _=(p k-k)*(num*t) := by ring
        _≤(p k-k)*(den*N) := Nat.mul_le_mul_left _ hpay
        _=den*((p k-k)*N) := by ring
    exact le_of_mul_le_mul_left hh hden
  · intro k hk
    have hh : den*(4*(k-1)*(JointCount (p k)+1)*t)≤den*((5*k-9)*N) := by
      calc
        den*(4*(k-1)*(JointCount (p k)+1)*t)=
            (den*(4*(k-1)*(JointCount (p k)+1)))*t := by ring
        _≤((5*k-9)*num)*t := Nat.mul_le_mul_right t (hrows k hk).2.2.2.2
        _=(5*k-9)*(num*t) := by ring
        _≤(5*k-9)*(den*N) := Nat.mul_le_mul_left _ hpay
        _=den*((5*k-9)*N) := by ring
    exact le_of_mul_le_mul_left hh hden

theorem actual_adaptive_restore_ratio
    (r num den Pmax : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r) (hden : 0<den) (hnum : 42*den≤num)
    (hrows : RatioRankTable r num den Pmax p) (hsize : Pmax^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : num*(L+N-R)≤den*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<r*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  obtain ⟨hthin,hp,hcube,hgeometry,hquarter⟩ :=
    ratio_rank_physical_payments hrows hden hnum hsize hpay
  exact actual_adaptive_restore_rank_table r p N c L R F G E hN hr hp hcube
    hc hcL hLR hRN hthin hgeometry hquarter hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore_ratio
    (r num den Pmax : ℕ) (p : ℕ→ℕ) (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hr : 2≤r) (hden : 0<den) (hnum : 42*den≤num)
    (hrows : RatioRankTable r num den Pmax p) (hsize : Pmax^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : num*(L+N-R)≤den*N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N r F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  obtain ⟨hthin,hp,hcube,hgeometry,hquarter⟩ :=
    ratio_rank_physical_payments hrows hden hnum hsize hpay
  exact actual_deleted_avoider_restore_rank_table r p N c L R F hN hr hp hcube
    hc hcL hLR hRN hthin hgeometry hquarter hlegal hne hi

theorem rank_width20_ratio_payments : RatioRankTable 20 684 7 26 RankWidth20 := by
  intro k hk
  obtain ⟨h2,h20⟩ := Finset.mem_Icc.mp hk
  interval_cases k <;> decide

theorem actual_adaptive_restore20_ratio
    (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 684*(L+N-R)≤7*N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈E,¬IsAP S) (hdense : ∀S∈E,N<20*S.card)
    (havoid : ∀S∈E,(c:ℤ)∉S)
    (hne : (Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders G (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_adaptive_restore_ratio 20 684 7 26 RankWidth20 N c L R F G E hN
    (by decide) (by decide) (by decide) rank_width20_ratio_payments hsize
    hc hcL hLR hRN hpay hG hEF hlegal hbad hdense havoid hne hi

theorem actual_deleted_avoider_restore20_ratio
    (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : N<2^50) (hsize : 26^3≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hpay : 684*(L+N-R)≤7*N)
    (hlegal : Legal (Ground N) F) (hne : (Avoiders (Retained N 20 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 20 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b)) : F.card≤B N := by
  exact actual_deleted_avoider_restore_ratio 20 684 7 26 RankWidth20 N c L R F hN
    (by decide) (by decide) (by decide) rank_width20_ratio_payments hsize
    hc hcL hLR hRN hpay hlegal hne hi

#print axioms uniform_rank_physical_payments
#print axioms actual_adaptive_restore_uniform
#print axioms actual_deleted_avoider_restore_uniform
#print axioms rank_width20_payments
#print axioms actual_adaptive_restore20
#print axioms actual_deleted_avoider_restore20
#print axioms ratio_rank_physical_payments
#print axioms actual_adaptive_restore_ratio
#print axioms actual_deleted_avoider_restore_ratio
#print axioms rank_width20_ratio_payments
#print axioms actual_adaptive_restore20_ratio
#print axioms actual_deleted_avoider_restore20_ratio
end
end JSP233.RankTwenty58
