import Erdos272.Capacity.StepHall33
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Max

/-! Arithmetic and actual long-row matching from the physical long-core
condition. No totient supply or Hall premise is assumed in the final bridge. -/
namespace JSP233.ThinCore36
open StarCompletion StaircaseGeometry AffineLine30 CrossLine30 StepHall33
open scoped Classical BigOperators
noncomputable section

theorem product_ratio_card_bound (s : Finset ℕ) (hs : ∀ p∈s, 2≤p) :
    (∏ p∈s, p)≤(s.card+1)*(∏ p∈s, (p-1)) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have hnot : a∉s := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have ha : 2≤a := hs a (Finset.mem_insert_self a s)
    have hs0 : ∀ p∈s, 2≤p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hsub : s⊆Finset.Icc 2 (a-1) := by
      intro p hp
      exact Finset.mem_Icc.mpr ⟨hs0 p hp,by have hh := hmax p hp; omega⟩
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    have hca : s.card+2≤a := by omega
    have hcoef : a*(s.card+1)≤(s.card+2)*(a-1) := by
      have he : a-1+1=a := by omega
      nlinarith
    have hbase := Nat.mul_le_mul_left a (ih hs0)
    have hscale := Nat.mul_le_mul_right (∏ p∈s,(p-1)) hcoef
    rw [Finset.prod_insert hnot,Finset.prod_insert hnot,Finset.card_insert_of_notMem hnot]
    nlinarith

theorem le_prime_factor_count_mul_totient (m : ℕ) :
    m≤(m.primeFactors.card+1)*Nat.totient m := by
  have hp : ∀ p∈m.primeFactors, 2≤p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have hc := product_ratio_card_bound m.primeFactors hp
  have hs := Nat.mul_le_mul_left (Nat.totient m) hc
  have he := Nat.totient_mul_prod_primeFactors m
  have hpos : 0<∏ p∈m.primeFactors,(p-1) := by
    apply Finset.prod_pos
    intro p hp0
    have hh := hp p hp0
    omega
  have hmul : m*(∏ p∈m.primeFactors,(p-1))≤
      ((m.primeFactors.card+1)*Nat.totient m)*(∏ p∈m.primeFactors,(p-1)) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hpos).mp hmul

theorem prime_factor_count_le_log {m : ℕ} (hm : m≠0) :
    m.primeFactors.card≤Nat.log 2 m := by
  apply (Nat.le_log_iff_pow_le (by decide) hm).mpr
  calc
    2^m.primeFactors.card≤∏ p∈m.primeFactors,p :=
      Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    _≤m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.prod_primeFactors_dvd m)

theorem actual_totient_log_bound (m : ℕ) :
    m≤(Nat.log 2 m+1)*Nat.totient m := by
  by_cases hm : m=0
  · simp [hm]
  · exact (le_prime_factor_count_mul_totient m).trans
      (Nat.mul_le_mul_right _ (Nat.add_le_add_right (prime_factor_count_le_log hm) 1))

theorem actual_totient_log_bound_of_le (N m : ℕ) (hmN : m≤N) :
    m≤(Nat.log 2 N+1)*Nat.totient m :=
  (actual_totient_log_bound m).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.log_mono_right hmN) 1))

theorem long_core_totient_supply_coarse (N c L R d r : ℕ)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hr : (R-c)/d<r) (hrN : r≤N/d) :
    ((L-c)/d+1)+c/d+1≤Nat.totient r := by
  let t := L+N-R
  let J := Nat.log 2 N+1
  have ht : L≤t := by dsimp [t]; omega
  have htp : 0<t := by omega
  have hct : c≤t := by omega
  have hsum : N+L=t+R := by dsimp [t]; omega
  have hrc : R-c+c=R := by omega
  have hlc : L-c+c=L := by omega
  have hrphi : r≤J*Nat.totient r :=
    actual_totient_log_bound_of_le N r (hrN.trans (Nat.div_le_self N d))
  have hrlow : R-c<r*d := (Nat.div_lt_iff_lt_mul hd).mp hr
  by_contra hfail
  have hphi : Nat.totient r≤(L-c)/d+c/d+1 := by omega
  have hdphi : d*Nat.totient r≤2*t := by
    have hLdiv := Nat.mul_div_le (L-c) d
    have hcdiv := Nat.mul_div_le c d
    have hm := Nat.mul_le_mul_left d hphi
    change d≤t at hdt
    nlinarith
  have hupper : d*r≤J*(2*t) := by
    calc
      d*r≤d*(J*Nat.totient r) := Nat.mul_le_mul_left d hrphi
      _=J*(d*Nat.totient r) := by ring
      _≤J*(2*t) := Nat.mul_le_mul_left J hdphi
  have hJ : 1≤J := by dsimp [J]; omega
  have htJ : t≤t*J := by nlinarith
  change 4*t*J≤N at hcore
  nlinarith

theorem long_core_totient_supply (N c L R d r : ℕ)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hr : (R-c)/d<r) (hrN : r≤N/d) :
    ((L-c)/d+1)+(c-1)/d+1≤Nat.totient r := by
  have hcdiv : (c-1)/d≤c/d := Nat.div_le_div_right (Nat.sub_le c 1)
  have hh := long_core_totient_supply_coarse N c L R d r hcL hLR hRN hd hdt hcore hr hrN
  omega

theorem long_core_normalized_cutoff (N c L R d : ℕ)
    (hcL : c<L) (hLR : L≤R) (_hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N) :
    2≤(R-c)/d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have hsum : N+L=(L+N-R)+R := by omega
  have hrc : R-c+c=R := by omega
  have hthin : 4*(L+N-R)≤N := by
    have hh := Nat.mul_le_mul_left (4*(L+N-R))
      (show 1≤Nat.log 2 N+1 by omega)
    omega
  nlinarith

theorem normalized_start_above_core (c L d : ℕ) (hcL : c<L) (hd : 0<d) :
    L<c+d*((L-c)/d+1) := by
  have hh : L-c<((L-c)/d+1)*d :=
    (Nat.div_lt_iff_lt_mul hd).mp (by omega)
  have he : L-c+c=L := by omega
  nlinarith

theorem physical_window_row_bounds (N c d l r : ℕ) (hc : 1≤c) (hd : 0<d)
    (hground : mapSet (c:ℤ) (d:ℤ) (Window l r)⊆Ground N) :
    l≤(c-1)/d ∧ r≤N/d := by
  have hxL : (c:ℤ)-(d:ℤ)*(l:ℤ)∈mapSet (c:ℤ) (d:ℤ) (Window l r) := by
    refine Finset.mem_image.mpr ⟨-(l:ℤ),by simp [Window],?_⟩
    dsimp [affine]; ring
  have hxR : (c:ℤ)+(d:ℤ)*(r:ℤ)∈mapSet (c:ℤ) (d:ℤ) (Window l r) := by
    exact Finset.mem_image.mpr ⟨(r:ℤ),by simp [Window],rfl⟩
  have hL := ((mem_ground N _).mp (hground hxL)).1
  have hR := ((mem_ground N _).mp (hground hxR)).2
  have hcsub : ((c-1:ℕ):ℤ)=(c:ℤ)-1 := by omega
  constructor
  · apply (Nat.le_div_iff_mul_le hd).mpr
    have hh : (l:ℤ)*(d:ℤ)≤((c-1:ℕ):ℤ) := by nlinarith
    exact_mod_cast hh
  · apply (Nat.le_div_iff_mul_le hd).mpr
    have hh : (r:ℤ)*(d:ℤ)≤(N:ℤ) := by nlinarith
    exact_mod_cast hh

theorem long_core_normalized_matching (N c L R d : ℕ) (C : Finset (ℕ×ℕ))
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hleft : ∀ p∈C, p.1≤(c-1)/d)
    (hlong : ∀ p∈C, (R-c)/d<p.2 ∧ p.2≤N/d) :
    ∃ f : C→Finset ℤ, Function.Injective f ∧
      ∀ p, f p⊆Window p.val.1 p.val.2 ∧ IsPrimitiveBadPair (f p) ∧
        ∀ x∈f p, (((L-c)/d+1:ℕ):ℤ)≤x := by
  apply actual_long_row_matching C ((L-c)/d+1) ((c-1)/d)
    (Nat.succ_le_succ (Nat.zero_le _)) hleft
  · intro p hp
    have hb := long_core_normalized_cutoff N c L R d hcL hLR hRN hd hdt hcore
    have hr := (hlong p hp).1
    omega
  · intro p hp
    exact long_core_totient_supply N c L R d p.2 hcL hLR hRN hd hdt hcore
      (hlong p hp).1 (hlong p hp).2

theorem actual_long_core_matching (N c L R d : ℕ) (C : Finset (ℕ×ℕ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ p∈C, mapSet (c:ℤ) (d:ℤ) (Window p.1 p.2)⊆Ground N)
    (hlong : ∀ p∈C, (R-c)/d<p.2) :
    ∃ f : C→Finset ℤ, Function.Injective f ∧
      ∀ p, f p⊆mapSet (c:ℤ) (d:ℤ) (Window p.val.1 p.val.2) ∧
        IsStepPrimitive (c:ℤ) (d:ℤ) (f p) ∧ ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) (f p) := by
  have hb : ∀ p∈C, p.1≤(c-1)/d ∧ p.2≤N/d := by
    intro p hp
    exact physical_window_row_bounds N c d p.1 p.2 hc hd (hground p hp)
  apply actual_affine_long_row_matching C ((L-c)/d+1) ((c-1)/d)
    (c:ℤ) (d:ℤ) (L:ℤ) (R:ℤ) (by exact_mod_cast hd)
    (Nat.succ_le_succ (Nat.zero_le _))
    (fun p hp => (hb p hp).1)
  · intro p hp
    have hh := long_core_normalized_cutoff N c L R d hcL hLR hRN hd hdt hcore
    have hr := hlong p hp
    omega
  · intro p hp
    exact long_core_totient_supply N c L R d p.2 hcL hLR hRN hd hdt hcore
      (hlong p hp) (hb p hp).2
  · have hh := (normalized_start_above_core c L d hcL hd).le
    exact_mod_cast hh

def CornerPool (A B : ℕ) (p : ℕ×ℕ) : Finset (Finset ℤ) :=
  if p.2≤B then PrimitiveBadPairs (Window p.1 p.2) else PositiveRowPool A p.2

theorem coordinate_subfamily_hall (C : Finset (ℕ×ℕ))
    (hvalid : ∀ p∈C, 3≤p.1+p.2) :
    C.card≤(C.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2))).card+1 := by
  have hh := StaircaseComplete29.unbounded_coordinates_defect_le_one (C:=C) hvalid
  have hpool : PrimitivePool (Family C)=
      C.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2)) := by
    ext Q
    simp [PrimitivePool,Family]
  rw [family_card,hpool] at hh
  omega

theorem coordinate_subfamily_thin_hall (C : Finset (ℕ×ℕ))
    (hvalid : ∀ p∈C, 3≤p.1+p.2) (hleft : ∀ p∈C, p.1≤1) :
    C.card≤(C.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2))).card := by
  have hh := StaircaseThin.left_thin_coordinates_card hvalid hleft
  have hpool : PrimitivePool (Family C)=
      C.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2)) := by
    ext Q
    simp [PrimitivePool,Family]
  rwa [family_card,hpool] at hh

theorem positive_row_pool_geometry (A l r : ℕ) (hA : 1≤A) (hr : 3≤r)
    (Q : Finset ℤ) (hQ : Q∈PositiveRowPool A r) :
    Q⊆Window l r ∧ IsPrimitiveBadPair Q ∧ (r:ℤ)∈Q ∧
      (∀ x∈Q, (A:ℤ)≤x) ∧ (∀ x∈Q, x≤(r:ℤ)) := by
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hQ
  obtain ⟨har,hAa,hcop⟩ := Finset.mem_filter.mp ha
  have har0 := Finset.mem_range.mp har
  rw [←he]
  refine ⟨?_,?_,by simp,?_,?_⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp only [Window,Finset.mem_Icc] <;> omega
  · exact (StaircaseSupply.positive_pair_iff r a (by omega) har0).mpr ⟨hcop.symm,hr⟩
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> omega

theorem short_long_pools_disjoint (C : Finset (ℕ×ℕ)) (A B : ℕ) :
    Disjoint
      ((C.filter (fun p => p.2≤B)).biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2)))
      ((C.filter (fun p => ¬p.2≤B)).biUnion (fun p => PositiveRowPool A p.2)) := by
  apply Finset.disjoint_left.mpr
  intro Q hshort hlong
  obtain ⟨p,hp,hQp⟩ := Finset.mem_biUnion.mp hshort
  obtain ⟨q,hq,hQq⟩ := Finset.mem_biUnion.mp hlong
  have hpB := (Finset.mem_filter.mp hp).2
  have hqB := (Finset.mem_filter.mp hq).2
  have hsub := (mem_primitiveBadPairs _ _).mp hQp
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hQq
  have hqmem : (q.2:ℤ)∈Q := by rw [←he]; simp
  have hh := hsub.1 hqmem
  rw [Window,Finset.mem_Icc] at hh
  omega

theorem corner_pool_hall_from_short_bound (C : Finset (ℕ×ℕ)) (A B H ε : ℕ)
    (hshort : ∀ S⊆C, (∀ p∈S, p.2≤B) →
      S.card≤(S.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2))).card+ε)
    (hleft : ∀ p∈C, p.1≤H)
    (hphi : ∀ p∈C, B<p.2 → A+H+1≤Nat.totient p.2) :
    ∀ T⊆C, T.card≤(T.biUnion (CornerPool A B)).card+ε := by
  intro T hTC
  let S := T.filter (fun p => p.2≤B)
  let U := T.filter (fun p => ¬p.2≤B)
  have hST : S⊆T := Finset.filter_subset _ _
  have hUT : U⊆T := Finset.filter_subset _ _
  have hs := hshort S (hST.trans hTC) (fun p hp => (Finset.mem_filter.mp hp).2)
  have hu := graded_hall_count U Prod.snd (PositiveRowPool A)
    (fun r _ s _ hne => positive_row_pools_disjoint A r s hne) (by
      intro r hr
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
      have hf := row_fibre_card U H p.2 (fun q hq => hleft q (hTC (hUT hq)))
      have hr0 := row_residue_card A p.2
      have hp0 : p∈C := hTC (hUT hp)
      have hpB : B<p.2 := by have hh := (Finset.mem_filter.mp hp).2; omega
      have htot := hphi p hp0 hpB
      rw [positive_row_pool_card]
      omega) U (Finset.Subset.refl U)
  have hcount : S.card+U.card=T.card :=
    Finset.card_filter_add_card_filter_not (s:=T) (fun p => p.2≤B)
  have hdis := short_long_pools_disjoint T A B
  have hpool : T.biUnion (CornerPool A B)=
      (S.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2)))∪
        (U.biUnion (fun p => PositiveRowPool A p.2)) := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨p,hp,hpQ⟩ := Finset.mem_biUnion.mp hQ
      by_cases hpB : p.2≤B
      · apply Finset.mem_union_left
        exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hpB⟩,
          by simpa only [CornerPool,if_pos hpB] using hpQ⟩
      · apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,hpB⟩,
          by simpa only [CornerPool,if_neg hpB] using hpQ⟩
    · intro hQ
      rcases Finset.mem_union.mp hQ with hQ | hQ
      · obtain ⟨p,hp,hpQ⟩ := Finset.mem_biUnion.mp hQ
        obtain ⟨hpT,hpB⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_biUnion.mpr ⟨p,hpT,by simpa only [CornerPool,if_pos hpB] using hpQ⟩
      · obtain ⟨p,hp,hpQ⟩ := Finset.mem_biUnion.mp hQ
        obtain ⟨hpT,hpB⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_biUnion.mpr ⟨p,hpT,by simpa only [CornerPool,if_neg hpB] using hpQ⟩
  have hcard := Finset.card_union_of_disjoint hdis
  change ((S.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2)))∪
      U.biUnion (fun p => PositiveRowPool A p.2)).card=
      (S.biUnion (fun p => PrimitiveBadPairs (Window p.1 p.2))).card+
        (U.biUnion (fun p => PositiveRowPool A p.2)).card at hcard
  rw [hpool,hcard]
  omega

theorem corner_pool_hall (C : Finset (ℕ×ℕ)) (A B H : ℕ)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) (hleft : ∀ p∈C, p.1≤H)
    (hphi : ∀ p∈C, B<p.2 → A+H+1≤Nat.totient p.2) :
    ∀ T⊆C, T.card≤(T.biUnion (CornerPool A B)).card+1 :=
  corner_pool_hall_from_short_bound C A B H 1
    (fun S hSC _ => coordinate_subfamily_hall S (fun p hp => hvalid p (hSC hp))) hleft hphi

theorem corner_pool_thin_hall (C : Finset (ℕ×ℕ)) (A B H : ℕ)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) (hleft : ∀ p∈C, p.1≤H) (hH : H≤1)
    (hphi : ∀ p∈C, B<p.2 → A+H+1≤Nat.totient p.2) :
    ∀ T⊆C, T.card≤(T.biUnion (CornerPool A B)).card := by
  have hh := corner_pool_hall_from_short_bound C A B H 0 (by
    intro S hSC _
    have hs := coordinate_subfamily_thin_hall S (fun p hp => hvalid p (hSC hp))
      (fun p hp => (hleft p (hSC hp)).trans hH)
    simpa only [add_zero] using hs) hleft hphi
  simpa only [add_zero] using hh

theorem corner_pool_geometry (A B : ℕ) (p : ℕ×ℕ) (Q : Finset ℤ)
    (hA : 1≤A) (hB : 2≤B) (hQ : Q∈CornerPool A B p) :
    Q⊆Window p.1 p.2 ∧ IsPrimitiveBadPair Q ∧
      ((∀ x∈Q, x≤(B:ℤ)) ∨ (∀ x∈Q, (A:ℤ)≤x)) := by
  by_cases hpB : p.2≤B
  · rw [CornerPool,if_pos hpB] at hQ
    obtain ⟨hsub,hprim⟩ := (mem_primitiveBadPairs _ _).mp hQ
    refine ⟨hsub,hprim,Or.inl ?_⟩
    intro x hx
    have hh := hsub hx
    rw [Window,Finset.mem_Icc] at hh
    omega
  · rw [CornerPool,if_neg hpB] at hQ
    obtain ⟨hsub,hprim,_,hlow,_⟩ := positive_row_pool_geometry A p.1 p.2 hA (by omega) Q hQ
    exact ⟨hsub,hprim,Or.inr hlow⟩

theorem corner_pool_matching (C : Finset (ℕ×ℕ)) (A B H : ℕ)
    (hA : 1≤A) (hB : 2≤B)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) (hleft : ∀ p∈C, p.1≤H)
    (hphi : ∀ p∈C, B<p.2 → A+H+1≤Nat.totient p.2) :
    ∃ f : C→Option (Finset ℤ), Function.Injective f ∧
      ∀ p, f p=none ∨ ∃ Q, f p=some Q ∧ Q⊆Window p.val.1 p.val.2 ∧
        IsPrimitiveBadPair Q ∧
          ((∀ x∈Q, x≤(B:ℤ)) ∨ (∀ x∈Q, (A:ℤ)≤x)) := by
  obtain ⟨f,hf,hm⟩ := hall_with_dummy C (CornerPool A B)
    (corner_pool_hall C A B H hvalid hleft hphi)
  refine ⟨f,hf,?_⟩
  intro p
  rcases Finset.mem_insert.mp (hm p) with he | he
  · exact Or.inl he
  · obtain ⟨Q,hQ,he⟩ := Finset.mem_image.mp he
    have hg := corner_pool_geometry A B p.val Q hA hB hQ
    exact Or.inr ⟨Q,he.symm,hg.1,hg.2.1,hg.2.2⟩

theorem corner_pool_matching_with_dummy_geometry (C : Finset (ℕ×ℕ)) (A B H : ℕ)
    (hA : 1≤A) (hB : 2≤B)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) (hleft : ∀ p∈C, p.1≤H)
    (hphi : ∀ p∈C, B<p.2 → A+H+1≤Nat.totient p.2) :
    ∃ f : C→Option (Finset ℤ), Function.Injective f ∧
      (∀ p, f p=none → 2≤H) ∧
      ∀ p, f p=none ∨ ∃ Q, f p=some Q ∧ Q⊆Window p.val.1 p.val.2 ∧
        IsPrimitiveBadPair Q ∧
          ((∀ x∈Q, x≤(B:ℤ)) ∨ (∀ x∈Q, (A:ℤ)≤x)) := by
  by_cases hH : H≤1
  · obtain ⟨f,hf,hm⟩ := hall_without_dummy C (CornerPool A B)
      (corner_pool_thin_hall C A B H hvalid hleft hH hphi)
    refine ⟨fun p => some (f p),(Option.some_injective _).comp hf,?_,?_⟩
    · intro p hn
      simp at hn
    · intro p
      have hg := corner_pool_geometry A B p.val (f p) hA hB (hm p)
      exact Or.inr ⟨f p,rfl,hg.1,hg.2.1,hg.2.2⟩
  · obtain ⟨f,hf,hm⟩ := corner_pool_matching C A B H hA hB hvalid hleft hphi
    exact ⟨f,hf,fun _ _ => by omega,hm⟩

theorem actual_normalized_core_cutoff_matching (N c L R d : ℕ) (C : Finset (ℕ×ℕ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ p∈C, mapSet (c:ℤ) (d:ℤ) (Window p.1 p.2)⊆Ground N)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) :
    ∃ f : C→Option (Finset ℤ), Function.Injective f ∧
      ∀ p, f p=none ∨ ∃ Q, f p=some Q ∧ Q⊆Window p.val.1 p.val.2 ∧
        IsPrimitiveBadPair Q ∧
          ((∀ x∈Q, x≤(((R-c)/d:ℕ):ℤ)) ∨
            (∀ x∈Q, (((L-c)/d+1:ℕ):ℤ)≤x)) := by
  have hb : ∀ p∈C, p.1≤(c-1)/d ∧ p.2≤N/d := by
    intro p hp
    exact physical_window_row_bounds N c d p.1 p.2 hc hd (hground p hp)
  exact corner_pool_matching C ((L-c)/d+1) ((R-c)/d) ((c-1)/d)
    (Nat.succ_le_succ (Nat.zero_le _))
    (long_core_normalized_cutoff N c L R d hcL hLR hRN hd hdt hcore)
    hvalid (fun p hp => (hb p hp).1)
    (fun p hp hlong => long_core_totient_supply N c L R d p.2 hcL hLR hRN hd hdt hcore
      hlong (hb p hp).2)

theorem option_map_injective {α β : Type*} (f : α→β) (hf : Function.Injective f) :
    Function.Injective (Option.map f) := by
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => simp at he
  | some x =>
    cases y with
    | none => simp at he
    | some y =>
      have hxy : f x=f y := Option.some.inj he
      exact congrArg some (hf hxy)

theorem actual_core_cutoff_matching (N c L R d : ℕ) (C : Finset (ℕ×ℕ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hdt : d≤L+N-R)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ p∈C, mapSet (c:ℤ) (d:ℤ) (Window p.1 p.2)⊆Ground N)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) :
    ∃ f : C→Option (Finset ℤ), Function.Injective f ∧
      (∀ p, f p=none → 2*d≤c-1) ∧
      ∀ p, f p=none ∨ ∃ Q, f p=some Q ∧
        Q⊆mapSet (c:ℤ) (d:ℤ) (Window p.val.1 p.val.2) ∧
        IsStepPrimitive (c:ℤ) (d:ℤ) Q ∧ ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q := by
  have hb : ∀ p∈C, p.1≤(c-1)/d ∧ p.2≤N/d := by
    intro p hp
    exact physical_window_row_bounds N c d p.1 p.2 hc hd (hground p hp)
  obtain ⟨f,hf,hfn,hm⟩ := corner_pool_matching_with_dummy_geometry C
    ((L-c)/d+1) ((R-c)/d) ((c-1)/d) (Nat.succ_le_succ (Nat.zero_le _))
    (long_core_normalized_cutoff N c L R d hcL hLR hRN hd hdt hcore)
    hvalid (fun p hp => (hb p hp).1)
    (fun p hp hlong => long_core_totient_supply N c L R d p.2 hcL hLR hRN hd hdt hcore
      hlong (hb p hp).2)
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  let g : C→Option (Finset ℤ) := fun p => (f p).map (mapSet (c:ℤ) (d:ℤ))
  have hg : Function.Injective g :=
    (option_map_injective (mapSet (c:ℤ) (d:ℤ)) (mapSet_injective _ _ hdZ)).comp hf
  have hstart : (L:ℤ)≤(c:ℤ)+(d:ℤ)*(((L-c)/d+1:ℕ):ℤ) := by
    exact_mod_cast (normalized_start_above_core c L d hcL hd).le
  have hend : (c:ℤ)+(d:ℤ)*(((R-c)/d:ℕ):ℤ)≤(R:ℤ) := by
    have hm0 := Nat.mul_div_le (R-c) d
    have he0 : R-c+c=R := by omega
    have hh : c+d*((R-c)/d)≤R := by omega
    exact_mod_cast hh
  refine ⟨g,hg,?_,?_⟩
  · intro p hn
    have hfp : f p=none := by
      cases he : f p with
      | none => rfl
      | some Q => simp [g,he] at hn
    exact (Nat.le_div_iff_mul_le hd).mp (hfn p hfp)
  · intro p
    rcases hm p with hn | ⟨Q,he,hsub,hprim,hcut⟩
    · exact Or.inl (by simp [g,hn])
    · refine Or.inr ⟨mapSet (c:ℤ) (d:ℤ) Q,by simp [g,he],
        (mapSet_subset_iff _ _ hdZ _ _).mpr hsub,
        (isStepPrimitive_map_iff _ _ hdZ _).mpr hprim,?_⟩
      rintro ⟨u,v,hrep,hcu,huL,hRv⟩
      rcases hcut with hshort | hlong
      · have hv : v∈mapSet (c:ℤ) (d:ℤ) Q := by rw [hrep]; simp
        obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp hv
        have hxB := hshort x hx
        have hmul := mul_le_mul_of_nonneg_left hxB hdZ.le
        dsimp [affine] at hxe
        nlinarith
      · have hu : u∈mapSet (c:ℤ) (d:ℤ) Q := by rw [hrep]; simp
        obtain ⟨x,hx,hxe⟩ := Finset.mem_image.mp hu
        have hAx := hlong x hx
        have hmul := mul_le_mul_of_nonneg_left hAx hdZ.le
        dsimp [affine] at hxe
        nlinarith

#print axioms product_ratio_card_bound
#print axioms le_prime_factor_count_mul_totient
#print axioms prime_factor_count_le_log
#print axioms actual_totient_log_bound
#print axioms actual_totient_log_bound_of_le
#print axioms long_core_totient_supply_coarse
#print axioms long_core_totient_supply
#print axioms long_core_normalized_cutoff
#print axioms normalized_start_above_core
#print axioms physical_window_row_bounds
#print axioms long_core_normalized_matching
#print axioms actual_long_core_matching
#print axioms coordinate_subfamily_hall
#print axioms coordinate_subfamily_thin_hall
#print axioms positive_row_pool_geometry
#print axioms short_long_pools_disjoint
#print axioms corner_pool_hall_from_short_bound
#print axioms corner_pool_hall
#print axioms corner_pool_thin_hall
#print axioms corner_pool_geometry
#print axioms corner_pool_matching
#print axioms corner_pool_matching_with_dummy_geometry
#print axioms actual_normalized_core_cutoff_matching
#print axioms option_map_injective
#print axioms actual_core_cutoff_matching
end
end JSP233.ThinCore36
