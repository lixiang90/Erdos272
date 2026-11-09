module

public import Erdos272.Retention.ThinFringe38
public import Erdos272.Global.DenseDeletion40

@[expose] public section

/-! A rank-parameterized actual dense crooked fringe: positive grid anchors
use only r+1 positions under the stronger physical thinness r*(r+1)*t<=N, with exact finite AnchorCount r. -/
namespace JSP233.ThinFringe42
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section

def AnchorKeys (r : ℕ) : Finset (Σ _d : ℕ, ℕ×ℕ) :=
  (Finset.Icc 1 r).sigma (fun d => (Finset.Icc 1 d).product (Finset.Icc 1 ((r+1)/d)))

def AnchorCount (r : ℕ) : ℕ := ∑ d∈Finset.Icc 1 r,d*((r+1)/d)

def AnchorPoint (r N : ℕ) (k : Σ _d : ℕ, ℕ×ℕ) : ℤ :=
  (k.2.1:ℤ)+(k.2.2:ℤ)*(N/(r+1):ℕ)*(k.1:ℤ)

def HasAnchor (r N : ℕ) (L R : ℤ) (k : Σ _d : ℕ, ℕ×ℕ) (S : Finset ℤ) : Prop :=
  APAt (k.1:ℤ) (AnchorPoint r N k) (S∩Finset.Icc L R) ∧
    AnchorPoint r N k∈S∩Finset.Icc L R ∧
    AnchorPoint r N k+(k.1:ℤ)∈S∩Finset.Icc L R

theorem anchor_keys_card (r : ℕ) : (AnchorKeys r).card=AnchorCount r := by
  simp [AnchorKeys,AnchorCount,Finset.card_sigma,Finset.card_product]

theorem anchor_count18 : AnchorCount 18=278 := by
  norm_num [AnchorCount,Finset.sum_Icc_succ_top]

theorem anchor_count24 : AnchorCount 24=497 := by
  norm_num [AnchorCount,Finset.sum_Icc_succ_top]

theorem anchor_count_geometry_payment (r : ℕ) : r*(r+1)≤4*AnchorCount r := by
  have hgauss : ∀ n:ℕ,2*(∑ d∈Finset.Icc 1 n,d)=n*(n+1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1≤n+1)]
      nlinarith only [ih]
  have hbound : (∑ d∈Finset.Icc 1 r,d)≤AnchorCount r := by
    apply Finset.sum_le_sum
    intro d hd
    have hdr := Finset.mem_Icc.mp hd
    have hq : 1≤(r+1)/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr (by omega)
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left d hq
  nlinarith only [hbound,hgauss r]

theorem trace_count_lower (r N m outside : ℕ) (hr : 2≤r)
    (hdense : N<r*(m+outside)) (hthin : r*(r+1)*(outside+1)≤N) :
    N/(r+1)+1<m := by
  have hq := Nat.mul_div_le N (r+1)
  by_contra hn
  have hm : m≤N/(r+1)+1 := by omega
  have hmN : (r+1)*m≤N+(r+1) := by
    have hh := Nat.mul_le_mul_left (r+1) hm
    nlinarith only [hh,hq]
  have h1 := Nat.mul_lt_mul_of_pos_left hdense (by omega : 0<r+1)
  have h2 := Nat.mul_le_mul_left r hmN
  have hr0 : 0<r := by omega
  nlinarith only [h1,h2,hthin,hr0]

theorem dense_trace_geometry (r N : ℕ) (hr : 2≤r) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hdense : N<r*S.card)
    (hthin : r*(r+1)*((Ground N\Finset.Icc L R).card+1)≤N) :
    ∃ d p, APAt d p (S∩Finset.Icc L R) ∧ d≤(r:ℤ) ∧
      N/(r+1)+1<(S∩Finset.Icc L R).card := by
  let m := (S∩Finset.Icc L R).card
  let o := (Ground N\Finset.Icc L R).card
  have hc := card_le_trace_add_exterior (K:=Finset.Icc L R) hS
  have hcr := Nat.mul_le_mul_left r hc
  have hD : N<r*(m+o) := by
    dsimp [m,o]
    exact hdense.trans_le hcr
  have hm : N/(r+1)+1<m := trace_count_lower r N m o hr hD hthin
  have hthinold : r^2*((Ground N\Finset.Icc L R).card+1)≤N := by
    have hp := Nat.mul_le_mul_right ((Ground N\Finset.Icc L R).card+1)
      (show r^2≤r*(r+1) by nlinarith)
    exact hp.trans hthin
  obtain ⟨d,p,hAP,hdr,_⟩ := ThinFringe38.dense_trace_geometry r N hr hS hpair hKH
    hL hLR hR hdense hthinold
  exact ⟨d,p,hAP,hdr,hm⟩

theorem grid_anchor_cover (r N a b d m : ℕ) (hr : 2≤r) (hN : (r+1)^2≤N)
    (ha : 1≤a) (hb : b≤N) (hd : 1≤d) (hdr : d≤r)
    (hspan : b=a+d*(m-1)) (hm : N/(r+1)+1<m) :
    ∃ k∈AnchorKeys r, k.1=d ∧ a≤(AnchorPoint r N k).toNat ∧
      (AnchorPoint r N k).toNat+d≤b ∧
      d∣(AnchorPoint r N k).toNat-a := by
  let q := N/(r+1)
  have hqr : r+1≤q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le (by omega : 0<r+1)).mpr
    nlinarith only [hN]
  have hq : 0<q := by omega
  let rho := (a-1)%d+1
  let z := (a-1)/d
  let j := z/q+1
  have hr : 1≤rho ∧ rho≤d := by
    have hh := Nat.mod_lt (a-1) (by omega : 0<d)
    dsimp [rho]; omega
  have haz : a=rho+d*z := by
    have hh := Nat.mod_add_div (a-1) d
    dsimp [rho,z]; omega
  have hj : z<j*q ∧ j*q≤z+q := by
    have hh := Nat.mod_add_div z q
    have hl := Nat.mod_lt z hq
    dsimp [j]
    constructor <;> nlinarith [Nat.zero_le (z%q)]
  let u := rho+j*q*d
  have hua : a≤u := by dsimp [u]; nlinarith
  have hub : u+d≤b := by
    have hmm : q+1≤m-1 := by dsimp [q]; omega
    dsimp [u]; nlinarith
  have hNq : N<(r+1)*(q+1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ N (by omega)
  have hjd : j*d≤r+1 := by
    by_contra hn
    have hh : r+2≤j*d := by omega
    have hmul := Nat.mul_le_mul_right q hh
    have he : j*q*d=(j*d)*q := by ring
    dsimp [u] at hub
    rw [he] at hub
    nlinarith
  have hjlo : 1≤j := Nat.le_add_left 1 (z/q)
  have hjhi : j≤(r+1)/d := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr hjd
  let k : Σ _d : ℕ, ℕ×ℕ := ⟨d,rho,j⟩
  have hk : k∈AnchorKeys r := by
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,hdr⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr,Finset.mem_Icc.mpr ⟨hjlo,hjhi⟩⟩⟩
  have hpoint : AnchorPoint r N k=(u:ℤ) := by
    dsimp [AnchorPoint,k,u,q]
  refine ⟨k,hk,rfl,?_,?_,?_⟩
  · rw [hpoint,Int.toNat_natCast]; exact hua
  · rw [hpoint,Int.toNat_natCast]; exact hub
  · rw [hpoint,Int.toNat_natCast]
    have ht : (j*q-z)+z=j*q := Nat.sub_add_cancel hj.1.le
    have he : u=a+d*(j*q-z) := by dsimp [u]; nlinarith
    exact ⟨j*q-z,by omega⟩

theorem actual_trace_anchor (r N : ℕ) (hr : 2≤r) (hN : (r+1)^2≤N) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hdense : N<r*S.card)
    (hthin : r*(r+1)*((Ground N\Finset.Icc L R).card+1)≤N) :
    ∃ k∈AnchorKeys r, HasAnchor r N L R k S := by
  obtain ⟨d,p,hAP,hdr,hm⟩ := dense_trace_geometry r N hr hS hpair hKH hL hLR hR hdense hthin
  have hd := hAP.1
  have hcard : 2≤(S∩Finset.Icc L R).card := by
    have hz := Nat.zero_le (N/(r+1))
    omega
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by omega)
  let a := (S∩Finset.Icc L R).min' hne
  let b := (S∩Finset.Icc L R).max' hne
  have haS : a∈S∩Finset.Icc L R := Finset.min'_mem _ hne
  have hbS : b∈S∩Finset.Icc L R := Finset.max'_mem _ hne
  have haK := Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2
  have hbK := Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2
  have ha : 1≤a := by omega
  have hab : a≤b := Finset.min'_le _ b hbS
  have haCast : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hbCast : (b.toNat:ℤ)=b := Int.toNat_of_nonneg (by omega)
  have hdCast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have hspan := apAt_span_eq hAP hne
  have hsub : (((S∩Finset.Icc L R).card-1:ℕ):ℤ)=((S∩Finset.Icc L R).card:ℤ)-1 := by omega
  have hspanN : b.toNat=a.toNat+d.toNat*((S∩Finset.Icc L R).card-1) := by
    have hh : (b.toNat:ℤ)=(a.toNat:ℤ)+(d.toNat:ℤ)*(((S∩Finset.Icc L R).card-1:ℕ):ℤ) := by
      rw [haCast,hbCast,hdCast,hsub]
      dsimp [a,b]
      linarith
    exact_mod_cast hh
  obtain ⟨k,hk,hkd,hau,hub,hdiv⟩ := grid_anchor_cover r N a.toNat b.toNat d.toNat
    (S∩Finset.Icc L R).card hr hN (by omega) (by omega) (by omega) (by omega) hspanN hm
  have hu0 : 0≤AnchorPoint r N k := by unfold AnchorPoint; positivity
  have huCast : ((AnchorPoint r N k).toNat:ℤ)=AnchorPoint r N k := Int.toNat_of_nonneg hu0
  have hkdZ : (k.1:ℤ)=d := by rw [hkd,hdCast]
  have hauZ : a≤AnchorPoint r N k := by omega
  have hubZ : AnchorPoint r N k+d≤b := by omega
  have hdivZ : d∣AnchorPoint r N k-a := by
    have hh : (d.toNat:ℤ)∣(((AnchorPoint r N k).toNat-a.toNat:ℕ):ℤ) := by exact_mod_cast hdiv
    rw [Nat.cast_sub hau,huCast,haCast,hdCast] at hh
    exact hh
  have huS : AnchorPoint r N k∈S∩Finset.Icc L R :=
    apAt_fill hAP haS hbS hauZ (by omega) hdivZ
  have hvS : AnchorPoint r N k+d∈S∩Finset.Icc L R :=
    apAt_fill hAP haS hbS (by omega) hubZ (by
      have hh := Int.dvd_add hdivZ (dvd_refl d)
      convert hh using 1
      ring)
  refine ⟨k,hk,?_,huS,?_⟩
  · rw [hkdZ]
    exact apAt_rebase hAP huS
  · simpa only [hkdZ] using hvS

theorem actual_anchor_class_card (r N : ℕ) (F E : Finset (Finset ℤ)) (L R : ℤ)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (k : Σ _d : ℕ, ℕ×ℕ) :
    (E.filter (HasAnchor r N L R k)).card≤(Ground N\Finset.Icc L R).card := by
  apply actual_class_card_le_exterior
  · intro S hS
    exact hlegal.1 S (hEF (Finset.mem_filter.mp hS).1)
  · intro S hS
    exact hbad S (Finset.mem_filter.mp hS).1
  · intro S hS T hT hne
    exact hlegal.2 S (hEF (Finset.mem_filter.mp hS).1)
      T (hEF (Finset.mem_filter.mp hT).1) hne
  · intro S hS; exact (Finset.mem_filter.mp hS).2.1
  · intro S hS; exact (Finset.mem_filter.mp hS).2.2.1
  · intro S hS; exact (Finset.mem_filter.mp hS).2.2.2

theorem actual_dense_fringe_bound (r N : ℕ) (hr : 2≤r) (hN : (r+1)^2≤N) (F E : Finset (Finset ℤ))
    (L R : ℤ) (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<r*S.card)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F, IsAP H ∧ Finset.Icc L R⊆H)
    (hthin : r*(r+1)*((Ground N\Finset.Icc L R).card+1)≤N) :
    E.card≤(AnchorCount r)*(Ground N\Finset.Icc L R).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  have hcover : ∀ S∈E, ∃ k∈AnchorKeys r, HasAnchor r N L R k S := by
    intro S hS
    have hne : S≠H := by intro he; exact hbad S hS (he ▸ hHAP)
    exact actual_trace_anchor r N hr hN (hlegal.1 S (hEF hS))
      (hlegal.2 S (hEF hS) H hHF hne) hKH hL hLR hR (hdense S hS) hthin
  let C := fun k => E.filter (HasAnchor r N L R k)
  have hsub : E⊆(AnchorKeys r).biUnion C := by
    intro S hS
    obtain ⟨k,hk,hanchor⟩ := hcover S hS
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨hS,hanchor⟩⟩
  calc
    E.card≤((AnchorKeys r).biUnion C).card := Finset.card_le_card hsub
    _≤∑ k∈AnchorKeys r, (C k).card := Finset.card_biUnion_le
    _≤∑ _k∈AnchorKeys r, (Ground N\Finset.Icc L R).card := by
      apply Finset.sum_le_sum
      intro k hk
      exact actual_anchor_class_card r N F E L R hlegal hEF hbad k
    _=(AnchorKeys r).card*(Ground N\Finset.Icc L R).card := by simp
    _≤(AnchorCount r)*(Ground N\Finset.Icc L R).card := Nat.mul_le_mul_right _ (anchor_keys_card r).le

theorem actual_dense_fringe_bound_of_length (r N t : ℕ) (hr : 2≤r) (hN : (r+1)^2≤N) (F E : Finset (Finset ℤ))
    (L R : ℤ) (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<r*S.card)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : r*(r+1)*t≤N) :
    E.card≤(AnchorCount r)*(t-1) := by
  have ho := ground_interval_exterior_card N hL hLR hR
  have he : (Ground N\Finset.Icc L R).card+1=t := by omega
  have hh := actual_dense_fringe_bound r N hr hN F E L R hlegal hEF hbad hdense hL hLR hR hcore
    (by rw [he]; exact hthin : r*(r+1)*((Ground N\Finset.Icc L R).card+1)≤N)
  have he' : (Ground N\Finset.Icc L R).card=t-1 := by omega
  simpa only [he'] using hh

theorem fringe_quarter_payment (r N t : ℕ) (hN : 1≤N)
    (hpay : 4*AnchorCount r*t≤N) :
    AnchorCount r*(t-1)≤(N-1)/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  by_cases ha : AnchorCount r=0
  · simp [ha]
  by_cases ht : t=0
  · simp [ht]
  have ha1 : 1≤AnchorCount r := by omega
  have he : t-1+1=t := by omega
  have hm : AnchorCount r*(t-1)+AnchorCount r=AnchorCount r*t := by
    nlinarith only [he]
  have hNm : N-1+1=N := by omega
  nlinarith

theorem actual_deleted_fringe_quarter (r N t : ℕ) (F G E : Finset (Finset ℤ)) (L R : ℤ)
    (hr : 2≤r) (hN : (r+1)^2≤N) (hG : G=F\E) (hEF : E⊆F)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈E, ¬IsAP S)
    (hdense : ∀ S∈E, N<r*S.card)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcoreG : ∃ H∈G, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : r*(r+1)*t≤N)
    (hpay : 4*AnchorCount r*t≤N) : E.card≤(N-1)/4 := by
  obtain ⟨H,hHG,hHAP,hKH⟩ := hcoreG
  have hHF : H∈F := by rw [hG] at hHG; exact (Finset.mem_sdiff.mp hHG).1
  have hc := actual_dense_fringe_bound_of_length r N t hr hN F E L R hlegal hEF
    hbad hdense hL hLR hR ⟨H,hHF,hHAP,hKH⟩ ht hthin
  exact hc.trans (fringe_quarter_payment r N t (by nlinarith) hpay)

theorem actual_long_core_restore (r N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hr : 2≤r) (hN : (r+1)^2≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hrthin : r*(r+1)*(L+N-R)≤N) (hfringe : 4*AnchorCount r*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<r*S.card)
    (hne : (StarCompletion.Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  have hterminal := Terminal36.actual_native_interval_terminal N c L R G hc hcL hLR hRN hthin
    (RestoreTerminal35.retained_legal hG hlegal) hne hi
  have hcm := RestoreTerminal35.actual_interval_core_member N c L R G hLR hne hi
  have ht : ((L+N-R:ℕ):ℤ)=(L:ℤ)+(N:ℤ)-(R:ℤ) := by omega
  have hE := actual_deleted_fringe_quarter r N (L+N-R) F G E (L:ℤ) (R:ℤ)
    hr hN hG hEF hlegal hbad hdense (by omega) (by omega) (by omega) hcm ht hrthin hfringe
  have hcF := deletion_card_exact F E hEF
  rw [←hG] at hcF
  unfold B
  omega

theorem actual_long_core_restore_paid (r N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hr : 2≤r) (hN : (r+1)^2≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hfringe : 4*AnchorCount r*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<r*S.card)
    (hne : (StarCompletion.Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  have hpay := Nat.mul_le_mul_right (L+N-R) (anchor_count_geometry_payment r)
  exact actual_long_core_restore r N c L R F G E hr hN hc hcL hLR hRN hthin
    (hpay.trans hfringe) hfringe hG hEF hlegal hbad hdense hne hi

theorem actual_long_core_restore18 (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : 361≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hfringe : 1112*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<18*S.card)
    (hne : (StarCompletion.Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  apply actual_long_core_restore_paid 18 N c L R F G E (by decide) (by norm_num; exact hN)
    hc hcL hLR hRN hthin ?_ hG hEF hlegal hbad hdense hne hi
  simpa only [anchor_count18,show 4*278=1112 by norm_num] using hfringe

theorem actual_long_core_restore24 (N c L R : ℕ) (F G E : Finset (Finset ℤ))
    (hN : 625≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hfringe : 1988*(L+N-R)≤N)
    (hG : G=F\E) (hEF : E⊆F) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<24*S.card)
    (hne : (StarCompletion.Avoiders G (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders G (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  apply actual_long_core_restore_paid 24 N c L R F G E (by decide) (by norm_num; exact hN)
    hc hcL hLR hRN hthin ?_ hG hEF hlegal hbad hdense hne hi
  simpa only [anchor_count24,show 4*497=1988 by norm_num] using hfringe

theorem actual_deleted_long_core_restore (r N c L R : ℕ) (F : Finset (Finset ℤ))
    (hr : 2≤r) (hN : (r+1)^2≤N)
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hfringe : 4*AnchorCount r*(L+N-R)≤N) (hlegal : Legal (Ground N) F)
    (hne : (StarCompletion.Avoiders (DenseDeletion40.Retained N r F) (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders (DenseDeletion40.Retained N r F) (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  exact actual_long_core_restore_paid r N c L R F (DenseDeletion40.Retained N r F)
    (DenseDeletion40.Deleted N r F) hr hN hc hcL hLR hRN hthin hfringe rfl
    (DenseDeletion40.actual_deleted_subset N r F) hlegal
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2) hne hi

theorem actual_deleted_long_core_restore18 (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hN : 361≤N) (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hthin : 6*(L+N-R)*(Nat.log 2 N+1)≤N) (hfringe : 1112*(L+N-R)≤N)
    (hlegal : Legal (Ground N) F)
    (hne : (StarCompletion.Avoiders (DenseDeletion40.Retained N 18 F) (c:ℤ)).Nonempty)
    (hi : ∀ S∈StarCompletion.Avoiders (DenseDeletion40.Retained N 18 F) (c:ℤ), ∃ a b : ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=LongTerminal35.Interval (a,b)) : F.card≤B N := by
  apply actual_deleted_long_core_restore 18 N c L R F (by decide) (by norm_num; exact hN)
    hc hcL hLR hRN hthin ?_ hlegal hne hi
  simpa only [anchor_count18,show 4*278=1112 by norm_num] using hfringe

#print axioms anchor_keys_card
#print axioms anchor_count18
#print axioms anchor_count24
#print axioms anchor_count_geometry_payment
#print axioms trace_count_lower
#print axioms dense_trace_geometry
#print axioms grid_anchor_cover
#print axioms actual_trace_anchor
#print axioms actual_anchor_class_card
#print axioms actual_dense_fringe_bound
#print axioms actual_dense_fringe_bound_of_length
#print axioms fringe_quarter_payment
#print axioms actual_deleted_fringe_quarter
#print axioms actual_long_core_restore
#print axioms actual_long_core_restore_paid
#print axioms actual_long_core_restore18
#print axioms actual_long_core_restore24
#print axioms actual_deleted_long_core_restore
#print axioms actual_deleted_long_core_restore18

end
end JSP233.ThinFringe42
