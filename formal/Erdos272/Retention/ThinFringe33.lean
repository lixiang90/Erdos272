import Erdos272.Resources.StarBoundConcrete30
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals

/-! Actual adjacent trace classes and exterior private points. -/
namespace JSP233.ThinFringe33
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section

theorem isAP_predicate_iff (S : Finset ℤ) :
    PrivateUnion.IsAP (fun x => x∈S) ↔ IsAP S := by
  rw [isAP_iff_exists_APAt]
  rfl

theorem adjacent_trace_gap {S : Finset ℤ} {L R d u : ℤ}
    (htrace : APAt d u (S∩Finset.Icc L R))
    (hu : u∈S∩Finset.Icc L R) (hv : u+d∈S∩Finset.Icc L R) :
    ∀ x, u<x → x<u+d → x∉S := by
  intro x hux hxu hx
  have huK := Finset.mem_Icc.mp (Finset.mem_inter.mp hu).2
  have hvK := Finset.mem_Icc.mp (Finset.mem_inter.mp hv).2
  have hxK : x∈Finset.Icc L R := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hdvd := apAt_dvd_sub htrace hu (Finset.mem_inter.mpr ⟨hx,hxK⟩)
  have hh := Int.le_of_dvd (by omega : 0<x-u) hdvd
  omega

theorem actual_pair_same_step {C : Finset (Finset ℤ)} {L R d u : ℤ}
    (hpair : ∀ S∈C, ∀ T∈C, S≠T → IsAP (S∩T))
    (htrace : ∀ S∈C, APAt d u (S∩Finset.Icc L R))
    (hu : ∀ S∈C, u∈S∩Finset.Icc L R)
    (hv : ∀ S∈C, u+d∈S∩Finset.Icc L R)
    {S T : Finset ℤ} (hS : S∈C) (hT : T∈C) (hne : S≠T) :
    APAt d u (S∩T) := by
  have hAP := (isAP_predicate_iff (S∩T)).mpr (hpair S hS T hT hne)
  apply PrivateUnion.IsAP_same_step_of_adjacent d u (fun x => x∈S)
    (fun x => x∈S∩T) (htrace S hS).1 hAP
  · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hu S hS)).1,
      (Finset.mem_inter.mp (hu T hT)).1⟩
  · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hv S hS)).1,
      (Finset.mem_inter.mp (hv T hT)).1⟩
  · intro x hx; exact (Finset.mem_inter.mp hx).1
  · exact adjacent_trace_gap (htrace S hS) (hu S hS) (hv S hS)

theorem actual_class_private_point {C : Finset (Finset ℤ)} {L R d u : ℤ}
    (hbad : ∀ S∈C, ¬IsAP S)
    (hpair : ∀ S∈C, ∀ T∈C, S≠T → IsAP (S∩T))
    (htrace : ∀ S∈C, APAt d u (S∩Finset.Icc L R))
    (hu : ∀ S∈C, u∈S∩Finset.Icc L R)
    (hv : ∀ S∈C, u+d∈S∩Finset.Icc L R)
    {S : Finset ℤ} (hS : S∈C) :
    ∃ x, x∈S ∧ x∉Finset.Icc L R ∧ ∀ T∈C, T≠S → x∉T := by
  let others : List (ℤ→Prop) := (C.erase S).toList.map (fun T x => x∈T)
  have hp := Finset.mem_inter.mp (hu S hS)
  have hcore : PrivateUnion.APAt d u (fun x => x∈S ∧ x∈Finset.Icc L R) := by
    simpa only [APAt,Finset.mem_inter] using htrace S hS
  have htraces : ∀ T∈others,
      PrivateUnion.APAt d u (fun x => x∈S ∧ T x) ∧ T u := by
    intro T hT
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp hT
    have hUe := Finset.mem_toList.mp hU
    obtain ⟨hUS,hUC⟩ := Finset.mem_erase.mp hUe
    refine ⟨?_,(Finset.mem_inter.mp (hu U hUC)).1⟩
    simpa only [APAt,Finset.mem_inter] using
      actual_pair_same_step hpair htrace hu hv hS hUC hUS.symm
  obtain ⟨x,hx,hxK,hprivate⟩ := PrivateUnion.private_outside_core d u
    (fun x => x∈S) (fun x => x∈Finset.Icc L R) others
    (fun h => hbad S hS ((isAP_predicate_iff S).mp h)) hp hcore htraces
  refine ⟨x,hx,hxK,?_⟩
  intro T hT hTS
  exact hprivate (fun x => x∈T) (List.mem_map.mpr
    ⟨T,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hTS,hT⟩),rfl⟩)

theorem actual_class_card_le_exterior {Ω : Finset ℤ} {C : Finset (Finset ℤ)}
    {L R d u : ℤ} (hground : ∀ S∈C, S⊆Ω)
    (hbad : ∀ S∈C, ¬IsAP S)
    (hpair : ∀ S∈C, ∀ T∈C, S≠T → IsAP (S∩T))
    (htrace : ∀ S∈C, APAt d u (S∩Finset.Icc L R))
    (hu : ∀ S∈C, u∈S∩Finset.Icc L R)
    (hv : ∀ S∈C, u+d∈S∩Finset.Icc L R) :
    C.card≤(Ω\Finset.Icc L R).card := by
  have hex : ∀ S∈C, ∃ x, x∈S ∧ x∉Finset.Icc L R ∧ ∀ T∈C, T≠S → x∉T :=
    fun S hS => actual_class_private_point hbad hpair htrace hu hv hS
  choose f hf using hex
  apply Finset.card_le_card_of_injective (f:=fun S : C =>
    (⟨f S.val S.property,Finset.mem_sdiff.mpr
      ⟨hground S.val S.property (hf S.val S.property).1,(hf S.val S.property).2.1⟩⟩ :
      ↥(Ω\Finset.Icc L R)))
  intro S T heq
  apply Subtype.ext
  by_contra hne
  have hval := congrArg Subtype.val heq
  change f S.val S.property=f T.val T.property at hval
  have htmem : f S.val S.property∈T.val := by
    rw [hval]
    exact (hf T.val T.property).1
  exact (hf S.val S.property).2.2 T.val T.property (fun he => hne he.symm) htmem

def AnchorKeys : Finset (Σ _d : ℕ, ℕ×ℕ) :=
  (Finset.Icc 1 16).sigma (fun d => (Finset.Icc 1 d).product (Finset.range (64/d+1)))

def AnchorPoint (N : ℕ) (k : Σ _d : ℕ, ℕ×ℕ) : ℤ :=
  (k.2.1:ℤ)+(k.2.2:ℤ)*(N/32:ℕ)*(k.1:ℤ)

theorem anchor_keys_card : AnchorKeys.card≤1160 := by
  norm_num [AnchorKeys,Finset.card_sigma,Finset.card_product,
    Finset.sum_Icc_succ_top]

theorem trace_count_lower (N m outside : ℕ)
    (hdense : N<16*(m+outside)) (hthin : 256*(outside+1)≤N) :
    N/32+1<m := by
  have hq : 32*(N/32)≤N := Nat.mul_div_le N 32
  omega

theorem grid_anchor_cover (N a b d m : ℕ) (hN : 64≤N)
    (ha : 1≤a) (hb : b≤N) (hd : 1≤d) (hd16 : d≤16)
    (hspan : b=a+d*(m-1)) (hm : N/32+1<m) :
    ∃ k∈AnchorKeys, k.1=d ∧ a≤(AnchorPoint N k).toNat ∧
      (AnchorPoint N k).toNat+d≤b ∧
      d∣(AnchorPoint N k).toNat-a := by
  let q := N/32
  have hq : 0<q := by dsimp [q]; omega
  have hNq : N≤64*q := by dsimp [q]; omega
  let r := (a-1)%d+1
  let z := (a-1)/d
  let j := z/q+1
  have hr : 1≤r ∧ r≤d := by
    have hh := Nat.mod_lt (a-1) (by omega : 0<d)
    dsimp [r]; omega
  have haz : a=r+d*z := by
    have hh := Nat.mod_add_div (a-1) d
    dsimp [r,z]; omega
  have hj : z<j*q ∧ j*q≤z+q := by
    have hh := Nat.mod_add_div z q
    have hl := Nat.mod_lt z hq
    dsimp [j]
    constructor <;> nlinarith [Nat.zero_le (z%q)]
  let u := r+j*q*d
  have hua : a≤u := by dsimp [u]; nlinarith
  have hub : u+d≤b := by
    have hmm : q+1≤m-1 := by dsimp [q]; omega
    dsimp [u]; nlinarith
  have hjd : j*d≤64 := by dsimp [u] at hub; nlinarith
  have hjrange : j<64/d+1 := by
    have hh := (Nat.le_div_iff_mul_le (by omega : 0<d)).mpr hjd
    omega
  let k : Σ _d : ℕ, ℕ×ℕ := ⟨d,r,j⟩
  have hk : k∈AnchorKeys := by
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,hd16⟩,
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hr,Finset.mem_range.mpr hjrange⟩⟩
  have hpoint : AnchorPoint N k=(u:ℤ) := by
    dsimp [AnchorPoint,k,u,q]
  refine ⟨k,hk,rfl,?_,?_,?_⟩
  · rw [hpoint,Int.toNat_natCast]; exact hua
  · rw [hpoint,Int.toNat_natCast]; exact hub
  · rw [hpoint,Int.toNat_natCast]
    have ht : (j*q-z)+z=j*q := Nat.sub_add_cancel hj.1.le
    have he : u=a+d*(j*q-z) := by dsimp [u]; nlinarith
    exact ⟨j*q-z,by omega⟩

theorem card_le_trace_add_exterior {Ω S K : Finset ℤ} (hS : S⊆Ω) :
    S.card≤(S∩K).card+(Ω\K).card := by
  have hsub : S⊆(S∩K)∪(Ω\K) := by
    intro x hx
    by_cases hxK : x∈K
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx,hxK⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hS hx,hxK⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem apAt_interval_trace {S H : Finset ℤ} {L R : ℤ}
    (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H) :
    ∃ d p, APAt d p (S∩Finset.Icc L R) := by
  obtain ⟨d,p,⟨hd,a,b,hr⟩,hp⟩ := (isAP_iff_exists_APAt _).mp hpair
  refine ⟨d,p,hd,max a L,min b R,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hxS,hxK⟩ := Finset.mem_inter.mp hx
    have hh := (hr x).mp (Finset.mem_inter.mpr ⟨hxS,hKH hxK⟩)
    have hi := Finset.mem_Icc.mp hxK
    exact ⟨by omega,by omega,hh.2.2⟩
  · rintro ⟨hlo,hhi,hdiv⟩
    have hh := (hr x).mpr ⟨by omega,by omega,hdiv⟩
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hh).1,
      Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩

theorem ground_interval_exterior_card (N : ℕ) {L R : ℤ}
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ)) :
    ((Ground N\Finset.Icc L R).card:ℤ)=(N:ℤ)-(R-L+1) := by
  have hsub : Finset.Icc L R⊆Ground N := by
    intro x hx
    rw [StarBoundConcrete30.ground_eq_Icc]
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [ground_card] at hc
  have hcZ : ((Ground N\Finset.Icc L R).card:ℤ)+(Finset.Icc L R).card=N := by
    exact_mod_cast hc
  have hi : ((Finset.Icc L R).card:ℤ)=R-L+1 := by
    have hh := Int.card_Icc_of_le L R (by omega : L≤R+1)
    omega
  omega

theorem dense_trace_geometry (N : ℕ) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hdense : N<16*S.card)
    (hthin : 256*((Ground N\Finset.Icc L R).card+1)≤N) :
    ∃ d p, APAt d p (S∩Finset.Icc L R) ∧ d≤16 ∧
      N/32+1<(S∩Finset.Icc L R).card := by
  let m := (S∩Finset.Icc L R).card
  let o := (Ground N\Finset.Icc L R).card
  have hc := card_le_trace_add_exterior (K:=Finset.Icc L R) hS
  have hm : N/32+1<m := trace_count_lower N m o (by dsimp [m,o]; omega) hthin
  obtain ⟨d,p,hAP⟩ := apAt_interval_trace hpair hKH
  refine ⟨d,p,hAP,?_,hm⟩
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by omega : 0<m)
  let a := (S∩Finset.Icc L R).min' hne
  let b := (S∩Finset.Icc L R).max' hne
  have ha := Finset.mem_Icc.mp (Finset.mem_inter.mp
    (Finset.min'_mem (S∩Finset.Icc L R) hne)).2
  have hb := Finset.mem_Icc.mp (Finset.mem_inter.mp
    (Finset.max'_mem (S∩Finset.Icc L R) hne)).2
  have hspan := apAt_span_eq hAP hne
  have ho := ground_interval_exterior_card N hL hLR hR
  have hbound : d*((m:ℤ)-1)≤(N:ℤ)-(o:ℤ)-1 := by
    dsimp [m,o]
    omega
  have hdenseZ : (N:ℤ)<16*((m:ℤ)+(o:ℤ)) := by
    have hh : N<16*(m+o) := by dsimp [m,o]; omega
    exact_mod_cast hh
  have hthinZ : 256*((o:ℤ)+1)≤(N:ℤ) := by exact_mod_cast hthin
  have hmZ : (2:ℤ)≤m := by omega
  by_contra hn
  have h17 : 17≤d := by omega
  have hh : 17*((m:ℤ)-1)≤d*((m:ℤ)-1) := by nlinarith
  omega

def HasAnchor (N : ℕ) (L R : ℤ) (k : Σ _d : ℕ, ℕ×ℕ) (S : Finset ℤ) : Prop :=
  APAt (k.1:ℤ) (AnchorPoint N k) (S∩Finset.Icc L R) ∧
    AnchorPoint N k∈S∩Finset.Icc L R ∧
    AnchorPoint N k+(k.1:ℤ)∈S∩Finset.Icc L R

theorem actual_trace_anchor (N : ℕ) {S H : Finset ℤ} {L R : ℤ}
    (hS : S⊆Ground N) (hpair : IsAP (S∩H)) (hKH : Finset.Icc L R⊆H)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hdense : N<16*S.card)
    (hthin : 256*((Ground N\Finset.Icc L R).card+1)≤N) :
    ∃ k∈AnchorKeys, HasAnchor N L R k S := by
  obtain ⟨d,p,hAP,hd16,hm⟩ := dense_trace_geometry N hS hpair hKH hL hLR hR hdense hthin
  have hd := hAP.1
  have hne : (S∩Finset.Icc L R).Nonempty := Finset.card_pos.mp (by omega)
  let a := (S∩Finset.Icc L R).min' hne
  let b := (S∩Finset.Icc L R).max' hne
  have haS : a∈S∩Finset.Icc L R := Finset.min'_mem _ hne
  have hbS : b∈S∩Finset.Icc L R := Finset.max'_mem _ hne
  have haK := Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2
  have hbK := Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2
  have ha : 1≤a := by omega
  have hab : a≤b := Finset.min'_le _ b hbS
  have hN : 64≤N := by omega
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
  obtain ⟨k,hk,hkd,hau,hub,hdiv⟩ := grid_anchor_cover N a.toNat b.toNat d.toNat
    (S∩Finset.Icc L R).card hN (by omega) (by omega) (by omega) (by omega) hspanN hm
  have hu0 : 0≤AnchorPoint N k := by unfold AnchorPoint; positivity
  have huCast : ((AnchorPoint N k).toNat:ℤ)=AnchorPoint N k := Int.toNat_of_nonneg hu0
  have hkdZ : (k.1:ℤ)=d := by rw [hkd,hdCast]
  have hauZ : a≤AnchorPoint N k := by omega
  have hubZ : AnchorPoint N k+d≤b := by omega
  have hdivZ : d∣AnchorPoint N k-a := by
    have hh : (d.toNat:ℤ)∣(((AnchorPoint N k).toNat-a.toNat:ℕ):ℤ) := by exact_mod_cast hdiv
    rw [Nat.cast_sub hau,huCast,haCast,hdCast] at hh
    exact hh
  have huS : AnchorPoint N k∈S∩Finset.Icc L R :=
    apAt_fill hAP haS hbS hauZ (by omega) hdivZ
  have hvS : AnchorPoint N k+d∈S∩Finset.Icc L R :=
    apAt_fill hAP haS hbS (by omega) hubZ (by
      have hh := Int.dvd_add hdivZ (dvd_refl d)
      convert hh using 1
      ring)
  refine ⟨k,hk,?_,huS,?_⟩
  · rw [hkdZ]
    exact apAt_rebase hAP huS
  · simpa only [hkdZ] using hvS

theorem actual_anchor_class_card (N : ℕ) (F E : Finset (Finset ℤ)) (L R : ℤ)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (k : Σ _d : ℕ, ℕ×ℕ) :
    (E.filter (HasAnchor N L R k)).card≤(Ground N\Finset.Icc L R).card := by
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

theorem actual_dense_fringe_bound (N : ℕ) (F E : Finset (Finset ℤ))
    (L R : ℤ) (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F, IsAP H ∧ Finset.Icc L R⊆H)
    (hthin : 256*((Ground N\Finset.Icc L R).card+1)≤N) :
    E.card≤1160*(Ground N\Finset.Icc L R).card := by
  obtain ⟨H,hHF,hHAP,hKH⟩ := hcore
  have hcover : ∀ S∈E, ∃ k∈AnchorKeys, HasAnchor N L R k S := by
    intro S hS
    have hne : S≠H := by intro he; exact hbad S hS (he ▸ hHAP)
    exact actual_trace_anchor N (hlegal.1 S (hEF hS))
      (hlegal.2 S (hEF hS) H hHF hne) hKH hL hLR hR (hdense S hS) hthin
  let C := fun k => E.filter (HasAnchor N L R k)
  have hsub : E⊆AnchorKeys.biUnion C := by
    intro S hS
    obtain ⟨k,hk,hanchor⟩ := hcover S hS
    exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_filter.mpr ⟨hS,hanchor⟩⟩
  calc
    E.card≤(AnchorKeys.biUnion C).card := Finset.card_le_card hsub
    _≤∑ k∈AnchorKeys, (C k).card := Finset.card_biUnion_le
    _≤∑ _k∈AnchorKeys, (Ground N\Finset.Icc L R).card := by
      apply Finset.sum_le_sum
      intro k hk
      exact actual_anchor_class_card N F E L R hlegal hEF hbad k
    _=AnchorKeys.card*(Ground N\Finset.Icc L R).card := by simp
    _≤1160*(Ground N\Finset.Icc L R).card := Nat.mul_le_mul_right _ anchor_keys_card

theorem actual_dense_fringe_bound_of_length (N t : ℕ) (F E : Finset (Finset ℤ))
    (L R : ℤ) (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, N<16*S.card)
    (hL : 1≤L) (hLR : L≤R) (hR : R≤(N:ℤ))
    (hcore : ∃ H∈F, IsAP H ∧ Finset.Icc L R⊆H)
    (ht : (t:ℤ)=L+(N:ℤ)-R) (hthin : 256*t≤N) :
    E.card≤1160*(t-1) := by
  have ho := ground_interval_exterior_card N hL hLR hR
  have he : (Ground N\Finset.Icc L R).card+1=t := by omega
  have hh := actual_dense_fringe_bound N F E L R hlegal hEF hbad hdense hL hLR hR hcore
    (by omega : 256*((Ground N\Finset.Icc L R).card+1)≤N)
  have he' : (Ground N\Finset.Icc L R).card=t-1 := by omega
  simpa only [he'] using hh

theorem fringe_quarter_payment (N t J : ℕ) (hN : 1≤N) (hJ : 19≤J)
    (hthin : 256*t*J≤N) : 1160*(t-1)≤(N-1)/4 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
  have hp := Nat.mul_le_mul_left (256*t) hJ
  have ht : 4864*t≤N := by nlinarith
  by_cases hzero : t=0
  · simp [hzero]
  · omega

#print axioms isAP_predicate_iff
#print axioms adjacent_trace_gap
#print axioms actual_pair_same_step
#print axioms actual_class_private_point
#print axioms actual_class_card_le_exterior
#print axioms anchor_keys_card
#print axioms trace_count_lower
#print axioms grid_anchor_cover
#print axioms card_le_trace_add_exterior
#print axioms apAt_interval_trace
#print axioms ground_interval_exterior_card
#print axioms dense_trace_geometry
#print axioms actual_trace_anchor
#print axioms actual_anchor_class_card
#print axioms actual_dense_fringe_bound
#print axioms actual_dense_fringe_bound_of_length
#print axioms fringe_quarter_payment
end
end JSP233.ThinFringe33
