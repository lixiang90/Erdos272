import Erdos272.Core.CoreAP34
import Mathlib.Data.Finset.Sigma

/-! Actual maximal AP cores, long overlaps, and private remainders.
The original family's AP intersections are used, rather than an abstract
cardinality budget for a size band. -/
namespace JSP233.NearAP36
open StarCompletion APGeometry AffineLine30
open scoped Classical BigOperators
noncomputable section

def Grid (a d k : ℕ) : Finset ℤ :=
  (Finset.range k).image (fun i:ℕ => (a:ℤ)+(i:ℤ)*(d:ℤ))

def MaximalAPCore (S P : Finset ℤ) : Prop :=
  P⊆S ∧ IsAP P ∧ ∀ U : Finset ℤ, P⊆U → U⊆S → IsAP U → U=P

theorem mem_grid (a d k : ℕ) (x : ℤ) :
    x∈Grid a d k ↔ ∃ i:ℕ, i<k ∧ x=(a:ℤ)+(i:ℤ)*(d:ℤ) := by
  simp only [Grid,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨i,hi,he⟩; exact ⟨i,hi,he.symm⟩
  · rintro ⟨i,hi,he⟩; exact ⟨i,hi,he.symm⟩

theorem grid_card (a d k : ℕ) (hd : 0<d) : (Grid a d k).card=k := by
  have hinj : Function.Injective (fun i:ℕ => (a:ℤ)+(i:ℤ)*(d:ℤ)) := by
    intro i j he
    have hdZ : (0:ℤ)<d := by exact_mod_cast hd
    have hh : (i:ℤ)=j := by nlinarith
    exact_mod_cast hh
  rw [Grid,Finset.card_image_of_injective _ hinj,Finset.card_range]

theorem grid_APAt (a d k : ℕ) (hd : 0<d) : APAt (d:ℤ) (a:ℤ) (Grid a d k) := by
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  refine ⟨hdZ,a,(a:ℤ)+((k:ℤ)-1)*(d:ℤ),?_⟩
  intro x
  change x∈Grid a d k ↔ _
  rw [mem_grid]
  constructor
  · rintro ⟨i,hi,rfl⟩
    refine ⟨?_,?_,?_⟩
    · have hh : (0:ℤ)≤(i:ℤ)*(d:ℤ) := by positivity
      omega
    · have h : (i:ℤ)≤(k:ℤ)-1 := by omega
      nlinarith
    · exact ⟨i,by ring⟩
  · rintro ⟨hax,hxk,q,hq⟩
    have hq0 : 0≤q := by nlinarith
    have hqk : q<(k:ℤ) := by nlinarith
    refine ⟨q.toNat,by omega,?_⟩
    have hqt : (q.toNat:ℤ)=q := Int.toNat_of_nonneg hq0
    rw [hqt]
    nlinarith

theorem grid_isAP (a d k : ℕ) (hd : 0<d) (hk : 0<k) : IsAP (Grid a d k) := by
  exact (isAP_iff_exists_APAt _).mpr ⟨d,a,grid_APAt a d k hd,
    (mem_grid _ _ _ _).mpr ⟨0,hk,by simp⟩⟩

theorem grid_member_ge_start {a d k : ℕ} {x : ℤ} (hx : x∈Grid a d k) : (a:ℤ)≤x := by
  obtain ⟨i,_,rfl⟩ := (mem_grid _ _ _ _).mp hx
  have hh : (0:ℤ)≤(i:ℤ)*(d:ℤ) := by positivity
  omega

theorem long_overlap_AP_subset_maximal {S P Q : Finset ℤ} {a b d k K : ℕ}
    (hd : 0<d) (hP : P=Grid b d k) (hPS : P⊆S) (hQS : Q⊆S) (hQ : IsAP Q)
    (hlong : Grid a d (K+1)⊆P∩Q) (hsmall : (S\P).card<K)
    (hmax : ∀ U : Finset ℤ, P⊆U → U⊆S → IsAP U → U=P) : Q⊆P := by
  have hK : 0<K := by omega
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have ha : (a:ℤ)∈P∩Q := hlong ((mem_grid _ _ _ _).mpr ⟨0,by omega,by simp⟩)
  have hav : (a:ℤ)+(d:ℤ)∈P∩Q := hlong ((mem_grid _ _ _ _).mpr ⟨1,by omega,by simp⟩)
  have hal : (a:ℤ)+(K:ℤ)*(d:ℤ)∈P∩Q := hlong ((mem_grid _ _ _ _).mpr ⟨K,by omega,rfl⟩)
  have haP := (Finset.mem_inter.mp ha).1
  have haQ := (Finset.mem_inter.mp ha).2
  have havQ := (Finset.mem_inter.mp hav).2
  have halQ := (Finset.mem_inter.mp hal).2
  obtain ⟨e,p,hQAt,_⟩ := (isAP_iff_exists_APAt _).mp hQ
  have he := hQAt.1
  have hed : e∣(d:ℤ) := by
    have hh := apAt_dvd_sub hQAt haQ havQ
    convert hh using 1; ring
  have hedle : e≤d := Int.le_of_dvd hdZ hed
  have hPAt : APAt (d:ℤ) (b:ℤ) P := by rw [hP]; exact grid_APAt b d k hd
  have heq : e=(d:ℤ) := by
    by_contra hne
    have hlt : e<(d:ℤ) := by omega
    let f : ℕ→ℤ := fun i => (a:ℤ)+(i:ℤ)*(d:ℤ)+e
    have hmaps : Set.MapsTo f (Finset.range K:Set ℕ) ((S\P:Finset ℤ):Set ℤ) := by
      intro i hi
      have hiK := Finset.mem_range.mp hi
      have hyQ : f i∈Q := by
        apply apAt_fill hQAt haQ halQ
        · dsimp [f]
          have hh : (0:ℤ)≤(i:ℤ)*(d:ℤ) := by positivity
          linarith
        · dsimp [f]
          have hiZ : (i:ℤ)+1≤K := by exact_mod_cast (show i+1≤K by omega)
          nlinarith
        · change e∣(a:ℤ)+(i:ℤ)*(d:ℤ)+e-(a:ℤ)
          rw [show (a:ℤ)+(i:ℤ)*(d:ℤ)+e-(a:ℤ)=(i:ℤ)*(d:ℤ)+e by ring]
          exact dvd_add (dvd_mul_of_dvd_right hed (i:ℤ)) (dvd_refl e)
      apply Finset.mem_sdiff.mpr
      refine ⟨hQS hyQ,?_⟩
      intro hyP
      have hdiv := apAt_dvd_sub hPAt haP hyP
      have hdiv' : (d:ℤ)∣(i:ℤ)*(d:ℤ)+e := by
        have he' : f i-(a:ℤ)=(i:ℤ)*(d:ℤ)+e := by dsimp [f]; ring
        rw [he'] at hdiv
        exact hdiv
      have hediv : (d:ℤ)∣e := by
        have hh := dvd_sub hdiv' (dvd_mul_left (d:ℤ) (i:ℤ))
        simpa only [add_sub_cancel_left] using hh
      have hh := Int.le_of_dvd he hediv
      omega
    have hinj : Function.Injective f := by
      intro i j hh
      dsimp [f] at hh
      have heij : (i:ℤ)=j := by nlinarith
      exact_mod_cast heij
    have hcount := Finset.card_le_card_of_injOn f hmaps hinj.injOn
    rw [Finset.card_range] at hcount
    omega
  have hQd : APAt (d:ℤ) (a:ℤ) Q := by
    have hh := apAt_rebase hQAt haQ
    rw [heq] at hh
    exact hh
  have hPd := apAt_rebase hPAt haP
  have hu : APAt (d:ℤ) (a:ℤ) (P∪Q) := by
    have hh := PrivateUnion.union_APAt (d:ℤ) (a:ℤ) (fun x => x∈P) (fun x => x∈Q)
      hPd hQd haP haQ
    simpa only [APAt,Finset.mem_union] using hh
  have hAPu : IsAP (P∪Q) := (isAP_iff_exists_APAt _).mpr
    ⟨d,a,hu,Finset.mem_union_left _ haP⟩
  have hU := hmax (P∪Q) Finset.subset_union_left (Finset.union_subset hPS hQS) hAPu
  exact hU ▸ Finset.subset_union_right

theorem actual_remainder_private_of_long_overlap {N a b d k K : ℕ}
    {F : Finset (Finset ℤ)} {S T P : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hS : S∈F) (hT : T∈F) (hne : S≠T)
    (hd : 0<d) (hP : P=Grid b d k) (hPS : P⊆S)
    (hprefixP : Grid a d (K+1)⊆P) (hprefixT : Grid a d (K+1)⊆T)
    (hsmall : (S\P).card<K)
    (hmax : ∀ U : Finset ℤ, P⊆U → U⊆S → IsAP U → U=P) : Disjoint (S\P) T := by
  have hh := long_overlap_AP_subset_maximal hd hP hPS Finset.inter_subset_left
    (hlegal.2 S hS T hT hne)
    (fun x hx => Finset.mem_inter.mpr ⟨hprefixP hx,Finset.mem_inter.mpr ⟨hPS (hprefixP hx),hprefixT hx⟩⟩)
    hsmall hmax
  exact Finset.disjoint_left.mpr (fun x hxS hxT =>
    (Finset.mem_sdiff.mp hxS).2 (hh (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hxS).1,hxT⟩)))

theorem actual_common_prefix_remainders_disjoint {N a d K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hd : 0<d) (core : Finset ℤ→Finset ℤ)
    (hform : ∀ S∈F, ∃ b k, core S=Grid b d k) (hsub : ∀ S∈F, core S⊆S)
    (hprefix : ∀ S∈F, Grid a d (K+1)⊆core S)
    (hsmall : ∀ S∈F, (S\core S).card<K)
    (hmax : ∀ S∈F, ∀ U : Finset ℤ, core S⊆U → U⊆S → IsAP U → U=core S) :
    ∀ S∈F, ∀ T∈F, S≠T → Disjoint (S\core S) (T\core T) := by
  intro S hS T hT hne
  obtain ⟨b,k,hP⟩ := hform S hS
  have hh := actual_remainder_private_of_long_overlap hlegal hS hT hne hd hP (hsub S hS)
    (hprefix S hS) ((hprefix T hT).trans (hsub T hT)) (hsmall S hS) (hmax S hS)
  exact Finset.disjoint_left.mpr (fun x hx hy =>
    Finset.disjoint_left.mp hh hx (Finset.mem_sdiff.mp hy).1)

theorem crooked_disjoint_remainders_card {N : ℕ} {F : Finset (Finset ℤ)}
    (hground : ∀ S∈F, S⊆Ground N) (core : Finset ℤ→Finset ℤ)
    (hbad : ∀ S∈F, ¬IsAP S) (hAP : ∀ S∈F, IsAP (core S))
    (hsub : ∀ S∈F, core S⊆S)
    (hdis : ∀ S∈F, ∀ T∈F, S≠T → Disjoint (S\core S) (T\core T)) : F.card≤N := by
  have hex : ∀ S:F, ∃ x:ℤ, x∈S.val\core S.val := by
    intro S
    have hn : (S.val\core S.val).Nonempty := by
      by_contra he
      have hSC : S.val⊆core S.val := by
        intro x hx
        by_contra hxC
        exact he ⟨x,Finset.mem_sdiff.mpr ⟨hx,hxC⟩⟩
      exact hbad S.val S.property ((Finset.Subset.antisymm hSC (hsub S.val S.property)).symm ▸ hAP S.val S.property)
    exact hn
  choose x hx using hex
  let f : F→Ground N := fun S => ⟨x S,hground S.val S.property (Finset.mem_sdiff.mp (hx S)).1⟩
  have hf : Function.Injective f := by
    intro S T he
    apply Subtype.ext
    by_contra hne
    have hval : x S=x T := congrArg Subtype.val he
    have hh := hdis S.val S.property T.val T.property hne
    exact Finset.disjoint_left.mp hh (hx S) (hval.symm ▸ hx T)
  have hc := Finset.card_le_card_of_injective hf
  simpa only [ground_card] using hc

theorem disjoint_pieces_hit_card {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (piece : ι→Finset ℤ) (U : Finset ℤ)
    (hdis : ∀ i∈I, ∀ j∈I, i≠j → Disjoint (piece i) (piece j))
    (hhit : ∀ i∈I, (piece i∩U).Nonempty) : I.card≤U.card := by
  choose x hx using (fun i:I => hhit i.val i.property)
  let f : I→U := fun i => ⟨x i,(Finset.mem_inter.mp (hx i)).2⟩
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    have hval : x i=x j := congrArg Subtype.val he
    exact Finset.disjoint_left.mp (hdis i.val i.property j.val j.property hne)
      (Finset.mem_inter.mp (hx i)).1 (hval.symm ▸ (Finset.mem_inter.mp (hx j)).1)
  exact Finset.card_le_card_of_injective hf

theorem exists_disjoint_piece {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (piece : ι→Finset ℤ) (U : Finset ℤ)
    (hdis : ∀ i∈I, ∀ j∈I, i≠j → Disjoint (piece i) (piece j))
    (hcard : U.card<I.card) : ∃ i∈I, Disjoint (piece i) U := by
  by_contra hn
  have hhit : ∀ i∈I, (piece i∩U).Nonempty := by
    intro i hi
    by_contra he
    apply hn
    refine ⟨i,hi,Finset.disjoint_left.mpr ?_⟩
    intro x hx hU
    exact he ⟨x,Finset.mem_inter.mpr ⟨hx,hU⟩⟩
  have hh := disjoint_pieces_hit_card I piece U hdis hhit
  omega

theorem heavy_core_pools_intersect {F G : Finset (Finset ℤ)} {U V : Finset ℤ}
    {s : ℕ} (core : Finset ℤ→Finset ℤ)
    (hFU : ∀ S∈F, core S⊆U) (hGV : ∀ T∈G, core T⊆V)
    (hFD : ∀ S∈F, ∀ T∈F, S≠T → Disjoint (S\core S) (T\core T))
    (hGD : ∀ S∈G, ∀ T∈G, S≠T → Disjoint (S\core S) (T\core T))
    (hcross : ∀ S∈F, ∀ T∈G, (S∩T).Nonempty)
    (hsmall : ∀ T∈G, T.card≤s) (hFL : s<F.card) (hGL : U.card<G.card) :
    (U∩V).Nonempty := by
  by_contra he
  have hUV : Disjoint U V := Finset.disjoint_left.mpr
    (fun x hx hy => he ⟨x,Finset.mem_inter.mpr ⟨hx,hy⟩⟩)
  obtain ⟨T,hT,hTU⟩ := exists_disjoint_piece G (fun T=>T\core T) U hGD hGL
  have hTfull : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxU
    by_cases hxC : x∈core T
    · exact Finset.disjoint_left.mp hUV hxU (hGV T hT hxC)
    · exact Finset.disjoint_left.mp hTU (Finset.mem_sdiff.mpr ⟨hxT,hxC⟩) hxU
  have hhit : ∀ S∈F, ((S\core S)∩T).Nonempty := by
    intro S hS
    obtain ⟨x,hx⟩ := hcross S hS T hT
    obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
    exact ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS,
      fun hxC=>Finset.disjoint_left.mp hTfull hxT (hFU S hS hxC)⟩,hxT⟩⟩
  have hh := (disjoint_pieces_hit_card F (fun S=>S\core S) T hFD hhit).trans (hsmall T hT)
  omega

def StartCode (d K a : ℕ) : ℕ×ℕ := (a%d,(a/d)/K)
def CoreWindow (d K : ℕ) (q : ℕ×ℕ) : Finset ℤ := Grid (q.1+q.2*K*d) d (65*K)
def WindowPrefix (d K : ℕ) (q : ℕ×ℕ) : Finset ℤ := Grid (q.1+(q.2+1)*K*d) d (K+1)
def StartPool (N d K : ℕ) : Finset (ℕ×ℕ) :=
  Finset.range d×ˢFinset.range (N/(K*d)+1)

theorem start_decomposition {d K a : ℕ} (hK : 0<K) :
    ∃ j<K, a=(StartCode d K a).1+((StartCode d K a).2*K+j)*d := by
  refine ⟨(a/d)%K,Nat.mod_lt _ hK,?_⟩
  have h1 := Nat.mod_add_div a d
  have h2 := Nat.mod_add_div (a/d) K
  dsimp [StartCode]
  nlinarith only [h1,congrArg (fun n=>n*d) h2]

theorem grid_subset_window {a d k K : ℕ} (hK : 0<K) (hk : k≤64*K) :
    Grid a d k⊆CoreWindow d K (StartCode d K a) := by
  obtain ⟨j,hj,ha⟩ := start_decomposition (a:=a) (d:=d) hK
  intro x hx
  obtain ⟨i,hi,hx⟩ := (mem_grid _ _ _ _).mp hx
  apply (mem_grid _ _ _ _).mpr
  refine ⟨j+i,by omega,?_⟩
  have haZ : (a:ℤ)=(StartCode d K a).1+((StartCode d K a).2*(K:ℤ)+j)*d := by exact_mod_cast ha
  push_cast
  nlinarith only [hx,haZ]

theorem window_prefix_subset_grid {a d k K : ℕ} (hK : 0<K) (hk : 2*K+1≤k) :
    WindowPrefix d K (StartCode d K a)⊆Grid a d k := by
  obtain ⟨j,hj,ha⟩ := start_decomposition (a:=a) (d:=d) hK
  intro x hx
  obtain ⟨i,hi,hx⟩ := (mem_grid _ _ _ _).mp hx
  apply (mem_grid _ _ _ _).mpr
  refine ⟨K-j+i,by omega,?_⟩
  have hsum : K-j+j=K := by omega
  have haZ : (a:ℤ)=(StartCode d K a).1+((StartCode d K a).2*(K:ℤ)+j)*d := by exact_mod_cast ha
  have hsumZ : ((K-j:ℕ):ℤ)+j=K := by exact_mod_cast hsum
  dsimp [WindowPrefix] at hx
  push_cast at hx ⊢
  nlinarith only [hx,haZ,hsumZ]

theorem window_card {d K : ℕ} (hd : 0<d) (q : ℕ×ℕ) : (CoreWindow d K q).card=65*K :=
  grid_card _ _ _ hd

theorem window_intersection_code_bounds {d K : ℕ} {q r : ℕ×ℕ}
    (hd : 0<d) (hK : 0<K) (hq : q.1<d) (hr : r.1<d)
    (hinter : (CoreWindow d K q∩CoreWindow d K r).Nonempty) :
    q.1=r.1 ∧ q.2≤r.2+65 ∧ r.2≤q.2+65 := by
  obtain ⟨x,hx⟩ := hinter
  obtain ⟨hxq,hxr⟩ := Finset.mem_inter.mp hx
  obtain ⟨i,hi,hix⟩ := (mem_grid _ _ _ _).mp hxq
  obtain ⟨j,hj,hjx⟩ := (mem_grid _ _ _ _).mp hxr
  have he : q.1+q.2*K*d+i*d=r.1+r.2*K*d+j*d := by
    have heZ : ((q.1+q.2*K*d+i*d:ℕ):ℤ)=(r.1+r.2*K*d+j*d:ℕ) := by
      push_cast
      exact hix.symm.trans hjx
    exact_mod_cast heZ
  have hres : q.1=r.1 := by
    have hh := congrArg (fun n=>n%d) he
    simpa only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hq,Nat.mod_eq_of_lt hr] using hh
  have hiq : q.2*K+i=r.2*K+j := by rw [hres] at he; nlinarith
  refine ⟨hres,?_,?_⟩
  · by_contra hn
    have hh : (r.2+66)*K≤q.2*K := Nat.mul_le_mul_right K (by omega)
    nlinarith
  · by_contra hn
    have hh : (q.2+66)*K≤r.2*K := Nat.mul_le_mul_right K (by omega)
    nlinarith

theorem start_code_mem_pool {N d K a : ℕ} (hd : 0<d) (_hK : 0<K) (ha : a≤N) :
    StartCode d K a∈StartPool N d K := by
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd),Finset.mem_range.mpr ?_⟩
  change (a/d)/K<N/(K*d)+1
  rw [Nat.div_div_eq_div_mul]
  simpa only [Nat.mul_comm d K] using Nat.lt_succ_of_le (Nat.div_le_div_right ha)

theorem start_pool_card_mul {N d K : ℕ} (_hd : 0<d) (_hK : 0<K) (hdN : d*K≤N) :
    (StartPool N d K).card*K≤2*N := by
  have hh := Nat.div_mul_le_self N (K*d)
  simp only [StartPool,Finset.card_product,Finset.card_range]
  nlinarith only [hh,hdN]

theorem window_class_card_sum {N d K : ℕ} {B : Finset (ℕ×ℕ)}
    (hd : 0<d) (hK : 0<K) (hdN : d*K≤N) (hB : B⊆StartPool N d K)
    (family : (ℕ×ℕ)→Finset (Finset ℤ)) (core : Finset ℤ→Finset ℤ)
    (hcore : ∀ q∈B, ∀ S∈family q, core S⊆CoreWindow d K q)
    (hdis : ∀ q∈B, ∀ S∈family q, ∀ T∈family q,
      S≠T → Disjoint (S\core S) (T\core T))
    (hcross : ∀ q∈B, ∀ r∈B, ∀ S∈family q, ∀ T∈family r, (S∩T).Nonempty)
    (hsmall : ∀ q∈B, ∀ S∈family q, S.card≤64*K)
    (hlinear : ∀ q∈B, (family q).card≤N) : (∑ q∈B, (family q).card)≤261*N := by
  let H := B.filter (fun q=>65*K<(family q).card)
  have hHB : H⊆B := Finset.filter_subset _ _
  have hHcard : H.card≤131 := by
    rcases H.eq_empty_or_nonempty with he|hne
    · simp [he]
    obtain ⟨q0,hq0⟩ := hne
    have hq0B := hHB hq0
    have hq0large := (Finset.mem_filter.mp hq0).2
    have hb : ∀ q∈H, q.1=q0.1 ∧ q.2≤q0.2+65 ∧ q0.2≤q.2+65 := by
      intro q hq
      have hqB := hHB hq
      have hqlarge := (Finset.mem_filter.mp hq).2
      have hinter := heavy_core_pools_intersect core (hcore q hqB) (hcore q0 hq0B)
        (hdis q hqB) (hdis q0 hq0B) (hcross q hqB q0 hq0B) (hsmall q0 hq0B)
        (by omega : 64*K<(family q).card)
        (by simpa only [window_card hd] using hq0large)
      exact window_intersection_code_bounds hd hK
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hqB)).1)
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hq0B)).1) hinter
    have hm : Set.MapsTo Prod.snd (H:Set (ℕ×ℕ))
        (Finset.Icc (q0.2-65) (q0.2+65):Set ℕ) := by
      intro q hq
      have hh := hb q hq
      exact Finset.mem_Icc.mpr ⟨by omega,hh.2.1⟩
    have hi : Set.InjOn Prod.snd (H:Set (ℕ×ℕ)) := by
      intro q hq r hr he
      exact Prod.ext ((hb q hq).1.trans (hb r hr).1.symm) he
    have hc := Finset.card_le_card_of_injOn Prod.snd hm hi
    rw [Nat.card_Icc] at hc
    omega
  have hlight : (∑ q∈B\H, (family q).card)≤B.card*(65*K) := by
    have hp : ∀ q∈B\H, (family q).card≤65*K := by
      intro q hq
      obtain ⟨hqB,hqH⟩ := Finset.mem_sdiff.mp hq
      have hh : ¬65*K<(family q).card := fun hn=>hqH (Finset.mem_filter.mpr ⟨hqB,hn⟩)
      omega
    have hs := Finset.sum_le_sum hp
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset))
  have hheavy : (∑ q∈H, (family q).card)≤131*N := by
    have hs := Finset.sum_le_sum (fun q hq=>hlinear q (hHB hq))
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right N hHcard)
  have hpart := Finset.sum_sdiff hHB (f:=fun q=>(family q).card)
  have hpool := start_pool_card_mul hd hK hdN
  have hbs := (Nat.mul_le_mul_right K (Finset.card_le_card hB)).trans hpool
  have hlight' : (∑ q∈B\H, (family q).card)≤130*N := by
    have hm := Nat.mul_le_mul_left 65 hbs
    nlinarith
  omega

theorem actual_nearAP_same_step_card {N d K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hd : 0<d) (hK : 0<K)
    (start length : Finset ℤ→ℕ) (hbad : ∀ S∈F, ¬IsAP S)
    (hcard : ∀ S∈F, S.card≤64*K)
    (hsub : ∀ S∈F, Grid (start S) d (length S)⊆S)
    (hlow : ∀ S∈F, 2*K+1≤length S) (hhigh : ∀ S∈F, length S≤64*K)
    (hsmall : ∀ S∈F, (S\Grid (start S) d (length S)).card<K)
    (hmax : ∀ S∈F, ∀ U : Finset ℤ, Grid (start S) d (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) d (length S)) : F.card≤261*N := by
  rcases F.eq_empty_or_nonempty with he|hne
  · simp [he]
  let core : Finset ℤ→Finset ℤ := fun S=>Grid (start S) d (length S)
  let code : Finset ℤ→ℕ×ℕ := fun S=>StartCode d K (start S)
  let B := StartPool N d K
  let family : (ℕ×ℕ)→Finset (Finset ℤ) := fun q=>F.filter (fun S=>code S=q)
  have hstartN : ∀ S∈F, start S≤N := by
    intro S hS
    have hs := hlow S hS
    have ha : (start S:ℤ)∈S := hsub S hS ((mem_grid _ _ _ _).mpr ⟨0,by omega,by simp⟩)
    have hh := ((mem_ground N _).mp (hlegal.1 S hS ha)).2
    exact_mod_cast hh
  have hdN : d*K≤N := by
    obtain ⟨S,hS⟩ := hne
    have hs := hlow S hS
    have hx := hsub S hS ((mem_grid _ _ _ _).mpr ⟨K,by omega,rfl⟩)
    have hh := ((mem_ground N _).mp (hlegal.1 S hS hx)).2
    have hhN : start S+K*d≤N := by exact_mod_cast hh
    nlinarith
  have hfamily : ∀ q, family q⊆F := fun q=>Finset.filter_subset _ _
  have hprefix : ∀ q, ∀ S∈family q, WindowPrefix d K q⊆core S := by
    intro q S hS
    have hh := window_prefix_subset_grid (a:=start S) (d:=d) hK (hlow S (hfamily q hS))
    have he := (Finset.mem_filter.mp hS).2
    change code S=q at he
    change WindowPrefix d K (code S)⊆core S at hh
    simpa only [he] using hh
  have hdis : ∀ q, ∀ S∈family q, ∀ T∈family q,
      S≠T → Disjoint (S\core S) (T\core T) := by
    intro q
    have hqlegal : Legal (Ground N) (family q) :=
      ⟨fun S hS=>hlegal.1 S (hfamily q hS),
       fun S hS T hT he=>hlegal.2 S (hfamily q hS) T (hfamily q hT) he⟩
    apply actual_common_prefix_remainders_disjoint (a:=q.1+(q.2+1)*K*d) hqlegal hd core
      (fun S _=>⟨start S,length S,rfl⟩) (fun S hS=>hsub S (hfamily q hS))
      (hprefix q) (fun S hS=>hsmall S (hfamily q hS)) (fun S hS=>hmax S (hfamily q hS))
  have hlinear : ∀ q, (family q).card≤N := by
    intro q
    exact crooked_disjoint_remainders_card (fun S hS=>hlegal.1 S (hfamily q hS)) core
      (fun S hS=>hbad S (hfamily q hS))
      (fun S hS=>grid_isAP _ _ _ hd (by have hh:=hlow S (hfamily q hS); omega))
      (fun S hS=>hsub S (hfamily q hS)) (hdis q)
  have hsum := window_class_card_sum (B:=B) hd hK hdN (Finset.Subset.refl _) family core
    (by
      intro q hq S hS
      have hh := grid_subset_window (a:=start S) (d:=d) hK (hhigh S (hfamily q hS))
      have he := (Finset.mem_filter.mp hS).2
      change code S=q at he
      change core S⊆CoreWindow d K (code S) at hh
      simpa only [he] using hh)
    (fun q _=>hdis q)
    (by
      intro q hq r hr S hS T hT
      by_cases he:S=T
      · have hs : S.Nonempty := Finset.card_pos.mp (by
          have hh := grid_card (start S) d (length S) hd
          have hb := Finset.card_le_card (hsub S (hfamily q hS))
          have hl := hlow S (hfamily q hS)
          omega)
        obtain ⟨x,hx⟩ := hs
        exact ⟨x,Finset.mem_inter.mpr ⟨hx,he ▸ hx⟩⟩
      · exact isAP_nonempty (hlegal.2 S (hfamily q hS) T (hfamily r hT) he))
    (fun q _ S hS=>hcard S (hfamily q hS)) (fun q _=>hlinear q)
  have hmaps : ∀ S∈F, code S∈B := fun S hS=>start_code_mem_pool hd hK (hstartN S hS)
  have hpart : F.card=∑ q∈B, (family q).card := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpart]
  exact hsum

def HasNearAPCore (K : ℕ) (S : Finset ℤ) : Prop :=
  ∃ P : Finset ℤ, MaximalAPCore S P ∧ 2*K+1≤P.card ∧ (S\P).card<K

def NearMembers (K : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.filter (HasNearAPCore K)

theorem actual_AP_grid_representation {N : ℕ} {S : Finset ℤ}
    (hground : S⊆Ground N) (hAP : IsAP S) :
    ∃ a d : ℕ, 0<d ∧ S=Grid a d S.card := by
  obtain ⟨d,p,hAt,hp⟩ := (isAP_iff_exists_APAt _).mp hAP
  have hne : S.Nonempty := ⟨p,hp⟩
  let a := S.min' hne
  have ha : a∈S := Finset.min'_mem S hne
  have ha1 := ((mem_ground N a).mp (hground ha)).1
  have hca : (a.toNat:ℤ)=a := Int.toNat_of_nonneg (by omega)
  have hcd : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hAt.1.le
  have hdp : 0<d.toNat := by have hh:=hAt.1; omega
  refine ⟨a.toNat,d.toNat,hdp,?_⟩
  calc
    S=(Finset.range S.card).image (fun i:ℕ=>a+d*(i:ℤ)) := apAt_eq_range hAt hne
    _=Grid a.toNat d.toNat S.card := by
      unfold Grid
      apply Finset.image_congr
      intro i _
      rw [hca,hcd]
      ring

theorem actual_nearAP_coordinate_selection {N K : ℕ} {F : Finset (Finset ℤ)}
    (hground : ∀ S∈F, S⊆Ground N) (hcard : ∀ S∈F, S.card≤64*K)
    (hnear : ∀ S∈F, HasNearAPCore K S) :
    ∃ start step length : Finset ℤ→ℕ, ∀ S∈F,
      0<step S ∧ Grid (start S) (step S) (length S)⊆S ∧
      2*K+1≤length S ∧ length S≤64*K ∧
      (S\Grid (start S) (step S) (length S)).card<K ∧
      ∀ U : Finset ℤ, Grid (start S) (step S) (length S)⊆U → U⊆S → IsAP U →
        U=Grid (start S) (step S) (length S) := by
  have hex : ∀ S : Finset ℤ, ∃ a d k : ℕ, S∈F →
      0<d ∧ Grid a d k⊆S ∧ 2*K+1≤k ∧ k≤64*K ∧ (S\Grid a d k).card<K ∧
      ∀ U : Finset ℤ, Grid a d k⊆U → U⊆S → IsAP U → U=Grid a d k := by
    intro S
    by_cases hS:S∈F
    · obtain ⟨P,⟨hPS,hPAP,hPM⟩,hPlow,hPsmall⟩ := hnear S hS
      obtain ⟨a,d,hd,hform⟩ := actual_AP_grid_representation (hPS.trans (hground S hS)) hPAP
      have hhigh := (Finset.card_le_card hPS).trans (hcard S hS)
      refine ⟨a,d,P.card,fun _=>⟨hd,?_,hPlow,hhigh,?_,?_⟩⟩
      · rw [←hform]; exact hPS
      · rw [←hform]; exact hPsmall
      · rw [←hform]; exact hPM
    · exact ⟨0,1,0,fun hh=>False.elim (hS hh)⟩
  choose a d k hk using hex
  exact ⟨a,d,k,hk⟩

theorem actual_nearAP_step_budget {N K A : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 0<A)
    (start step length : Finset ℤ→ℕ) (hbad : ∀ S∈F, ¬IsAP S)
    (hcard : ∀ S∈F, S.card≤64*K) (hstep : ∀ S∈F, 0<step S)
    (hsub : ∀ S∈F, Grid (start S) (step S) (length S)⊆S)
    (hlow : ∀ S∈F, 2*K+1≤length S) (hhigh : ∀ S∈F, length S≤64*K)
    (hstrong : ∀ S∈F, A*K+1≤length S)
    (hsmall : ∀ S∈F, (S\Grid (start S) (step S) (length S)).card<K)
    (hmax : ∀ S∈F, ∀ U : Finset ℤ, Grid (start S) (step S) (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) (step S) (length S)) : (A*K)*F.card≤261*N^2 := by
  let family : ℕ→Finset (Finset ℤ) := fun d=>F.filter (fun S=>step S=d)
  have hfamily : ∀ d, family d⊆F := fun d=>Finset.filter_subset _ _
  have hmaps : ∀ S∈F, step S∈Finset.Icc 1 (N/(A*K)) := by
    intro S hS
    have hl := hstrong S hS
    have hx : (start S:ℤ)+(A*K:ℕ)*(step S:ℤ)∈S :=
      hsub S hS ((mem_grid _ _ _ _).mpr ⟨A*K,by omega,rfl⟩)
    have hxN := ((mem_ground N _).mp (hlegal.1 S hS hx)).2
    have hxNN : start S+(A*K)*step S≤N := by exact_mod_cast hxN
    exact Finset.mem_Icc.mpr ⟨hstep S hS,(Nat.le_div_iff_mul_le (by positivity : 0<A*K)).mpr (by nlinarith)⟩
  have hb : ∀ d∈Finset.Icc 1 (N/(A*K)), (family d).card≤261*N := by
    intro d hd
    have hflegal : Legal (Ground N) (family d) :=
      ⟨fun S hS=>hlegal.1 S (hfamily d hS),
       fun S hS T hT he=>hlegal.2 S (hfamily d hS) T (hfamily d hT) he⟩
    apply actual_nearAP_same_step_card hflegal (Finset.mem_Icc.mp hd).1 hK start length
      (fun S hS=>hbad S (hfamily d hS)) (fun S hS=>hcard S (hfamily d hS))
    · intro S hS
      have hh := hsub S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · exact fun S hS=>hlow S (hfamily d hS)
    · exact fun S hS=>hhigh S (hfamily d hS)
    · intro S hS
      have hh := hsmall S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · intro S hS
      have hh := hmax S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
  have hs := Finset.sum_le_sum hb
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel] at hs
  have hpart : F.card=∑ d∈Finset.Icc 1 (N/(A*K)), (family d).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [←hpart] at hs
  have hm := Nat.mul_le_mul_right (A*K) hs
  have hdv := Nat.mul_le_mul_left (261*N) (Nat.div_mul_le_self N (A*K))
  nlinarith

theorem actual_nearAP_band_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 16*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤64*K)
    (hnear : ∀ S∈F, HasNearAPCore K S) : (15*K)*F.card≤261*N^2 := by
  obtain ⟨start,step,length,hcoords⟩ := actual_nearAP_coordinate_selection hlegal.1 hhigh hnear
  have hstep : ∀ S∈F, 0<step S := fun S hS=>(hcoords S hS).1
  have hsub : ∀ S∈F, Grid (start S) (step S) (length S)⊆S := fun S hS=>(hcoords S hS).2.1
  have hstrong : ∀ S∈F, 15*K+1≤length S := by
    intro S hS
    have hc := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    rw [grid_card _ _ _ (hstep S hS)] at hc
    have hsm := (hcoords S hS).2.2.2.2.1
    have hlo := hlow S hS
    omega
  exact actual_nearAP_step_budget hlegal hK (by decide : 0<15) start step length hbad hhigh
    hstep hsub (fun S hS=>(hcoords S hS).2.2.1) (fun S hS=>(hcoords S hS).2.2.2.1)
    hstrong (fun S hS=>(hcoords S hS).2.2.2.2.1) (fun S hS=>(hcoords S hS).2.2.2.2.2)

theorem actual_near_members_band_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 16*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤64*K) :
    (15*K)*(NearMembers K F).card≤261*N^2 := by
  have hsub : NearMembers K F⊆F := Finset.filter_subset _ _
  have hL : Legal (Ground N) (NearMembers K F) :=
    ⟨fun S hS=>hlegal.1 S (hsub hS),fun S hS T hT he=>hlegal.2 S (hsub hS) T (hsub hT) he⟩
  exact actual_nearAP_band_budget hL hK (fun S hS=>hbad S (hsub hS))
    (fun S hS=>hlow S (hsub hS)) (fun S hS=>hhigh S (hsub hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2)

theorem actual_maximal_AP_extension {S U : Finset ℤ} (hUS : U⊆S) (hAP : IsAP U) :
    ∃ P : Finset ℤ, U⊆P ∧ MaximalAPCore S P := by
  let A := S.powerset.filter (fun P:Finset ℤ=>U⊆P ∧ IsAP P)
  have hUA : U∈A := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hUS,Finset.Subset.refl _,hAP⟩
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image A Finset.card ⟨U,hUA⟩
  obtain ⟨hPS,hUP,hPAP⟩ := Finset.mem_filter.mp hP
  refine ⟨P,hUP,Finset.mem_powerset.mp hPS,hPAP,?_⟩
  intro Q hPQ hQS hQAP
  have hQA : Q∈A := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hQS,hUP.trans hPQ,hQAP⟩
  exact (Finset.eq_of_subset_of_card_le hPQ (hmax Q hQA)).symm

theorem near_core_of_actual_approximation {K : ℕ} {S U : Finset ℤ}
    (hlarge : 16*K+1≤S.card) (hUS : U⊆S) (hAP : IsAP U) (hsmall : (S\U).card<K) :
    HasNearAPCore K S := by
  obtain ⟨P,hUP,hPS,hPAP,hmax⟩ := actual_maximal_AP_extension hUS hAP
  have hsub : S\P⊆S\U := by
    intro x hx
    obtain ⟨hxS,hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxS,fun hxU=>hxP (hUP hxU)⟩
  have hsm := (Finset.card_le_card hsub).trans_lt hsmall
  have hc := Finset.card_sdiff_add_card_eq_card hPS
  exact ⟨P,⟨hPS,hPAP,hmax⟩,by omega,hsm⟩

theorem non_near_actual_AP_remainder {K : ℕ} {S : Finset ℤ}
    (hlarge : 16*K+1≤S.card) (hnot : ¬HasNearAPCore K S) :
    ∀ U⊆S, IsAP U → K≤(S\U).card := by
  intro U hUS hAP
  by_contra hn
  exact hnot (near_core_of_actual_approximation hlarge hUS hAP (by omega))

theorem actual_AP_approximation_band_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 16*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤64*K)
    (happrox : ∀ S∈F, ∃ U : Finset ℤ, U⊆S ∧ IsAP U ∧ (S\U).card<K) :
    (15*K)*F.card≤261*N^2 := by
  apply actual_nearAP_band_budget hlegal hK hbad hlow hhigh
  intro S hS
  obtain ⟨U,hUS,hAP,hsmall⟩ := happrox S hS
  exact near_core_of_actual_approximation (hlow S hS) hUS hAP hsmall

#print axioms actual_maximal_AP_extension
#print axioms near_core_of_actual_approximation
#print axioms non_near_actual_AP_remainder
#print axioms actual_AP_approximation_band_budget

#print axioms actual_AP_grid_representation
#print axioms actual_nearAP_coordinate_selection
#print axioms actual_nearAP_step_budget
#print axioms actual_nearAP_band_budget
#print axioms actual_near_members_band_budget

#print axioms window_class_card_sum
#print axioms actual_nearAP_same_step_card

#print axioms disjoint_pieces_hit_card
#print axioms exists_disjoint_piece
#print axioms heavy_core_pools_intersect
#print axioms start_decomposition
#print axioms grid_subset_window
#print axioms window_prefix_subset_grid
#print axioms window_card
#print axioms window_intersection_code_bounds
#print axioms start_code_mem_pool
#print axioms start_pool_card_mul
#print axioms mem_grid
#print axioms grid_card
#print axioms grid_APAt
#print axioms grid_isAP
#print axioms grid_member_ge_start
#print axioms long_overlap_AP_subset_maximal
#print axioms actual_remainder_private_of_long_overlap
#print axioms actual_common_prefix_remainders_disjoint
#print axioms crooked_disjoint_remainders_card
end
end JSP233.NearAP36
