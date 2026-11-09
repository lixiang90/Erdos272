module

public import Erdos272.Core.NearAP36
public import Erdos272.Counting.BandAggregation34
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual near-AP cores of arbitrary member width, with a one-dimensional
Helly bound for the genuine heavy start-code windows. -/
namespace JSP233.NearHelly54
open StarCompletion APGeometry AffineLine30 NearAP36 BandAggregation34
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

def CoreWindow (b d K : ℕ) (q : ℕ×ℕ) : Finset ℤ :=
  Grid (q.1+q.2*K*d) d ((b+1)*K)

theorem grid_subset_window {a b d k K : ℕ} (hK : 0<K) (hk : k≤b*K) :
    Grid a d k⊆CoreWindow b d K (StartCode d K a) := by
  obtain ⟨j,hj,ha⟩ := start_decomposition (a:=a) (d:=d) hK
  intro x hx
  obtain ⟨i,hi,hx⟩ := (mem_grid _ _ _ _).mp hx
  apply (mem_grid _ _ _ _).mpr
  refine ⟨j+i,by nlinarith only [hi,hk,hj],?_⟩
  have haZ : (a:ℤ)=(StartCode d K a).1+((StartCode d K a).2*(K:ℤ)+j)*d := by exact_mod_cast ha
  push_cast
  nlinarith only [hx,haZ]

theorem window_card {b d K : ℕ} (hd : 0<d) (q : ℕ×ℕ) : (CoreWindow b d K q).card=(b+1)*K :=
  grid_card _ _ _ hd

theorem window_intersection_code_bounds {b d K : ℕ} {q r : ℕ×ℕ}
    (hd : 0<d) (_hK : 0<K) (hq : q.1<d) (hr : r.1<d)
    (hinter : (CoreWindow b d K q∩CoreWindow b d K r).Nonempty) :
    q.1=r.1 ∧ q.2≤r.2+b ∧ r.2≤q.2+b := by
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
    have hh : (r.2+(b+1))*K≤q.2*K := Nat.mul_le_mul_right K (by omega)
    nlinarith only [hh,hi,hj,hiq]
  · by_contra hn
    have hh : (q.2+(b+1))*K≤r.2*K := Nat.mul_le_mul_right K (by omega)
    nlinarith only [hh,hi,hj,hiq]

theorem window_class_card_sum {N b d K : ℕ} {B : Finset (ℕ×ℕ)}
    (hd : 0<d) (hK : 0<K) (hdN : d*K≤N) (hB : B⊆StartPool N d K)
    (family : (ℕ×ℕ)→Finset (Finset ℤ)) (core : Finset ℤ→Finset ℤ)
    (hcore : ∀ q∈B, ∀ S∈family q, core S⊆CoreWindow b d K q)
    (hdis : ∀ q∈B, ∀ S∈family q, ∀ T∈family q,
      S≠T → Disjoint (S\core S) (T\core T))
    (hcross : ∀ q∈B, ∀ r∈B, ∀ S∈family q, ∀ T∈family r, (S∩T).Nonempty)
    (hsmall : ∀ q∈B, ∀ S∈family q, S.card≤b*K)
    (hlinear : ∀ q∈B, (family q).card≤N) : (∑ q∈B, (family q).card)≤3*(b+1)*N := by
  let H := B.filter (fun q=>(b+1)*K<(family q).card)
  have hHB : H⊆B := Finset.filter_subset _ _
  have hHcard : H.card≤b+1 := by
    rcases H.eq_empty_or_nonempty with he|hne
    · simp [he]
    obtain ⟨q0,hq0,hmin⟩ := Finset.exists_min_image H Prod.snd hne
    have hq0B := hHB hq0
    have hq0large := (Finset.mem_filter.mp hq0).2
    have hb : ∀ q∈H, q.1=q0.1 ∧ q0.2≤q.2 ∧ q.2≤q0.2+b := by
      intro q hq
      have hqB := hHB hq
      have hqlarge := (Finset.mem_filter.mp hq).2
      have hinter := heavy_core_pools_intersect core (hcore q hqB) (hcore q0 hq0B)
        (hdis q hqB) (hdis q0 hq0B) (hcross q hqB q0 hq0B) (hsmall q0 hq0B)
        (by nlinarith only [hqlarge,Nat.zero_le K] : b*K<(family q).card)
        (by simpa only [window_card hd] using hq0large)
      have hi := window_intersection_code_bounds hd hK
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hqB)).1)
        (Finset.mem_range.mp (Finset.mem_product.mp (hB hq0B)).1) hinter
      exact ⟨hi.1,hmin q hq,hi.2.1⟩
    have hm : Set.MapsTo Prod.snd (H:Set (ℕ×ℕ))
        (Finset.Icc q0.2 (q0.2+b):Set ℕ) := by
      intro q hq
      exact Finset.mem_Icc.mpr (hb q hq).2
    have hi : Set.InjOn Prod.snd (H:Set (ℕ×ℕ)) := by
      intro q hq r hr he
      exact Prod.ext ((hb q hq).1.trans (hb r hr).1.symm) he
    have hc := Finset.card_le_card_of_injOn Prod.snd hm hi
    rw [Nat.card_Icc] at hc
    omega
  have hlight : (∑ q∈B\H, (family q).card)≤B.card*((b+1)*K) := by
    have hp : ∀ q∈B\H, (family q).card≤(b+1)*K := by
      intro q hq
      obtain ⟨hqB,hqH⟩ := Finset.mem_sdiff.mp hq
      have hh : ¬(b+1)*K<(family q).card := fun hn=>hqH (Finset.mem_filter.mpr ⟨hqB,hn⟩)
      omega
    have hs := Finset.sum_le_sum hp
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right _ (Finset.card_le_card Finset.sdiff_subset))
  have hheavy : (∑ q∈H, (family q).card)≤(b+1)*N := by
    have hs := Finset.sum_le_sum (fun q hq=>hlinear q (hHB hq))
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right N hHcard)
  have hpart := Finset.sum_sdiff hHB (f:=fun q=>(family q).card)
  have hpool := start_pool_card_mul hd hK hdN
  have hbs := (Nat.mul_le_mul_right K (Finset.card_le_card hB)).trans hpool
  have hlight' : (∑ q∈B\H, (family q).card)≤2*(b+1)*N := by
    have hm := Nat.mul_le_mul_left (b+1) hbs
    nlinarith
  nlinarith only [hpart,hlight',hheavy]

theorem actual_nearAP_same_step_card {N b d K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hd : 0<d) (hK : 0<K)
    (start length : Finset ℤ→ℕ) (hbad : ∀ S∈F, ¬IsAP S)
    (hcard : ∀ S∈F, S.card≤b*K)
    (hsub : ∀ S∈F, Grid (start S) d (length S)⊆S)
    (hlow : ∀ S∈F, 2*K+1≤length S) (hhigh : ∀ S∈F, length S≤b*K)
    (hsmall : ∀ S∈F, (S\Grid (start S) d (length S)).card<K)
    (hmax : ∀ S∈F, ∀ U : Finset ℤ, Grid (start S) d (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) d (length S)) : F.card≤3*(b+1)*N := by
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
  have hsum := window_class_card_sum (b:=b) (B:=B) hd hK hdN (Finset.Subset.refl _) family core
    (by
      intro q hq S hS
      have hh := grid_subset_window (a:=start S) (d:=d) hK (hhigh S (hfamily q hS))
      have he := (Finset.mem_filter.mp hS).2
      change code S=q at he
      change core S⊆CoreWindow b d K (code S) at hh
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

theorem actual_nearAP_coordinate_selection {N K b : ℕ} {F : Finset (Finset ℤ)}
    (hground : ∀ S∈F, S⊆Ground N) (hcard : ∀ S∈F, S.card≤b*K)
    (hnear : ∀ S∈F, HasNearAPCore K S) :
    ∃ start step length : Finset ℤ→ℕ, ∀ S∈F,
      0<step S ∧ Grid (start S) (step S) (length S)⊆S ∧
      2*K+1≤length S ∧ length S≤b*K ∧
      (S\Grid (start S) (step S) (length S)).card<K ∧
      ∀ U : Finset ℤ, Grid (start S) (step S) (length S)⊆U → U⊆S → IsAP U →
        U=Grid (start S) (step S) (length S) := by
  have hex : ∀ S : Finset ℤ, ∃ a d k : ℕ, S∈F →
      0<d ∧ Grid a d k⊆S ∧ 2*K+1≤k ∧ k≤b*K ∧ (S\Grid a d k).card<K ∧
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

theorem actual_nearAP_step_budget {N K A b : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 0<A)
    (start step length : Finset ℤ→ℕ) (hbad : ∀ S∈F, ¬IsAP S)
    (hcard : ∀ S∈F, S.card≤b*K) (hstep : ∀ S∈F, 0<step S)
    (hsub : ∀ S∈F, Grid (start S) (step S) (length S)⊆S)
    (hlow : ∀ S∈F, 2*K+1≤length S) (hhigh : ∀ S∈F, length S≤b*K)
    (hstrong : ∀ S∈F, A*K+1≤length S)
    (hsmall : ∀ S∈F, (S\Grid (start S) (step S) (length S)).card<K)
    (hmax : ∀ S∈F, ∀ U : Finset ℤ, Grid (start S) (step S) (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) (step S) (length S)) : (A*K)*F.card≤3*(b+1)*N^2 := by
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
  have hb : ∀ d∈Finset.Icc 1 (N/(A*K)), (family d).card≤3*(b+1)*N := by
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
  have hdv := Nat.mul_le_mul_left (3*(b+1)*N) (Nat.div_mul_le_self N (A*K))
  nlinarith

theorem actual_nearAP_band_budget {N K A b : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, (A+1)*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤b*K)
    (hnear : ∀ S∈F, HasNearAPCore K S) : (A*K)*F.card≤3*(b+1)*N^2 := by
  obtain ⟨start,step,length,hcoords⟩ := actual_nearAP_coordinate_selection hlegal.1 hhigh hnear
  have hstep : ∀ S∈F, 0<step S := fun S hS=>(hcoords S hS).1
  have hsub : ∀ S∈F, Grid (start S) (step S) (length S)⊆S := fun S hS=>(hcoords S hS).2.1
  have hstrong : ∀ S∈F, A*K+1≤length S := by
    intro S hS
    have hc := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    rw [grid_card _ _ _ (hstep S hS)] at hc
    have hsm := (hcoords S hS).2.2.2.2.1
    have hlo := hlow S hS
    have he : (A+1)*K=A*K+K := by ring
    omega
  exact actual_nearAP_step_budget hlegal hK (by omega : 0<A) start step length hbad hhigh
    hstep hsub (fun S hS=>(hcoords S hS).2.2.1) (fun S hS=>(hcoords S hS).2.2.2.1)
    hstrong (fun S hS=>(hcoords S hS).2.2.2.2.1) (fun S hS=>(hcoords S hS).2.2.2.2.2)

theorem near_core_of_actual_approximation {K A : ℕ} {S U : Finset ℤ}
    (_hK : 0<K) (hA : 2≤A) (hlarge : (A+1)*K+1≤S.card)
    (hUS : U⊆S) (hAP : IsAP U) (hsmall : (S\U).card<K) :
    HasNearAPCore K S := by
  obtain ⟨P,hUP,hPS,hPAP,hmax⟩ := actual_maximal_AP_extension hUS hAP
  have hsub : S\P⊆S\U := by
    intro x hx
    obtain ⟨hxS,hxP⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxS,fun hxU=>hxP (hUP hxU)⟩
  have hsm := (Finset.card_le_card hsub).trans_lt hsmall
  have hc := Finset.card_sdiff_add_card_eq_card hPS
  have hAK := Nat.mul_le_mul_right K hA
  have he : (A+1)*K=A*K+K := by ring
  exact ⟨P,⟨hPS,hPAP,hmax⟩,by omega,hsm⟩

theorem actual_AP_approximation_band_budget {N K A b : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, (A+1)*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤b*K)
    (happrox : ∀ S∈F, ∃ U : Finset ℤ, U⊆S ∧ IsAP U ∧ (S\U).card<K) :
    (A*K)*F.card≤3*(b+1)*N^2 := by
  apply actual_nearAP_band_budget hlegal hK hA hbad hlow hhigh
  intro S hS
  obtain ⟨U,hUS,hAP,hsmall⟩ := happrox S hS
  exact near_core_of_actual_approximation hK hA (hlow S hS) hUS hAP hsmall

theorem actual_near_members_band_budget {N K A b : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, (A+1)*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤b*K) :
    (A*K)*(NearMembers K F).card≤3*(b+1)*N^2 := by
  have hsub : NearMembers K F⊆F := Finset.filter_subset _ _
  have hL : Legal (Ground N) (NearMembers K F) :=
    ⟨fun S hS=>hlegal.1 S (hsub hS),fun S hS T hT he=>hlegal.2 S (hsub hS) T (hsub hT) he⟩
  exact actual_nearAP_band_budget hL hK hA (fun S hS=>hbad S (hsub hS))
    (fun S hS=>hlow S (hsub hS)) (fun S hS=>hhigh S (hsub hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2)

theorem actual_near19_band_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 9*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤19*K) :
    (8*K)*(NearMembers K F).card≤60*N^2 := by
  simpa only [show 8+1=9 by norm_num,show 3*(19+1)=60 by norm_num] using
    actual_near_members_band_budget (A:=8) hlegal hK (by decide) hbad hlow hhigh


theorem actual_dyadic_near_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 9*(2^(level S)*K)+1≤S.card)
    (hhigh : ∀ S∈F, S.card≤19*(2^(level S)*K))
    (hnear : ∀ S∈F, HasNearAPCore (2^(level S)*K) S) :
    (F.card:ℝ)*K≤15*(N:ℝ)^2 := by
  let n := ∑ S∈F, (level S+1)
  let family : ℕ→Finset (Finset ℤ) := fun j=>F.filter (fun S=>level S=j)
  have hfamily : ∀ j, family j⊆F := fun j=>Finset.filter_subset _ _
  have hmaps : ∀ S∈F, level S∈Finset.range n := by
    intro S hS
    have hh := Finset.single_le_sum (fun T (_hT:T∈F)=>Nat.zero_le (level T+1)) hS
    exact Finset.mem_range.mpr (by dsimp [n];omega)
  have hpart : F.card=∑ j∈Finset.range n, (family j).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hrow : ∀ j∈Finset.range n,
      8*(K:ℝ)*(family j).card≤60*(N:ℝ)^2*(1/2:ℝ)^j := by
    intro j _hj
    have hlegalj : Legal (Ground N) (family j) :=
      ⟨fun S hS=>hlegal.1 S (hfamily j hS),fun S hS T hT he=>
        hlegal.2 S (hfamily j hS) T (hfamily j hT) he⟩
    have hh := actual_nearAP_band_budget (A:=8) (b:=19) hlegalj
      (by positivity : 0<2^j*K) (by decide)
      (fun S hS=>hbad S (hfamily j hS)) (by
        intro S hS
        have hs := hlow S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs) (by
        intro S hS
        have hs := hhigh S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs) (by
        intro S hS
        have hs := hnear S (hfamily j hS)
        simpa only [(Finset.mem_filter.mp hS).2] using hs)
    have hhR : 8*((2:ℝ)^j*K)*(family j).card≤60*(N:ℝ)^2 := by exact_mod_cast hh
    have hp : 0<(2:ℝ)^j := by positivity
    have hd := div_le_div_of_nonneg_right hhR hp.le
    have he : (8*((2:ℝ)^j*K)*(family j).card)/(2:ℝ)^j=8*K*(family j).card := by field_simp
    have hr : (60*(N:ℝ)^2)/(2:ℝ)^j=60*(N:ℝ)^2*(1/2:ℝ)^j := by
      rw [one_div,inv_pow,div_eq_mul_inv]
    rw [he,hr] at hd
    exact hd
  have hs := Finset.sum_le_sum hrow
  simp only [←Finset.mul_sum] at hs
  have hpartR : (F.card:ℝ)=∑ j∈Finset.range n, ((family j).card:ℝ) := by exact_mod_cast hpart
  rw [←hpartR] at hs
  have ht := mul_le_mul_of_nonneg_left (dyadic_sum_le_two n)
    (show (0:ℝ)≤60*(N:ℝ)^2 by positivity)
  nlinarith only [hs,ht]

theorem actual_dyadic_near_members_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (level : Finset ℤ→ℕ) (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 9*(2^(level S)*K)+1≤S.card)
    (hhigh : ∀ S∈F, S.card≤19*(2^(level S)*K)) :
    ((F.filter (fun S=>HasNearAPCore (2^(level S)*K) S)).card:ℝ)*K≤15*(N:ℝ)^2 := by
  let G := F.filter (fun S=>HasNearAPCore (2^(level S)*K) S)
  have hGF : G⊆F := Finset.filter_subset _ _
  exact actual_dyadic_near_budget level
    (show Legal (Ground N) G from ⟨fun S hS=>hlegal.1 S (hGF hS),
      fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩) hK
    (fun S hS=>hbad S (hGF hS)) (fun S hS=>hlow S (hGF hS))
    (fun S hS=>hhigh S (hGF hS)) (fun S hS=>(Finset.mem_filter.mp hS).2)

#print axioms grid_subset_window
#print axioms window_card
#print axioms window_intersection_code_bounds
#print axioms window_class_card_sum
#print axioms actual_nearAP_same_step_card
#print axioms actual_nearAP_coordinate_selection
#print axioms actual_nearAP_step_budget
#print axioms actual_nearAP_band_budget
#print axioms near_core_of_actual_approximation
#print axioms actual_AP_approximation_band_budget
#print axioms actual_near_members_band_budget
#print axioms actual_near19_band_budget
#print axioms actual_dyadic_near_budget
#print axioms actual_dyadic_near_members_budget
end
end JSP233.NearHelly54
