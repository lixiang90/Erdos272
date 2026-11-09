module

public import Erdos272.Core.NearHelly54
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Actual near-core start slack and exact finite floor budgets.
The refined code pool is derived from the actual core's A*K-th member.
No target family cardinality or class capacity is supplied to actual endpoints.
-/
namespace JSP233.NearFloor63
open StarCompletion APGeometry AffineLine30 NearAP36
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def OriginStartPool (N A d K : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range d ×ˢ Finset.range (N / (K*d) + 1 - A)

theorem actual_grid_start_slack {N A d K a k : ℕ} {S : Finset ℤ}
    (hground : S ⊆ Ground N) (hsub : Grid a d k ⊆ S)
    (hlength : A*K+1 ≤ k) : a+(A*K)*d ≤ N := by
  have hx := hsub ((mem_grid _ _ _ _).mpr ⟨A*K,by omega,rfl⟩)
  have hxN := ((mem_ground N _).mp (hground hx)).2
  exact_mod_cast hxN

theorem start_code_mem_origin_pool {N A d K a : ℕ} (hd : 0<d) (hK : 0<K)
    (hslack : a+(A*K)*d ≤ N) : StartCode d K a ∈ OriginStartPool N A d K := by
  obtain ⟨j,hj,ha⟩ := start_decomposition (a:=a) (d:=d) hK
  have hcode : ((StartCode d K a).2+A)*(K*d) ≤ N := by
    nlinarith only [ha,hslack,Nat.zero_le (StartCode d K a).1,Nat.zero_le (j*d)]
  have hquot := (Nat.le_div_iff_mul_le (by positivity : 0<K*d)).mpr hcode
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr (Nat.mod_lt _ hd),Finset.mem_range.mpr (by omega)⟩

theorem actual_start_code_mem_origin_pool {N A d K a k : ℕ} {S : Finset ℤ}
    (hd : 0<d) (hK : 0<K) (hground : S ⊆ Ground N)
    (hsub : Grid a d k ⊆ S) (hlength : A*K+1 ≤ k) :
    StartCode d K a ∈ OriginStartPool N A d K :=
  start_code_mem_origin_pool hd hK (actual_grid_start_slack hground hsub hlength)

theorem origin_start_pool_card (N A d K : ℕ) :
    (OriginStartPool N A d K).card = d*(N/(K*d)+1-A) := by
  simp only [OriginStartPool,Finset.card_product,Finset.card_range]

theorem origin_start_pool_payment_exact {N A d K : ℕ} (hA : 1≤A)
    (hd : 0<d) (hK : 0<K) (hvalid : (A*K)*d≤N) :
    (OriginStartPool N A d K).card*K+(A-1)*K*d = (N/(K*d))*(K*d) := by
  have hAd : A≤N/(K*d) := (Nat.le_div_iff_mul_le (by positivity : 0<K*d)).mpr (by nlinarith)
  have he : N/(K*d)+1-A+(A-1)=N/(K*d) := by omega
  rw [origin_start_pool_card]
  nlinarith only [congrArg (fun n=>n*(K*d)) he]

theorem origin_start_pool_payment {N A d K : ℕ} (hA : 1≤A)
    (hd : 0<d) (hK : 0<K) (hvalid : (A*K)*d≤N) :
    (OriginStartPool N A d K).card*K+(A-1)*K*d ≤ N := by
  rw [origin_start_pool_payment_exact hA hd hK hvalid]
  exact Nat.div_mul_le_self N (K*d)

theorem origin_start_pool_subset {N A d K : ℕ} :
    OriginStartPool N A d K ⊆ StartPool N d K := by
  intro q hq
  obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
  apply Finset.mem_product.mpr
  refine ⟨hq1,Finset.mem_range.mpr ?_⟩
  have hh := Finset.mem_range.mp hq2
  omega

theorem divisor_row_filter {T d : ℕ} (hd : 0<d) :
    (Finset.Icc 1 T).filter (fun j=>d*j≤T) = Finset.Icc 1 (T/d) := by
  ext j
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hj,_⟩,hp⟩
    exact ⟨hj,(Nat.le_div_iff_mul_le hd).mpr (by nlinarith)⟩
  · rintro ⟨hj,hq⟩
    refine ⟨⟨hj,hq.trans (Nat.div_le_self _ _)⟩,?_⟩
    have hh := (Nat.le_div_iff_mul_le hd).mp hq
    nlinarith only [hh]

theorem divisor_column_filter {T D j : ℕ} (hj : 0<j) :
    (Finset.Icc 1 D).filter (fun d=>d*j≤T) = Finset.Icc 1 (min D (T/j)) := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,le_min_iff]
  exact ⟨fun ⟨⟨hd,hD⟩,hT⟩=>⟨hd,hD,(Nat.le_div_iff_mul_le hj).mpr hT⟩,
    fun ⟨hd,hD,hT⟩=>⟨⟨hd,hD⟩,(Nat.le_div_iff_mul_le hj).mp hT⟩⟩

theorem weighted_floor_double_sum (T D : ℕ) (f : ℕ→ℕ) :
    (∑d∈Finset.Icc 1 D,f d*(T/d)) =
      ∑j∈Finset.Icc 1 T, ∑d∈Finset.Icc 1 (min D (T/j)),f d := by
  calc
    _ = ∑d∈Finset.Icc 1 D, ∑j∈Finset.Icc 1 T, if d*j≤T then f d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [←Finset.sum_filter,divisor_row_filter (by have hh:=Finset.mem_Icc.mp hd;omega)]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id,mul_comm]
    _ = ∑j∈Finset.Icc 1 T, ∑d∈Finset.Icc 1 D, if d*j≤T then f d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.sum_filter,divisor_column_filter (by have hh:=Finset.mem_Icc.mp hj;omega)]

theorem floor_double_sum (T D : ℕ) :
    (∑d∈Finset.Icc 1 D,T/d) = ∑j∈Finset.Icc 1 T,min D (T/j) := by
  simpa only [one_mul,Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id,mul_one] using
    weighted_floor_double_sum T D (fun _=>1)

theorem triangle_sum_twice (D : ℕ) :
    2*(∑d∈Finset.Icc 1 D,d) = D*(D+1) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1≤D+1)]
    nlinarith only [ih]

theorem weighted_floor_triangle_sum (T D : ℕ) :
    2*(∑d∈Finset.Icc 1 D,d*(T/d)) =
      ∑j∈Finset.Icc 1 T,min D (T/j)*(min D (T/j)+1) := by
  rw [weighted_floor_double_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _=>triangle_sum_twice _)

theorem window_class_origin_card_sum {N A b d K : ℕ} {B : Finset (ℕ×ℕ)}
    (hd : 0<d) (hK : 0<K) (hB : B⊆OriginStartPool N A d K)
    (family : (ℕ×ℕ)→Finset (Finset ℤ)) (core : Finset ℤ→Finset ℤ)
    (hcore : ∀q∈B, ∀S∈family q, core S⊆NearHelly54.CoreWindow b d K q)
    (hdis : ∀q∈B, ∀S∈family q, ∀T∈family q,
      S≠T → Disjoint (S\core S) (T\core T))
    (hcross : ∀q∈B, ∀r∈B, ∀S∈family q, ∀T∈family r, (S∩T).Nonempty)
    (hsmall : ∀q∈B, ∀S∈family q, S.card≤b*K)
    (hlinear : ∀q∈B, (family q).card≤N) :
    (∑q∈B,(family q).card) ≤ (b+1)*(N+K*(OriginStartPool N A d K).card) := by
  let H := B.filter (fun q=>(b+1)*K<(family q).card)
  have hHB : H⊆B := Finset.filter_subset _ _
  have hHcard : H.card≤b+1 := by
    rcases H.eq_empty_or_nonempty with he|hne
    · simp [he]
    obtain ⟨q0,hq0,hmin⟩ := Finset.exists_min_image H Prod.snd hne
    have hq0B := hHB hq0
    have hq0large := (Finset.mem_filter.mp hq0).2
    have hb : ∀q∈H, q.1=q0.1 ∧ q0.2≤q.2 ∧ q.2≤q0.2+b := by
      intro q hq
      have hqB := hHB hq
      have hqlarge := (Finset.mem_filter.mp hq).2
      have hinter := heavy_core_pools_intersect core (hcore q hqB) (hcore q0 hq0B)
        (hdis q hqB) (hdis q0 hq0B) (hcross q hqB q0 hq0B) (hsmall q0 hq0B)
        (by nlinarith only [hqlarge,Nat.zero_le K] : b*K<(family q).card)
        (by simpa only [NearHelly54.window_card hd] using hq0large)
      have hi := NearHelly54.window_intersection_code_bounds hd hK
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
  have hlight : (∑q∈B\H,(family q).card) ≤
      (OriginStartPool N A d K).card*((b+1)*K) := by
    have hp : ∀q∈B\H,(family q).card≤(b+1)*K := by
      intro q hq
      obtain ⟨hqB,hqH⟩ := Finset.mem_sdiff.mp hq
      have hh : ¬(b+1)*K<(family q).card := fun hn=>hqH (Finset.mem_filter.mpr ⟨hqB,hn⟩)
      omega
    have hs := Finset.sum_le_sum hp
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right _
      ((Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_le_card hB)))
  have hheavy : (∑q∈H,(family q).card)≤(b+1)*N := by
    have hs := Finset.sum_le_sum (fun q hq=>hlinear q (hHB hq))
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right N hHcard)
  have hpart := Finset.sum_sdiff hHB (f:=fun q=>(family q).card)
  nlinarith only [hpart,hlight,hheavy]

theorem actual_near_same_step_floor_card {N A b d K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hd : 0<d) (hK : 0<K) (hA : 2≤A)
    (start length : Finset ℤ→ℕ) (hbad : ∀S∈F,¬IsAP S)
    (hcard : ∀S∈F,S.card≤b*K) (hsub : ∀S∈F,Grid (start S) d (length S)⊆S)
    (hstrong : ∀S∈F,A*K+1≤length S)
    (hsmall : ∀S∈F,(S\Grid (start S) d (length S)).card<K)
    (hmax : ∀S∈F,∀U : Finset ℤ,Grid (start S) d (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) d (length S)) :
    F.card ≤ (b+1)*(N+K*d*(N/(K*d)+1-A)) := by
  let core : Finset ℤ→Finset ℤ := fun S=>Grid (start S) d (length S)
  let code : Finset ℤ→ℕ×ℕ := fun S=>StartCode d K (start S)
  let B := OriginStartPool N A d K
  let family : (ℕ×ℕ)→Finset (Finset ℤ) := fun q=>F.filter (fun S=>code S=q)
  have hfamily : ∀q,family q⊆F := fun q=>Finset.filter_subset _ _
  have hlow : ∀S∈F,2*K+1≤length S := by
    intro S hS
    have hh := hstrong S hS
    have hm := Nat.mul_le_mul_right K hA
    omega
  have hhigh : ∀S∈F,length S≤b*K := by
    intro S hS
    have hc := Finset.card_le_card (hsub S hS)
    rw [grid_card _ _ _ hd] at hc
    exact hc.trans (hcard S hS)
  have hprefix : ∀q,∀S∈family q,WindowPrefix d K q⊆core S := by
    intro q S hS
    have hh := window_prefix_subset_grid (a:=start S) (d:=d) hK (hlow S (hfamily q hS))
    have he := (Finset.mem_filter.mp hS).2
    change code S=q at he
    change WindowPrefix d K (code S)⊆core S at hh
    simpa only [he] using hh
  have hdis : ∀q,∀S∈family q,∀T∈family q,
      S≠T → Disjoint (S\core S) (T\core T) := by
    intro q
    have hqlegal : Legal (Ground N) (family q) :=
      ⟨fun S hS=>hlegal.1 S (hfamily q hS),
       fun S hS T hT he=>hlegal.2 S (hfamily q hS) T (hfamily q hT) he⟩
    apply actual_common_prefix_remainders_disjoint (a:=q.1+(q.2+1)*K*d) hqlegal hd core
      (fun S _=>⟨start S,length S,rfl⟩) (fun S hS=>hsub S (hfamily q hS))
      (hprefix q) (fun S hS=>hsmall S (hfamily q hS)) (fun S hS=>hmax S (hfamily q hS))
  have hlinear : ∀q,(family q).card≤N := by
    intro q
    exact crooked_disjoint_remainders_card (fun S hS=>hlegal.1 S (hfamily q hS)) core
      (fun S hS=>hbad S (hfamily q hS))
      (fun S hS=>grid_isAP _ _ _ hd (by have hh:=hlow S (hfamily q hS);omega))
      (fun S hS=>hsub S (hfamily q hS)) (hdis q)
  have hsum := window_class_origin_card_sum (b:=b) (B:=B) hd hK
    (Finset.Subset.refl _) family core
    (by
      intro q _hq S hS
      have hh := NearHelly54.grid_subset_window (a:=start S) (d:=d) hK (hhigh S (hfamily q hS))
      have he := (Finset.mem_filter.mp hS).2
      change code S=q at he
      change core S⊆NearHelly54.CoreWindow b d K (code S) at hh
      simpa only [he] using hh)
    (fun q _=>hdis q)
    (by
      intro q _hq r _hr S hS T hT
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
  have hmaps : ∀S∈F,code S∈B := fun S hS=>
    actual_start_code_mem_origin_pool hd hK (hlegal.1 S hS) (hsub S hS) (hstrong S hS)
  have hpart : F.card=∑q∈B,(family q).card := Finset.card_eq_sum_card_fiberwise hmaps
  rw [←hpart] at hsum
  simpa only [B,origin_start_pool_card,mul_assoc,mul_left_comm,mul_comm] using hsum

theorem actual_near_same_step_origin_payment {N A b d K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hd : 0<d) (hK : 0<K) (hA : 2≤A)
    (hvalid : (A*K)*d≤N) (start length : Finset ℤ→ℕ)
    (hbad : ∀S∈F,¬IsAP S) (hcard : ∀S∈F,S.card≤b*K)
    (hsub : ∀S∈F,Grid (start S) d (length S)⊆S)
    (hstrong : ∀S∈F,A*K+1≤length S)
    (hsmall : ∀S∈F,(S\Grid (start S) d (length S)).card<K)
    (hmax : ∀S∈F,∀U : Finset ℤ,Grid (start S) d (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) d (length S)) :
    F.card+(b+1)*(A-1)*K*d ≤ 2*(b+1)*N := by
  have hb := actual_near_same_step_floor_card hlegal hd hK hA start length hbad hcard
    hsub hstrong hsmall hmax
  have hp := origin_start_pool_payment (by omega : 1≤A) hd hK hvalid
  rw [origin_start_pool_card] at hp
  nlinarith only [hb,Nat.mul_le_mul_left (b+1) hp]

theorem shifted_floor_payment_sum {N A K D : ℕ} (hA : 1≤A) (hK : 0<K)
    (hvalid : (A*K)*D≤N) :
    (∑d∈Finset.Icc 1 D,K*d*(N/(K*d)+1-A)) +
      (A-1)*K*(∑d∈Finset.Icc 1 D,d) = K*(∑d∈Finset.Icc 1 D,d*(N/(K*d))) := by
  have he : ∀d∈Finset.Icc 1 D,
      K*d*(N/(K*d)+1-A)+(A-1)*K*d = K*(d*(N/(K*d))) := by
    intro d hd
    obtain ⟨hd1,hdD⟩ := Finset.mem_Icc.mp hd
    have hv : (A*K)*d≤N := (Nat.mul_le_mul_left (A*K) hdD).trans hvalid
    have hp := origin_start_pool_payment_exact hA (by omega : 0<d) hK hv
    rw [origin_start_pool_card] at hp
    nlinarith only [hp]
  have hs := Finset.sum_congr rfl he
  have hf : (∑d∈Finset.Icc 1 D,(A-1)*K*d) = (A-1)*K*(∑d∈Finset.Icc 1 D,d) := by
    rw [Finset.mul_sum]
  simpa only [Finset.sum_add_distrib,hf,←Finset.mul_sum] using hs

theorem shifted_floor_triangle_payment {N A K D : ℕ} (hA : 1≤A) (hK : 0<K)
    (hvalid : (A*K)*D≤N) :
    2*(∑d∈Finset.Icc 1 D,K*d*(N/(K*d)+1-A))+(A-1)*K*D*(D+1) =
      K*(∑j∈Finset.Icc 1 (N/K),min D ((N/K)/j)*(min D ((N/K)/j)+1)) := by
  have hs := shifted_floor_payment_sum hA hK hvalid
  have ht := weighted_floor_triangle_sum (N/K) D
  have he : (∑d∈Finset.Icc 1 D,d*((N/K)/d)) =
      ∑d∈Finset.Icc 1 D,d*(N/(K*d)) := by
    simp only [Nat.div_div_eq_div_mul]
  rw [he] at ht
  have htri := triangle_sum_twice D
  nlinarith only [congrArg (fun n=>2*n) hs,congrArg (fun n=>K*n) ht,
    congrArg (fun n=>(A-1)*K*n) htri]

theorem actual_near_floor_step_budget {N A b K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (start step length : Finset ℤ→ℕ) (hbad : ∀S∈F,¬IsAP S)
    (hcard : ∀S∈F,S.card≤b*K) (hstep : ∀S∈F,0<step S)
    (hsub : ∀S∈F,Grid (start S) (step S) (length S)⊆S)
    (hstrong : ∀S∈F,A*K+1≤length S)
    (hsmall : ∀S∈F,(S\Grid (start S) (step S) (length S)).card<K)
    (hmax : ∀S∈F,∀U : Finset ℤ,Grid (start S) (step S) (length S)⊆U → U⊆S →
      IsAP U → U=Grid (start S) (step S) (length S)) :
    F.card ≤ (b+1)*((N/(A*K))*N+
      K*(∑d∈Finset.Icc 1 (N/(A*K)),d*(N/(K*d)+1-A))) := by
  let D := N/(A*K)
  let family : ℕ→Finset (Finset ℤ) := fun d=>F.filter (fun S=>step S=d)
  have hfamily : ∀d,family d⊆F := fun d=>Finset.filter_subset _ _
  have hmaps : ∀S∈F,step S∈Finset.Icc 1 D := by
    intro S hS
    have hs := actual_grid_start_slack (hlegal.1 S hS) (hsub S hS) (hstrong S hS)
    apply Finset.mem_Icc.mpr
    exact ⟨hstep S hS,(Nat.le_div_iff_mul_le (by positivity : 0<A*K)).mpr (by nlinarith)⟩
  have hb : ∀d∈Finset.Icc 1 D,
      (family d).card≤(b+1)*(N+K*d*(N/(K*d)+1-A)) := by
    intro d hd
    have hflegal : Legal (Ground N) (family d) :=
      ⟨fun S hS=>hlegal.1 S (hfamily d hS),
       fun S hS T hT he=>hlegal.2 S (hfamily d hS) T (hfamily d hT) he⟩
    apply actual_near_same_step_floor_card hflegal (Finset.mem_Icc.mp hd).1 hK hA start length
      (fun S hS=>hbad S (hfamily d hS)) (fun S hS=>hcard S (hfamily d hS))
    · intro S hS
      have hh := hsub S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · exact fun S hS=>hstrong S (hfamily d hS)
    · intro S hS
      have hh := hsmall S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    · intro S hS
      have hh := hmax S (hfamily d hS)
      simpa only [(Finset.mem_filter.mp hS).2] using hh
  have hpart : F.card=∑d∈Finset.Icc 1 D,(family d).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpart]
  calc
    _ ≤ ∑d∈Finset.Icc 1 D,(b+1)*(N+K*d*(N/(K*d)+1-A)) := Finset.sum_le_sum hb
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib,Finset.sum_const]
      simp only [Nat.card_Icc,Nat.add_sub_cancel,Nat.cast_id,nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

theorem actual_near_floor_band_budget {N A b K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,(A+1)*K+1≤S.card)
    (hhigh : ∀S∈F,S.card≤b*K) (hnear : ∀S∈F,HasNearAPCore K S) :
    F.card ≤ (b+1)*((N/(A*K))*N+
      K*(∑d∈Finset.Icc 1 (N/(A*K)),d*(N/(K*d)+1-A))) := by
  obtain ⟨start,step,length,hcoords⟩ := NearHelly54.actual_nearAP_coordinate_selection hlegal.1 hhigh hnear
  have hstep : ∀S∈F,0<step S := fun S hS=>(hcoords S hS).1
  have hsub : ∀S∈F,Grid (start S) (step S) (length S)⊆S := fun S hS=>(hcoords S hS).2.1
  have hstrong : ∀S∈F,A*K+1≤length S := by
    intro S hS
    have hc := Finset.card_sdiff_add_card_eq_card (hsub S hS)
    rw [grid_card _ _ _ (hstep S hS)] at hc
    have hsm := (hcoords S hS).2.2.2.2.1
    have hlo := hlow S hS
    have he : (A+1)*K=A*K+K := by ring
    omega
  exact actual_near_floor_step_budget hlegal hK hA start step length hbad hhigh hstep hsub
    hstrong (fun S hS=>(hcoords S hS).2.2.2.2.1) (fun S hS=>(hcoords S hS).2.2.2.2.2)

theorem actual_near_members_floor_budget {N A b K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hA : 2≤A)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,(A+1)*K+1≤S.card)
    (hhigh : ∀S∈F,S.card≤b*K) :
    (NearMembers K F).card ≤ (b+1)*((N/(A*K))*N+
      K*(∑d∈Finset.Icc 1 (N/(A*K)),d*(N/(K*d)+1-A))) := by
  have hsub : NearMembers K F⊆F := Finset.filter_subset _ _
  have hL : Legal (Ground N) (NearMembers K F) :=
    ⟨fun S hS=>hlegal.1 S (hsub hS),fun S hS T hT he=>hlegal.2 S (hsub hS) T (hsub hT) he⟩
  exact actual_near_floor_band_budget hL hK hA (fun S hS=>hbad S (hsub hS))
    (fun S hS=>hlow S (hsub hS)) (fun S hS=>hhigh S (hsub hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2)

theorem origin_divisor_row_filter {T A d : ℕ} (hd : 0<d) :
    (Finset.Icc A T).filter (fun j=>d*j≤T) = Finset.Icc A (T/d) := by
  ext j
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hj,_⟩,hp⟩
    exact ⟨hj,(Nat.le_div_iff_mul_le hd).mpr (by nlinarith)⟩
  · rintro ⟨hj,hq⟩
    refine ⟨⟨hj,hq.trans (Nat.div_le_self _ _)⟩,?_⟩
    have hh := (Nat.le_div_iff_mul_le hd).mp hq
    nlinarith only [hh]

theorem origin_divisor_column_filter {T A j : ℕ} (hA : 1≤A) (hj : A≤j) :
    (Finset.Icc 1 (T/A)).filter (fun d=>d*j≤T) = Finset.Icc 1 (T/j) := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd,_⟩,hp⟩
    exact ⟨hd,(Nat.le_div_iff_mul_le (by omega : 0<j)).mpr hp⟩
  · rintro ⟨hd,hq⟩
    have hp := (Nat.le_div_iff_mul_le (by omega : 0<j)).mp hq
    refine ⟨⟨hd,(Nat.le_div_iff_mul_le (by omega : 0<A)).mpr ?_⟩,hp⟩
    nlinarith only [hp,Nat.mul_le_mul_left d hj]

theorem weighted_origin_floor_double_sum (T A : ℕ) (hA : 1≤A) (f : ℕ→ℕ) :
    (∑d∈Finset.Icc 1 (T/A),f d*(T/d+1-A)) =
      ∑j∈Finset.Icc A T, ∑d∈Finset.Icc 1 (T/j),f d := by
  calc
    _ = ∑d∈Finset.Icc 1 (T/A), ∑j∈Finset.Icc A T, if d*j≤T then f d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [←Finset.sum_filter,origin_divisor_row_filter (by have hh:=Finset.mem_Icc.mp hd;omega)]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.cast_id,mul_comm]
    _ = ∑j∈Finset.Icc A T, ∑d∈Finset.Icc 1 (T/A), if d*j≤T then f d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.sum_filter,origin_divisor_column_filter hA (Finset.mem_Icc.mp hj).1]

theorem origin_floor_triangle_sum (T A : ℕ) (hA : 1≤A) :
    2*(∑d∈Finset.Icc 1 (T/A),d*(T/d+1-A)) =
      ∑j∈Finset.Icc A T,(T/j)*(T/j+1) := by
  rw [weighted_origin_floor_double_sum T A hA,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _=>triangle_sum_twice _)

theorem actual_near_floor_swap (N K A : ℕ) (hA : 1≤A) :
    2*(∑d∈Finset.Icc 1 (N/(A*K)),d*(N/(K*d)+1-A)) =
      ∑j∈Finset.Icc A (N/K),(N/(K*j))*(N/(K*j)+1) := by
  simpa only [Nat.div_div_eq_div_mul,mul_comm K A] using origin_floor_triangle_sum (N/K) A hA

#print axioms actual_grid_start_slack
#print axioms start_code_mem_origin_pool
#print axioms actual_start_code_mem_origin_pool
#print axioms origin_start_pool_card
#print axioms origin_start_pool_payment_exact
#print axioms origin_start_pool_payment
#print axioms origin_start_pool_subset
#print axioms divisor_row_filter
#print axioms divisor_column_filter
#print axioms weighted_floor_double_sum
#print axioms floor_double_sum
#print axioms triangle_sum_twice
#print axioms weighted_floor_triangle_sum
#print axioms window_class_origin_card_sum
#print axioms actual_near_same_step_floor_card
#print axioms actual_near_same_step_origin_payment
#print axioms shifted_floor_payment_sum
#print axioms shifted_floor_triangle_payment
#print axioms actual_near_floor_step_budget
#print axioms actual_near_floor_band_budget
#print axioms actual_near_members_floor_budget
#print axioms origin_divisor_row_filter
#print axioms origin_divisor_column_filter
#print axioms weighted_origin_floor_double_sum
#print axioms origin_floor_triangle_sum
#print axioms actual_near_floor_swap
end
end JSP233.NearFloor63
