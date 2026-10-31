import Erdos272.Counting.APLinearCount49

/-! Actual exterior AP endpoint rectangles, summed over all nonunit steps. -/
namespace JSP233.APExterior50
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def ExteriorAP (F : Finset (Finset ℤ)) (L R : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>IsAP S ∧ 2≤S.card ∧ 2≤Step S ∧ Low S≤(L:ℤ) ∧ (R:ℤ)≤High S)

theorem actual_residue_interval_card {a d u v : ℕ} {S : Finset ℕ}
    (hsub : S⊆Finset.Icc u v) (hmod : ∀ x∈S,Nat.ModEq d a x) :
    S.card≤(v-u)/d+1 := by
  have hmaps : Set.MapsTo (fun x:ℕ=>(x-u)/d) (S:Set ℕ)
      (Finset.range ((v-u)/d+1)) := by
    intro x hx
    have hxv := (Finset.mem_Icc.mp (hsub hx)).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.sub_le_sub_right hxv u)))
  have hinj : Set.InjOn (fun x:ℕ=>(x-u)/d) (S:Set ℕ) := by
    intro x hx y hy he
    have hux := (Finset.mem_Icc.mp (hsub hx)).1
    have huy := (Finset.mem_Icc.mp (hsub hy)).1
    have hxy := (hmod x hx).symm.trans (hmod y hy)
    have hrem : Nat.ModEq d (x-u) (y-u) := Nat.ModEq.sub_right hux huy hxy
    change (x-u)%d=(y-u)%d at hrem
    change (x-u)/d=(y-u)/d at he
    have hnx := Nat.mod_add_div (x-u) d
    have hny := Nat.mod_add_div (y-u) d
    rw [he,hrem] at hnx
    omega
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmaps hinj

theorem actual_same_step_endpoint_rectangle {N L R d : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hne : ∀ S∈F,S.Nonempty)
    (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S)
    (hends : ∀ S∈F,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    F.card≤(L/d+1)*((N-R)/d+1) := by
  by_cases hf : F.Nonempty
  · obtain ⟨c,hc,hroot⟩ := actual_same_step_common_root hf hF hne hstep
    have hcN := (mem_ground N c).mp hc
    have hcc : (c.toNat:ℤ)=c := Int.toNat_of_nonneg (by omega)
    let X := {S // S∈F}
    let a (S:X) := (Low S.val).toNat
    let b (S:X) := (High S.val).toNat
    have haN : ∀ S:X,1≤Low S.val ∧ Low S.val≤N := fun S=>
      (mem_ground N _).mp (hF.1 S.val S.property (low_spec (hne S.val S.property)).1)
    have hbN : ∀ S:X,1≤High S.val ∧ High S.val≤N := fun S=>
      (mem_ground N _).mp (hF.1 S.val S.property (high_spec (hne S.val S.property)).1)
    have hac : ∀ S:X,(a S:ℤ)=Low S.val := fun S=>Int.toNat_of_nonneg (by have hh:=haN S;omega)
    have hbc : ∀ S:X,(b S:ℤ)=High S.val := fun S=>Int.toNat_of_nonneg (by have hh:=hbN S;omega)
    have hamod : ∀ S:X,Nat.ModEq d c.toNat (a S) := by
      intro S
      apply Nat.modEq_of_dvd
      rw [hac S,hcc]
      obtain ⟨p,hp⟩ := hstep S.val S.property
      exact apAt_dvd_sub hp (hroot S.val S.property) (low_spec (hne S.val S.property)).1
    have hbmod : ∀ S:X,Nat.ModEq d c.toNat (b S) := by
      intro S
      apply Nat.modEq_of_dvd
      rw [hbc S,hcc]
      obtain ⟨p,hp⟩ := hstep S.val S.property
      exact apAt_dvd_sub hp (hroot S.val S.property) (high_spec (hne S.val S.property)).1
    let A := (Finset.univ:Finset X).image a
    let B := (Finset.univ:Finset X).image b
    have hAcard : A.card≤L/d+1 := by
      have hh : A.card≤(L-1)/d+1 := by
        apply actual_residue_interval_card (a:=c.toNat)
        · intro x hx
          obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
          have hLo := (hends S.val S.property).1
          have hh := haN S
          have hc := hac S
          exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
        · intro x hx
          obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
          exact hamod S
      have hdiv : (L-1)/d≤L/d := Nat.div_le_div_right (Nat.sub_le L 1)
      omega
    have hBcard : B.card≤(N-R)/d+1 := by
      apply actual_residue_interval_card (a:=c.toNat)
      · intro x hx
        obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
        have hHi := (hends S.val S.property).2
        have hh := hbN S
        have hc := hbc S
        exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      · intro x hx
        obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
        exact hbmod S
    let f (S:X) := (a S,b S)
    have hinj : Function.Injective f := by
      intro S T he
      have ha : a S=a T := congrArg Prod.fst he
      have hb : b S=b T := congrArg Prod.snd he
      have hlo : Low S.val=Low T.val := by rw [←hac S,←hac T,ha]
      have hhi : High S.val=High T.val := by rw [←hbc S,←hbc T,hb]
      obtain ⟨p,hp⟩ := hstep S.val S.property
      obtain ⟨q,hq⟩ := hstep T.val T.property
      apply Subtype.ext
      exact same_step_equal_of_endpoints (hne S.val S.property) (hne T.val T.property) hp hq hlo hhi
    have hmaps : Set.MapsTo f (Finset.univ:Finset X) (A.product B) := by
      intro S _
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨S,Finset.mem_univ _,rfl⟩,
        Finset.mem_image.mpr ⟨S,Finset.mem_univ _,rfl⟩⟩
    have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
    have hcount : F.card≤A.card*B.card := by
      simpa only [Finset.card_univ,Finset.product_eq_sprod,Finset.card_product,X,Fintype.card_coe] using hh
    exact hcount.trans (Nat.mul_le_mul hAcard hBcard)
  · have hz : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hf
    simp only [hz,Finset.card_empty,Nat.zero_le]

theorem actual_same_step_endpoint_real {N L R d : ℕ} {F : Finset (Finset ℤ)}
    (hLN : L≤N) (hRN : R≤N) (hd : 0<d) (hF : Legal (Ground N) F)
    (hne : ∀ S∈F,S.Nonempty) (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S)
    (hends : ∀ S∈F,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    (F.card:ℝ)≤(L:ℝ)*(N-R)/(d:ℝ)^2+2*N/d+1 := by
  have hh := actual_same_step_endpoint_rectangle hF hne hstep hends
  have hhR : (F.card:ℝ)≤((L/d:ℕ)+1:ℝ)*(((N-R)/d:ℕ)+1:ℝ) := by exact_mod_cast hh
  have ha := Nat.cast_div_le (α:=ℝ) (m:=L) (n:=d)
  have hb := Nat.cast_div_le (α:=ℝ) (m:=N-R) (n:=d)
  rw [Nat.cast_sub hRN] at hb
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hRN' : (R:ℝ)≤N := by exact_mod_cast hRN
  have hLN' : (L:ℝ)≤N := by exact_mod_cast hLN
  have hprod : (F.card:ℝ)≤((L:ℝ)/d+1)*(((N:ℝ)-R)/d+1) :=
    hhR.trans (mul_le_mul (by linarith only [ha]) (by linarith only [hb]) (by positivity) (by positivity))
  have hsum : ((L:ℝ)+(N-R))/d≤2*N/d :=
    (div_le_div_iff_of_pos_right hdR).mpr (by have hh:=Nat.cast_nonneg (α:=ℝ) R;linarith)
  have hid : ((L:ℝ)/d+1)*(((N:ℝ)-R)/d+1)=
      (L:ℝ)*(N-R)/(d:ℝ)^2+((L:ℝ)+(N-R))/d+1 := by ring
  linarith only [hprod,hsum,hid]

theorem reciprocal_square_tail_two (N : ℕ) :
    (∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)≤2/3 := by
  by_cases hN : 1≤N
  · have hsplit : Finset.Icc 1 N=insert 1 (Finset.Icc 2 N) := by
      ext d
      simp only [Finset.mem_Icc,Finset.mem_insert]
      omega
    have hh := square_reciprocal_bound N
    dsimp only [SquareReciprocal] at hh
    rw [hsplit,Finset.sum_insert (by simp)] at hh
    norm_num only [Nat.cast_one,one_pow,div_one] at hh
    linarith only [hh]
  · have hz : N=0 := by omega
    norm_num [hz]

theorem actual_large_step_endpoint_count {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hLN : L≤N) (hRN : R≤N) (hF : Legal (Ground N) F)
    (hAP : ∀ S∈F,IsAP S) (htwo : ∀ S∈F,2≤S.card)
    (hlarge : ∀ S∈F,2≤Step S) (hends : ∀ S∈F,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    (F.card:ℝ)≤(2/3)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hmaps : Set.MapsTo Step (F:Set (Finset ℤ)) (Finset.Icc 2 N) := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨hlarge S hS,actual_step_bound (hF.1 S hS) (hAP S hS) (htwo S hS)⟩
  have hpart : (F.card:ℝ)=∑ d∈Finset.Icc 2 N,((F.filter (fun S=>Step S=d)).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hbound : ∀ d∈Finset.Icc 2 N,((F.filter (fun S=>Step S=d)).card:ℝ)≤
      (L:ℝ)*(N-R)/(d:ℝ)^2+2*N/d+1 := by
    intro d hd
    have hAF : F.filter (fun S=>Step S=d)⊆F := Finset.filter_subset _ _
    have hlegal : Legal (Ground N) (F.filter (fun S=>Step S=d)) :=
      ⟨fun S hS=>hF.1 S (hAF hS),fun S hS T hT hne=>hF.2 S (hAF hS) T (hAF hT) hne⟩
    apply actual_same_step_endpoint_real hLN hRN (by have hh:=Finset.mem_Icc.mp hd;omega) hlegal
      (fun S hS=>isAP_nonempty (hAP S (hAF hS)))
    · intro S hS
      obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
      obtain ⟨_,p,hp⟩ := actual_step (hAP S hSF)
      exact ⟨p,by simpa only [hSd] using hp⟩
    · exact fun S hS=>hends S (hAF hS)
  have hinv : (∑ d∈Finset.Icc 2 N,(d:ℝ)⁻¹)≤HarmonicAbel29.Harmonic N := by
    simp only [HarmonicAbel29.Harmonic,one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hd,hdN⟩ := Finset.mem_Icc.mp hd
      exact Finset.mem_Icc.mpr ⟨by omega,hdN⟩
    · intro d _ _
      positivity
  have hcardI : ((Finset.Icc 2 N).card:ℝ)≤N := by
    exact_mod_cast (show (Finset.Icc 2 N).card≤N by rw [Nat.card_Icc];omega)
  have hsum : (F.card:ℝ)≤(L:ℝ)*(N-R)*(∑ d∈Finset.Icc 2 N,(1:ℝ)/(d:ℝ)^2)+
      2*N*(∑ d∈Finset.Icc 2 N,(d:ℝ)⁻¹)+(Finset.Icc 2 N).card := by
    calc
      _≤∑ d∈Finset.Icc 2 N,((L:ℝ)*(N-R)/(d:ℝ)^2+2*N/d+1) := by
        rw [hpart]
        exact Finset.sum_le_sum hbound
      _=_ := by simp only [div_eq_mul_inv,one_mul,Finset.sum_add_distrib,←Finset.mul_sum,
        Finset.sum_const,nsmul_eq_mul,mul_one]
  have hRN' : (R:ℝ)≤N := by exact_mod_cast hRN
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail_two N)
    (show (0:ℝ)≤(L:ℝ)*(N-R) by positivity)
  have hharm := mul_le_mul_of_nonneg_left hinv (show (0:ℝ)≤2*N by positivity)
  linarith only [hsum,hquad,hharm,hcardI]

theorem actual_exterior_AP_count {N L R : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hLN : L≤N) (hRN : R≤N) :
    ((ExteriorAP F L R).card:ℝ)≤(2/3)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hEF : ExteriorAP F L R⊆F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (ExteriorAP F L R) :=
    ⟨fun S hS=>hF.1 S (hEF hS),fun S hS T hT hne=>hF.2 S (hEF hS) T (hEF hT) hne⟩
  apply actual_large_step_endpoint_count hLN hRN hlegal
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.2.1
  · exact fun S hS=>(Finset.mem_filter.mp hS).2.2.2.2

theorem actual_selected_exterior_count {N L R : ℕ} {F E : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hLN : L≤N) (hRN : R≤N) (hEF : E⊆F)
    (hAP : ∀ S∈E,IsAP S) (htwo : ∀ S∈E,2≤S.card)
    (hlarge : ∀ S∈E,2≤Step S) (hends : ∀ S∈E,Low S≤(L:ℤ) ∧ (R:ℤ)≤High S) :
    (E.card:ℝ)≤(2/3)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hs : E⊆ExteriorAP F L R := by
    intro S hS
    exact Finset.mem_filter.mpr ⟨hEF hS,hAP S hS,htwo S hS,hlarge S hS,hends S hS⟩
  have hh : (E.card:ℝ)≤(ExteriorAP F L R).card := by exact_mod_cast Finset.card_le_card hs
  exact hh.trans (actual_exterior_AP_count hF hLN hRN)

#print axioms actual_residue_interval_card
#print axioms actual_same_step_endpoint_rectangle
#print axioms actual_same_step_endpoint_real
#print axioms reciprocal_square_tail_two
#print axioms actual_large_step_endpoint_count
#print axioms actual_exterior_AP_count
#print axioms actual_selected_exterior_count
end
end JSP233.APExterior50
