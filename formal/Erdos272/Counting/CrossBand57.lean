import Erdos272.Resources.WeightedFar38
import Erdos272.Counting.SmallSpan48
import Erdos272.Traces.FractionalWitness55

namespace JSP233.CrossBand57
open StarCompletion APGeometry TraceWitnessCodes36 FarWitness36 NearAP36
open WeightedFar38 SmallSpan48
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Scale (K j : ℕ) : ℕ := 2^j*K

def Band (F : Finset (Finset ℤ)) (L j : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>Scale L j<S.card ∧ S.card≤2*Scale L j)

def LargeMembers (F : Finset (Finset ℤ)) (L : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>L<S.card)

def FarMembers (F : Finset (Finset ℤ)) (L U : ℕ) : Finset (Finset ℤ) :=
  (LargeMembers F L).filter (fun S=>∃j:ℕ,S∈Band F L j ∧ ¬HasNearAPCore (Scale U j) S)

def NearMembers (F : Finset (Finset ℤ)) (L U : ℕ) : Finset (Finset ℤ) :=
  (LargeMembers F L).filter (fun S=>¬∃j:ℕ,S∈Band F L j ∧ ¬HasNearAPCore (Scale U j) S)

theorem actual_band_exists {L n : ℕ} (hL : 0<L) (hn : L<n) :
    ∃j:ℕ,Scale L j<n ∧ n≤2*Scale L j := by
  let q := (n-1)/L
  have hq : 0<q := Nat.div_pos (by omega) hL
  let j := Nat.log 2 q
  have hl := Nat.pow_log_le_self 2 (by omega : q≠0)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) q
  have hprod := Nat.div_mul_le_self (n-1) L
  have hquot : n-1<2^(j+1)*L := (Nat.div_lt_iff_lt_mul hL).mp hu
  change 2^j≤q at hl
  have hh := Nat.mul_le_mul_right L hl
  have he : n-1+1=n := by omega
  refine ⟨j,?_,?_⟩
  · dsimp only [Scale]
    change q*L≤n-1 at hprod
    omega
  · dsimp only [Scale]
    rw [pow_succ] at hquot
    nlinarith only [hquot,he]

theorem actual_band_unique {L n i j : ℕ}
    (hi : Scale L i<n ∧ n≤2*Scale L i)
    (hj : Scale L j<n ∧ n≤2*Scale L j) : i=j := by
  have hnot : ∀a b:ℕ,a<b→Scale L a<n→n≤2*Scale L a→Scale L b<n→False := by
    intro a b hab _ha hna hbn
    have hp := Nat.pow_le_pow_right (by decide : 1≤2) (show a+1≤b by omega)
    have hm := Nat.mul_le_mul_right L hp
    rw [pow_succ] at hm
    dsimp only [Scale] at *
    nlinarith only [hm,hna,hbn]
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij|hji
  · exact hnot i j hij hi.1 hi.2 hj.1
  · exact hnot j i hji hj.1 hj.2 hi.1

theorem actual_member_unique_band {N L : ℕ} {F : Finset (Finset ℤ)}
    (hL : 0<L) (hground : ∀S∈F,S⊆Ground N) {S : Finset ℤ}
    (hS : S∈F) (hlarge : L<S.card) : ∃!j:ℕ,S∈Band F L j ∧ j≤N := by
  obtain ⟨j,hlo,hhi⟩ := actual_band_exists hL hlarge
  have hp : j<2^j := Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul_left (2^j) (show 1≤L by omega)
  have hN : S.card≤N := by simpa only [ground_card] using Finset.card_le_card (hground S hS)
  have hjN : j≤N := by dsimp only [Scale] at hlo;omega
  refine ⟨j,⟨Finset.mem_filter.mpr ⟨hS,hlo,hhi⟩,hjN⟩,?_⟩
  intro i hi
  exact actual_band_unique (Finset.mem_filter.mp hi.1).2 ⟨hlo,hhi⟩

theorem coefficient_growth_shift (C : ℕ→ℝ)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (j h : ℕ) : C (j+h)≤(2:ℝ)^h*C j := by
  induction h with
  | zero => simp
  | succ h ih =>
    calc
      C (j+(h+1))=C ((j+h)+1) := by congr 1
      _≤2*C (j+h) := hgrowth _
      _≤2*((2:ℝ)^h*C j) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _=(2:ℝ)^(h+1)*C j := by rw [pow_succ];ring

theorem actual_scale_shift (K j h : ℕ) : Scale K (j+h)=2^h*Scale K j := by
  dsimp only [Scale]
  rw [pow_add]
  ring

theorem actual_uniform_certificate {K h j : ℕ} {C : ℕ→ℝ} {W : ℝ}
    (hgrowth : ∀i:ℕ,C (i+1)≤2*C i) (hhj : h≤j) (hW : 0≤W)
    (hcert : (Scale K j:ℝ)^2≤C j*W) : (Scale K h:ℝ)^2≤C h*W := by
  let e := j-h
  have he : h+e=j := Nat.add_sub_of_le hhj
  have hc : C j≤(2:ℝ)^e*C h := by simpa only [he] using coefficient_growth_shift C hgrowth h e
  have hs : (Scale K j:ℝ)=(2:ℝ)^e*Scale K h := by
    rw [←he,actual_scale_shift]
    push_cast
    rfl
  have hp : 0<(2:ℝ)^e := by positivity
  have hp1 : 1≤(2:ℝ)^e := one_le_pow₀ (by norm_num)
  have hh := hcert.trans (mul_le_mul_of_nonneg_right hc hW)
  rw [hs] at hh
  have heq : ((2:ℝ)^e*Scale K h)^2=(2:ℝ)^e*((2:ℝ)^e*(Scale K h)^2) := by ring
  rw [heq,mul_assoc] at hh
  have hcancel := (mul_le_mul_iff_right₀ hp).mp hh
  nlinarith only [hcancel,hp1,sq_nonneg (Scale K h:ℝ)]

theorem actual_far_data {F : Finset (Finset ℤ)} {L U : ℕ} {S : Finset ℤ}
    (hS : S∈FarMembers F L U) :
    S∈F ∧ L<S.card ∧ ∃j:ℕ,S∈Band F L j ∧ ¬HasNearAPCore (Scale U j) S := by
  obtain ⟨hlarge,hfar⟩ := Finset.mem_filter.mp hS
  obtain ⟨hF,hL⟩ := Finset.mem_filter.mp hlarge
  exact ⟨hF,hL,hfar⟩

theorem actual_three_way_card (F : Finset (Finset ℤ)) (L U : ℕ) :
    (SpanMembers F L).card+(NearMembers F L U).card+(FarMembers F L U).card=F.card := by
  have hs := Finset.card_filter_add_card_filter_not (s:=F) (fun S=>S.card≤L)
  have hl := Finset.card_filter_add_card_filter_not (s:=LargeMembers F L)
    (fun S=>∃j:ℕ,S∈Band F L j ∧ ¬HasNearAPCore (Scale U j) S)
  have he : F.filter (fun S=>¬S.card≤L)=LargeMembers F L := by simp only [LargeMembers,not_le]
  change (SpanMembers F L).card+(F.filter (fun S=>¬S.card≤L)).card=F.card at hs
  rw [he] at hs
  change (FarMembers F L U).card+(NearMembers F L U).card=(LargeMembers F L).card at hl
  omega

theorem actual_small_nonempty_far_budget {N K L U : ℕ} {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j)
    (hsmall : (SpanMembers F L).Nonempty)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K^2≤(L:ℝ)*C 0*N.choose 2 := by
  obtain ⟨A,hA⟩ := hsmall
  have hC0 := hC 0
  obtain ⟨hAF,hAL⟩ := Finset.mem_filter.mp hA
  have hMF : FarMembers F L U⊆F := fun S hS=>(actual_far_data hS).1
  have hLM : Legal (Ground N) (FarMembers F L U) :=
    ⟨fun S hS=>hlegal.1 S (hMF hS),fun S hS T hT hne=>hlegal.2 S (hMF hS) T (hMF hT) hne⟩
  have hb := actual_real_transversal_budget N K (C 0) (FarMembers F L U) A (hC 0) hLM (by
    intro S hS
    obtain ⟨hSF,hSL,j,hSj,hfar⟩ := actual_far_data hS
    have hne : S≠A := by intro he;subst S;omega
    obtain ⟨c,hc⟩ := isAP_nonempty (hlegal.2 S hSF A hAF hne)
    obtain ⟨hcS,hcA⟩ := Finset.mem_inter.mp hc
    refine ⟨c,hcS,hcA,?_⟩
    have hh := actual_uniform_certificate hgrowth (Nat.zero_le j) (by positivity)
      (hcert j S hSj hfar c hcS)
    simpa only [Scale,pow_zero,one_mul] using hh)
  have hAR : (A.card:ℝ)≤L := by exact_mod_cast hAL
  have hh := mul_le_mul_of_nonneg_left hAR (show 0≤C 0*(N.choose 2:ℝ) by positivity)
  nlinarith only [hb,hh]

theorem actual_small_empty_first_band {N L : ℕ} {F : Finset (Finset ℤ)}
    (hL : 0<L) (hlegal : Legal (Ground N) F)
    (hsmall : SpanMembers F L=∅) (hne : F.Nonempty) :
    ∃h:ℕ,∃A∈Band F L h,h≤N ∧ A.Nonempty ∧
      ∀j:ℕ,(Band F L j).Nonempty→h≤j := by
  have hex : ∃j:ℕ,(Band F L j).Nonempty := by
    obtain ⟨S,hS⟩ := hne
    have hlo : L<S.card := by
      by_contra hn
      have hm : S∈SpanMembers F L := Finset.mem_filter.mpr ⟨hS,by omega⟩
      simp [hsmall] at hm
    obtain ⟨j,hj,_huniq⟩ := actual_member_unique_band hL hlegal.1 hS hlo
    exact ⟨j,S,hj.1⟩
  let h := Nat.find hex
  obtain ⟨A,hA⟩ := Nat.find_spec hex
  change A∈Band F L h at hA
  have hdata := (Finset.mem_filter.mp hA).2
  have hAN : A.Nonempty := Finset.card_pos.mp (by omega)
  have hp : h<2^h := Nat.lt_two_pow_self
  have hm := Nat.mul_le_mul_left (2^h) (show 1≤L by omega)
  have hN : A.card≤N := by
    simpa only [ground_card] using Finset.card_le_card (hlegal.1 A (Finset.mem_filter.mp hA).1)
  refine ⟨h,A,hA,?_,hAN,?_⟩
  · dsimp only [Scale] at hdata
    omega
  · intro j hj
    exact Nat.find_min' hex hj

theorem actual_small_empty_far_budget {N K L U : ℕ} {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hL : 0<L) (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (hsmall : SpanMembers F L=∅)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K^2≤2*(L:ℝ)*C 0*N.choose 2 := by
  have hC0 := hC 0
  rcases F.eq_empty_or_nonempty with he|hne
  · subst F
    simp only [FarMembers,LargeMembers,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,zero_mul]
    positivity
  obtain ⟨h,A,hA,_hN,hAN,hfirst⟩ := actual_small_empty_first_band hL hlegal hsmall hne
  have hCh := hC h
  have hAF := (Finset.mem_filter.mp hA).1
  have hAL : (A.card:ℝ)≤2*(Scale L h:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hA).2.2
  have hMF : FarMembers F L U⊆F := fun S hS=>(actual_far_data hS).1
  have hLM : Legal (Ground N) (FarMembers F L U) :=
    ⟨fun S hS=>hlegal.1 S (hMF hS),fun S hS T hT hne=>hlegal.2 S (hMF hS) T (hMF hT) hne⟩
  have hb := actual_real_transversal_budget N (Scale K h) (C h) (FarMembers F L U) A (hC h) hLM (by
    intro S hS
    obtain ⟨hSF,_hSL,j,hSj,hfar⟩ := actual_far_data hS
    obtain ⟨c,hc⟩ := actual_member_hits_family hlegal hAF hAN S hSF
    obtain ⟨hcS,hcA⟩ := Finset.mem_inter.mp hc
    exact ⟨c,hcS,hcA,actual_uniform_certificate hgrowth (hfirst j ⟨S,hSj⟩)
      (by positivity) (hcert j S hSj hfar c hcS)⟩)
  have hg : C h≤(2:ℝ)^h*C 0 := by simpa only [zero_add] using coefficient_growth_shift C hgrowth 0 h
  have ha := mul_le_mul_of_nonneg_left hAL (show 0≤C h*(N.choose 2:ℝ) by positivity)
  have hh := mul_le_mul_of_nonneg_right hg (show 0≤2*(Scale L h:ℝ)*(N.choose 2:ℝ) by positivity)
  have hscaled : ((2:ℝ)^h)^2*(((FarMembers F L U).card:ℝ)*K^2)≤
      ((2:ℝ)^h)^2*(2*(L:ℝ)*C 0*N.choose 2) := by
    dsimp only [Scale] at hb ha hh
    push_cast at hb ha hh
    nlinarith only [hb,ha,hh]
  exact (mul_le_mul_iff_right₀ (by positivity : 0<((2:ℝ)^h)^2)).mp hscaled

theorem actual_small_empty_far_quadratic {N K L U : ℕ} {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hL : 0<L) (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (hsmall : SpanMembers F L=∅)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K^2≤(L:ℝ)*C 0*(N:ℝ)^2 := by
  have hh := actual_small_empty_far_budget hL hlegal hC hgrowth hsmall hcert
  have hc := mul_le_mul_of_nonneg_left (choose_two_real_le_quadratic N)
    (show 0≤2*(L:ℝ)*C 0 by have := hC 0;positivity)
  nlinarith only [hh,hc]

theorem actual_small_nonempty_far_quadratic {N K L U : ℕ} {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (hsmall : (SpanMembers F L).Nonempty)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K^2≤((L:ℝ)/2)*C 0*(N:ℝ)^2 := by
  have hh := actual_small_nonempty_far_budget hlegal hC hgrowth hsmall hcert
  have hc := mul_le_mul_of_nonneg_left (choose_two_real_le_quadratic N)
    (show 0≤(L:ℝ)*C 0 by have := hC 0;positivity)
  nlinarith only [hh,hc]

theorem actual_small_empty_far_scaled {N K L U : ℕ} {a : ℝ}
    {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hL : 0<L) (hK : 0<K) (hcut : (L:ℝ)≤a*K)
    (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (hsmall : SpanMembers F L=∅)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K≤a*C 0*(N:ℝ)^2 := by
  have hb := actual_small_empty_far_quadratic hL hlegal hC hgrowth hsmall hcert
  have hh := mul_le_mul_of_nonneg_right hcut
    (show 0≤C 0*(N:ℝ)^2 by have := hC 0;positivity)
  have hm : (((FarMembers F L U).card:ℝ)*K)*(K:ℝ)≤(a*C 0*(N:ℝ)^2)*(K:ℝ) := by
    nlinarith only [hb,hh]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hK : (0:ℝ)<K)).mp hm

theorem actual_small_nonempty_far_scaled {N K L U : ℕ} {a : ℝ}
    {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hK : 0<K) (hcut : (L:ℝ)≤a*K)
    (hlegal : Legal (Ground N) F) (hC : ∀j:ℕ,0≤C j)
    (hgrowth : ∀j:ℕ,C (j+1)≤2*C j) (hsmall : (SpanMembers F L).Nonempty)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    ((FarMembers F L U).card:ℝ)*K≤(a/2)*C 0*(N:ℝ)^2 := by
  have hb := actual_small_nonempty_far_quadratic hlegal hC hgrowth hsmall hcert
  have hh := mul_le_mul_of_nonneg_right hcut
    (show 0≤C 0*(N:ℝ)^2 by have := hC 0;positivity)
  have hm : (((FarMembers F L U).card:ℝ)*K)*(K:ℝ)≤((a/2)*C 0*(N:ℝ)^2)*(K:ℝ) := by
    nlinarith only [hb,hh]
  exact (mul_le_mul_iff_left₀ (by exact_mod_cast hK : (0:ℝ)<K)).mp hm

theorem actual_near_data {L U : ℕ} {F : Finset (Finset ℤ)}
    (hL : 0<L) {S : Finset ℤ} (hS : S∈NearMembers F L U) :
    S∈F ∧ ∃j:ℕ,S∈Band F L j ∧ HasNearAPCore (Scale U j) S := by
  obtain ⟨hlarge,hnot⟩ := Finset.mem_filter.mp hS
  obtain ⟨hF,hSL⟩ := Finset.mem_filter.mp hlarge
  obtain ⟨j,hlo,hhi⟩ := actual_band_exists hL hSL
  have hj : S∈Band F L j := Finset.mem_filter.mpr ⟨hF,hlo,hhi⟩
  refine ⟨hF,j,hj,?_⟩
  by_contra hn
  exact hnot ⟨j,hj,hn⟩

theorem actual_near_joint_budget {N L U A b : ℕ} {F : Finset (Finset ℤ)}
    (hL : 0<L) (hU : 0<U) (hA : 2≤A)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hlow : (A+1)*U≤L) (hhigh : 2*L≤b*U) :
    (A:ℝ)*U*(NearMembers F L U).card≤6*((b:ℝ)+1)*(N:ℝ)^2 := by
  have hex : ∀S:Finset ℤ,∃j:ℕ,S∈NearMembers F L U→S∈Band F L j ∧ HasNearAPCore (Scale U j) S := by
    intro S
    by_cases hs : S∈NearMembers F L U
    · obtain ⟨_hSF,j,hj⟩ := actual_near_data hL hs
      exact ⟨j,fun _=>hj⟩
    · exact ⟨0,fun hh=>False.elim (hs hh)⟩
  choose level hl using hex
  have hNF : NearMembers F L U⊆F := fun S hS=>(actual_near_data hL hS).1
  have hNL : Legal (Ground N) (NearMembers F L U) :=
    ⟨fun S hS=>hlegal.1 S (hNF hS),fun S hS T hT hne=>hlegal.2 S (hNF hS) T (hNF hT) hne⟩
  apply FractionalWitness55.actual_general_dyadic_near_budget level hNL hU hA
    (fun S hS=>hbad S (hNF hS))
  · intro S hS
    have hs := (Finset.mem_filter.mp (hl S hS).1).2.1
    have hm := Nat.mul_le_mul_left (2^(level S)) hlow
    dsimp only [Scale] at hs
    nlinarith only [hs,hm]
  · intro S hS
    have hs := (Finset.mem_filter.mp (hl S hS).1).2.2
    have hm := Nat.mul_le_mul_left (2^(level S)) hhigh
    dsimp only [Scale] at hs
    nlinarith only [hs,hm]
  · intro S hS
    exact (hl S hS).2

theorem actual_family_small_empty {N K L U A b : ℕ} {a : ℝ}
    {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hL : 0<L) (hK : 0<K) (hU : 0<U) (hA : 2≤A)
    (hcut : (L:ℝ)≤a*K) (hlow : (A+1)*U≤L) (hhigh : 2*L≤b*U)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hC : ∀j:ℕ,0≤C j) (hgrowth : ∀j:ℕ,C (j+1)≤2*C j)
    (hsmall : SpanMembers F L=∅)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    (F.card:ℝ)*K≤(6*((b:ℝ)+1)*K/((A:ℝ)*U)+a*C 0)*(N:ℝ)^2 := by
  have hf := actual_small_empty_far_scaled hL hK hcut hlegal hC hgrowth hsmall hcert
  have hn := actual_near_joint_budget hL hU hA hlegal hbad hlow hhigh
  have hd : 0<(A:ℝ)*U := by
    have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
    have hu : (0:ℝ)<U := by exact_mod_cast hU
    exact mul_pos ha hu
  have hh : ((NearMembers F L U).card:ℝ)≤6*((b:ℝ)+1)*(N:ℝ)^2/((A:ℝ)*U) :=
    (le_div_iff₀ hd).mpr (by nlinarith only [hn])
  have hp := actual_three_way_card F L U
  rw [hsmall,Finset.card_empty,zero_add] at hp
  have hpR : ((NearMembers F L U).card:ℝ)+((FarMembers F L U).card:ℝ)=F.card := by exact_mod_cast hp
  have hmul := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤K by positivity)
  have he : (6*((b:ℝ)+1)*(N:ℝ)^2/((A:ℝ)*U))*(K:ℝ)=
      (6*((b:ℝ)+1)*K/((A:ℝ)*U))*(N:ℝ)^2 := by ring
  rw [he] at hmul
  nlinarith only [hf,hmul,hpR]

theorem actual_family_small_nonempty {N r K L U A b : ℕ} {a : ℝ}
    {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hN : 4≤N) (hr : 2≤r) (hL : 0<L) (hK : 0<K) (hU : 0<U) (hA : 2≤A)
    (hcut : (L:ℝ)≤a*K) (hlow : (A+1)*U≤L) (hhigh : 2*L≤b*U)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,r*S.card≤N) (hkernel : PrivateFinset.Kernel (Ground N) F=∅)
    (hC : ∀j:ℕ,0≤C j) (hgrowth : ∀j:ℕ,C (j+1)≤2*C j)
    (hsmall : (SpanMembers F L).Nonempty)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    (F.card:ℝ)*K≤
      max ((((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))))
        ((L:ℝ)^2*(N:ℝ))*K+
      (6*((b:ℝ)+1)*K/((A:ℝ)*U)+(a/2)*C 0)*(N:ℝ)^2 := by
  have hf := actual_small_nonempty_far_scaled hK hcut hlegal hC hgrowth hsmall hcert
  have hn := actual_near_joint_budget hL hU hA hlegal hbad hlow hhigh
  have hs := actual_span_empty_kernel hN hr hL hlegal hbad hsize hkernel
  have hd : 0<(A:ℝ)*U := by
    have ha : (0:ℝ)<A := by exact_mod_cast (show 0<A by omega)
    have hu : (0:ℝ)<U := by exact_mod_cast hU
    exact mul_pos ha hu
  have hh : ((NearMembers F L U).card:ℝ)≤6*((b:ℝ)+1)*(N:ℝ)^2/((A:ℝ)*U) :=
    (le_div_iff₀ hd).mpr (by nlinarith only [hn])
  have hp := actual_three_way_card F L U
  have hpR : ((SpanMembers F L).card:ℝ)+((NearMembers F L U).card:ℝ)+
      ((FarMembers F L U).card:ℝ)=F.card := by exact_mod_cast hp
  have hnear := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤K by positivity)
  have hsmallmul := mul_le_mul_of_nonneg_right hs (show (0:ℝ)≤K by positivity)
  have he : (6*((b:ℝ)+1)*(N:ℝ)^2/((A:ℝ)*U))*(K:ℝ)=
      (6*((b:ℝ)+1)*K/((A:ℝ)*U))*(N:ℝ)^2 := by ring
  rw [he] at hnear
  nlinarith only [hf,hnear,hsmallmul,hpR]

theorem actual_family_two_small_branches {N r K L U A b : ℕ} {a : ℝ}
    {F : Finset (Finset ℤ)} {C : ℕ→ℝ}
    (hN : 4≤N) (hr : 2≤r) (hL : 0<L) (hK : 0<K) (hU : 0<U) (hA : 2≤A)
    (hcut : (L:ℝ)≤a*K) (hlow : (A+1)*U≤L) (hhigh : 2*L≤b*U)
    (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hsize : ∀S∈F,r*S.card≤N) (hkernel : PrivateFinset.Kernel (Ground N) F=∅)
    (hC : ∀j:ℕ,0≤C j) (hgrowth : ∀j:ℕ,C (j+1)≤2*C j)
    (hcert : ∀j:ℕ,∀S∈Band F L j,¬HasNearAPCore (Scale U j) S→∀c∈S,
      (Scale K j:ℝ)^2≤C j*(StructuralPairs c S).card) :
    (SpanMembers F L=∅ ∧ (F.card:ℝ)*K≤
      (6*((b:ℝ)+1)*K/((A:ℝ)*U)+a*C 0)*(N:ℝ)^2) ∨
    ((SpanMembers F L).Nonempty ∧ (F.card:ℝ)*K≤
      max ((((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))))
        ((L:ℝ)^2*(N:ℝ))*K+
      (6*((b:ℝ)+1)*K/((A:ℝ)*U)+(a/2)*C 0)*(N:ℝ)^2) := by
  rcases (SpanMembers F L).eq_empty_or_nonempty with he|hne
  · exact Or.inl ⟨he,actual_family_small_empty hL hK hU hA hcut hlow hhigh hlegal hbad hC hgrowth he hcert⟩
  · exact Or.inr ⟨hne,actual_family_small_nonempty hN hr hL hK hU hA hcut hlow hhigh
      hlegal hbad hsize hkernel hC hgrowth hne hcert⟩

#print axioms actual_band_exists
#print axioms actual_band_unique
#print axioms actual_member_unique_band
#print axioms coefficient_growth_shift
#print axioms actual_scale_shift
#print axioms actual_uniform_certificate
#print axioms actual_far_data
#print axioms actual_three_way_card
#print axioms actual_small_nonempty_far_budget
#print axioms actual_small_empty_first_band
#print axioms actual_small_empty_far_budget
#print axioms actual_small_empty_far_quadratic
#print axioms actual_small_nonempty_far_quadratic
#print axioms actual_small_empty_far_scaled
#print axioms actual_small_nonempty_far_scaled
#print axioms actual_near_data
#print axioms actual_near_joint_budget
#print axioms actual_family_small_empty
#print axioms actual_family_small_nonempty
#print axioms actual_family_two_small_branches
end
end JSP233.CrossBand57
