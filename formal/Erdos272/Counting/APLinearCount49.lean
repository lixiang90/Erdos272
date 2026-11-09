module

public import Erdos272.Counting.APCount41
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Actual short-AP and prescribed-endpoint counts, with no capacity input. -/
namespace JSP233.APLinearCount49
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

theorem singleton_of_root_card_le_one {S : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hcard : S.card≤1) : S={c} := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard x hx c hc)
  · intro hx
    exact (Finset.mem_singleton.mp hx).symm ▸ hc

theorem actual_rooted_short_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hcard : ∀ S∈F,2≤S.card ∧ S.card≤3) (hroot : ∀ S∈F,c∈S) :
    F.card≤6*N := by
  let X := {S // S∈F}
  let i (S : X) := Index (Low S.val) c (Step S.val)
  have hs : ∀ S:X,0<Step S.val ∧ Step S.val≤N ∧ i S<S.val.card ∧
      Low S.val+(i S:ℤ)*(Step S.val:ℤ)=c := by
    intro S
    obtain ⟨hd,p,hp⟩ := actual_step (hAP S.val S.property)
    have hne : S.val.Nonempty := ⟨c,hroot S.val S.property⟩
    have hl := low_spec hne
    have hb := high_spec hne
    have hi := index_equation (hl.2 c (hroot S.val S.property))
      (apAt_dvd_sub hp hl.1 (hroot S.val S.property))
    have hspan := apAt_span_eq hp hne
    have hcb := hb.2 c (hroot S.val S.property)
    have hdN := actual_step_bound (hsub S.val S.property) (hAP S.val S.property)
      (hcard S.val S.property).1
    have hLow : Low S.val=S.val.min' hne := by simp only [Low,dif_pos hne]
    have hHigh : High S.val=S.val.max' hne := by simp only [High,dif_pos hne]
    rw [←hLow,←hHigh] at hspan
    have hic : i S<S.val.card := by
      have hdZ : (0:ℤ)<Step S.val := by exact_mod_cast hd
      change Low S.val+(i S:ℤ)*(Step S.val:ℤ)=c at hi
      have hh : (i S:ℤ)<S.val.card := by nlinarith
      exact_mod_cast hh
    exact ⟨hd,hdN,hic,hi⟩
  let f (S:X) : ℕ×ℕ×ℕ := (S.val.card,i S,Step S.val)
  have hinj : Function.Injective f := by
    intro S T he
    have hk : S.val.card=T.val.card := congrArg Prod.fst he
    have hi : i S=i T := congrArg (fun q:ℕ×ℕ×ℕ=>q.2.1) he
    have hd : Step S.val=Step T.val := congrArg (fun q:ℕ×ℕ×ℕ=>q.2.2) he
    have hlo : Low S.val=Low T.val := by
      have hS := (hs S).2.2.2
      have hT := (hs T).2.2.2
      rw [hi,hd] at hS
      omega
    have hnS : S.val.Nonempty := ⟨c,hroot S.val S.property⟩
    have hnT : T.val.Nonempty := ⟨c,hroot T.val T.property⟩
    obtain ⟨_,p,hp⟩ := actual_step (hAP S.val S.property)
    obtain ⟨_,q,hq⟩ := actual_step (hAP T.val T.property)
    have hbS : High S.val-Low S.val=(Step S.val:ℤ)*((S.val.card:ℤ)-1) := by
      simpa only [High,Low,dif_pos hnS] using apAt_span_eq hp hnS
    have hbT : High T.val-Low T.val=(Step T.val:ℤ)*((T.val.card:ℤ)-1) := by
      simpa only [High,Low,dif_pos hnT] using apAt_span_eq hq hnT
    have hhi : High S.val=High T.val := by rw [hlo,hd,hk] at hbS;omega
    apply Subtype.ext
    apply same_step_equal_of_endpoints hnS hnT hp (by simpa only [hd] using hq) hlo hhi
  have hmaps : Set.MapsTo f (Finset.univ:Finset X)
      ((Finset.Icc 2 3).product ((Finset.range 3).product (Finset.Icc 1 N))) := by
    intro S _
    have hh := hs S
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hcard S.val S.property),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change i S<3;have h:=hcard S.val S.property;omega),
        Finset.mem_Icc.mpr ⟨hh.1,hh.2.1⟩⟩⟩
  have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  norm_num [X,Finset.card_product] at hh
  omega

theorem actual_rooted_small_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hcard : ∀ S∈F,S.card≤3) (hroot : ∀ S∈F,c∈S) :
    F.card≤6*N+1 := by
  let A := F.filter (fun S=>2≤S.card)
  let B := F.filter (fun S=>¬2≤S.card)
  have hA : A.card≤6*N := actual_rooted_short_AP_count
    (fun S hS=>hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hAP S (Finset.mem_filter.mp hS).1)
    (fun S hS=>⟨(Finset.mem_filter.mp hS).2,hcard S (Finset.mem_filter.mp hS).1⟩)
    (fun S hS=>hroot S (Finset.mem_filter.mp hS).1)
  have hB : B.card≤1 := by
    apply Finset.card_le_one.mpr
    intro S hS T hT
    obtain ⟨hSF,hsizeS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF,hsizeT⟩ := Finset.mem_filter.mp hT
    rw [singleton_of_root_card_le_one (hroot S hSF) (by omega),
      singleton_of_root_card_le_one (hroot T hTF) (by omega)]
  have hp := Finset.card_filter_add_card_filter_not (s:=F) (fun S=>2≤S.card)
  change A.card+B.card=F.card at hp
  omega

theorem actual_small_AP_family_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S) (hcard : ∀ S∈F,S.card≤3) :
    F.card≤18*N+3 := by
  by_cases hne : F.Nonempty
  · obtain ⟨S₀,hS₀⟩ := hne
    let D (c:ℤ) := F.filter (fun S=>c∈S)
    have hcover : F⊆S₀.biUnion D := by
      intro S hS
      have hh : (S₀∩S).Nonempty := by
        by_cases he : S₀=S
        · simpa only [he,Finset.inter_self] using isAP_nonempty (hAP S hS)
        · exact isAP_nonempty (hF.2 S₀ hS₀ S hS he)
      obtain ⟨c,hc⟩ := hh
      obtain ⟨hc₀,hcS⟩ := Finset.mem_inter.mp hc
      exact Finset.mem_biUnion.mpr ⟨c,hc₀,Finset.mem_filter.mpr ⟨hS,hcS⟩⟩
    have hD : ∀ c∈S₀,(D c).card≤6*N+1 := by
      intro c _
      exact actual_rooted_small_AP_count
        (fun S hS=>hF.1 S (Finset.mem_filter.mp hS).1)
        (fun S hS=>hAP S (Finset.mem_filter.mp hS).1)
        (fun S hS=>hcard S (Finset.mem_filter.mp hS).1)
        (fun S hS=>(Finset.mem_filter.mp hS).2)
    calc
      F.card≤(S₀.biUnion D).card := Finset.card_le_card hcover
      _≤∑ c∈S₀,(D c).card := Finset.card_biUnion_le
      _≤∑ _c∈S₀,(6*N+1) := Finset.sum_le_sum hD
      _=S₀.card*(6*N+1) := by simp
      _≤18*N+3 := by have hh:=Nat.mul_le_mul_right (6*N+1) (hcard S₀ hS₀);omega
  · have hz : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Finset.card_empty,Nat.zero_le]

theorem actual_same_step_fixed_endpoint {N d : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (first : Bool) (hd : 0<d) (hsub : ∀ S∈F,S⊆Ground N)
    (hne : ∀ S∈F,S.Nonempty) (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S)
    (hend : ∀ S∈F,(if first then Low S else High S)=q) : F.card≤N/d+1 := by
  let X := {S // S∈F}
  let f (S:X) := S.val.card-1
  have hlen : ∀ S:X,f S≤N/d := by
    intro S
    obtain ⟨p,hp⟩ := hstep S.val S.property
    have hground : S.val⊆Finset.Icc 1 (N:ℤ) := by
      intro x hx
      exact Finset.mem_Icc.mpr ((mem_ground N x).mp (hsub S.val S.property hx))
    have hspan := apAt_card_span hp (hne S.val S.property) hground
    have hpos : 0<S.val.card := Finset.card_pos.mpr (hne S.val S.property)
    have hh : d*(S.val.card-1)≤N := by
      have hc : ((S.val.card-1:ℕ):ℤ)=(S.val.card:ℤ)-1 := by omega
      have hcast : ((d*(S.val.card-1):ℕ):ℤ)≤(N:ℤ) := by push_cast;rw [hc];omega
      exact_mod_cast hcast
    exact (Nat.le_div_iff_mul_le hd).mpr (by dsimp [f];nlinarith only [hh])
  have hinj : Function.Injective f := by
    intro S T he
    have hposS : 0<S.val.card := Finset.card_pos.mpr (hne S.val S.property)
    have hposT : 0<T.val.card := Finset.card_pos.mpr (hne T.val T.property)
    have hk : S.val.card=T.val.card := by dsimp [f] at he;omega
    obtain ⟨p,hp⟩ := hstep S.val S.property
    obtain ⟨r,hr⟩ := hstep T.val T.property
    have hs : High S.val-Low S.val=(d:ℤ)*((S.val.card:ℤ)-1) := by
      simpa only [High,Low,dif_pos (hne S.val S.property)] using apAt_span_eq hp (hne S.val S.property)
    have ht : High T.val-Low T.val=(d:ℤ)*((T.val.card:ℤ)-1) := by
      simpa only [High,Low,dif_pos (hne T.val T.property)] using apAt_span_eq hr (hne T.val T.property)
    have hS := hend S.val S.property
    have hT := hend T.val T.property
    have heq : Low S.val=Low T.val ∧ High S.val=High T.val := by
      cases first <;> simp only [Bool.false_eq_true,↓reduceIte] at hS hT
      · rw [hk] at hs;constructor <;>omega
      · rw [hk] at hs;constructor <;>omega
    apply Subtype.ext
    exact same_step_equal_of_endpoints (hne S.val S.property) (hne T.val T.property) hp hr heq.1 heq.2
  have hmaps : Set.MapsTo f (Finset.univ:Finset X) (Finset.range (N/d+1)) := by
    intro S _
    exact Finset.mem_range.mpr (by have hh:=hlen S;omega)
  have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  simpa only [Finset.card_univ,Finset.card_range,X,Fintype.card_coe] using hh

def BoundedStep (S : Finset ℤ) : ℕ := if S.card≤1 then 1 else Step S

theorem actual_bounded_step {N : ℕ} {S : Finset ℤ} (hsub : S⊆Ground N) (hAP : IsAP S) :
    0<BoundedStep S ∧ BoundedStep S≤N ∧ ∃ p:ℤ,APAt (BoundedStep S:ℤ) p S := by
  by_cases hsmall : S.card≤1
  · obtain ⟨a,ha⟩ := isAP_nonempty hAP
    have he := singleton_of_root_card_le_one ha hsmall
    have haN := (mem_ground N a).mp (hsub ha)
    simp only [BoundedStep,if_pos hsmall]
    refine ⟨by norm_num,by omega,a,?_⟩
    rw [he]
    change PrivateUnion.APAt 1 a (fun x=>x∈({a}:Finset ℤ))
    refine ⟨by norm_num,a,a,?_⟩
    intro x
    simp only [Finset.mem_singleton,one_dvd,and_true]
    omega
  · obtain ⟨hd,p,hp⟩ := actual_step hAP
    have hdN := actual_step_bound hsub hAP (by omega)
    simpa only [BoundedStep,if_neg hsmall] using (show 0<Step S ∧ Step S≤N ∧ ∃ p,APAt (Step S:ℤ) p S from ⟨hd,hdN,p,hp⟩)

theorem actual_fixed_endpoint_all_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (first : Bool) (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hend : ∀ S∈F,(if first then Low S else High S)=q) :
    (F.card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  have hdata := fun S hS=>actual_bounded_step (hsub S hS) (hAP S hS)
  have hpart : F.card=∑ d∈Finset.Icc 1 N,(F.filter (fun S=>BoundedStep S=d)).card :=
    Finset.card_eq_sum_card_fiberwise (show Set.MapsTo BoundedStep (F:Set (Finset ℤ))
      (Finset.Icc 1 N:Set ℕ) from fun S hS=>Finset.mem_Icc.mpr ⟨(hdata S hS).1,(hdata S hS).2.1⟩)
  have hbound : ∀ d∈Finset.Icc 1 N,
      ((F.filter (fun S=>BoundedStep S=d)).card:ℝ)≤(N:ℝ)/d+1 := by
    intro d hd
    have hh := actual_same_step_fixed_endpoint (F:=F.filter (fun S=>BoundedStep S=d))
      first (Finset.mem_Icc.mp hd).1
      (fun S hS=>hsub S (Finset.mem_filter.mp hS).1)
      (fun S hS=>isAP_nonempty (hAP S (Finset.mem_filter.mp hS).1))
      (by
        intro S hS
        obtain ⟨hSF,hSd⟩ := Finset.mem_filter.mp hS
        simpa only [hSd] using (hdata S hSF).2.2)
      (fun S hS=>hend S (Finset.mem_filter.mp hS).1)
    have hhR : ((F.filter (fun S=>BoundedStep S=d)).card:ℝ)≤((N/d:ℕ):ℝ)+1 := by exact_mod_cast hh
    have hdiv := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=d)
    linarith only [hhR,hdiv]
  have hpartR : (F.card:ℝ)=∑ d∈Finset.Icc 1 N,((F.filter (fun S=>BoundedStep S=d)).card:ℝ) := by exact_mod_cast hpart
  rw [hpartR]
  calc
    _≤∑ d∈Finset.Icc 1 N,((N:ℝ)/d+1) := Finset.sum_le_sum hbound
    _=(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
      simp [HarmonicAbel29.Harmonic,div_eq_mul_inv,Finset.sum_add_distrib,←Finset.mul_sum]

theorem actual_fixed_low_all_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S) (hend : ∀ S∈F,Low S=q) :
    (F.card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  exact actual_fixed_endpoint_all_AP_count true hsub hAP (by simpa only [↓reduceIte] using hend)

theorem actual_fixed_high_all_AP_count {N : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S) (hend : ∀ S∈F,High S=q) :
    (F.card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  exact actual_fixed_endpoint_all_AP_count false hsub hAP (by simpa only [Bool.false_eq_true,↓reduceIte] using hend)

theorem actual_fixed_low_count {N : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S) (htwo : ∀ S∈F,2≤S.card)
    (hend : ∀ S∈F,Low S=q) : (F.card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  have hn : ∀ S∈F,S.Nonempty := fun S hS=>Finset.card_pos.mp (by have hh:=htwo S hS;omega)
  have hp : ∀ S∈F,IsAP S := fun S hS=>by have _h:=hn S hS;exact hAP S hS
  exact actual_fixed_low_all_AP_count hsub hp hend

theorem actual_fixed_high_count {N : ℕ} {F : Finset (Finset ℤ)} {q : ℤ}
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S) (htwo : ∀ S∈F,2≤S.card)
    (hend : ∀ S∈F,High S=q) : (F.card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  have hn : ∀ S∈F,S.Nonempty := fun S hS=>Finset.card_pos.mp (by have hh:=htwo S hS;omega)
  have hp : ∀ S∈F,IsAP S := fun S hS=>by have _h:=hn S hS;exact hAP S hS
  exact actual_fixed_high_all_AP_count hsub hp hend

#print axioms singleton_of_root_card_le_one
#print axioms actual_rooted_short_AP_count
#print axioms actual_rooted_small_AP_count
#print axioms actual_small_AP_family_count
#print axioms actual_same_step_fixed_endpoint
#print axioms actual_bounded_step
#print axioms actual_fixed_endpoint_all_AP_count
#print axioms actual_fixed_low_all_AP_count
#print axioms actual_fixed_high_all_AP_count
#print axioms actual_fixed_low_count
#print axioms actual_fixed_high_count
end
end JSP233.APLinearCount49
