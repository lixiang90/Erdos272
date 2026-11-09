module

public import Erdos272.Arithmetic.HarmonicSharp39
public import Erdos272.Foundation.JSP233
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! Native counting of actual intersecting arithmetic progressions. -/
namespace JSP233.APCount41
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section

def Low (S : Finset ℤ) : ℤ := if h:S.Nonempty then S.min' h else 0
def High (S : Finset ℤ) : ℤ := if h:S.Nonempty then S.max' h else 0

theorem low_spec {S : Finset ℤ} (hS : S.Nonempty) :
    Low S∈S ∧ ∀ x∈S,Low S≤x := by
  simp only [Low,dif_pos hS]
  exact ⟨Finset.min'_mem _ hS,fun x hx=>Finset.min'_le _ x hx⟩

theorem high_spec {S : Finset ℤ} (hS : S.Nonempty) :
    High S∈S ∧ ∀ x∈S,x≤High S := by
  simp only [High,dif_pos hS]
  exact ⟨Finset.max'_mem _ hS,fun x hx=>Finset.le_max' _ x hx⟩

def HasNatStep (S : Finset ℤ) : Prop := ∃ d:ℕ,∃ p:ℤ,APAt (d:ℤ) p S
def Step (S : Finset ℤ) : ℕ := if h:HasNatStep S then Classical.choose h else 0

theorem actual_step {S : Finset ℤ} (hAP : IsAP S) :
    0<Step S ∧ ∃ p:ℤ,APAt (Step S:ℤ) p S := by
  obtain ⟨d,p,hd,_⟩ := (isAP_iff_exists_APAt _).mp hAP
  have hcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.1.le
  have hex : HasNatStep S := ⟨d.toNat,p,by rwa [hcast]⟩
  have hp := Classical.choose_spec hex
  have he : Step S=Classical.choose hex := by simp only [Step,dif_pos hex]
  rw [←he] at hp
  exact ⟨by obtain ⟨p,hp⟩:=hp; exact_mod_cast hp.1,hp⟩

theorem actual_step_bound {N : ℕ} {S : Finset ℤ}
    (hS : S⊆Ground N) (hAP : IsAP S) (htwo : 2≤S.card) : Step S≤N := by
  obtain ⟨_,p,hp⟩ := actual_step hAP
  obtain ⟨a,b,ha,had,_,_,_⟩ := apAt_adjacent_min hp htwo
  have haN := (mem_ground N a).mp (hS ha)
  have hdN := (mem_ground N (a+(Step S:ℤ))).mp (hS had)
  omega

theorem actual_same_step_common_root {N d : ℕ} {F : Finset (Finset ℤ)}
    (hF : F.Nonempty) (hlegal : Legal (Ground N) F)
    (hne : ∀ S∈F,S.Nonempty) (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S) :
    ∃ c∈Ground N,∀ S∈F,c∈S := by
  let M := F.image Low
  have hM : M.Nonempty := hF.image Low
  let c := M.max' hM
  have hcM : c∈M := Finset.max'_mem _ hM
  obtain ⟨A,hA,hAc⟩ := Finset.mem_image.mp hcM
  have hcA : c∈A := hAc ▸ (low_spec (hne A hA)).1
  refine ⟨c,hlegal.1 A hA hcA,?_⟩
  intro S hS
  by_cases he : S=A
  · exact he.symm ▸ hcA
  obtain ⟨y,hy⟩ := isAP_nonempty (hlegal.2 A hA S hS (Ne.symm he))
  obtain ⟨hyA,hyS⟩ := Finset.mem_inter.mp hy
  obtain ⟨p,hp⟩ := hstep S hS
  obtain ⟨q,hq⟩ := hstep A hA
  have hlow : Low S≤c := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  have hcy : c≤y := hAc ▸ (low_spec (hne A hA)).2 y hyA
  have hcdiv : (d:ℤ)∣c-Low S := by
    have h1 := apAt_dvd_sub hp (low_spec (hne S hS)).1 hyS
    have h2 := apAt_dvd_sub hq hcA hyA
    have hh := Int.dvd_sub h1 h2
    convert hh using 1
    ring
  exact apAt_fill hp (low_spec (hne S hS)).1 hyS hlow hcy hcdiv

def Index (a b : ℤ) (d : ℕ) : ℕ := ((b-a)/(d:ℤ)).toNat

theorem index_equation {a b : ℤ} {d : ℕ} (hab : a≤b) (hdiv : (d:ℤ)∣b-a) :
    a+(Index a b d:ℤ)*(d:ℤ)=b := by
  have hn : 0≤(b-a)/(d:ℤ) := Int.ediv_nonneg (by omega) (by positivity)
  have hh := Int.ediv_mul_cancel hdiv
  dsimp [Index]
  rw [Int.toNat_of_nonneg hn]
  omega

theorem same_step_equal_of_endpoints {S T : Finset ℤ} {d : ℕ} {p q : ℤ}
    (hS : S.Nonempty) (hT : T.Nonempty) (hp : APAt (d:ℤ) p S) (hq : APAt (d:ℤ) q T)
    (hlow : Low S=Low T) (hhigh : High S=High T) : S=T := by
  apply Finset.Subset.antisymm
  · intro x hx
    apply apAt_fill hq (low_spec hT).1 (high_spec hT).1
    · rw [←hlow]; exact (low_spec hS).2 x hx
    · rw [←hhigh]; exact (high_spec hS).2 x hx
    · rw [←hlow]; exact apAt_dvd_sub hp (low_spec hS).1 hx
  · intro x hx
    apply apAt_fill hp (low_spec hS).1 (high_spec hS).1
    · rw [hlow]; exact (low_spec hT).2 x hx
    · rw [hhigh]; exact (high_spec hT).2 x hx
    · rw [hlow]; exact apAt_dvd_sub hq (low_spec hT).1 hx

theorem actual_same_step_rectangle {N d : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hd : 0<d) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hroot : ∀ S∈F,c∈S) (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S) :
    F.card≤((c-1).toNat/d+1)*(((N:ℤ)-c).toNat/d+1) := by
  let X := {S // S∈F}
  let U := (c-1).toNat/d
  let V := ((N:ℤ)-c).toNat/d
  let f : X→ℕ×ℕ := fun S => (Index (Low S.val) c d,Index c (High S.val) d)
  have hcN := (mem_ground N c).mp hc
  have data : ∀ S:X, Low S.val+(f S).1*(d:ℤ)=c ∧ c+(f S).2*(d:ℤ)=High S.val := by
    intro S
    have hcS := hroot S.val S.property
    have hne : S.val.Nonempty := ⟨c,hcS⟩
    obtain ⟨p,hp⟩ := hstep S.val S.property
    exact ⟨index_equation ((low_spec hne).2 c hcS) (apAt_dvd_sub hp (low_spec hne).1 hcS),
      index_equation ((high_spec hne).2 c hcS) (apAt_dvd_sub hp hcS (high_spec hne).1)⟩
  have hmaps : Set.MapsTo f (Finset.univ:Finset X) ((Finset.range (U+1)).product (Finset.range (V+1))) := by
    intro S _
    have he := data S
    have hne : S.val.Nonempty := ⟨c,hroot S.val S.property⟩
    have hlo := (mem_ground N (Low S.val)).mp (hlegal.1 S.val S.property (low_spec hne).1)
    have hhi := (mem_ground N (High S.val)).mp (hlegal.1 S.val S.property (high_spec hne).1)
    have hu : (f S).1≤U := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    have hv : (f S).2≤V := (Nat.le_div_iff_mul_le hd).mpr (by omega)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩
  have hinj : Function.Injective f := by
    intro S T he
    have heS := data S
    have heT := data T
    have hfirst := congrArg Prod.fst he
    have hsecond := congrArg Prod.snd he
    rw [hfirst,hsecond] at heS
    obtain ⟨p,hp⟩ := hstep S.val S.property
    obtain ⟨q,hq⟩ := hstep T.val T.property
    apply Subtype.ext
    apply same_step_equal_of_endpoints ⟨c,hroot S.val S.property⟩ ⟨c,hroot T.val T.property⟩ hp hq
    · omega
    · omega
  have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  simpa [X,U,V] using hh

theorem rectangle_real_bound (N d U V : ℕ) (hd : 0<d) (hsum : d*(U+V)≤N) :
    ((U+1)*(V+1):ℝ)≤(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1 := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hsR : (d:ℝ)*((U:ℝ)+V)≤N := by exact_mod_cast hsum
  have hUV : (U:ℝ)+V≤(N:ℝ)/d := (le_div_iff₀ hdR).mpr (by nlinarith only [hsR])
  have hsq := mul_le_mul hUV hUV (show (0:ℝ)≤(U:ℝ)+V by positivity)
    (show (0:ℝ)≤(N:ℝ)/d by positivity)
  have hskew := sq_nonneg ((U:ℝ)-V)
  have hh : ((U+1)*(V+1):ℝ)≤((N:ℝ)/d)^2/4+(N:ℝ)/d+1 := by
    nlinarith only [hUV,hsq,hskew]
  have he : ((N:ℝ)/d)^2/4=(N:ℝ)^2/(4*(d:ℝ)^2) := by ring
  rwa [he] at hh

theorem actual_same_step_count {N d : ℕ} {F : Finset (Finset ℤ)}
    (hd : 0<d) (hlegal : Legal (Ground N) F) (hne : ∀ S∈F,S.Nonempty)
    (hstep : ∀ S∈F,∃ p:ℤ,APAt (d:ℤ) p S) :
    (F.card:ℝ)≤(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1 := by
  by_cases hF : F.Nonempty
  · obtain ⟨c,hc,hroot⟩ := actual_same_step_common_root hF hlegal hne hstep
    have hb := actual_same_step_rectangle hd hc hlegal hroot hstep
    have hcN := (mem_ground N c).mp hc
    have hu := Nat.div_mul_le_self (c-1).toNat d
    have hv := Nat.div_mul_le_self ((N:ℤ)-c).toNat d
    have hlen : (c-1).toNat+((N:ℤ)-c).toNat≤N := by omega
    have hsum : d*((c-1).toNat/d+((N:ℤ)-c).toNat/d)≤N := by nlinarith only [hu,hv,hlen]
    have hbR : (F.card:ℝ)≤((((c-1).toNat/d+1)*(((N:ℤ)-c).toNat/d+1):ℕ):ℝ) := by exact_mod_cast hb
    exact hbR.trans (by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using rectangle_real_bound N d ((c-1).toNat/d) (((N:ℤ)-c).toNat/d) hd hsum)
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

def SquareReciprocal (N : ℕ) : ℝ := ∑ d∈Finset.Icc 1 N,(1:ℝ)/(d:ℝ)^2

theorem square_reciprocal_succ (N : ℕ) :
    SquareReciprocal (N+1)=SquareReciprocal N+1/((N:ℝ)+1)^2 := by
  simp only [SquareReciprocal,Finset.sum_Icc_succ_top (by omega : 1≤N+1),Nat.cast_add,Nat.cast_one]

theorem square_reciprocal_tail (n : ℕ) :
    SquareReciprocal (n+5)+1/((n:ℝ)+5)≤5/3 := by
  induction n with
  | zero => norm_num [SquareReciprocal,Finset.sum_Icc_succ_top]
  | succ n ih =>
    have he : n+1+5=(n+5)+1 := by omega
    rw [he,square_reciprocal_succ]
    push_cast
    have hn : (0:ℝ)<(n:ℝ)+5 := by positivity
    have hn1 : (0:ℝ)<(n:ℝ)+6 := by positivity
    have hh : 1/((n:ℝ)+6)^2+1/((n:ℝ)+6)≤1/((n:ℝ)+5) := by
      apply (le_div_iff₀ hn).mpr
      field_simp
      nlinarith
    convert (show SquareReciprocal (n+5)+1/((n:ℝ)+6)^2+1/((n:ℝ)+6)≤5/3 by linarith only [ih,hh]) using 1
    ring

theorem square_reciprocal_bound (N : ℕ) : SquareReciprocal N≤5/3 := by
  by_cases hN : 5≤N
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hN
    have hh := square_reciprocal_tail n
    have hp : 0≤1/((n:ℝ)+5) := by positivity
    simpa only [Nat.add_comm] using (by linarith : SquareReciprocal (n+5)≤5/3)
  · interval_cases N <;> norm_num [SquareReciprocal,Finset.sum_Icc_succ_top]

theorem actual_AP_two_or_more_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S) (htwo : ∀ S∈F,2≤S.card) :
    (F.card:ℝ)≤5*(N:ℝ)^2/12+(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
  have hmaps : ∀ S∈F,Step S∈Finset.Icc 1 N := by
    intro S hS
    exact Finset.mem_Icc.mpr ⟨(actual_step (hAP S hS)).1,
      actual_step_bound (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ d∈Finset.Icc 1 N,
      ((F.filter (fun S => Step S=d)).card:ℝ)≤(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1 := by
    intro d hd
    let C := F.filter (fun S => Step S=d)
    have hCF : C⊆F := Finset.filter_subset _ _
    have hLC : Legal (Ground N) C := ⟨fun S hS => hlegal.1 S (hCF hS),
      fun S hS T hT hne => hlegal.2 S (hCF hS) T (hCF hT) hne⟩
    apply actual_same_step_count (by have hh:=Finset.mem_Icc.mp hd; omega) hLC
      (fun S hS => isAP_nonempty (hAP S (hCF hS)))
    intro S hS
    obtain ⟨_,p,hp⟩ := actual_step (hAP S (hCF hS))
    exact ⟨p,by rwa [(Finset.mem_filter.mp hS).2] at hp⟩
  have hsum : (∑ d∈Finset.Icc 1 N,((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1))=
      (N:ℝ)^2/4*SquareReciprocal N+(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
    have ht : ∀ d:ℕ,(N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1=
        (N:ℝ)^2/4*(1/(d:ℝ)^2)+(N:ℝ)*(1/(d:ℝ))+1 := by intro d; ring
    simp_rw [ht]
    simp [SquareReciprocal,HarmonicAbel29.Harmonic,Finset.sum_add_distrib,←Finset.mul_sum]
  have hs := mul_le_mul_of_nonneg_left (square_reciprocal_bound N) (show (0:ℝ)≤(N:ℝ)^2/4 by positivity)
  calc
    (F.card:ℝ)=(∑ d∈Finset.Icc 1 N,((F.filter (fun S => Step S=d)).card:ℝ)) := by exact_mod_cast he
    _≤∑ d∈Finset.Icc 1 N,((N:ℝ)^2/(4*(d:ℝ)^2)+(N:ℝ)/d+1) := Finset.sum_le_sum hclass
    _≤_ := by rw [hsum]; nlinarith only [hs]

theorem actual_singleton_family_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hsize : ∀ S∈F,S.card≤1) : F.card≤1 := by
  apply Finset.card_le_one.mpr
  intro S hS T hT
  by_contra hne
  obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 S hS T hT hne)
  obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
  apply hne
  ext y
  constructor
  · intro hy
    have hh := Finset.card_le_one.mp (hsize S hS) y hy x hxS
    exact hh.symm ▸ hxT
  · intro hy
    have hh := Finset.card_le_one.mp (hsize T hT) y hy x hxT
    exact hh.symm ▸ hxS

theorem actual_AP_count_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S) :
    (F.card:ℝ)≤5*(N:ℝ)^2/12+(N:ℝ)*HarmonicAbel29.Harmonic N+N+1 := by
  let A := F.filter (fun S => 2≤S.card)
  let C := F.filter (fun S => ¬2≤S.card)
  have hAF : A⊆F := Finset.filter_subset _ _
  have hCF : C⊆F := Finset.filter_subset _ _
  have hLA : Legal (Ground N) A := ⟨fun S hS => hlegal.1 S (hAF hS),
    fun S hS T hT hne => hlegal.2 S (hAF hS) T (hAF hT) hne⟩
  have hLC : Legal (Ground N) C := ⟨fun S hS => hlegal.1 S (hCF hS),
    fun S hS T hT hne => hlegal.2 S (hCF hS) T (hCF hT) hne⟩
  have ha := actual_AP_two_or_more_count hLA (fun S hS=>hAP S (hAF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hc := actual_singleton_family_count hLC (fun S hS=>by have hh:=(Finset.mem_filter.mp hS).2; omega)
  have hpart := Finset.card_filter_add_card_filter_not (s:=F) (fun S => 2≤S.card)
  change A.card+C.card=F.card at hpart
  have hpartR : (A.card:ℝ)+C.card=F.card := by exact_mod_cast hpart
  have hcR : (C.card:ℝ)≤1 := by exact_mod_cast hc
  linarith

theorem actual_AP_count_dyadic {N J : ℕ} {F : Finset (Finset ℤ)}
    (hN : N<2^J) (hlegal : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S) :
    (F.card:ℝ)≤5*(N:ℝ)^2/12+(7/10:ℝ)*(N:ℝ)*J+2*N+1 := by
  have hh := actual_AP_count_harmonic hlegal hAP
  have hs := mul_le_mul_of_nonneg_left (HarmonicSharp39.actual_harmonic_seven_tenths N J hN)
    (show (0:ℝ)≤N by positivity)
  nlinarith only [hh,hs]

theorem actual_AP_count_original_budget {N J : ℕ} {F : Finset (Finset ℤ)}
    (hN : N<2^J) (hlegal : Legal (Ground N) F) (hAP : ∀ S∈F,IsAP S) :
    (F.card:ℝ)≤5*(N:ℝ)^2/12+(N:ℝ)*J+20*N+3 := by
  have hh := actual_AP_count_dyadic hN hlegal hAP
  have hp := mul_nonneg (show (0:ℝ)≤N by positivity) (show (0:ℝ)≤J by positivity)
  have hN0 : (0:ℝ)≤N := by positivity
  nlinarith only [hh,hp,hN0]

#print axioms low_spec
#print axioms high_spec
#print axioms actual_step
#print axioms actual_step_bound
#print axioms actual_same_step_common_root
#print axioms index_equation
#print axioms same_step_equal_of_endpoints
#print axioms actual_same_step_rectangle
#print axioms rectangle_real_bound
#print axioms actual_same_step_count
#print axioms square_reciprocal_succ
#print axioms square_reciprocal_tail
#print axioms square_reciprocal_bound
#print axioms actual_AP_two_or_more_count
#print axioms actual_singleton_family_count
#print axioms actual_AP_count_harmonic
#print axioms actual_AP_count_dyadic
#print axioms actual_AP_count_original_budget

end
end JSP233.APCount41
