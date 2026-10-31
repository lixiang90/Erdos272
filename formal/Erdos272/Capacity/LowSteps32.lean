import Erdos272.Geometry.AffineMiddleWitness31
import Erdos272.Resources.JointResources31
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast

/-! Finite, actual-coordinate counting behind low-step concentration.
No classification or complement existence assertion is assumed proved here. -/
namespace JSP233.LowSteps32
open StarCompletion StarResources30 CrossLine30 AffineLine30 StaircaseGeometry
open HarmonicAbel29
open scoped Classical BigOperators
noncomputable section

theorem valid_coordinates_card (C : Finset (ℕ × ℕ))
    (hvalid : ∀ p∈C, 3≤p.1+p.2) :
    C.card≤Height C*Width C+Height C+Width C := by
  have hsub : C⊆(Finset.range (Height C+1)).product (Finset.range (Width C+1)) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by
      have hh : p.1≤Height C := Finset.le_sup (f:=Prod.fst) hp
      omega),Finset.mem_range.mpr (by
      have hh : p.2≤Width C := Finset.le_sup (f:=Prod.snd) hp
      omega)⟩
  have hzero : (0,0)∉C := by intro h; have := hvalid (0,0) h; omega
  have hstrict : C⊂(Finset.range (Height C+1)).product (Finset.range (Width C+1)) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub,?_⟩
    intro heq
    apply hzero
    rw [heq]
    simp
  have hh : C.card<(Height C+1)*(Width C+1) := by
    simpa using Finset.card_lt_card hstrict
  nlinarith

theorem thin_coordinates_card (C : Finset (ℕ × ℕ))
    (hthin : Height C≤1 ∨ Width C≤1) :
    C.card≤2*(Height C+Width C)+1 := by
  have hh : C.card≤(Height C+1)*(Width C+1) := by
    have hb := QuantitativeTail31.family_card_le_rectangle C
    rw [family_card] at hb
    exact hb
  rcases hthin with h | h <;> nlinarith

theorem harmonic_1024_le_eleven : Harmonic 1024≤11 := by
  have ht : Real.log (2:ℝ)≤1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hl : Real.log (1024:ℝ)≤10 := by
    rw [show (1024:ℝ)=2^10 by norm_num,Real.log_pow]
    norm_num
    linarith
  have hh := HarmonicAbel29.harmonic_le_one_add_log 1024
  change Harmonic 1024≤1+Real.log (1024:ℝ) at hh
  linarith

theorem harmonic_linear (n : ℕ) : Harmonic n≤11+(n:ℝ)/1024 := by
  by_cases hn : 1024≤n
  · induction n,hn using Nat.le_induction with
    | base => have hh := harmonic_1024_le_eleven; norm_num; linarith
    | succ n hn ih =>
      have hi : (1:ℝ)/((n:ℝ)+1)≤1/1024 := by
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast (show 1024≤n+1 by omega)
      rw [QuantitativeTail31.harmonic_succ]
      push_cast
      linarith
  · have hh := harmonic_mono (show n≤1024 by omega)
    have hb := harmonic_1024_le_eleven
    have hp : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith

theorem concentration_numeric (n : ℝ) (hn : 65535≤n) :
    n^2/320 < 83*n^2/23040-61*n/2+9 := by
  have hm : 0≤(n-65535)*(n+65535-702720/11) := by
    apply mul_nonneg <;> linarith
  nlinarith

def leftCapacity (c : ℤ) : ℕ := (c-1).toNat
def rightCapacity (N : ℕ) (c : ℤ) : ℕ := ((N:ℤ)-c).toNat

theorem actual_class_coordinates (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card)
    (hc : c∈Ground N) (d : ℕ) (hd : 0<d) :
    ∃ C : Finset (ℕ × ℕ),
      mapFamily c (d:ℤ) (Family C)=StepClass F (trueStep c) (d:ℤ) ∧
      (∀ p∈C, 3≤p.1+p.2) ∧
      (∀ p∈C, p.1*d≤leftCapacity c ∧ p.2*d≤rightCapacity N c) := by
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  obtain ⟨U,hU,hunit⟩ := exists_normalized_family c (d:ℤ) hdZ
    (StepClass F (trueStep c) (d:ℤ)) (fun _ _ => True) (by
      intro S hS
      obtain ⟨l,r,heq,hcard⟩ := actual_step_class_representation c F hAP hroot hlarge (d:ℤ) S hS
      exact ⟨l,r,heq,hcard,trivial⟩)
  obtain ⟨C,hC,hvalid⟩ := exists_coordinates U (by
    intro S hS
    obtain ⟨l,r,heq,hcard,htrue⟩ := hunit S hS
    exact ⟨l,r,heq,hcard⟩)
  have hcI : 1≤c ∧ c≤(N:ℤ) := by
    rw [StarBoundConcrete30.ground_eq_Icc] at hc
    exact Finset.mem_Icc.mp hc
  have hlcast : (leftCapacity c:ℤ)=c-1 := Int.toNat_of_nonneg (by omega)
  have hrcast : (rightCapacity N c:ℤ)=(N:ℤ)-c := Int.toNat_of_nonneg (by omega)
  refine ⟨C,by rw [hC]; exact hU,?_,?_⟩
  · intro p hp
    exact hvalid p hp
  · intro p hp
    have hSC : mapSet c (d:ℤ) (Window p.1 p.2)∈StepClass F (trueStep c) (d:ℤ) := by
      rw [←hU,←hC]
      exact Finset.mem_image.mpr ⟨Window p.1 p.2,
        Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩
    have hSF := stepClass_subset F (trueStep c) (d:ℤ) hSC
    have hsubset := hground _ hSF
    rw [StarBoundConcrete30.ground_eq_Icc] at hsubset
    have hL : c-(d:ℤ)*(p.1:ℤ)∈mapSet c (d:ℤ) (Window p.1 p.2) := by
      refine Finset.mem_image.mpr ⟨-(p.1:ℤ),by simp [Window],?_⟩
      dsimp [affine]; ring
    have hR : c+(d:ℤ)*(p.2:ℤ)∈mapSet c (d:ℤ) (Window p.1 p.2) := by
      refine Finset.mem_image.mpr ⟨(p.2:ℤ),by simp [Window],rfl⟩
    have hLb := (Finset.mem_Icc.mp (hsubset hL)).1
    have hRb := (Finset.mem_Icc.mp (hsubset hR)).2
    constructor
    · have hh : (p.1:ℤ)*(d:ℤ)≤(leftCapacity c:ℤ) := by nlinarith
      exact_mod_cast hh
    · have hh : (p.2:ℤ)*(d:ℤ)≤(rightCapacity N c:ℤ) := by nlinarith
      exact_mod_cast hh

theorem coordinates_thin_of_inactive (c : ℤ) (d : ℕ)
    (F : Finset (Finset ℤ)) (C : Finset (ℕ × ℕ))
    (hC : mapFamily c (d:ℤ) (Family C)=StepClass F (trueStep c) (d:ℤ))
    (hinactive : (d:ℤ)∉APActiveSteps c F) : Height C≤1 ∨ Width C≤1 := by
  have hmem (p : ℕ × ℕ) (hp : p∈C) :
      mapSet c (d:ℤ) (Window p.1 p.2)∈StepClass F (trueStep c) (d:ℤ) := by
    rw [←hC]
    exact Finset.mem_image.mpr ⟨Window p.1 p.2,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩,rfl⟩
  by_cases hleft : ∃ S∈StepClass F (trueStep c) (d:ℤ), c-2*(d:ℤ)∈S
  · right
    apply Finset.sup_le
    intro p hp
    by_contra hpr
    have hright : ∃ S∈StepClass F (trueStep c) (d:ℤ), c+2*(d:ℤ)∈S :=
      ⟨_,hmem p hp,mapWindow_pos_two_mem c (d:ℤ) p.1 p.2 (by omega)⟩
    obtain ⟨S,hS,hpoint⟩ := hleft
    have hlabel : (d:ℤ)∈StepLabels F (trueStep c) := by
      obtain ⟨hSF,hstep⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_image.mpr ⟨S,hSF,hstep⟩
    exact hinactive (Finset.mem_filter.mpr ⟨hlabel,⟨S,hS,hpoint⟩,hright⟩)
  · left
    apply Finset.sup_le
    intro p hp
    by_contra hpl
    exact hleft ⟨_,hmem p hp,mapWindow_neg_two_mem c (d:ℤ) p.1 p.2 (by omega)⟩

theorem actual_class_count (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card)
    (hc : c∈Ground N) (d : ℕ) (hd : 0<d) :
    ((StepClass F (trueStep c) (d:ℤ)).card:ℝ)≤
      (if (d:ℤ)∈APActiveSteps c F then
        (leftCapacity c:ℝ)*(rightCapacity N c:ℝ)/(d:ℝ)^2 else 0)
      +2*((leftCapacity c:ℝ)+(rightCapacity N c:ℝ))/(d:ℝ)+1 := by
  obtain ⟨C,hC,hvalid,hbounds⟩ := actual_class_coordinates N c F hground hAP hroot hlarge hc d hd
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  have hcard : (StepClass F (trueStep c) (d:ℤ)).card=C.card := by
    rw [←hC,mapFamily_card c (d:ℤ) hdZ,family_card]
  have hl : Height C≤leftCapacity c/d := by
    apply Finset.sup_le
    intro p hp
    exact (Nat.le_div_iff_mul_le hd).mpr (hbounds p hp).1
  have hr : Width C≤rightCapacity N c/d := by
    apply Finset.sup_le
    intro p hp
    exact (Nat.le_div_iff_mul_le hd).mpr (hbounds p hp).2
  have hlm : Height C*d≤leftCapacity c :=
    (Nat.le_div_iff_mul_le hd).mp hl
  have hrm : Width C*d≤rightCapacity N c :=
    (Nat.le_div_iff_mul_le hd).mp hr
  have hlR : (Height C:ℝ)≤(leftCapacity c:ℝ)/(d:ℝ) := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast hlm
  have hrR : (Width C:ℝ)≤(rightCapacity N c:ℝ)/(d:ℝ) := by
    apply (le_div_iff₀ hdR).mpr
    exact_mod_cast hrm
  have hsum : (Height C:ℝ)+(Width C:ℝ)≤
      ((leftCapacity c:ℝ)+(rightCapacity N c:ℝ))/(d:ℝ) := by
    rw [add_div]
    exact add_le_add hlR hrR
  have hsnonneg : (0:ℝ)≤((leftCapacity c:ℝ)+(rightCapacity N c:ℝ))/(d:ℝ) :=
    div_nonneg (by positivity) hdR.le
  rw [hcard]
  simp only [mul_div_assoc]
  by_cases ha : (d:ℤ)∈APActiveSteps c F
  · rw [if_pos ha]
    have hb : (C.card:ℝ)≤(Height C:ℝ)*(Width C:ℝ)+(Height C:ℝ)+(Width C:ℝ) := by
      exact_mod_cast valid_coordinates_card C hvalid
    have hp := mul_le_mul hlR hrR (Nat.cast_nonneg (Width C))
      (div_nonneg (Nat.cast_nonneg (leftCapacity c)) hdR.le)
    rw [div_mul_div_comm,←pow_two] at hp
    simp only [mul_div_assoc] at hp
    linarith
  · rw [if_neg ha]
    have hb : (C.card:ℝ)≤2*((Height C:ℝ)+(Width C:ℝ))+1 := by
      exact_mod_cast thin_coordinates_card C (coordinates_thin_of_inactive c d F C hC ha)
    linarith

theorem reciprocal_square_step (n : ℕ) (hn : 1≤n) :
    (1:ℝ)/((n:ℝ)+1)^2≤1/(n:ℝ)-1/((n:ℝ)+1) := by
  have hp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1))).mpr
  field_simp
  nlinarith

theorem reciprocal_square_tail (n : ℕ) :
    (∑ d∈Finset.Icc 6 n, (1:ℝ)/(d:ℝ)^2)≤1/5 := by
  by_cases hn : 6≤n
  · have hs : (∑ d∈Finset.Icc 6 n, (1:ℝ)/(d:ℝ)^2)≤1/5-1/(n:ℝ) := by
      induction n,hn using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hh := reciprocal_square_step n (by omega)
        push_cast
        linarith
    have hp : (0:ℝ)≤1/(n:ℝ) := by positivity
    linarith
  · have he : Finset.Icc 6 n=∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [he]
    norm_num

theorem actual_step_label_bound (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card)
    {d : ℤ} (hd : d∈StepLabels F (trueStep c)) : 1≤d ∧ d≤((N-1:ℕ):ℤ) := by
  obtain ⟨S,hS,he⟩ := Finset.mem_image.mp hd
  obtain ⟨hdpos,l,r,hrep⟩ := trueStep_representation (hAP S hS) (hroot S hS)
  rw [he] at hdpos hrep
  have hpointL : c-d*(l:ℤ)∈S := by
    rw [hrep]
    refine Finset.mem_image.mpr ⟨-(l:ℤ),by simp [Window],?_⟩
    dsimp [affine]; ring
  have hpointR : c+d*(r:ℤ)∈S := by
    rw [hrep]
    exact Finset.mem_image.mpr ⟨(r:ℤ),by simp [Window],rfl⟩
  have hbL := hground S hS hpointL
  have hbR := hground S hS hpointR
  rw [StarBoundConcrete30.ground_eq_Icc,Finset.mem_Icc] at hbL hbR
  have hcard : S.card=l+r+1 := by rw [hrep,mapSet_card c d hdpos,window_card]
  have hlen : (3:ℤ)≤(l:ℤ)+(r:ℤ) := by have := hlarge S hS; omega
  have hlenmul : 3*d≤d*((l:ℤ)+(r:ℤ)) := by nlinarith
  have hN : 1≤N := by omega
  have hsub : ((N-1:ℕ):ℤ)=(N:ℤ)-1 := by omega
  constructor
  · omega
  · rw [hsub]
    nlinarith

theorem transversal_complement_count (V : Finset ℤ) (D : Finset (Finset ℤ))
    (T : Finset ℤ) (hT : T∈D) :
    (JointResources31.TwoTransversals V D).card+((V\T).card).choose 2≤V.card.choose 2 := by
  let A := JointResources31.TwoTransversals V D
  let B := (V\T).powersetCard 2
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro Q hQA hQB
    obtain ⟨x,hx⟩ := (Finset.mem_filter.mp hQA).2 T hT
    have hQsub := (Finset.mem_powersetCard.mp hQB).1
    have hxQ := (Finset.mem_inter.mp hx).1
    exact (Finset.mem_sdiff.mp (hQsub hxQ)).2 (Finset.mem_inter.mp hx).2
  have hsub : A∪B⊆V.powersetCard 2 := by
    intro Q hQ
    rcases Finset.mem_union.mp hQ with hA | hB
    · exact (Finset.mem_filter.mp hA).1
    · obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp hB
      exact Finset.mem_powersetCard.mpr ⟨hsub.trans (Finset.sdiff_subset),hcard⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,Finset.card_powersetCard,
    Finset.card_powersetCard] at hh
  exact hh

theorem finite_class_total (n : ℕ) (J : Finset ℕ) (a : ℕ→ℝ) (active : ℕ→Prop)
    (L R : ℝ) (hL : 0≤L) (hR : 0≤R) (hJ : J⊆Finset.Icc 1 n)
    (hcount : ∀ d∈J, a d≤(if active d then L*R/(d:ℝ)^2 else 0)+2*(n:ℝ)/(d:ℝ)+1) :
    (∑ d∈J, a d)≤(∑ d∈J.filter (fun d => active d ∧ d≤5), a d)
      +L*R/5+2*(n:ℝ)*Harmonic n+n := by
  let low := J.filter (fun d => active d ∧ d≤5)
  let rest := J\low
  let B := rest.filter active
  have hrJ : rest⊆Finset.Icc 1 n := (Finset.sdiff_subset).trans hJ
  have hB : B⊆Finset.Icc 6 n := by
    intro d hd
    obtain ⟨hdr,hact⟩ := Finset.mem_filter.mp hd
    obtain ⟨hdJ,hdlow⟩ := Finset.mem_sdiff.mp hdr
    obtain ⟨hd1,hdn⟩ := Finset.mem_Icc.mp (hJ hdJ)
    have hd5 : ¬d≤5 := by
      intro hh
      exact hdlow (Finset.mem_filter.mpr ⟨hdJ,hact,hh⟩)
    exact Finset.mem_Icc.mpr ⟨by omega,hdn⟩
  have htail : (∑ d∈B, (1:ℝ)/(d:ℝ)^2)≤1/5 := by
    calc
      _≤∑ d∈Finset.Icc 6 n, (1:ℝ)/(d:ℝ)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hB (by intro d hd hn; positivity)
      _≤1/5 := reciprocal_square_tail n
  have hprod : (∑ d∈rest, if active d then L*R/(d:ℝ)^2 else 0)≤L*R/5 := by
    rw [←Finset.sum_filter]
    change (∑ d∈B, L*R/(d:ℝ)^2)≤L*R/5
    have he (d : ℕ) : L*R/(d:ℝ)^2=L*R*((1:ℝ)/(d:ℝ)^2) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    simpa only [one_div,div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left htail (mul_nonneg hL hR)
  have hhar : (∑ d∈rest, (1:ℝ)/(d:ℝ))≤Harmonic n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hrJ (by intro d hd hn; positivity)
  have hlin : (∑ d∈rest, 2*(n:ℝ)/(d:ℝ))≤2*(n:ℝ)*Harmonic n := by
    have he (d : ℕ) : 2*(n:ℝ)/(d:ℝ)=2*(n:ℝ)*((1:ℝ)/(d:ℝ)) := by ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hhar (by positivity)
  have hcard : (rest.card:ℝ)≤n := by
    have hh := Finset.card_le_card hrJ
    have hI : (Finset.Icc 1 n).card=n := by simp
    rw [hI] at hh
    exact_mod_cast hh
  have hrest := Finset.sum_le_sum (s:=rest) (fun d hd => hcount d (Finset.mem_sdiff.mp hd).1)
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one] at hrest
  have hpart := Finset.sum_sdiff (f:=a) (Finset.filter_subset (fun d => active d ∧ d≤5) J)
  change (∑ d∈rest,a d)+(∑ d∈low,a d)=∑ d∈J,a d at hpart
  change (∑ d∈J,a d)≤(∑ d∈low,a d)+L*R/5+2*(n:ℝ)*Harmonic n+n
  linarith

theorem finite_low_pigeonhole (n : ℝ) (J : Finset ℕ)
    (a : ℕ→ℝ) (active : ℕ→Prop)
    (hpos : ∀ d∈J, 1≤d)
    (hlarge : n^2/320<(∑ d∈J.filter (fun d => active d ∧ d≤5), a d)) :
    ∃ d∈J, active d ∧ d≤5 ∧ n^2/1600≤a d := by
  let low := J.filter (fun d => active d ∧ d≤5)
  have hsub : low⊆Finset.Icc 1 5 := by
    intro d hd
    obtain ⟨hdJ,ha,hd5⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨hpos d hdJ,hd5⟩
  have hc : low.card≤5 := by simpa using Finset.card_le_card hsub
  by_contra hno
  push Not at hno
  have hh : ∀ d∈low, a d≤n^2/1600 := by
    intro d hd
    obtain ⟨hdJ,ha,hd5⟩ := Finset.mem_filter.mp hd
    exact le_of_lt (hno d hdJ ha hd5)
  have hs := Finset.sum_le_sum hh
  have hcR : (low.card:ℝ)≤5 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_right hcR (show (0:ℝ)≤n^2/1600 by positivity)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  change n^2/320<(∑ d∈low,a d) at hlarge
  nlinarith

def NatLabels (c : ℤ) (F : Finset (Finset ℤ)) : Finset ℕ :=
  (StepLabels F (trueStep c)).image Int.toNat

def LowActive (c : ℤ) (F : Finset (Finset ℤ)) : Finset ℕ :=
  (NatLabels c F).filter (fun d => (d:ℤ)∈APActiveSteps c F ∧ d≤5)

theorem nat_labels_bound (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) :
    NatLabels c F⊆Finset.Icc 1 (N-1) := by
  intro d hd
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨he1,hen⟩ := actual_step_label_bound N c F hground hAP hroot hlarge he
  exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem sum_nat_class_card (c : ℤ) (F : Finset (Finset ℤ))
    (hAP : ∀ S∈F, IsAP S) (hroot : Rooted F c) :
    (∑ d∈NatLabels c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))=(F.card:ℝ) := by
  have hinj : Set.InjOn Int.toNat (↑(StepLabels F (trueStep c)) : Set ℤ) := by
    intro i hi j hj heq
    have hip := actual_step_labels_positive c F hAP hroot i hi
    have hjp := actual_step_labels_positive c F hAP hroot j hj
    omega
  rw [NatLabels,Finset.sum_image hinj]
  calc
    _=∑ d∈StepLabels F (trueStep c), ((StepClass F (trueStep c) d).card:ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Int.toNat_of_nonneg (le_of_lt (actual_step_labels_positive c F hAP hroot d hd))]
    _=(F.card:ℝ) := by exact_mod_cast sum_stepClass_card F (trueStep c)

theorem actual_AP_total (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F c) (hlarge : ∀ S∈F, 4≤S.card) (hc : c∈Ground N) :
    (F.card:ℝ)≤(∑ d∈LowActive c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(((N-1:ℕ):ℝ)^2/20)+2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
  have hcI : 1≤c ∧ c≤(N:ℤ) := by
    rw [StarBoundConcrete30.ground_eq_Icc] at hc
    exact Finset.mem_Icc.mp hc
  have hl : (leftCapacity c:ℤ)=c-1 := Int.toNat_of_nonneg (by omega)
  have hr : (rightCapacity N c:ℤ)=(N:ℤ)-c := Int.toNat_of_nonneg (by omega)
  have hcap : leftCapacity c+rightCapacity N c=N-1 := by omega
  have hcapR : (leftCapacity c:ℝ)+(rightCapacity N c:ℝ)=((N-1:ℕ):ℝ) := by exact_mod_cast hcap
  have hJ := nat_labels_bound N c F hground hAP hroot hlarge
  have hh := finite_class_total (N-1) (NatLabels c F)
    (fun d => ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
    (fun d => (d:ℤ)∈APActiveSteps c F) (leftCapacity c:ℝ) (rightCapacity N c:ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hJ (by
      intro d hd
      have hdpos : 0<d := by have := (Finset.mem_Icc.mp (hJ hd)).1; omega
      have hb := actual_class_count N c F hground hAP hroot hlarge hc d hdpos
      rw [hcapR] at hb
      by_cases ha : (d:ℤ)∈APActiveSteps c F
      · simpa only [if_pos ha] using hb
      · simpa only [if_neg ha] using hb)
  rw [sum_nat_class_card c F hAP hroot] at hh
  have hp : (leftCapacity c:ℝ)*(rightCapacity N c:ℝ)≤((N-1:ℕ):ℝ)^2/4 := by
    nlinarith [sq_nonneg ((leftCapacity c:ℝ)-(rightCapacity N c:ℝ))]
  have hh' : (F.card:ℝ)≤(∑ d∈LowActive c F, ((StepClass F (trueStep c) (d:ℤ)).card:ℝ))
      +(leftCapacity c:ℝ)*(rightCapacity N c:ℝ)/5
      +2*((N-1:ℕ):ℝ)*Harmonic (N-1)+((N-1:ℕ):ℝ) := by
    convert hh using 1
    congr 4
    ext d
    simp only [LowActive,Finset.mem_filter]
  linarith

#print axioms valid_coordinates_card
#print axioms thin_coordinates_card
#print axioms harmonic_1024_le_eleven
#print axioms harmonic_linear
#print axioms concentration_numeric
#print axioms actual_class_coordinates
#print axioms coordinates_thin_of_inactive
#print axioms actual_class_count
#print axioms reciprocal_square_step
#print axioms reciprocal_square_tail
#print axioms actual_step_label_bound
#print axioms transversal_complement_count
#print axioms finite_class_total
#print axioms finite_low_pigeonhole
#print axioms nat_labels_bound
#print axioms sum_nat_class_card
#print axioms actual_AP_total
end
end JSP233.LowSteps32
