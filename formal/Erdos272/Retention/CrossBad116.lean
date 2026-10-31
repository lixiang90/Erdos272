import Erdos272.Retention.BalancedFringe115

/-! Actual AP intersections of two short traces cannot use both exterior
arms.  The sources remain on Ground N; their exterior rectangles are real. -/
namespace JSP233.CrossBad116
open StarCompletion APGeometry ThinFringe33 KKRetention32 Restore33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem crossing_interval_card_lower {C : Finset ℤ} {d p u v L R : ℤ} {n : ℕ}
    (hAP : APAt d p C) (hu : u∈C) (hv : v∈C) (huL : u<L) (hRv : R<v)
    (hspan : d*(n:ℤ)≤R-L+1) : n≤(C∩Finset.Icc L R).card := by
  let f : ℕ→ℤ := fun i=>L+(u-L)%d+d*(i:ℤ)
  have hd := hAP.1
  have hr0 := Int.emod_nonneg (u-L) (by omega : d≠0)
  have hrlt := Int.emod_lt_of_pos (u-L) hd
  have he := Int.emod_add_mul_ediv (u-L) d
  have hsub : (Finset.range n).image f⊆C∩Finset.Icc L R := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hi' : (i:ℤ)+1≤n := by exact_mod_cast (show i+1≤n from Finset.mem_range.mp hi)
    have hmul := mul_le_mul_of_nonneg_left hi' hd.le
    have hLf : L≤f i := by dsimp only [f];nlinarith [Int.natCast_nonneg i]
    have hfR : f i≤R := by dsimp only [f];nlinarith only [hspan,hmul,hrlt]
    refine Finset.mem_inter.mpr ⟨?_,Finset.mem_Icc.mpr ⟨hLf,hfR⟩⟩
    apply apAt_fill hAP hu hv (by omega) (by omega)
    refine ⟨(i:ℤ)-(u-L)/d,?_⟩
    dsimp only [f]
    nlinarith only [he]
  have hinj : Function.Injective f := by
    intro i j hij
    dsimp only [f] at hij
    have hh : (i:ℤ)=(j:ℤ) := by nlinarith only [hij,hd]
    exact_mod_cast hh
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj,Finset.card_range] at hc
  exact hc

theorem crossing_small_trace_step_ge13 {C S : Finset ℤ} {d p u v : ℤ} {L R : ℕ}
    (hLR : L≤R) (hM : 325≤R-L+1) (hAP : APAt d p C)
    (hu : u∈C) (hv : v∈C) (huL : u<(L:ℤ)) (hRv : (R:ℤ)<v)
    (hCS : C⊆S) (hshort : (S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1) :
    (13:ℤ)≤d := by
  by_contra hn
  have hd : d≤12 := by omega
  have hq : 25≤(R-L+1)/13 := by omega
  have hdiv := Nat.mul_div_le (R-L+1) 13
  have hdivZ : (13:ℤ)*((R-L+1)/13:ℕ)≤(R-L+1:ℕ) := by exact_mod_cast hdiv
  have hqZ : (25:ℤ)≤((R-L+1)/13:ℕ) := by exact_mod_cast hq
  have hmul := mul_le_mul_of_nonneg_right hd (show (0:ℤ)≤((R-L+1)/13+2:ℕ) by positivity)
  have hspan : d*(((R-L+1)/13+2:ℕ):ℤ)≤(R:ℤ)-L+1 := by
    have hc : ((R-L+1:ℕ):ℤ)=(R:ℤ)-L+1 := by omega
    norm_num only [Nat.cast_add,Nat.cast_ofNat] at hmul ⊢
    nlinarith only [hmul,hdivZ,hqZ,hc]
  have hc := crossing_interval_card_lower hAP hu hv huL hRv hspan
  have hsub : C∩Finset.Icc (L:ℤ) (R:ℤ)⊆S∩Finset.Icc (L:ℤ) (R:ℤ) := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨hCS (Finset.mem_inter.mp hx).1,(Finset.mem_inter.mp hx).2⟩
  have hcard := Finset.card_le_card hsub
  omega

theorem arm_card_upper13 {C : Finset ℤ} {d p a z : ℤ}
    (hAP : APAt d p C) (hd : 13≤d) :
    13*(C∩Finset.Icc a z).card≤(Finset.Icc a z).card+12 := by
  by_cases hne : (C∩Finset.Icc a z).Nonempty
  · have hp := BadFringe115.restrict_APAt (a:=a) (z:=z) hAP
    have hspan := apAt_span_eq hp hne
    have hlo := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.min'_mem _ hne)).2
    have hhi := Finset.mem_Icc.mp (Finset.mem_inter.mp (Finset.max'_mem _ hne)).2
    have hcard : ((Finset.Icc a z).card:ℤ)=z-a+1 := by simp only [Int.card_Icc];omega
    have hn : (0:ℤ)≤(C∩Finset.Icc a z).card-1 := by have hh := Finset.card_pos.mpr hne;omega
    have hm := mul_le_mul_of_nonneg_right hd hn
    have hb : (13:ℤ)*(C∩Finset.Icc a z).card≤(Finset.Icc a z).card+12 := by omega
    exact_mod_cast hb
  · have he : C∩Finset.Icc a z=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [he]

theorem actual_bad_rectangles_disjoint {N L R b : ℕ} {F E : Finset (Finset ℤ)}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hM : 325≤R-L+1)
    (hlegal : Legal (Ground N) F) (hEF : E⊆F)
    (hmiss : ∀S∈E,((Ground N\Finset.Icc (L:ℤ) (R:ℤ))\S).card≤b)
    (hshort : ∀S∈E,(S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1)
    (hshape : 64*b≤21*(L+N-R)) (hlarge : 90<L+N-R) :
    ∀S∈E,∀T∈E,S≠T→
      Disjoint ((S∩Finset.Icc (1:ℤ) ((L:ℤ)-1)).product (S∩Finset.Icc ((R:ℤ)+1) N))
        ((T∩Finset.Icc (1:ℤ) ((L:ℤ)-1)).product (T∩Finset.Icc ((R:ℤ)+1) N)) := by
  let O := Ground N\Finset.Icc (L:ℤ) (R:ℤ)
  let A := Finset.Icc (1:ℤ) ((L:ℤ)-1)
  let B := Finset.Icc ((R:ℤ)+1) N
  have hO : O=A∪B := by
    ext x
    simp only [O,A,B,Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_union,mem_ground]
    omega
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have ha := Finset.mem_Icc.mp hx
    have hb := Finset.mem_Icc.mp hy
    omega
  have hOc : O.card+1=L+N-R := by
    have he := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
      (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
    dsimp only [O]
    omega
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨haS,hbS⟩ := Finset.mem_product.mp hzS
  obtain ⟨haT,hbT⟩ := Finset.mem_product.mp hzT
  have hu : z.1∈S∩T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp haS).1,(Finset.mem_inter.mp haT).1⟩
  have hv : z.2∈S∩T := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hbS).1,(Finset.mem_inter.mp hbT).1⟩
  have hlu := (Finset.mem_Icc.mp (Finset.mem_inter.mp haS).2).2
  have hrv := (Finset.mem_Icc.mp (Finset.mem_inter.mp hbS).2).1
  obtain ⟨d,p,hAP,_hp⟩ := (isAP_iff_exists_APAt _).mp (hlegal.2 S (hEF hS) T (hEF hT) hne)
  have hd := crossing_small_trace_step_ge13 hLR hM hAP hu hv (by omega) (by omega)
    Finset.inter_subset_left (hshort S hS)
  have ha := arm_card_upper13 (a:=(1:ℤ)) (z:=(L:ℤ)-1) hAP hd
  have hb := arm_card_upper13 (a:=(R:ℤ)+1) (z:=(N:ℤ)) hAP hd
  have hc := BadFringe115.common_arm_card (O:=O) (A:=O) (Finset.Subset.refl O) (hmiss S hS) (hmiss T hT)
  have hcup : (S∩T)∩O=((S∩T)∩A)∪((S∩T)∩B) := by rw [hO,Finset.inter_union_distrib_left]
  have hupp := Finset.card_union_le ((S∩T)∩A) ((S∩T)∩B)
  have hOc' : O.card=A.card+B.card := by rw [hO,Finset.card_union_of_disjoint hAB]
  have hup : 13*((S∩T)∩O).card≤O.card+24 := by
    rw [hcup]
    change 13*((S∩T)∩A).card≤A.card+12 at ha
    change 13*((S∩T)∩B).card≤B.card+12 at hb
    omega
  omega

theorem actual_bad13_missing {N L R m : ℕ} {S : Finset ℤ}
    (hL : 1≤L) (hLR : L≤R) (hRN : R≤N) (hS : S⊆Ground N) (hm : m≤S.card)
    (hshort : (S∩Finset.Icc (L:ℤ) (R:ℤ)).card≤(R-L+1)/13+1) :
    ((Ground N\Finset.Icc (L:ℤ) (R:ℤ))\S).card≤(L+N-R)+(R-L+1)/13-m := by
  let I := Finset.Icc (L:ℤ) (R:ℤ)
  let O := Ground N\I
  have hs := Finset.card_sdiff_add_card_inter S I
  have ho := Finset.card_sdiff_add_card_inter O S
  have he : S\I=O∩S := by
    ext x
    change x∈S\I ↔ x∈(Ground N\I)∩S
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    constructor
    · intro h;exact ⟨⟨hS h.1,h.2⟩,h.1⟩
    · intro h;exact ⟨h.2,h.1.2⟩
  rw [he] at hs
  have hext := ground_interval_exterior_card N (by exact_mod_cast hL : (1:ℤ)≤L)
    (by exact_mod_cast hLR : (L:ℤ)≤R) (by exact_mod_cast hRN : (R:ℤ)≤N)
  have hext' : O.card+1=L+N-R := by dsimp only [O,I];omega
  change (O\S).card≤(L+N-R)+(R-L+1)/13-m
  change (S∩I).card≤(R-L+1)/13+1 at hshort
  omega

theorem actual_bad13_shape {N L R m : ℕ}
    (hLR : L≤R) (hRN : R≤N) (hm : N<11*m) (hpay : 2596*(L+N-R)≤61*N) :
    64*((L+N-R)+(R-L+1)/13-m)≤21*(L+N-R) := by
  let w := L+N-R
  let M := R-L+1
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 13
  by_cases hs : w+M/13<m
  · have hb : w+M/13-m=0 := by omega
    change 64*(w+M/13-m)≤21*w
    rw [hb]
    omega
  · have hsub := Nat.sub_add_cancel (show m≤w+M/13 by omega)
    have hd : 143*(w+M/13-m)+2*N+2≤132*w := by nlinarith only [hsub,hdiv,hMw,hm]
    change 2596*w≤61*N at hpay
    change 64*(w+M/13-m)≤21*w
    omega

#print axioms crossing_interval_card_lower
#print axioms crossing_small_trace_step_ge13
#print axioms arm_card_upper13
#print axioms actual_bad_rectangles_disjoint
#print axioms actual_bad13_missing
#print axioms actual_bad13_shape
end
end JSP233.CrossBad116
