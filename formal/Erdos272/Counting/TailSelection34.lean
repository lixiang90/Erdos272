module

public import Erdos272.Capacity.AnchorCapacity33

@[expose] public section

/-! Actual pure-trace tail choices and same-side collision-class exclusion.
No collision tree or numerical capacity is assumed. -/
namespace JSP233.TailSelection34
open StarCompletion APGeometry AnchorCapacity33
open scoped Classical
noncomputable section

def PureTrace (u v g d : ℤ) (S : Finset ℤ) : Prop :=
  0<d ∧ d∣g ∧ S∩Finset.Icc u v=AnchorTrace u v d

def TailChoice (D : Finset (Finset ℤ)) (step : Finset ℤ→ℤ) (u v : ℤ)
    (tail : Finset ℤ→ℤ) : Prop :=
  ∀ S∈D, tail S∈S ∧ tail S∉Finset.Icc u v ∧
    ∀ T∈D, T≠S → step T∣step S → tail S∉T

theorem pure_trace_points {u v g d : ℤ} {S : Finset ℤ} (hg : 0<g)
    (hspan : u+g≤v) (hvg : g∣v-u) (hS : PureTrace u v g d S) :
    u∈S ∧ u+g∈S ∧ v∈S := by
  obtain ⟨hd,hdg,he⟩ := hS
  have hu : u∈S∩Finset.Icc u v := by
    rw [he]
    exact (mem_anchorTrace u v d u).mpr ⟨by omega,by omega,by simp⟩
  have hug : u+g∈S∩Finset.Icc u v := by
    rw [he]
    exact (mem_anchorTrace u v d _).mpr ⟨by omega,hspan,by simpa using hdg⟩
  have hv : v∈S∩Finset.Icc u v := by
    rw [he]
    exact (mem_anchorTrace u v d v).mpr ⟨by omega,le_rfl,hdg.trans hvg⟩
  exact ⟨(Finset.mem_inter.mp hu).1,(Finset.mem_inter.mp hug).1,(Finset.mem_inter.mp hv).1⟩

theorem pure_trace_APAt {u v g d : ℤ} {S : Finset ℤ} (hS : PureTrace u v g d S) :
    APAt d u (S∩Finset.Icc u v) := by
  refine ⟨hS.1,u,v,?_⟩
  intro x
  rw [hS.2.2]
  exact mem_anchorTrace u v d x

theorem APAt_trace_eq {u v d : ℤ} {S : Finset ℤ}
    (hS : APAt d u S) (hu : u∈S) (hv : v∈S) :
    S∩Finset.Icc u v=AnchorTrace u v d := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_Icc,mem_anchorTrace]
  constructor
  · rintro ⟨hx,hux,hxv⟩
    exact ⟨hux,hxv,apAt_dvd_sub hS hu hx⟩
  · rintro ⟨hux,hxv,hdx⟩
    exact ⟨apAt_fill hS hu hv hux hxv hdx,hux,hxv⟩

theorem anchorTrace_inter_eq (u v d e : ℤ) :
    AnchorTrace u v d∩AnchorTrace u v e=AnchorTrace u v (Int.lcm d e : ℤ) := by
  ext x
  simp only [Finset.mem_inter,mem_anchorTrace,Int.coe_lcm_dvd_iff]
  tauto

theorem pure_pair_trace_lcm {u v g d e : ℤ} {S T : Finset ℤ}
    (hS : PureTrace u v g d S) (hT : PureTrace u v g e T) :
    (S∩T)∩Finset.Icc u v=AnchorTrace u v (Int.lcm d e : ℤ) := by
  have he : (S∩T)∩Finset.Icc u v=(S∩Finset.Icc u v)∩(T∩Finset.Icc u v) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  rw [he,hS.2.2,hT.2.2,anchorTrace_inter_eq]

theorem pure_pair_APAt_lcm {u v g d e : ℤ} {S T : Finset ℤ} (hg : 0<g)
    (hspan : u+g≤v) (hvg : g∣v-u) (hS : PureTrace u v g d S)
    (hT : PureTrace u v g e T) (hpair : IsAP (S∩T)) :
    APAt (Int.lcm d e : ℤ) u (S∩T) := by
  obtain ⟨huS,hugS,hvS⟩ := pure_trace_points hg hspan hvg hS
  obtain ⟨huT,hugT,hvT⟩ := pure_trace_points hg hspan hvg hT
  have hu : u∈S∩T := Finset.mem_inter.mpr ⟨huS,huT⟩
  have hug : u+g∈S∩T := Finset.mem_inter.mpr ⟨hugS,hugT⟩
  have hv : v∈S∩T := Finset.mem_inter.mpr ⟨hvS,hvT⟩
  obtain ⟨q,hq,hqg,hstep⟩ := PrimeKernel.step_dvd_gap (S∩T) u (u+g) hpair hu hug
  have hqg' : q∣g := by simpa using hqg
  have hL : 0<(Int.lcm d e : ℤ) := by
    exact_mod_cast Int.lcm_pos (by have := hS.1; omega) (by have := hT.1; omega)
  have hLg : (Int.lcm d e : ℤ)∣g := Int.coe_lcm_dvd_iff.mpr ⟨hS.2.1,hT.2.1⟩
  have he : q=(Int.lcm d e : ℤ) := (anchorTrace_eq_iff hg hspan hq hL hqg' hLg).mp
    ((APAt_trace_eq hstep hu hv).symm.trans (pure_pair_trace_lcm hS hT))
  simpa only [APAt,he] using hstep

theorem comparable_pair_trace {u v g d e : ℤ} {S T : Finset ℤ}
    (hS : PureTrace u v g d S) (hT : PureTrace u v g e T) (hed : e∣d) :
    (S∩T)∩Finset.Icc u v=AnchorTrace u v d := by
  have he : (S∩T)∩Finset.Icc u v=(S∩Finset.Icc u v)∩(T∩Finset.Icc u v) := by
    ext x
    simp only [Finset.mem_inter]
    tauto
  rw [he,hS.2.2,hT.2.2]
  exact Finset.inter_eq_left.mpr (anchorTrace_antitone hed)

theorem comparable_pair_APAt {u v g d e : ℤ} {S T : Finset ℤ} (hg : 0<g)
    (hspan : u+g≤v) (hvg : g∣v-u) (hS : PureTrace u v g d S)
    (hT : PureTrace u v g e T) (hpair : IsAP (S∩T)) (hed : e∣d) :
    APAt d u (S∩T) := by
  obtain ⟨huS,hugS,hvS⟩ := pure_trace_points hg hspan hvg hS
  obtain ⟨huT,hugT,hvT⟩ := pure_trace_points hg hspan hvg hT
  have hu : u∈S∩T := Finset.mem_inter.mpr ⟨huS,huT⟩
  have hug : u+g∈S∩T := Finset.mem_inter.mpr ⟨hugS,hugT⟩
  have hv : v∈S∩T := Finset.mem_inter.mpr ⟨hvS,hvT⟩
  obtain ⟨q,hq,hqg,hstep⟩ := PrimeKernel.step_dvd_gap (S∩T) u (u+g) hpair hu hug
  have hqg' : q∣g := by simpa using hqg
  have htq := APAt_trace_eq hstep hu hv
  have htd := comparable_pair_trace hS hT hed
  have he : q=d := (anchorTrace_eq_iff hg hspan hq hS.1 hqg' hS.2.1).mp (htq.symm.trans htd)
  simpa only [APAt,he] using hstep

theorem actual_pure_private_tail (D : Finset (Finset ℤ)) (step : Finset ℤ→ℤ)
    (u v g : ℤ) (hg : 0<g) (hspan : u+g≤v) (hvg : g∣v-u)
    (hpure : ∀ S∈D, PureTrace u v g (step S) S)
    (hbad : ∀ S∈D, ¬IsAP S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    {S : Finset ℤ} (hS : S∈D) :
    ∃ x, x∈S ∧ x∉Finset.Icc u v ∧ ∀ T∈D, T≠S → step T∣step S → x∉T := by
  let C := D.filter (fun T => step T∣step S)
  have huD : ∀ T∈D, u∈T := fun T hT => (pure_trace_points hg hspan hvg (hpure T hT)).1
  have huI : u∈Finset.Icc u v := Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hcore : PrivateUnion.APAt (step S) u (fun x => x∈S ∧ x∈Finset.Icc u v) := by
    simpa only [APAt,Finset.mem_inter] using pure_trace_APAt (hpure S hS)
  obtain ⟨x,hx,hxI,hpriv⟩ := TwoTraceGlobal.private_exterior_finset C S (Finset.Icc u v)
    (step S) u (huD S hS) huI
    (fun T hT => huD T (Finset.mem_filter.mp hT).1) (hbad S hS) hcore (by
      intro T hT hne
      obtain ⟨hTD,hdiv⟩ := Finset.mem_filter.mp hT
      simpa only [APAt,Finset.mem_inter] using comparable_pair_APAt hg hspan hvg
        (hpure S hS) (hpure T hTD) (hpair S hS T hTD hne) hdiv)
  exact ⟨x,hx,hxI,fun T hT hTS hdiv =>
    hpriv T (Finset.mem_filter.mpr ⟨hT,hdiv⟩) hTS.symm⟩

theorem actual_pure_tail_choice (D : Finset (Finset ℤ)) (step : Finset ℤ→ℤ)
    (u v g : ℤ) (hg : 0<g) (hspan : u+g≤v) (hvg : g∣v-u)
    (hpure : ∀ S∈D, PureTrace u v g (step S) S)
    (hbad : ∀ S∈D, ¬IsAP S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T)) :
    ∃ tail : Finset ℤ→ℤ, TailChoice D step u v tail := by
  have hex := fun (S : Finset ℤ) (hS : S∈D) =>
    actual_pure_private_tail D step u v g hg hspan hvg hpure hbad hpair hS
  let tail := fun S => if hs : S∈D then (hex S hs).choose else 0
  refine ⟨tail,?_⟩
  intro S hS
  simpa only [tail,dif_pos hS] using (hex S hS).choose_spec

theorem comparable_equal_tail_eq {D : Finset (Finset ℤ)} {step : Finset ℤ→ℤ}
    {u v : ℤ} {tail : Finset ℤ→ℤ} (hc : TailChoice D step u v tail)
    {S T : Finset ℤ} (hS : S∈D) (hT : T∈D)
    (he : tail S=tail T) (hcomp : step S∣step T ∨ step T∣step S) : S=T := by
  by_contra hne
  rcases hcomp with hST | hTS
  · exact (hc T hT).2.2 S hS hne hST (he ▸ (hc S hS).1)
  · exact (hc S hS).2.2 T hT (Ne.symm hne) hTS (he.symm ▸ (hc T hT).1)

theorem same_class_equal_tail_eq {D : Finset (Finset ℤ)} {step : Finset ℤ→ℤ}
    {u v : ℤ} {tail : Finset ℤ→ℤ} (hc : TailChoice D step u v tail)
    {S T : Finset ℤ} (hS : S∈D) (hT : T∈D)
    (he : tail S=tail T) (hs : step S=step T) : S=T := by
  apply comparable_equal_tail_eq hc hS hT he
  exact Or.inl (hs ▸ dvd_refl (step S))

theorem collision_steps_incomparable {D : Finset (Finset ℤ)} {step : Finset ℤ→ℤ}
    {u v : ℤ} {tail : Finset ℤ→ℤ} (hc : TailChoice D step u v tail)
    {S T : Finset ℤ} (hS : S∈D) (hT : T∈D) (hne : S≠T) (he : tail S=tail T) :
    ¬step S∣step T ∧ ¬step T∣step S := by
  exact ⟨fun h => hne (comparable_equal_tail_eq hc hS hT he (Or.inl h)),
    fun h => hne (comparable_equal_tail_eq hc hS hT he (Or.inr h))⟩

theorem left_same_label_collision_impossible {D : Finset (Finset ℤ)}
    {step : Finset ℤ→ℤ} {u v L x y : ℤ} {tail : Finset ℤ→ℤ}
    (hc : TailChoice D step u v tail) (hu : ∀ S∈D, u∈S)
    {S T U V : Finset ℤ} (hS : S∈D) (hT : T∈D) (hU : U∈D) (hV : V∈D)
    (hst : APAt L u (S∩T)) (huv : APAt L u (U∩V))
    (hSX : tail S=x) (hTX : tail T=x) (hUY : tail U=y) (hVY : tail V=y)
    (hxy : x<y) (hyu : y<u) (hclass : step S=step U) : False := by
  have hxS : x∈S := hSX ▸ (hc S hS).1
  have hxT : x∈T := hTX ▸ (hc T hT).1
  have hyU : y∈U := hUY ▸ (hc U hU).1
  have hyV : y∈V := hVY ▸ (hc V hV).1
  have hxst : x∈S∩T := Finset.mem_inter.mpr ⟨hxS,hxT⟩
  have hust : u∈S∩T := Finset.mem_inter.mpr ⟨hu S hS,hu T hT⟩
  have hyuv : y∈U∩V := Finset.mem_inter.mpr ⟨hyU,hyV⟩
  have huuv : u∈U∩V := Finset.mem_inter.mpr ⟨hu U hU,hu V hV⟩
  have hLyu := apAt_dvd_sub huv huuv hyuv
  have hLxu := apAt_dvd_sub hst hust hxst
  have hLyx : L∣y-x := by
    convert Int.dvd_sub hLyu hLxu using 1
    ring
  have hyS := (Finset.mem_inter.mp (apAt_fill hst hxst hust hxy.le hyu.le hLyx)).1
  have hSU : S≠U := by intro he; subst U; omega
  exact (hc U hU).2.2 S hS hSU (hclass ▸ dvd_refl (step S)) (hUY.symm ▸ hyS)

theorem right_same_label_collision_impossible {D : Finset (Finset ℤ)}
    {step : Finset ℤ→ℤ} {u v L x y : ℤ} {tail : Finset ℤ→ℤ}
    (hc : TailChoice D step u v tail) (hu : ∀ S∈D, u∈S)
    {S T U V : Finset ℤ} (hS : S∈D) (hT : T∈D) (hU : U∈D) (hV : V∈D)
    (hst : APAt L u (S∩T)) (huv : APAt L u (U∩V))
    (hSX : tail S=x) (hTX : tail T=x) (hUY : tail U=y) (hVY : tail V=y)
    (hux : u<x) (hxy : x<y) (hclass : step S=step U) : False := by
  have hxS : x∈S := hSX ▸ (hc S hS).1
  have hxT : x∈T := hTX ▸ (hc T hT).1
  have hyU : y∈U := hUY ▸ (hc U hU).1
  have hyV : y∈V := hVY ▸ (hc V hV).1
  have hxst : x∈S∩T := Finset.mem_inter.mpr ⟨hxS,hxT⟩
  have hust : u∈S∩T := Finset.mem_inter.mpr ⟨hu S hS,hu T hT⟩
  have hyuv : y∈U∩V := Finset.mem_inter.mpr ⟨hyU,hyV⟩
  have huuv : u∈U∩V := Finset.mem_inter.mpr ⟨hu U hU,hu V hV⟩
  have hLxu := apAt_dvd_sub hst hust hxst
  have hxU := (Finset.mem_inter.mp (apAt_fill huv huuv hyuv hux.le hxy.le hLxu)).1
  have hUS : U≠S := by intro he; subst U; omega
  exact (hc S hS).2.2 U hU hUS (hclass.symm ▸ dvd_refl (step U)) (hSX.symm ▸ hxU)

def CollisionClasses (D : Finset (Finset ℤ)) (step tail : Finset ℤ→ℤ)
    (u L x : ℤ) : Finset ℤ :=
  (D.filter (fun S => tail S=x ∧ ∃ T∈D, T≠S ∧ tail T=x ∧ APAt L u (S∩T))).image step

theorem same_side_collision_classes_disjoint {D : Finset (Finset ℤ)}
    {step tail : Finset ℤ→ℤ} {u v L x y : ℤ}
    (hc : TailChoice D step u v tail) (hu : ∀ S∈D, u∈S) (hne : x≠y)
    (hside : (x<u ∧ y<u) ∨ (u<x ∧ u<y)) :
    Disjoint (CollisionClasses D step tail u L x) (CollisionClasses D step tail u L y) := by
  apply Finset.disjoint_left.mpr
  intro d hd he
  obtain ⟨S,hSC,hSd⟩ := Finset.mem_image.mp hd
  obtain ⟨U,hUC,hUd⟩ := Finset.mem_image.mp he
  obtain ⟨hS,hSX,T,hT,hTS,hTX,hst⟩ := Finset.mem_filter.mp hSC
  obtain ⟨hU,hUY,V,hV,hVU,hVY,huv⟩ := Finset.mem_filter.mp hUC
  have hclass : step S=step U := hSd.trans hUd.symm
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · rcases hside with hleft | hright
    · exact left_same_label_collision_impossible hc hu hS hT hU hV hst huv hSX hTX hUY hVY
        hxy hleft.2 hclass
    · exact right_same_label_collision_impossible hc hu hS hT hU hV hst huv hSX hTX hUY hVY
        hright.1 hxy hclass
  · rcases hside with hleft | hright
    · exact left_same_label_collision_impossible hc hu hU hV hS hT huv hst hUY hVY hSX hTX
        hyx hleft.1 hclass.symm
    · exact right_same_label_collision_impossible hc hu hU hV hS hT huv hst hUY hVY hSX hTX
        hright.2 hyx hclass.symm

theorem actual_pure_tail_selection_geometry (D : Finset (Finset ℤ)) (step : Finset ℤ→ℤ)
    (u v g : ℤ) (hg : 0<g) (hspan : u+g≤v) (hvg : g∣v-u)
    (hpure : ∀ S∈D, PureTrace u v g (step S) S)
    (hbad : ∀ S∈D, ¬IsAP S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T)) :
    ∃ tail : Finset ℤ→ℤ, TailChoice D step u v tail ∧
      ∀ L x y : ℤ, x≠y → ((x<u ∧ y<u) ∨ (u<x ∧ u<y)) →
        Disjoint (CollisionClasses D step tail u L x) (CollisionClasses D step tail u L y) := by
  obtain ⟨tail,hc⟩ := actual_pure_tail_choice D step u v g hg hspan hvg hpure hbad hpair
  refine ⟨tail,hc,?_⟩
  intro L x y hne hside
  exact same_side_collision_classes_disjoint hc
    (fun S hS => (pure_trace_points hg hspan hvg (hpure S hS)).1) hne hside

#print axioms pure_trace_points
#print axioms pure_trace_APAt
#print axioms APAt_trace_eq
#print axioms anchorTrace_inter_eq
#print axioms pure_pair_trace_lcm
#print axioms pure_pair_APAt_lcm
#print axioms comparable_pair_trace
#print axioms comparable_pair_APAt
#print axioms actual_pure_private_tail
#print axioms actual_pure_tail_choice
#print axioms comparable_equal_tail_eq
#print axioms same_class_equal_tail_eq
#print axioms collision_steps_incomparable
#print axioms left_same_label_collision_impossible
#print axioms right_same_label_collision_impossible
#print axioms same_side_collision_classes_disjoint
#print axioms actual_pure_tail_selection_geometry
end
end JSP233.TailSelection34
