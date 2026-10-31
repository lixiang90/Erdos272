import Erdos272.Resources.StarBoundConcrete30
import Erdos272.Foundation.APGeometry
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval

/-! A genuine one-third complement for actual legal AP-intersection families.
The Helly argument fixes an anchor member before applying interval geometry. -/
namespace JSP233.OneThird32
open StarCompletion APGeometry
open scoped Classical
noncomputable section

def Interval (S : Finset ℤ) : Prop :=
  ∀ a∈S, ∀ b∈S, ∀ x, a≤x → x≤b → x∈S

def SmallStep (S : Finset ℤ) : Prop := ∃ d p : ℤ, APAt d p S ∧ d≤2

def Phase (p : ℤ) (S : Finset ℤ) : Prop := APAt 1 p S ∨ APAt 2 p S

def ParityIndex (p : ℤ) (S : Finset ℤ) : Finset ℤ :=
  (S.filter (fun x => (x-p)%2=0)).image (fun x => (x-p)/2)

theorem mem_parityIndex (p x : ℤ) (S : Finset ℤ) :
    x∈ParityIndex p S ↔ p+2*x∈S := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hyS,hym⟩ := Finset.mem_filter.mp hy
    have hy : y=p+2*x := by omega
    simpa only [hy] using hyS
  · intro hx
    refine Finset.mem_image.mpr ⟨p+2*x,Finset.mem_filter.mpr ⟨hx,by omega⟩,?_⟩
    omega

theorem parityIndex_inter (p : ℤ) (S T : Finset ℤ) :
    ParityIndex p (S∩T)=ParityIndex p S∩ParityIndex p T := by
  ext x
  simp only [mem_parityIndex,Finset.mem_inter]

theorem apAt_residue {d p x : ℤ} {S : Finset ℤ} (h : APAt d p S)
    (hx : x∈S) : d∣x-p := by
  obtain ⟨hd,lo,hi,hr⟩ := h
  exact ((hr x).mp hx).2.2

theorem apAt_change_phase {d p q : ℤ} {S : Finset ℤ}
    (h : APAt d q S) (hp : d∣p-q) : APAt d p S := by
  obtain ⟨hd,lo,hi,hr⟩ := h
  refine ⟨hd,lo,hi,?_⟩
  intro x
  constructor
  · intro hx
    obtain ⟨hl,hu,hdiv⟩ := (hr x).mp hx
    refine ⟨hl,hu,?_⟩
    convert Int.dvd_sub hdiv hp using 1; ring
  · rintro ⟨hl,hu,hdiv⟩
    apply (hr x).mpr
    refine ⟨hl,hu,?_⟩
    convert Int.dvd_add hdiv hp using 1; ring

theorem phase_inter {p : ℤ} {S T : Finset ℤ}
    (hS : Phase p S) (hT : Phase p T) : Phase p (S∩T) := by
  rcases hS with hS | hS <;> rcases hT with hT | hT
  · exact Or.inl (by simpa using apAt_inter hS hT)
  · exact Or.inr (by simpa using apAt_inter hS hT)
  · exact Or.inr (by simpa using apAt_inter hS hT)
  · exact Or.inr (by simpa using apAt_inter hS hT)

theorem common_phase (H : Finset (Finset ℤ))
    (hsmall : ∀ S∈H, SmallStep S)
    (hpair : ∀ S∈H, ∀ T∈H, (S∩T).Nonempty) :
    ∃ p : ℤ, ∀ S∈H, Phase p S := by
  by_cases htwo : ∃ S∈H, ∃ p : ℤ, APAt 2 p S
  · obtain ⟨R,hR,p,hRp⟩ := htwo
    refine ⟨p,?_⟩
    intro S hS
    obtain ⟨d,q,hd,hd2⟩ := hsmall S hS
    have hor : d=1 ∨ d=2 := by have := hd.1; omega
    rcases hor with rfl | rfl
    · exact Or.inl (apAt_change_phase hd (one_dvd _))
    · obtain ⟨x,hx⟩ := hpair R hR S hS
      obtain ⟨hxR,hxS⟩ := Finset.mem_inter.mp hx
      have hp := apAt_residue hRp hxR
      have hq := apAt_residue hd hxS
      have he : (2:ℤ)∣p-q := by
        convert Int.dvd_sub hq hp using 1; ring
      exact Or.inr (apAt_change_phase hd he)
  · refine ⟨0,?_⟩
    intro S hS
    obtain ⟨d,p,hd,hd2⟩ := hsmall S hS
    have hor : d=1 ∨ d=2 := by have := hd.1; omega
    rcases hor with rfl | rfl
    · exact Or.inl (apAt_change_phase hd (one_dvd _))
    · exact False.elim (htwo ⟨S,hS,p,hd⟩)

theorem parityIndex_interval {p : ℤ} {S : Finset ℤ} (hS : Phase p S) :
    Interval (ParityIndex p S) := by
  intro a ha b hb x hax hxb
  rw [mem_parityIndex] at ha hb ⊢
  rcases hS with hS | hS
  · apply apAt_fill hS ha hb (by omega) (by omega)
    exact one_dvd _
  · apply apAt_fill hS ha hb (by omega) (by omega)
    exact ⟨x-a,by ring⟩

theorem parityIndex_card_two {p : ℤ} {S : Finset ℤ}
    (hS : Phase p S) (hcard : 4≤S.card) : 2≤(ParityIndex p S).card := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let a := S.min' hne
  let b := S.max' hne
  have ha : a∈S := Finset.min'_mem S hne
  have hb : b∈S := Finset.max'_mem S hne
  rcases hS with hS | hS
  · have hspan := apAt_span_eq hS hne
    have hlen : a+3≤b := by dsimp only [a,b]; omega
    let x := (a-p+1)/2
    have hax : a≤p+2*x := by dsimp only [x]; omega
    have hxb : p+2*(x+1)≤b := by dsimp only [x]; omega
    have hx : x∈ParityIndex p S := by
      rw [mem_parityIndex]
      exact apAt_fill hS ha hb hax (by omega) (one_dvd _)
    have hy : x+1∈ParityIndex p S := by
      rw [mem_parityIndex]
      exact apAt_fill hS ha hb (by omega) hxb (one_dvd _)
    have := Finset.one_lt_card.mpr ⟨x,hx,x+1,hy,by omega⟩
    omega
  · have hspan := apAt_span_eq hS hne
    have hlen : a+2≤b := by dsimp only [a,b]; omega
    have hdiv := apAt_residue hS ha
    have hmod := Int.emod_eq_zero_of_dvd hdiv
    let x := (a-p)/2
    have he : p+2*x=a := by dsimp only [x]; omega
    have hx : x∈ParityIndex p S := by simpa only [mem_parityIndex,he] using ha
    have hy : x+1∈ParityIndex p S := by
      rw [mem_parityIndex]
      apply apAt_fill hS ha hb (by omega) (by omega)
      refine ⟨1,?_⟩
      omega
    have := Finset.one_lt_card.mpr ⟨x,hx,x+1,hy,by omega⟩
    omega

theorem interval_helly_two (H : Finset (Finset ℤ)) (hne : H.Nonempty)
    (hint : ∀ S∈H, Interval S)
    (hpair : ∀ S∈H, ∀ T∈H, 2≤(S∩T).card) :
    ∃ x y : ℤ, x≠y ∧ ∀ S∈H, x∈S ∧ y∈S := by
  have hn : ∀ S∈H, S.Nonempty := by
    intro S hS
    have hh := hpair S hS S hS
    have hp : 0<S.card := by simpa only [Finset.inter_self] using (show 0<(S∩S).card by omega)
    exact Finset.card_pos.mp hp
  let low (S : Finset ℤ) := if hs:S.Nonempty then S.min' hs else 0
  let high (S : Finset ℤ) := if hs:S.Nonempty then S.max' hs else 0
  obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image H low hne
  obtain ⟨B,hB,hmin⟩ := Finset.exists_min_image H high hne
  have hsub : ∀ z∈A∩B, ∀ S∈H, z∈S := by
    intro z hz S hS
    have hzA := (Finset.mem_inter.mp hz).1
    have hzB := (Finset.mem_inter.mp hz).2
    have hl := hmax S hS
    have hu := hmin S hS
    have hla := Finset.min'_le A z hzA
    have hub := Finset.le_max' B z hzB
    have hSlo : low S∈S := by simp only [low,dif_pos (hn S hS)]; exact Finset.min'_mem S _
    have hShi : high S∈S := by simp only [high,dif_pos (hn S hS)]; exact Finset.max'_mem S _
    have hloA : low A≤z := by simpa only [low,dif_pos (hn A hA)] using hla
    have hhiB : z≤high B := by simpa only [high,dif_pos (hn B hB)] using hub
    exact hint S hS _ hSlo _ hShi z (by omega) (by omega)
  have hcardAB : 1<(A∩B).card := by have := hpair A hA B hB; omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp hcardAB
  exact ⟨x,y,hxy,fun S hS => ⟨hsub x hx S hS,hsub y hy S hS⟩⟩

theorem smallStep_helly_four (H : Finset (Finset ℤ)) (hne : H.Nonempty)
    (hsmall : ∀ S∈H, SmallStep S)
    (hpair : ∀ S∈H, ∀ T∈H, 4≤(S∩T).card) :
    ∃ x y : ℤ, x≠y ∧ ∀ S∈H, x∈S ∧ y∈S := by
  obtain ⟨p,hphase⟩ := common_phase H hsmall (by
    intro S hS T hT
    exact Finset.card_pos.mp (by have := hpair S hS T hT; omega))
  let J := H.image (ParityIndex p)
  have hJ : J.Nonempty := hne.image _
  have hint : ∀ S∈J, Interval S := by
    intro S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    exact parityIndex_interval (hphase T hT)
  have hJpair : ∀ S∈J, ∀ T∈J, 2≤(S∩T).card := by
    intro S hS T hT
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
    rw [←parityIndex_inter]
    exact parityIndex_card_two (phase_inter (hphase A hA) (hphase B hB)) (hpair A hA B hB)
  obtain ⟨x,y,hxy,hall⟩ := interval_helly_two J hJ hint hJpair
  refine ⟨p+2*x,p+2*y,by omega,?_⟩
  intro S hS
  have hh := hall _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  exact ⟨(mem_parityIndex p x S).mp hh.1,(mem_parityIndex p y S).mp hh.2⟩

theorem card_inter_lower (V A B : Finset ℤ) (hA : A⊆V) (hB : B⊆V) :
    A.card+B.card≤V.card+(A∩B).card := by
  have hu := Finset.card_le_card (Finset.union_subset hA hB)
  have he := Finset.card_union_add_card_inter A B
  omega

theorem card_triple_lower (V A B C : Finset ℤ)
    (hA : A⊆V) (hB : B⊆V) (hC : C⊆V) :
    A.card+B.card+C.card≤2*V.card+((A∩B)∩C).card := by
  have h1 := card_inter_lower V A B hA hB
  have h2 := card_inter_lower V (A∩B) C (Finset.inter_subset_left.trans hA) hC
  omega

theorem dense_triple_card (V : Finset ℤ) (D : Finset (Finset ℤ))
    (hground : ∀ S∈D, S⊆V) (hdense : ∀ S∈D, 2*V.card+4≤3*S.card)
    {A B C : Finset ℤ} (hA : A∈D) (hB : B∈D) (hC : C∈D) :
    4≤((A∩B)∩C).card := by
  have hh := card_triple_lower V A B C (hground A hA) (hground B hB) (hground C hC)
  have ha := hdense A hA
  have hb := hdense B hB
  have hc := hdense C hC
  omega

theorem dense_pair_smallStep (N : ℕ) (c : ℤ) (D : Finset (Finset ℤ))
    (hc : c∈Ground N) (hground : ∀ S∈D, S⊆(Ground N).erase c)
    (hlegal : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    (hdense : ∀ S∈D, 2*((Ground N).erase c).card+4≤3*S.card)
    {A B : Finset ℤ} (hA : A∈D) (hB : B∈D) (hne : A≠B) : SmallStep (A∩B) := by
  obtain ⟨d,p,hd,hp⟩ := (isAP_iff_exists_APAt _).mp (hlegal A hA B hB hne)
  refine ⟨d,p,hd,?_⟩
  have hspan := apAt_card_span hd ⟨p,hp⟩ (by
    intro x hx
    have hxG := (Finset.mem_erase.mp (hground A hA (Finset.mem_inter.mp hx).1)).2
    exact Finset.mem_Icc.mpr ((mem_ground N x).mp hxG))
  have hu := card_inter_lower ((Ground N).erase c) A B (hground A hA) (hground B hB)
  have ha := hdense A hA
  have hb := hdense B hB
  have hv : ((Ground N).erase c).card=N-1 := by
    rw [Finset.card_erase_of_mem hc,ground_card]
  have hN : 1≤N := by have := (mem_ground N c).mp hc; omega
  have hsize : ((Ground N).erase c).card+8≤3*(A∩B).card := by omega
  have hpos : 1≤(A∩B).card := by omega
  by_contra hn
  have hd3 : 3≤d := by omega
  have hprod : (3:ℤ)*((A∩B).card-1)≤d*((A∩B).card-1) :=
    mul_le_mul_of_nonneg_right hd3 (by omega)
  have hs : (((Ground N).erase c).card:ℤ)+8≤3*((A∩B).card:ℤ) := by exact_mod_cast hsize
  omega

theorem dense_family_kernel_two (N : ℕ) (c : ℤ) (D : Finset (Finset ℤ))
    (hc : c∈Ground N) (hground : ∀ S∈D, S⊆(Ground N).erase c)
    (hlegal : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T)) (htwo : 2≤D.card)
    (hdense : ∀ S∈D, 2*((Ground N).erase c).card+4≤3*S.card) :
    2≤((Ground N).filter (fun x => ∀ S∈D, x∈S)).card := by
  obtain ⟨A,hA⟩ := Finset.card_pos.mp (by omega : 0<D.card)
  have he : (D.erase A).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hA]
    omega
  let H := (D.erase A).image (fun T => A∩T)
  have hH : H.Nonempty := he.image _
  have hsmall : ∀ S∈H, SmallStep S := by
    intro S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hTA,hTD⟩ := Finset.mem_erase.mp hT
    exact dense_pair_smallStep N c D hc hground hlegal hdense hA hTD hTA.symm
  have hpair : ∀ S∈H, ∀ T∈H, 4≤(S∩T).card := by
    intro S hS T hT
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hT
    have hh := dense_triple_card _ D hground hdense hA
      (Finset.mem_erase.mp hB).2 (Finset.mem_erase.mp hC).2
    have heq : (A∩B)∩(A∩C)=(A∩B)∩C := by
      ext x
      simp only [Finset.mem_inter]
      tauto
    simpa only [heq] using hh
  obtain ⟨x,y,hxy,hall⟩ := smallStep_helly_four H hH hsmall hpair
  have hcore : ∀ z : ℤ, (∀ S∈H, z∈S) →
      z∈(Ground N).filter (fun z => ∀ S∈D, z∈S) := by
    intro z hz
    obtain ⟨T,hT⟩ := he
    have hzAT := hz _ (Finset.mem_image.mpr ⟨T,hT,rfl⟩)
    have hzA := (Finset.mem_inter.mp hzAT).1
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_erase.mp (hground A hA hzA)).2,?_⟩
    intro S hS
    by_cases hSA : S=A
    · simpa only [hSA] using hzA
    · have hzAS := hz _ (Finset.mem_image.mpr ⟨S,Finset.mem_erase.mpr ⟨hSA,hS⟩,rfl⟩)
      exact (Finset.mem_inter.mp hzAS).2
  have hx := hcore x (fun S hS => (hall S hS).1)
  have hy := hcore y (fun S hS => (hall S hS).2)
  have hh := Finset.one_lt_card.mpr ⟨x,hx,y,hy,hxy⟩
  omega

theorem exists_one_third_complement (N : ℕ) (c : ℤ) (D : Finset (Finset ℤ))
    (hc : c∈Ground N) (hground : ∀ S∈D, S⊆(Ground N).erase c)
    (hlegal : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T)) (htwo : 2≤D.card)
    (hkernel : ((Ground N).filter (fun x => ∀ S∈D, x∈S)).card≤1) :
    ∃ T∈D, ((Ground N).erase c).card≤3*(((Ground N).erase c)\T).card+3 := by
  by_contra hn
  push Not at hn
  have hdense : ∀ T∈D, 2*((Ground N).erase c).card+4≤3*T.card := by
    intro T hT
    have hh := hn T hT
    have he := Finset.card_sdiff_add_card_eq_card (hground T hT)
    omega
  have hh := dense_family_kernel_two N c D hc hground hlegal htwo hdense
  omega

theorem actual_one_third_complement (N : ℕ) (c : ℤ) (F : Finset (Finset ℤ))
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (htwo : 2≤(Avoiders F c).card) (hkernel : (CommonKernel (Ground N) F c).card≤1) :
    ∃ T∈Avoiders F c, 3*(((Ground N).erase c)\T).card≥N-4 := by
  have hground : ∀ T∈Avoiders F c, T⊆(Ground N).erase c := by
    intro T hT x hx
    obtain ⟨hTF,hcT⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_erase.mpr ⟨by intro he; exact hcT (he ▸ hx),hlegal.1 T hTF hx⟩
  obtain ⟨T,hT,hq⟩ := exists_one_third_complement N c (Avoiders F c) hc hground
    (fun S hS T hT hne => hlegal.2 S (Finset.mem_filter.mp hS).1 T
      (Finset.mem_filter.mp hT).1 hne) htwo hkernel
  have hv : ((Ground N).erase c).card=N-1 := by
    rw [Finset.card_erase_of_mem hc,ground_card]
  refine ⟨T,hT,?_⟩
  omega

#print axioms mem_parityIndex
#print axioms parityIndex_inter
#print axioms apAt_residue
#print axioms apAt_change_phase
#print axioms phase_inter
#print axioms common_phase
#print axioms parityIndex_interval
#print axioms parityIndex_card_two
#print axioms interval_helly_two
#print axioms smallStep_helly_four
#print axioms card_inter_lower
#print axioms card_triple_lower
#print axioms dense_triple_card
#print axioms dense_pair_smallStep
#print axioms dense_family_kernel_two
#print axioms exists_one_third_complement
#print axioms actual_one_third_complement
end
end JSP233.OneThird32
