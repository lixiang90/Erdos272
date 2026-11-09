module

public import Erdos272.Traces.CollisionTree35
public import Erdos272.Resources.CollisionLabels34

@[expose] public section

/-! Actual pure-trace tail collisions, using the finite global decomposition.
Actual tail privacy gives faithful coordinate antichains. Every constructed
clique has a genuine lcm AP-intersection label, and the previously certified
same-side geometry supplies the packing needed for the two-sided net fee.
This module proves the pure collision payment, not the full anchor capacity. -/
namespace JSP233.PureTailCollision35
open StarCompletion APGeometry AnchorCapacity33 FactorCells34 TailSelection34 CollisionLabels34
open scoped Classical BigOperators
noncomputable section

def Owners (D : Finset (Finset ℤ)) (tail : Finset ℤ→ℤ) (x : ℤ) :=
  D.filter (fun S => tail S=x)

def OwnerPoints (g : ℕ) (D : Finset (Finset ℤ)) (step : Finset ℤ→ℕ)
    (tail : Finset ℤ→ℤ) (x : ℤ) : Finset (PrimeCoordinates g) :=
  (Owners D tail x).image (fun S => Exponent g (step S))

def CollisionPoints (g : ℕ) (D : Finset (Finset ℤ)) (step : Finset ℤ→ℕ)
    (tail : Finset ℤ→ℤ) (u : ℤ) (L : ℕ) (x : ℤ) : Finset (PrimeCoordinates g) :=
  (CollisionClasses D (fun S => (step S:ℤ)) tail u (L:ℤ) x).image
    (fun d => Exponent g d.toNat)

theorem owner_points_card {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hdiv : ∀ S∈D, step S∈g.divisors)
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail) (x : ℤ) :
    (OwnerPoints g D step tail x).card=(Owners D tail x).card := by
  apply Finset.card_image_of_injOn
  intro S hS T hT he
  obtain ⟨hSD,hSX⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTD,hTX⟩ := Finset.mem_filter.mp hT
  have heq := exponent_injective g hg (hdiv S hSD) (hdiv T hTD) he
  exact same_class_equal_tail_eq hc hSD hTD (hSX.trans hTX.symm) (congrArg Int.ofNat heq)

theorem owner_points_antichain {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hdiv : ∀ S∈D, step S∈g.divisors)
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail) (x : ℤ) :
    IsAntichain (·≤·) (OwnerPoints g D step tail x : Set (PrimeCoordinates g)) := by
  intro a ha z hz hne hle
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hSD,hSX⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTD,hTX⟩ := Finset.mem_filter.mp hT
  have hdvd := (exponent_le_iff g (step S) (step T) hg (hdiv S hSD) (hdiv T hTD)).mp hle
  have hdvdZ : (step T:ℤ)∣(step S:ℤ) := by exact_mod_cast hdvd
  have hST := comparable_equal_tail_eq hc hSD hTD (hSX.trans hTX.symm) (Or.inr hdvdZ)
  exact hne (congrArg (fun S => Exponent g (step S)) hST)

theorem actual_owner_decomposition {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hdiv : ∀ S∈D, step S∈g.divisors)
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail) (x : ℤ) :
    ∃ E : Finset (PrimeCoordinates g × Finset (PrimeCoordinates g)),
      (∀ e∈E, 2≤e.2.card ∧ e.2⊆OwnerPoints g D step tail x ∧ MeetClique e.1 e.2) ∧
      CollisionTree35.UniqueLabels E ∧ CollisionTree35.Fee E=(Owners D tail x).card-1 := by
  obtain ⟨E,hE,hunique,hfee⟩ := CollisionTree35.antichain_collision_decomposition
    (owner_points_antichain hg hdiv hc x)
  exact ⟨E,hE,hunique,by simpa only [owner_points_card hg hdiv hc x] using hfee⟩

theorem owner_clique_actual_label {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (hpure : ∀ S∈D, PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    {x : ℤ} {b : PrimeCoordinates g} {V : Finset (PrimeCoordinates g)}
    (hV2 : 2≤V.card) (hVA : V⊆OwnerPoints g D step tail x) (hcl : MeetClique b V) :
    ∃ L∈g.divisors, Exponent g L=b ∧ V⊆CollisionPoints g D step tail u L x := by
  have hdiv : ∀ S∈D, step S∈g.divisors := by
    intro S hS
    exact Nat.mem_divisors.mpr ⟨by exact_mod_cast (hpure S hS).2.1,hg.ne'⟩
  obtain ⟨a,ha,z,hz,haz⟩ := Finset.one_lt_card.mp (by omega : 1<V.card)
  obtain ⟨S,hS,hSa⟩ := Finset.mem_image.mp (hVA ha)
  obtain ⟨T,hT,hTz⟩ := Finset.mem_image.mp (hVA hz)
  obtain ⟨hSD,hSX⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTD,hTX⟩ := Finset.mem_filter.mp hT
  let L := Nat.lcm (step S) (step T)
  have hLg : L∈g.divisors := Nat.mem_divisors.mpr
    ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors (hdiv S hSD))
      (Nat.dvd_of_mem_divisors (hdiv T hTD)),hg.ne'⟩
  have hLb : Exponent g L=b := by
    rw [exponent_lcm_inf g _ _ hg (hdiv S hSD) (hdiv T hTD),hSa,hTz]
    exact hcl.2 a ha z hz haz
  refine ⟨L,hLg,hLb,?_⟩
  intro a ha
  obtain ⟨z,hz,hza⟩ := Finset.exists_mem_ne (by omega : 1<V.card) a
  obtain ⟨S,hS,hSa⟩ := Finset.mem_image.mp (hVA ha)
  obtain ⟨T,hT,hTz⟩ := Finset.mem_image.mp (hVA hz)
  obtain ⟨hSD,hSX⟩ := Finset.mem_filter.mp hS
  obtain ⟨hTD,hTX⟩ := Finset.mem_filter.mp hT
  have hTS : T≠S := by
    intro he; subst T
    exact hza (hTz.symm.trans hSa)
  have hAP := (actual_pure_pair_label u v g (step S) (step T) hg hspan hvg
    S T (hpure S hSD) (hpure T hTD) (hpair S hSD T hTD hTS.symm)).1
  have hL'g : Nat.lcm (step S) (step T)∈g.divisors := Nat.mem_divisors.mpr
    ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors (hdiv S hSD))
      (Nat.dvd_of_mem_divisors (hdiv T hTD)),hg.ne'⟩
  have hLL : Nat.lcm (step S) (step T)=L := by
    apply exponent_injective g hg hL'g hLg
    rw [exponent_lcm_inf g _ _ hg (hdiv S hSD) (hdiv T hTD),hSa,hTz,hLb]
    exact hcl.2 a ha z hz hza.symm
  rw [hLL] at hAP
  apply Finset.mem_image.mpr
  refine ⟨(step S:ℤ),?_,?_⟩
  · exact Finset.mem_image.mpr ⟨S,Finset.mem_filter.mpr
      ⟨hSD,hSX,T,hTD,hTS,hTX,hAP⟩,rfl⟩
  · simpa only [Int.toNat_natCast] using hSa

theorem collision_points_disjoint {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g L : ℕ} {x y : ℤ}
    (hg : 0<g) (hdiv : ∀ S∈D, step S∈g.divisors)
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail)
    (hu : ∀ S∈D, u∈S) (hne : x≠y)
    (hside : (x<u ∧ y<u) ∨ (u<x ∧ u<y)) :
    Disjoint (CollisionPoints g D step tail u L x) (CollisionPoints g D step tail u L y) := by
  have hh := same_side_collision_classes_disjoint hc hu hne hside (L:=(L:ℤ))
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨d,hd,hda⟩ := Finset.mem_image.mp ha
  obtain ⟨e,he,hea⟩ := Finset.mem_image.mp hb
  obtain ⟨S,hS,hSd⟩ := Finset.mem_image.mp hd
  obtain ⟨T,hT,hTe⟩ := Finset.mem_image.mp he
  have hSD := (Finset.mem_filter.mp hS).1
  have hTD := (Finset.mem_filter.mp hT).1
  have hst : step S=step T := by
    apply exponent_injective g hg (hdiv S hSD) (hdiv T hTD)
    simpa only [←hSd,←hTe,Int.toNat_natCast] using hda.trans hea.symm
  have hde : d=e := hSd.symm.trans ((congrArg Int.ofNat hst).trans hTe)
  exact Finset.disjoint_left.mp hh hd (hde.symm ▸ he)

theorem same_side_owner_cliques_disjoint {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (hpure : ∀ S∈D, PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail)
    {x y : ℤ} (hne : x≠y) (hside : (x<u ∧ y<u) ∨ (u<x ∧ u<y))
    {b : PrimeCoordinates g} {V W : Finset (PrimeCoordinates g)}
    (hV2 : 2≤V.card) (hVA : V⊆OwnerPoints g D step tail x) (hV : MeetClique b V)
    (hW2 : 2≤W.card) (hWA : W⊆OwnerPoints g D step tail y) (hW : MeetClique b W) :
    Disjoint V W := by
  obtain ⟨L,hL,hLb,hVP⟩ := owner_clique_actual_label hg hspan hvg hpure hpair hV2 hVA hV
  obtain ⟨K,hK,hKb,hWP⟩ := owner_clique_actual_label hg hspan hvg hpure hpair hW2 hWA hW
  have hKL : K=L := exponent_injective g hg hK hL (hKb.trans hLb.symm)
  subst K
  have hdiv : ∀ S∈D, step S∈g.divisors := by
    intro S hS
    exact Nat.mem_divisors.mpr ⟨by exact_mod_cast (hpure S hS).2.1,hg.ne'⟩
  have hu : ∀ S∈D, u∈S := by
    intro S hS
    exact (pure_trace_points (by exact_mod_cast hg) hspan hvg (hpure S hS)).1
  exact Finset.disjoint_of_subset_left hVP
    (Finset.disjoint_of_subset_right hWP (collision_points_disjoint hg hdiv hc hu hne hside))

theorem actual_side_net_cost_bound {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (hpure : ∀ S∈D, PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail)
    (pivot : ↥g.primeFactors) (Q : Finset (PrimeCoordinates g))
    (hQ : ∀ S∈D, Exponent g (step S)∈Q)
    (X : Finset ℤ) (hside : (∀ x∈X, x<u) ∨ (∀ x∈X, u<x)) :
    (∑ x∈X, ((Owners D tail x).card-1))≤PotentialScore pivot Q := by
  have hdiv : ∀ S∈D, step S∈g.divisors := by
    intro S hS
    exact Nat.mem_divisors.mpr ⟨by exact_mod_cast (hpure S hS).2.1,hg.ne'⟩
  have hh := CollisionTree35.antichain_family_net_cost_bound pivot X
    (OwnerPoints g D step tail) Q (owner_points_antichain hg hdiv hc)
    (by
      intro x _ a ha
      obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp ha
      exact hQ S (Finset.mem_filter.mp hS).1)
    (by
      intro x hx y hy hxy b V W hV2 hVA hV hW2 hWA hW
      have hs : (x<u ∧ y<u) ∨ (u<x ∧ u<y) := by
        rcases hside with hs | hs
        · exact Or.inl ⟨hs x hx,hs y hy⟩
        · exact Or.inr ⟨hs x hx,hs y hy⟩
      exact same_side_owner_cliques_disjoint hg hspan hvg hpure hpair hc hxy hs
        hV2 hVA hV hW2 hWA hW)
  simpa only [owner_points_card hg hdiv hc] using hh

theorem owners_net_fee (D : Finset (Finset ℤ)) (tail : Finset ℤ→ℤ) :
    (∑ x∈D.image tail, ((Owners D tail x).card-1))=D.card-(D.image tail).card := by
  have hsum : (∑ x∈D.image tail, ((Owners D tail x).card-1))+(D.image tail).card=D.card := by
    calc
      (∑ x∈D.image tail, ((Owners D tail x).card-1))+(D.image tail).card=
          ∑ x∈D.image tail, (((Owners D tail x).card-1)+1) := by
        rw [Finset.sum_add_distrib]
        simp
      _=∑ x∈D.image tail, (Owners D tail x).card := by
        apply Finset.sum_congr rfl
        intro x hx
        obtain ⟨S,hS,hSX⟩ := Finset.mem_image.mp hx
        have hh : (Owners D tail x).Nonempty := ⟨S,Finset.mem_filter.mpr ⟨hS,hSX⟩⟩
        have hp := hh.card_pos
        omega
      _=D.card := (Finset.card_eq_sum_card_image tail D).symm
  omega

theorem actual_two_sided_net_cost_bound {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {g : ℕ}
    (hg : 0<g) (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (hpure : ∀ S∈D, PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail)
    (pivot : ↥g.primeFactors) (Q : Finset (PrimeCoordinates g))
    (hQ : ∀ S∈D, Exponent g (step S)∈Q) :
    D.card-(D.image tail).card≤2*PotentialScore pivot Q := by
  let X := D.image tail
  let L := X.filter (fun x => x<u)
  let R := X.filter (fun x => u<x)
  have hnot : ∀ x∈X, x≠u := by
    intro x hx he
    obtain ⟨S,hS,hSx⟩ := Finset.mem_image.mp hx
    have hxI : tail S∈Finset.Icc u v := by
      rw [hSx,he]
      have hgZ : (0:ℤ)<g := by exact_mod_cast hg
      exact Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩
    exact (hc S hS).2.1 hxI
  have hcover : X=L∪R := by
    ext x
    simp only [L,R,Finset.mem_union,Finset.mem_filter]
    constructor
    · intro hx
      rcases lt_or_gt_of_ne (hnot x hx) with hxlt | hxgt
      · exact Or.inl ⟨hx,hxlt⟩
      · exact Or.inr ⟨hx,hxgt⟩
    · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
  have hdis : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hl := (Finset.mem_filter.mp hx).2
    have hr := (Finset.mem_filter.mp hy).2
    omega
  have hleft := actual_side_net_cost_bound hg hspan hvg hpure hpair hc pivot Q hQ L
    (Or.inl (fun x hx => (Finset.mem_filter.mp hx).2))
  have hright := actual_side_net_cost_bound hg hspan hvg hpure hpair hc pivot Q hQ R
    (Or.inr (fun x hx => (Finset.mem_filter.mp hx).2))
  have heq := owners_net_fee D tail
  change (∑ x∈X, ((Owners D tail x).card-1))=D.card-(D.image tail).card at heq
  rw [hcover,Finset.sum_union hdis] at heq
  omega

theorem actual_pure_net_collision_bound (D : Finset (Finset ℤ)) (step : Finset ℤ→ℕ)
    (u v : ℤ) (g : ℕ) (hg : 0<g) (hspan : u+(g:ℤ)≤v) (hvg : (g:ℤ)∣v-u)
    (hpure : ∀ S∈D, PureTrace u v (g:ℤ) (step S:ℤ) S)
    (hbad : ∀ S∈D, ¬IsAP S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T))
    (pivot : ↥g.primeFactors) (Q : Finset (PrimeCoordinates g))
    (hQ : ∀ S∈D, Exponent g (step S)∈Q) :
    ∃ tail : Finset ℤ→ℤ, TailChoice D (fun S => (step S:ℤ)) u v tail ∧
      D.card-(D.image tail).card≤2*PotentialScore pivot Q := by
  obtain ⟨tail,hc⟩ := actual_pure_tail_choice D (fun S => (step S:ℤ)) u v (g:ℤ)
    (by exact_mod_cast hg) hspan hvg hpure hbad hpair
  exact ⟨tail,hc,actual_two_sided_net_cost_bound hg hspan hvg hpure hpair hc pivot Q hQ⟩

theorem tail_injective_single_class {D : Finset (Finset ℤ)} {step : Finset ℤ→ℕ}
    {tail : Finset ℤ→ℤ} {u v : ℤ} {d : ℕ}
    (hc : TailChoice D (fun S => (step S:ℤ)) u v tail)
    (hstep : ∀ S∈D, step S=d) : Set.InjOn tail D := by
  intro S hS T hT he
  exact same_class_equal_tail_eq hc hS hT he
    (congrArg Int.ofNat ((hstep S hS).trans (hstep T hT).symm))

theorem actual_pure_unit_anchor_no_collision (D : Finset (Finset ℤ)) (step : Finset ℤ→ℕ)
    (u v : ℤ) (hspan : u+1≤v)
    (hpure : ∀ S∈D, PureTrace u v 1 (step S:ℤ) S)
    (hbad : ∀ S∈D, ¬IsAP S)
    (hpair : ∀ S∈D, ∀ T∈D, S≠T → IsAP (S∩T)) :
    ∃ tail : Finset ℤ→ℤ, TailChoice D (fun S => (step S:ℤ)) u v tail ∧
      (D.image tail).card=D.card := by
  obtain ⟨tail,hc⟩ := actual_pure_tail_choice D (fun S => (step S:ℤ)) u v 1
    (by omega) hspan (one_dvd _) hpure hbad hpair
  refine ⟨tail,hc,Finset.card_image_of_injOn (tail_injective_single_class (d:=1) hc ?_)⟩
  intro S hS
  have hh : step S∣1 := by exact_mod_cast (hpure S hS).2.1
  exact Nat.dvd_one.mp hh

#print axioms owner_points_card
#print axioms owner_points_antichain
#print axioms actual_owner_decomposition
#print axioms owner_clique_actual_label
#print axioms collision_points_disjoint
#print axioms same_side_owner_cliques_disjoint
#print axioms actual_side_net_cost_bound
#print axioms owners_net_fee
#print axioms actual_two_sided_net_cost_bound
#print axioms actual_pure_net_collision_bound
#print axioms tail_injective_single_class
#print axioms actual_pure_unit_anchor_no_collision
end
end JSP233.PureTailCollision35
