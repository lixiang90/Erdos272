module

public import Erdos272.Geometry.AnchorPrimitive136
public import Erdos272.Geometry.AnchorPacking136

@[expose] public section
namespace JSP233.AnchorHalf136
open StarCompletion APGeometry FarSlot112 FarCapacity112 LongTerminal35
open AnchorPrimitive136 AnchorPacking136
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Bad (S P:Finset ℤ) (d x:ℤ) : Finset ℤ :=
  (CoreEdges P d).filter (Coverable S d x)
def IntrinsicEdges (S P:Finset ℤ) (d x:ℤ) : Finset ℤ :=
  (CoreEdges P d).filter (fun a=>IntrinsicPair a S {a+d,x})

theorem edge_residue {P:Finset ℤ} {d p a:ℤ} (hAt:APAt d p P)
    (ha:a∈CoreEdges P d) : d∣a-p := by
  obtain ⟨_,_,_,hrep⟩:=hAt
  exact ((hrep a).mp (Finset.mem_filter.mp ha).1).2.2

theorem intrinsic_iff_not_coverable {S P:Finset ℤ} {d x a:ℤ}
    (hd:0<d) (hP:P⊆S) (ha:a∈CoreEdges P d) (hx:x∈S\P) :
    IntrinsicPair a S {a+d,x} ↔ ¬Coverable S d x a := by
  obtain ⟨haP,hbP⟩:=Finset.mem_filter.mp ha
  obtain ⟨hxS,hxP⟩:=Finset.mem_sdiff.mp hx
  have hbx:a+d≠x:=fun he=>hxP (he ▸ hbP)
  have hax:a≠x:=fun he=>hxP (he ▸ haP)
  refine ⟨fun h=>h.2.2.2,fun hn=>⟨Finset.card_pair hbx,?_,?_,hn⟩⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  · intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl
    · exact hP hbP
    · exact hxS

theorem offgrid_twice_gcd {d p x:ℤ} (hd:0<d) (hoff:¬d∣x-p) :
    0<(Int.gcd d (x-p):ℤ) ∧ 2*(Int.gcd d (x-p):ℤ)≤d := by
  let g:ℤ:=Int.gcd d (x-p)
  have hg:0<g:=by
    dsimp only [g]
    exact_mod_cast Int.gcd_pos_of_ne_zero_left (x-p) hd.ne'
  have hgd:g∣d:=Int.gcd_dvd_left d (x-p)
  have hgle:g≤d:=Int.gcd_le_left (x-p) hd
  have hneq:g≠d:=by
    intro he
    have hh:=Int.gcd_dvd_right d (x-p)
    change g∣x-p at hh
    rw [he] at hh
    exact hoff hh
  have hlt:g<d:=lt_of_le_of_ne hgle hneq
  obtain ⟨k,hk⟩:=hgd
  have hk2:2≤k:=by
    by_contra hn
    have hk1:k≤1:=by omega
    have hm:=mul_le_mul_of_nonneg_left hk1 hg.le
    rw [←hk,mul_one] at hm
    omega
  have hm:=mul_le_mul_of_nonneg_left hk2 hg.le
  refine ⟨hg,?_⟩
  change 2*g≤d
  nlinarith only [hm,hk]

theorem coverable_on_grid_false {S P:Finset ℤ} {d p x a:ℤ}
    (hmax:MaximumAPCore S P) (hAt:APAt d p P) (hx:x∈S\P)
    (ha:a∈CoreEdges P d) (hgrid:d∣x-p) : ¬Coverable S d x a := by
  intro hc
  have hda:=edge_residue hAt ha
  have hg:(Int.gcd d (x-p):ℤ)=d:=(Int.gcd_eq_left_iff_dvd hAt.1.le).mpr hgrid
  have hpiece:Piece d d x a⊆S:=by simpa only [hg] using piece_subset_of_coverable hda hc
  have hga:d∣a-x:=by
    rw [show a-x=(a-p)-(x-p) by ring]
    exact dvd_sub hda hgrid
  have hmem:=piece_contains_edge hAt.1 hga (dvd_refl d)
  have haP:a∈P:=(Finset.mem_filter.mp ha).1
  have hUAt:APAt d a (P∪Piece d d x a):=by
    simpa only [APAt,Finset.mem_union] using
      PrivateUnion.union_APAt d a (fun y=>y∈P) (fun y=>y∈Piece d d x a)
        (apAt_rebase hAt haP) (apAt_rebase (piece_APAt hAt.1) hmem.1) haP hmem.1
  have hUAP:IsAP (P∪Piece d d x a):=(isAP_iff_exists_APAt _).mpr
    ⟨d,a,hUAt,Finset.mem_union_left _ haP⟩
  have he: P∪Piece d d x a=P := (maximum_core_is_maximal hmax).2.2 _
    Finset.subset_union_left (Finset.union_subset hmax.1 hpiece) hUAP
  have hxU:x∈P∪Piece d d x a:=Finset.mem_union_right _ (piece_contains_shell d d x a)
  exact (Finset.mem_sdiff.mp hx).2 (he ▸ hxU)

theorem bad_anchor_card_le_half {S P:Finset ℤ} {d p x:ℤ}
    (hmax:MaximumAPCore S P) (hAt:APAt d p P) (hx:x∈S\P) :
    2*(Bad S P d x).card≤(CoreEdges P d).card := by
  let A:=Bad S P d x
  by_cases hA:A.Nonempty
  · have hmem:∀a∈A,a∈CoreEdges P d ∧ Coverable S d x a:=fun a ha=>Finset.mem_filter.mp ha
    by_cases hgrid:d∣x-p
    · obtain ⟨a,ha⟩:=hA
      exact False.elim (coverable_on_grid_false hmax hAt hx (hmem a ha).1 hgrid (hmem a ha).2)
    · let g:ℤ:=Int.gcd d (x-p)
      obtain ⟨hg,hdg⟩:=offgrid_twice_gcd hAt.1 hgrid
      have hgd:g∣d:=Int.gcd_dvd_left d (x-p)
      let a:=A.min' hA
      let b:=A.max' hA
      have ha:a∈A:=Finset.min'_mem A hA
      have hb:b∈A:=Finset.max'_mem A hA
      have hda:=edge_residue hAt (hmem a ha).1
      have hdb:=edge_residue hAt (hmem b hb).1
      let U:=Piece g d x a∪Piece g d x b
      have hU:=two_coverable_pieces hAt.1 hda hdb (hmem a ha).2 (hmem b hb).2
      have hUsub:U⊆S:=hU.1
      have hUAP:IsAP U:=hU.2
      have hga:g∣a-x:=by
        rw [show a-x=(a-p)-(x-p) by ring]
        exact dvd_sub (dvd_trans hgd hda) (Int.gcd_dvd_right d (x-p))
      have hgb:g∣b-x:=by
        rw [show b-x=(b-p)-(x-p) by ring]
        exact dvd_sub (dvd_trans hgd hdb) (Int.gcd_dvd_right d (x-p))
      have hl:a∈U:=Finset.mem_union_left _ (piece_contains_edge hAt.1 hga hgd).1
      have hr:b+d∈U:=Finset.mem_union_right _ (piece_contains_edge hAt.1 hgb hgd).2
      have hgr:∀u∈A,∀v∈A,d∣u-v:=by
        intro u hu v hv
        exact apAt_dvd_sub hAt (Finset.mem_filter.mp (hmem v hv).1).1 (Finset.mem_filter.mp (hmem u hu).1).1
      have hpack:2*A.card+1≤U.card:=pack_into_AP hA hg hdg hgd hgr (two_pieces_APAt hg) hl hr
      have hbound:=hmax.2.2 U hUsub hUAP
      have he: (CoreEdges P d).card=P.card-1:=coreEdges_card hAt (isAP_nonempty hmax.2.1)
      change 2*A.card≤(CoreEdges P d).card
      rw [he]
      omega
  · have he:A=∅:=Finset.not_nonempty_iff_eq_empty.mp hA
    change 2*A.card≤(CoreEdges P d).card
    rw [he]
    simp

theorem at_least_half_intrinsic_core_edges {S P:Finset ℤ} {d p x:ℤ}
    (hmax:MaximumAPCore S P) (hAt:APAt d p P) (hx:x∈S\P) :
    (CoreEdges P d).card≤2*(IntrinsicEdges S P d x).card := by
  have hpart:=Finset.card_filter_add_card_filter_not (s:=CoreEdges P d) (Coverable S d x)
  have he:IntrinsicEdges S P d x=(CoreEdges P d).filter (fun a=>¬Coverable S d x a):=by
    ext a
    simp only [IntrinsicEdges,Finset.mem_filter]
    constructor
    · rintro ⟨ha,hI⟩
      exact ⟨ha,(intrinsic_iff_not_coverable hAt.1 hmax.1 ha hx).mp hI⟩
    · rintro ⟨ha,hn⟩
      exact ⟨ha,(intrinsic_iff_not_coverable hAt.1 hmax.1 ha hx).mpr hn⟩
  have hb:=bad_anchor_card_le_half hmax hAt hx
  change 2*((CoreEdges P d).filter (Coverable S d x)).card≤(CoreEdges P d).card at hb
  rw [he]
  omega

#print axioms edge_residue
#print axioms intrinsic_iff_not_coverable
#print axioms offgrid_twice_gcd
#print axioms coverable_on_grid_false
#print axioms bad_anchor_card_le_half
#print axioms at_least_half_intrinsic_core_edges
end
end JSP233.AnchorHalf136
