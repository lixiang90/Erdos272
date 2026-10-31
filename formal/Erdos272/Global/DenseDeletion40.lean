import Erdos272.Core.AnchorCompletion38
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-! Actual short consecutive pairs and native deletion of dense crooked members. -/
namespace JSP233.DenseDeletion40
open StarCompletion AnchorCompletion38
open scoped Classical BigOperators
noncomputable section

def Block (r : ℕ) (x : ℤ) : ℕ := (x-1).toNat/(2*r)

def Nonminimal (S : Finset ℤ) (r : ℕ) : Finset ℤ :=
  S.filter (fun x => ∃ y∈S,Block r y=Block r x ∧ y<x)

def Minimal (S : Finset ℤ) (r : ℕ) : Finset ℤ :=
  S.filter (fun x => ¬∃ y∈S,Block r y=Block r x ∧ y<x)

theorem nonminimal_minimal_partition (S : Finset ℤ) (r : ℕ) :
    (Nonminimal S r).card+(Minimal S r).card=S.card := by
  exact Finset.card_filter_add_card_filter_not (s:=S) _

theorem actual_minimal_count {N r : ℕ} {S : Finset ℤ} (hS : S⊆Ground N) :
    (Minimal S r).card≤N/(2*r)+1 := by
  apply (Finset.card_le_card_of_injOn (Block r) (t:=Finset.range (N/(2*r)+1)) ?_ ?_).trans_eq
    (Finset.card_range _)
  · intro x hx
    have hxS := (Finset.mem_filter.mp hx).1
    have hxN := (mem_ground N x).mp (hS hxS)
    have hn : (x-1).toNat≤N := by omega
    have hh : (x-1).toNat/(2*r)≤N/(2*r) := Nat.div_le_div_right hn
    exact Finset.mem_range.mpr (by dsimp [Block]; omega)
  · intro x hx y hy he
    obtain ⟨hxS,hxmin⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyS,hymin⟩ := Finset.mem_filter.mp hy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact hymin ⟨x,hxS,he,hxy⟩
    · exact hxmin ⟨y,hyS,he.symm,hyx⟩

theorem actual_nonminimal_supply {N r : ℕ} {S : Finset ℤ}
    (hS : S⊆Ground N) (hdense : N<r*S.card) :
    N/(2*r)≤(Nonminimal S r).card := by
  have hq := Nat.div_mul_le_self N (2*r)
  have hlarge : 2*(N/(2*r))<S.card := by nlinarith only [hq,hdense]
  have hm := actual_minimal_count (r:=r) hS
  have hp := nonminimal_minimal_partition S r
  omega

theorem same_block_span {r : ℕ} {x y : ℤ} (hr : 0<r)
    (hx : 1≤x) (hy : 1≤y) (he : Block r y=Block r x) : x-y<(2*r:ℕ) := by
  have hp : 0<2*r := by omega
  have hxm := Nat.mod_lt (x-1).toNat hp
  have hym := Nat.mod_lt (y-1).toNat hp
  have hxe := Nat.mod_add_div (x-1).toNat (2*r)
  have hye := Nat.mod_add_div (y-1).toNat (2*r)
  dsimp [Block] at he
  rw [he] at hye
  omega

def Before (S : Finset ℤ) (x : ℤ) : Finset ℤ := S.filter (fun y => y<x)

def Previous (S : Finset ℤ) (x : ℤ) : ℤ :=
  if h : (Before S x).Nonempty then (Before S x).max' h else 0

theorem previous_spec {S : Finset ℤ} {x : ℤ} (hne : (Before S x).Nonempty) :
    Previous S x∈S ∧ Previous S x<x ∧ ∀ y∈S,y<x → y≤Previous S x := by
  have hm := Finset.max'_mem (Before S x) hne
  simp only [Previous,dif_pos hne]
  exact ⟨(Finset.mem_filter.mp hm).1,(Finset.mem_filter.mp hm).2,
    fun y hy hyx => Finset.le_max' _ y (Finset.mem_filter.mpr ⟨hy,hyx⟩)⟩

def ShortKeys (N r : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range N).product (Finset.Icc 1 (2*r))

def Left (k : ℕ×ℕ) : ℤ := (k.1:ℤ)+1
def Right (k : ℕ×ℕ) : ℤ := Left k+(k.2:ℤ)
def PairIn (S : Finset ℤ) (k : ℕ×ℕ) : Prop := Left k∈S ∧ Right k∈S

def Witness (S : Finset ℤ) (x : ℤ) : ℕ×ℕ :=
  ((Previous S x-1).toNat,(x-Previous S x).toNat)

theorem actual_witness_spec {N r : ℕ} {S : Finset ℤ} {x : ℤ}
    (hr : 0<r) (hS : S⊆Ground N) (hx : x∈Nonminimal S r) :
    Witness S x∈ShortKeys N r ∧ PairIn S (Witness S x) ∧ Right (Witness S x)=x := by
  obtain ⟨hxS,y,hyS,he,hyx⟩ := Finset.mem_filter.mp hx
  have hb : (Before S x).Nonempty := ⟨y,Finset.mem_filter.mpr ⟨hyS,hyx⟩⟩
  obtain ⟨haS,hax,hmax⟩ := previous_spec hb
  have haN := (mem_ground N (Previous S x)).mp (hS haS)
  have hxN := (mem_ground N x).mp (hS hxS)
  have hyN := (mem_ground N y).mp (hS hyS)
  have hspan := same_block_span hr hxN.1 hyN.1 he
  have hya := hmax y hyS hyx
  have hleft : Left (Witness S x)=Previous S x := by dsimp [Left,Witness]; omega
  have hright : Right (Witness S x)=x := by dsimp [Right,Left,Witness]; omega
  refine ⟨?_,?_,hright⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      dsimp [Witness]
      omega
    · apply Finset.mem_Icc.mpr
      dsimp [Witness]
      constructor <;> omega
  · exact ⟨hleft.symm ▸ haS,hright.symm ▸ hxS⟩

theorem actual_short_pair_supply {N r : ℕ} {S : Finset ℤ}
    (hr : 0<r) (hS : S⊆Ground N) (hdense : N<r*S.card) :
    N/(2*r)≤((ShortKeys N r).filter (PairIn S)).card := by
  apply (actual_nonminimal_supply hS hdense).trans
  apply Finset.card_le_card_of_injOn (Witness S)
  · intro x hx
    have hh := actual_witness_spec hr hS hx
    exact Finset.mem_filter.mpr ⟨hh.1,hh.2.1⟩
  · intro x hx y hy he
    have hxx := (actual_witness_spec hr hS hx).2.2
    have hyy := (actual_witness_spec hr hS hy).2.2
    rw [he] at hxx
    exact hxx.symm.trans hyy

theorem actual_witness_consecutive {N r : ℕ} {S : Finset ℤ} {x : ℤ}
    (hr : 0<r) (hS : S⊆Ground N) (hx : x∈Nonminimal S r) :
    ∀ z∈S,¬(Left (Witness S x)<z ∧ z<Right (Witness S x)) := by
  have hright := (actual_witness_spec hr hS hx).2.2
  obtain ⟨_,y,hyS,_,hyx⟩ := Finset.mem_filter.mp hx
  have hb : (Before S x).Nonempty := ⟨y,Finset.mem_filter.mpr ⟨hyS,hyx⟩⟩
  obtain ⟨haS,_,hmax⟩ := previous_spec hb
  have haN := (mem_ground N (Previous S x)).mp (hS haS)
  have hleft : Left (Witness S x)=Previous S x := by dsimp [Left,Witness]; omega
  intro z hz hbetween
  rw [hright,hleft] at hbetween
  have hh := hmax z hz hbetween.2
  omega

theorem floor_half_payment {N r : ℕ} (hr : 0<r) (hN : 4*r≤N) :
    N≤4*r*(N/(2*r)) := by
  have hp : 0<2*r := by omega
  have hm : 1≤N/(2*r) := (Nat.le_div_iff_mul_le hp).mpr (by nlinarith only [hN])
  have he := Nat.mod_add_div N (2*r)
  have ht := Nat.mod_lt N hp
  nlinarith only [he,ht,hm]

theorem actual_short_pair_supply_real {N r : ℕ} {S : Finset ℤ}
    (hr : 0<r) (hN : 4*r≤N) (hS : S⊆Ground N) (hdense : N<r*S.card) :
    (N:ℝ)/(4*(r:ℝ))≤(((ShortKeys N r).filter (PairIn S)).card:ℝ) := by
  have hh := Nat.mul_le_mul_left (4*r) (actual_short_pair_supply hr hS hdense)
  have hn := (floor_half_payment hr hN).trans hh
  have hnR : (N:ℝ)≤4*(r:ℝ)*(((ShortKeys N r).filter (PairIn S)).card:ℝ) := by
    exact_mod_cast hn
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(r:ℝ))).mpr
  nlinarith only [hnR]

theorem short_keys_card (N r : ℕ) : (ShortKeys N r).card=N*(2*r) := by
  simp [ShortKeys,Finset.card_product,Nat.card_Icc]

theorem actual_short_pair_class_capacity {N r : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    {k : ℕ×ℕ} (hk : k∈ShortKeys N r) : (F.filter (fun S => PairIn S k)).card≤N := by
  let C := F.filter (fun S => PairIn S k)
  by_cases hC : C.Nonempty
  · have hCF : C⊆F := Finset.filter_subset _ _
    have hLC : Legal (Ground N) C := ⟨fun S hS => hlegal.1 S (hCF hS),
      fun S hS T hT hne => hlegal.2 S (hCF hS) T (hCF hT) hne⟩
    have hd := (Finset.mem_Icc.mp (Finset.mem_product.mp hk).2).1
    have hne : Left k≠Right k := by dsimp [Left,Right]; omega
    have hh := actual_two_point_crooked_ground_capacity (Ground N) C (Left k) (Right k)
      hne hC hLC (fun S hS => hbad S (hCF hS))
      (fun S hS => (Finset.mem_filter.mp hS).2.1)
      (fun S hS => (Finset.mem_filter.mp hS).2.2)
    rw [ground_card] at hh
    change C.card≤N
    omega
  · have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    change C.card≤N
    simp [he]

theorem actual_dense_pair_double_count {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hdense : ∀ S∈F,N<r*S.card) : F.card*(N/(2*r))≤2*r*N^2 := by
  have hh := Finset.card_nsmul_le_card_nsmul (r:=PairIn) (s:=F) (t:=ShortKeys N r)
    (m:=N/(2*r)) (n:=N)
    (fun S hS => actual_short_pair_supply hr (hlegal.1 S hS) (hdense S hS))
    (fun k hk => actual_short_pair_class_capacity hlegal hbad hk)
  rw [nsmul_eq_mul,nsmul_eq_mul,short_keys_card] at hh
  nlinarith only [hh]

theorem actual_dense_crooked_bound {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : 4*r≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hdense : ∀ S∈F,N<r*S.card) : F.card≤8*r^2*N := by
  have hc := actual_dense_pair_double_count hr hlegal hbad hdense
  have hfloor := floor_half_payment hr hN
  have hscale := Nat.mul_le_mul_left (4*r) hc
  have hpay := Nat.mul_le_mul_left F.card hfloor
  have htotal : F.card*N≤(8*r^2*N)*N := by nlinarith only [hscale,hpay]
  exact Nat.le_of_mul_le_mul_right htotal (by omega : 0<N)

def Deleted (N r : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.filter (fun S => ¬IsAP S ∧ N<r*S.card)

def Retained (N r : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F\Deleted N r F

theorem actual_deleted_subset (N r : ℕ) (F : Finset (Finset ℤ)) : Deleted N r F⊆F :=
  Finset.filter_subset _ _

theorem actual_deleted_legal {N r : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) : Legal (Ground N) (Deleted N r F) :=
  ⟨fun S hS => hlegal.1 S (actual_deleted_subset N r F hS),
    fun S hS T hT hne => hlegal.2 S (actual_deleted_subset N r F hS)
      T (actual_deleted_subset N r F hT) hne⟩

theorem actual_dense_deletion_bound {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : 4*r≤N) (hlegal : Legal (Ground N) F) :
    (Deleted N r F).card≤8*r^2*N := by
  exact actual_dense_crooked_bound hr hN (actual_deleted_legal hlegal)
    (fun S hS => (Finset.mem_filter.mp hS).2.1)
    (fun S hS => (Finset.mem_filter.mp hS).2.2)

theorem actual_ap_retained {N r : ℕ} {F : Finset (Finset ℤ)} {S : Finset ℤ}
    (hS : S∈F) (hAP : IsAP S) : S∈Retained N r F := by
  apply Finset.mem_sdiff.mpr
  refine ⟨hS,?_⟩
  intro hdel
  exact (Finset.mem_filter.mp hdel).2.1 hAP

theorem actual_retained_crooked_sparse {N r : ℕ} {F : Finset (Finset ℤ)} {S : Finset ℤ}
    (hS : S∈Retained N r F) (hbad : ¬IsAP S) : r*S.card≤N := by
  obtain ⟨hSF,hnot⟩ := Finset.mem_sdiff.mp hS
  by_contra hn
  exact hnot (Finset.mem_filter.mpr ⟨hSF,hbad,by omega⟩)

theorem actual_retained_legal {N r : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) : Legal (Ground N) (Retained N r F) :=
  ⟨fun S hS => hlegal.1 S (Finset.mem_sdiff.mp hS).1,
    fun S hS T hT hne => hlegal.2 S (Finset.mem_sdiff.mp hS).1
      T (Finset.mem_sdiff.mp hT).1 hne⟩

theorem actual_deletion_card_identity (N r : ℕ) (F : Finset (Finset ℤ)) :
    (Retained N r F).card+(Deleted N r F).card=F.card := by
  exact Finset.card_sdiff_add_card_eq_card (actual_deleted_subset N r F)

theorem actual_retained_card_lower {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : 4*r≤N) (hlegal : Legal (Ground N) F) :
    F.card≤(Retained N r F).card+8*r^2*N := by
  have hb := actual_dense_deletion_bound hr hN hlegal
  have he := actual_deletion_card_identity N r F
  omega

theorem actual_retained_density {N r : ℕ} {F : Finset (Finset ℤ)} {D : ℝ}
    (hr : 0<r) (hN : 4*r≤N) (hlegal : Legal (Ground N) F) (hdense : D≤F.card) :
    D-8*(r:ℝ)^2*(N:ℝ)≤(Retained N r F).card := by
  have hb := actual_retained_card_lower hr hN hlegal
  have hbR : (F.card:ℝ)≤((Retained N r F).card:ℝ)+8*(r:ℝ)^2*(N:ℝ) := by
    exact_mod_cast hb
  linarith

theorem actual_dense_deletion_package {N r : ℕ} {F : Finset (Finset ℤ)}
    (hr : 0<r) (hN : 4*r≤N) (hlegal : Legal (Ground N) F) :
    Deleted N r F⊆F ∧ Legal (Ground N) (Retained N r F) ∧
    (Deleted N r F).card≤8*r^2*N ∧
    (∀ S∈F,IsAP S → S∈Retained N r F) ∧
    (∀ S∈Retained N r F,¬IsAP S → r*S.card≤N) ∧
    (Retained N r F).card+(Deleted N r F).card=F.card := by
  exact ⟨actual_deleted_subset N r F,actual_retained_legal hlegal,
    actual_dense_deletion_bound hr hN hlegal,
    fun _ hS hAP => actual_ap_retained hS hAP,
    fun _ hS hbad => actual_retained_crooked_sparse hS hbad,
    actual_deletion_card_identity N r F⟩

#print axioms nonminimal_minimal_partition
#print axioms actual_minimal_count
#print axioms actual_nonminimal_supply
#print axioms same_block_span
#print axioms previous_spec
#print axioms actual_witness_spec
#print axioms actual_short_pair_supply
#print axioms actual_witness_consecutive
#print axioms floor_half_payment
#print axioms actual_short_pair_supply_real
#print axioms short_keys_card
#print axioms actual_short_pair_class_capacity
#print axioms actual_dense_pair_double_count
#print axioms actual_dense_crooked_bound
#print axioms actual_deleted_subset
#print axioms actual_deleted_legal
#print axioms actual_dense_deletion_bound
#print axioms actual_ap_retained
#print axioms actual_retained_crooked_sparse
#print axioms actual_retained_legal
#print axioms actual_deletion_card_identity
#print axioms actual_retained_card_lower
#print axioms actual_retained_density
#print axioms actual_dense_deletion_package

end
end JSP233.DenseDeletion40
