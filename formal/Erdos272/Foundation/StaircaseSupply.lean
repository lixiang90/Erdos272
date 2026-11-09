module

public import Erdos272.Foundation.StaircaseGeometry
public import Erdos272.Foundation.PrivatePairExistence

@[expose] public section

/-! Actual primitive bad-pair supply, classified by the signs of its endpoints.
No finite range bound or supply-count oracle is assumed. -/

namespace JSP233.StaircaseSupply

open StarCompletion StaircaseGeometry StaircaseCertificate
open scoped BigOperators

theorem unit_three_isAP (a : Int) : IsAP ({a,a+1,a+2} : Finset Int) := by
  refine ⟨1, a, by decide, a, a+2, ?_, by simp⟩
  intro x
  simp only [Finset.mem_insert, Finset.mem_singleton, Int.one_dvd, and_true]
  omega

theorem negative_unit_isAP : IsAP ({0,-2,-1} : Finset Int) := by
  convert window_isAP 2 0 using 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Window, Finset.mem_Icc]
  omega

theorem mixed_unit_isAP : IsAP ({0,-1,1} : Finset Int) := by
  convert window_isAP 1 1 using 1
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton, Window, Finset.mem_Icc]
  omega

theorem primitive_triple_isAP_iff (u v : Int) (huv : u < v)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hg : Int.gcd u v = 1) :
    IsAP ({0,u,v} : Finset Int) ↔
      (u = -2 ∧ v = -1) ∨ (u = 1 ∧ v = 2) ∨ (u = -1 ∧ v = 1) := by
  constructor
  · intro hap
    have hsub : Finset.Icc (min 0 u) (max 0 v) ⊆ ({0,u,v} : Finset Int) := by
      intro x hx
      have hx' := Finset.mem_Icc.mp hx
      apply PrivatePairExistence.completion_least (u := u) (v := v) (x := x)
        hap (by simp) (by simp) (by simp)
      refine ⟨?_, ?_, ?_⟩
      · have := hx'.1
        omega
      · have := hx'.2
        omega
      · simp [hg]
    have hcard := Finset.card_le_card hsub
    have hthree : ({0,u,v} : Finset Int).card = 3 := by
      simp [huv.ne, Ne.symm hu0, Ne.symm hv0]
    rw [hthree, Int.card_Icc] at hcard
    omega
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact negative_unit_isAP
    · simpa using unit_three_isAP 0
    · exact mixed_unit_isAP

theorem primitive_pair_iff (u v : Int) (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    IsPrimitiveBadPair ({u,v} : Finset Int) ↔
      ¬ IsAP ({0,u,v} : Finset Int) ∧ Int.gcd u v = 1 := by
  simp [IsPrimitiveBadPair, huv, Ne.symm hu0, Ne.symm hv0,
    Ne.symm huv, Int.gcd_comm]

theorem positive_pair_iff (a b : Nat) (hb : 0 < b) (hba : b < a) :
    IsPrimitiveBadPair ({(b : Int),(a : Int)} : Finset Int) ↔
      Nat.gcd b a = 1 ∧ 3 ≤ a := by
  rw [primitive_pair_iff _ _ (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨hbad, hg⟩
    refine ⟨by simpa using hg, ?_⟩
    by_contra hn
    have hb1 : b = 1 := by omega
    have ha2 : a = 2 := by omega
    subst b
    subst a
    exact hbad (unit_three_isAP 0)
  · rintro ⟨hg, ha⟩
    refine ⟨?_, by simpa using hg⟩
    intro hap
    have hclass := (primitive_triple_isAP_iff b a (by omega) (by omega)
      (by omega) (by simpa using hg)).mp hap
    omega

theorem negative_pair_iff (a b : Nat) (hb : 0 < b) (hba : b < a) :
    IsPrimitiveBadPair ({-(a : Int),-(b : Int)} : Finset Int) ↔
      Nat.gcd b a = 1 ∧ 3 ≤ a := by
  rw [primitive_pair_iff _ _ (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨hbad, hg⟩
    refine ⟨by simpa [Nat.gcd_comm] using hg, ?_⟩
    by_contra hn
    have hb1 : b = 1 := by omega
    have ha2 : a = 2 := by omega
    subst b
    subst a
    apply hbad
    exact negative_unit_isAP
  · rintro ⟨hg, ha⟩
    have hg' : Int.gcd (-(a : Int)) (-(b : Int)) = 1 := by
      simpa [Nat.gcd_comm] using hg
    refine ⟨?_, hg'⟩
    intro hap
    have hclass := (primitive_triple_isAP_iff (-(a : Int)) (-(b : Int))
      (by omega) (by omega) (by omega) hg').mp hap
    omega

theorem mixed_pair_iff (a r : Nat) (ha : 0 < a) (hr : 0 < r) :
    IsPrimitiveBadPair ({-(a : Int),(r : Int)} : Finset Int) ↔
      Nat.gcd a r = 1 ∧ a ≠ r := by
  rw [primitive_pair_iff _ _ (by omega) (by omega) (by omega)]
  constructor
  · rintro ⟨hbad, hg⟩
    refine ⟨by simpa using hg, ?_⟩
    intro heq
    subst r
    have ha1 : a = 1 := by simpa using hg
    subst a
    apply hbad
    exact mixed_unit_isAP
  · rintro ⟨hg, hne⟩
    have hg' : Int.gcd (-(a : Int)) (r : Int) = 1 := by simpa using hg
    refine ⟨?_, hg'⟩
    intro hap
    have hclass := (primitive_triple_isAP_iff (-(a : Int)) r
      (by omega) (by omega) (by omega) hg').mp hap
    omega

theorem ordered_pair_ext {u v x y : Int} (huv : u < v) (hxy : x < y)
    (heq : ({u,v} : Finset Int) = {x,y}) : u = x ∧ v = y := by
  have hu : u = x ∨ u = y := by
    have h : u ∈ ({x,y} : Finset Int) := heq ▸ (by simp)
    simpa using h
  have hv : v = x ∨ v = y := by
    have h : v ∈ ({x,y} : Finset Int) := heq ▸ (by simp)
    simpa using h
  omega

def SameSlice (a : Nat) : Finset (Nat × Nat) :=
  ((Finset.range a).filter (fun b => Nat.gcd b a = 1)).image (fun b => (a,b))

def SameCoords (H : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (H+1)).filter (fun a => 3 ≤ a)).biUnion SameSlice

theorem mem_sameCoords (H : Nat) (p : Nat × Nat) :
    p ∈ SameCoords H ↔ p.1 ≤ H ∧ 3 ≤ p.1 ∧ p.2 < p.1 ∧ Nat.gcd p.2 p.1 = 1 := by
  rcases p with ⟨a,b⟩
  simp [SameCoords, SameSlice, Nat.lt_succ_iff, and_assoc]

theorem sameCoords_second_pos {H : Nat} {p : Nat × Nat} (hp : p ∈ SameCoords H) :
    0 < p.2 := by
  have hp' := (mem_sameCoords H p).mp hp
  by_contra hn
  have hz : p.2 = 0 := by omega
  have hg := hp'.2.2.2
  simp [hz] at hg
  omega

theorem sameSlice_card (a : Nat) : (SameSlice a).card = PrimitivePhi a := by
  have hinj : Function.Injective (fun b : Nat => (a,b)) := by
    intro b c h
    exact congrArg Prod.snd h
  exact Finset.card_image_of_injective _ hinj

theorem sameCoords_card (H : Nat) : (SameCoords H).card = LeftSupply H := by
  have hd : (((Finset.range (H+1)).filter (fun a => 3 ≤ a) : Finset Nat) : Set Nat).PairwiseDisjoint
      SameSlice := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    obtain ⟨x, hx, hpx⟩ := Finset.mem_image.mp hpa
    obtain ⟨y, hy, hpy⟩ := Finset.mem_image.mp hpb
    have he := congrArg Prod.fst (hpx.trans hpy.symm)
    exact hab he
  rw [SameCoords, Finset.card_biUnion hd]
  simp only [sameSlice_card, Finset.sum_filter, LeftSupply]

def MixedSlice (p : Nat → Nat) (r : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (p r)).filter
    (fun a => 0 < a ∧ Nat.gcd a r = 1 ∧ a ≠ r)).image (fun a => (a,r))

def MixedCoords (p : Nat → Nat) (B : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (B+1)).filter (fun r => 0 < r)).biUnion (MixedSlice p)

theorem mem_mixedCoords (p : Nat → Nat) (B : Nat) (q : Nat × Nat) :
    q ∈ MixedCoords p B ↔ q.2 ≤ B ∧ 0 < q.2 ∧ q.1 < p q.2 ∧
      0 < q.1 ∧ Nat.gcd q.1 q.2 = 1 ∧ q.1 ≠ q.2 := by
  rcases q with ⟨a,r⟩
  simp [MixedCoords, MixedSlice, Nat.lt_succ_iff, and_assoc]

theorem mixedSupply_zero (r : Nat) : MixedSupply 0 r = 0 := by
  unfold MixedSupply
  have heq : (Finset.range 1).filter (fun a => 0 < a ∧ Nat.gcd a r = 1 ∧ a ≠ r) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have := Finset.mem_range.mp ha'.1
    omega
  exact congrArg Finset.card heq

theorem mixedSlice_card (p : Nat → Nat) (r : Nat) :
    (MixedSlice p r).card = MixedSupply (p r - 1) r := by
  have hinj : Function.Injective (fun a : Nat => (a,r)) := by
    intro a b h
    exact congrArg Prod.fst h
  rw [MixedSlice, Finset.card_image_of_injective _ hinj]
  cases hi : p r with
  | zero => simpa using (mixedSupply_zero r).symm
  | succ h => simp [MixedSupply]

theorem mixedCoords_card (p : Nat → Nat) (B : Nat) :
    (MixedCoords p B).card = ∑ r ∈ Finset.range (B+1),
      if 0 < r then MixedSupply (p r-1) r else 0 := by
  have hd : (((Finset.range (B+1)).filter (fun r => 0 < r) : Finset Nat) : Set Nat).PairwiseDisjoint
      (MixedSlice p) := by
    intro r hr s hs hrs
    apply Finset.disjoint_left.mpr
    intro q hqr hqs
    obtain ⟨a, ha, hqa⟩ := Finset.mem_image.mp hqr
    obtain ⟨b, hb, hqb⟩ := Finset.mem_image.mp hqs
    exact hrs (congrArg Prod.snd (hqa.trans hqb.symm))
  rw [MixedCoords, Finset.card_biUnion hd]
  simp only [mixedSlice_card, Finset.sum_filter]

def NegativePair (p : Nat × Nat) : Finset Int := {-(p.1 : Int),-(p.2 : Int)}
def PositivePair (p : Nat × Nat) : Finset Int := {(p.2 : Int),(p.1 : Int)}
def CrossPair (p : Nat × Nat) : Finset Int := {-(p.1 : Int),(p.2 : Int)}

def LeftPool (H : Nat) : Finset (Finset Int) := (SameCoords H).image NegativePair
def RightPool (R : Nat) : Finset (Finset Int) := (SameCoords R).image PositivePair
def CrossPool (p : Nat → Nat) (B : Nat) : Finset (Finset Int) :=
  (MixedCoords p B).image CrossPair

theorem leftPool_card (H : Nat) : (LeftPool H).card = LeftSupply H := by
  rw [LeftPool, Finset.card_image_of_injOn]
  · exact sameCoords_card H
  · intro p hp q hq heq
    have hp' := (mem_sameCoords H p).mp hp
    have hq' := (mem_sameCoords H q).mp hq
    have he := ordered_pair_ext (by omega : -(p.1 : Int) < -(p.2 : Int))
      (by omega : -(q.1 : Int) < -(q.2 : Int)) heq
    apply Prod.ext <;> omega

theorem rightPool_card (R : Nat) : (RightPool R).card = LeftSupply R := by
  rw [RightPool, Finset.card_image_of_injOn]
  · exact sameCoords_card R
  · intro p hp q hq heq
    have hp' := (mem_sameCoords R p).mp hp
    have hq' := (mem_sameCoords R q).mp hq
    have he := ordered_pair_ext (by omega : (p.2 : Int) < (p.1 : Int))
      (by omega : (q.2 : Int) < (q.1 : Int)) heq
    apply Prod.ext <;> omega

theorem crossPool_card (p : Nat → Nat) (B : Nat) :
    (CrossPool p B).card = ∑ r ∈ Finset.range (B+1),
      if 0 < r then MixedSupply (p r-1) r else 0 := by
  rw [CrossPool, Finset.card_image_of_injOn]
  · exact mixedCoords_card p B
  · intro q hq t ht heq
    have hq' := (mem_mixedCoords p B q).mp hq
    have ht' := (mem_mixedCoords p B t).mp ht
    have he := ordered_pair_ext (by omega : -(q.1 : Int) < (q.2 : Int))
      (by omega : -(t.1 : Int) < (t.2 : Int)) heq
    apply Prod.ext <;> omega

theorem sorted_pair_representation (Q : Finset Int) (hQ : Q.card = 2) :
    ∃ u v : Int, u < v ∧ Q = {u,v} := by
  obtain ⟨u,v,hne,heq⟩ := Finset.card_eq_two.mp hQ
  rcases lt_or_gt_of_ne hne with huv | hvu
  · exact ⟨u,v,huv,heq⟩
  · exact ⟨v,u,hvu,heq.trans (Finset.pair_comm u v)⟩

theorem primitive_three_types (Q : Finset Int) (hQ : IsPrimitiveBadPair Q) :
    (∃ a b : Nat, Q = NegativePair (a,b) ∧ 0 < b ∧ b < a ∧ Nat.gcd b a = 1 ∧ 3 ≤ a) ∨
    (∃ a b : Nat, Q = PositivePair (a,b) ∧ 0 < b ∧ b < a ∧ Nat.gcd b a = 1 ∧ 3 ≤ a) ∨
    (∃ a r : Nat, Q = CrossPair (a,r) ∧ 0 < a ∧ 0 < r ∧ Nat.gcd a r = 1 ∧ a ≠ r) := by
  obtain ⟨u,v,huv,hrep⟩ := sorted_pair_representation Q hQ.1
  have hu0 : u ≠ 0 := by
    intro hz
    apply hQ.2.1
    rw [hrep]
    simp [hz]
  have hv0 : v ≠ 0 := by
    intro hz
    apply hQ.2.1
    rw [hrep]
    simp [hz]
  by_cases hv : v < 0
  · let a := (-u).toNat
    let b := (-v).toNat
    have ha : (a : Int) = -u := Int.toNat_of_nonneg (by omega)
    have hb : (b : Int) = -v := Int.toNat_of_nonneg (by omega)
    have hba : b < a := by omega
    have hbpos : 0 < b := by omega
    have heq : Q = NegativePair (a,b) := by
      rw [hrep]
      change ({u,v} : Finset Int) = {-(a : Int),-(b : Int)}
      rw [ha,hb]
      simp
    have hp := (negative_pair_iff a b hbpos hba).mp (by
      simpa only [heq, NegativePair] using hQ)
    exact Or.inl ⟨a,b,heq,hbpos,hba,hp⟩
  · by_cases hu : 0 < u
    · let a := v.toNat
      let b := u.toNat
      have ha : (a : Int) = v := Int.toNat_of_nonneg (by omega)
      have hb : (b : Int) = u := Int.toNat_of_nonneg (by omega)
      have hba : b < a := by omega
      have hbpos : 0 < b := by omega
      have heq : Q = PositivePair (a,b) := by
        rw [hrep]
        change ({u,v} : Finset Int) = {(b : Int),(a : Int)}
        rw [ha,hb]
      have hp := (positive_pair_iff a b hbpos hba).mp (by
        simpa only [heq, PositivePair] using hQ)
      exact Or.inr (Or.inl ⟨a,b,heq,hbpos,hba,hp⟩)
    · let a := (-u).toNat
      let r := v.toNat
      have ha : (a : Int) = -u := Int.toNat_of_nonneg (by omega)
      have hr : (r : Int) = v := Int.toNat_of_nonneg (by omega)
      have hapos : 0 < a := by omega
      have hrpos : 0 < r := by omega
      have heq : Q = CrossPair (a,r) := by
        rw [hrep]
        change ({u,v} : Finset Int) = {-(a : Int),(r : Int)}
        rw [ha,hr]
        simp
      have hp := (mixed_pair_iff a r hapos hrpos).mp (by
        simpa only [heq, CrossPair] using hQ)
      exact Or.inr (Or.inr ⟨a,r,heq,hapos,hrpos,hp⟩)

theorem mem_down_pool (C : Finset (Nat × Nat)) (Q : Finset Int) :
    Q ∈ PrimitivePool (Family (Down C)) ↔ IsPrimitiveBadPair Q ∧
      ∃ l r : Nat, (l,r) ∈ Down C ∧ Q ⊆ Window l r := by
  classical
  constructor
  · intro hQ
    obtain ⟨S,hS,hQS⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hS
    have hQS' := (mem_primitiveBadPairs _ Q).mp hQS
    exact ⟨hQS'.2,p.1,p.2,hp,hQS'.1⟩
  · rintro ⟨hQ,l,r,hlr,hsub⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨Window l r, Finset.mem_image.mpr ⟨(l,r),hlr,rfl⟩, ?_⟩
    exact (mem_primitiveBadPairs _ Q).mpr ⟨hsub,hQ⟩

theorem positive_width_cell (C : Finset (Nat × Nat)) (a : Nat)
    (ha : 0 < a) (hle : a ≤ Width C) : (0,a) ∈ Down C := by
  obtain ⟨p,hp,hpa⟩ := (Finset.le_sup_iff ha).mp hle
  exact (mem_down C (0,a)).mpr ⟨p,hp,Nat.zero_le _,hpa⟩

theorem leftPool_subset_down_pool (C : Finset (Nat × Nat)) :
    LeftPool (Profile C 0 - 1) ⊆ PrimitivePool (Family (Down C)) := by
  intro Q hQ
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  have hp' := (mem_sameCoords (Profile C 0-1) p).mp hp
  have hb := sameCoords_second_pos hp
  apply (mem_down_pool C _).mpr
  refine ⟨(negative_pair_iff p.1 p.2 hb hp'.2.2.1).mpr ⟨hp'.2.2.2,hp'.2.1⟩,
    p.1,0,(mem_down_iff_profile C p.1 0).mpr (by omega), ?_⟩
  intro x hx
  simp only [NegativePair, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_window]
  omega

theorem rightPool_subset_down_pool (C : Finset (Nat × Nat)) :
    RightPool (Width C) ⊆ PrimitivePool (Family (Down C)) := by
  intro Q hQ
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  have hp' := (mem_sameCoords (Width C) p).mp hp
  have hb := sameCoords_second_pos hp
  apply (mem_down_pool C _).mpr
  refine ⟨(positive_pair_iff p.1 p.2 hb hp'.2.2.1).mpr ⟨hp'.2.2.2,hp'.2.1⟩,
    0,p.1,positive_width_cell C p.1 (by omega) hp'.1, ?_⟩
  intro x hx
  simp only [PositivePair, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_window]
  omega

theorem crossPool_subset_down_pool (C : Finset (Nat × Nat)) :
    CrossPool (Profile C) (Width C) ⊆ PrimitivePool (Family (Down C)) := by
  intro Q hQ
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  have hp' := (mem_mixedCoords (Profile C) (Width C) p).mp hp
  apply (mem_down_pool C _).mpr
  refine ⟨(mixed_pair_iff p.1 p.2 hp'.2.2.2.1 hp'.2.1).mpr hp'.2.2.2.2,
    p.1,p.2,(mem_down_iff_profile C p.1 p.2).mpr hp'.2.2.1, ?_⟩
  intro x hx
  simp only [CrossPair, Finset.mem_insert, Finset.mem_singleton] at hx
  rw [mem_window]
  omega

theorem down_pool_eq_three_pools (C : Finset (Nat × Nat)) :
    PrimitivePool (Family (Down C)) =
      LeftPool (Profile C 0-1) ∪ RightPool (Width C) ∪ CrossPool (Profile C) (Width C) := by
  apply Finset.Subset.antisymm
  · intro Q hQ
    obtain ⟨hprim,l,r,hlr,hsub⟩ := (mem_down_pool C Q).mp hQ
    rcases primitive_three_types Q hprim with ⟨a,b,hrep,hb,hba,hg,ha⟩ |
      ⟨a,b,hrep,hb,hba,hg,ha⟩ | ⟨a,s,hrep,ha,hs,hg,hne⟩
    · have hpoint : -(a : Int) ∈ Window l r := hsub (by rw [hrep]; simp [NegativePair])
      have hpoint' := (mem_window l r _).mp hpoint
      have hl0 : (l,0) ∈ Down C := down_closed hlr le_rfl (Nat.zero_le _)
      have hprof := (mem_down_iff_profile C l 0).mp hl0
      apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_union.mpr
      apply Or.inl
      exact Finset.mem_image.mpr ⟨(a,b),
        (mem_sameCoords (Profile C 0-1) (a,b)).mpr ⟨by omega,ha,hba,hg⟩,hrep.symm⟩
    · have hpoint : (a : Int) ∈ Window l r := hsub (by rw [hrep]; simp [PositivePair])
      have hpoint' := (mem_window l r _).mp hpoint
      have hwidth := down_width_bound hlr
      apply Finset.mem_union.mpr
      apply Or.inl
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨(a,b),
        (mem_sameCoords (Width C) (a,b)).mpr ⟨by omega,ha,hba,hg⟩,hrep.symm⟩
    · have hleft : -(a : Int) ∈ Window l r := hsub (by rw [hrep]; simp [CrossPair])
      have hright : (s : Int) ∈ Window l r := hsub (by rw [hrep]; simp [CrossPair])
      have hl' := (mem_window l r _).mp hleft
      have hr' := (mem_window l r _).mp hright
      have has : (a,s) ∈ Down C := down_closed hlr (by omega) (by omega)
      have hprof := (mem_down_iff_profile C a s).mp has
      have hwidth := down_width_bound has
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨(a,s),
        (mem_mixedCoords (Profile C) (Width C) (a,s)).mpr ⟨hwidth,hs,hprof,ha,hg,hne⟩,
        hrep.symm⟩))
  · intro Q hQ
    rcases Finset.mem_union.mp hQ with hQ | hQ
    · rcases Finset.mem_union.mp hQ with hQ | hQ
      · exact leftPool_subset_down_pool C hQ
      · exact rightPool_subset_down_pool C hQ
    · exact crossPool_subset_down_pool C hQ

theorem leftPool_negative {H : Nat} {Q : Finset Int} (hQ : Q ∈ LeftPool H)
    (x : Int) (hx : x ∈ Q) : x < 0 := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  have hp' := (mem_sameCoords H p).mp hp
  have hb := sameCoords_second_pos hp
  simp only [NegativePair, Finset.mem_insert, Finset.mem_singleton] at hx
  omega

theorem rightPool_positive {R : Nat} {Q : Finset Int} (hQ : Q ∈ RightPool R)
    (x : Int) (hx : x ∈ Q) : 0 < x := by
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQ
  have hp' := (mem_sameCoords R p).mp hp
  have hb := sameCoords_second_pos hp
  simp only [PositivePair, Finset.mem_insert, Finset.mem_singleton] at hx
  omega

theorem crossPool_signs {p : Nat → Nat} {B : Nat} {Q : Finset Int}
    (hQ : Q ∈ CrossPool p B) : (∃ x ∈ Q, x < 0) ∧ ∃ y ∈ Q, 0 < y := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hQ
  have hq' := (mem_mixedCoords p B q).mp hq
  constructor
  · exact ⟨-(q.1 : Int), by simp [CrossPair], by omega⟩
  · exact ⟨(q.2 : Int), by simp [CrossPair], by omega⟩

theorem left_right_disjoint (H R : Nat) : Disjoint (LeftPool H) (RightPool R) := by
  apply Finset.disjoint_left.mpr
  intro Q hQL hQR
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hQL
  have hn := leftPool_negative (Finset.mem_image.mpr ⟨p,hp,rfl⟩) (-(p.1 : Int))
    (by simp [NegativePair])
  have hp := rightPool_positive hQR (-(p.1 : Int)) (by simp [NegativePair])
  omega

theorem left_cross_disjoint (H B : Nat) (p : Nat → Nat) :
    Disjoint (LeftPool H) (CrossPool p B) := by
  apply Finset.disjoint_left.mpr
  intro Q hQL hQC
  obtain ⟨y,hy,hpos⟩ := (crossPool_signs hQC).2
  have hneg := leftPool_negative hQL y hy
  omega

theorem right_cross_disjoint (R B : Nat) (p : Nat → Nat) :
    Disjoint (RightPool R) (CrossPool p B) := by
  apply Finset.disjoint_left.mpr
  intro Q hQR hQC
  obtain ⟨x,hx,hneg⟩ := (crossPool_signs hQC).1
  have hpos := rightPool_positive hQR x hx
  omega

theorem down_pool_card (C : Finset (Nat × Nat)) :
    (PrimitivePool (Family (Down C))).card =
      LeftSupply (Profile C 0-1) + LeftSupply (Width C) +
        ∑ r ∈ Finset.range (Width C+1),
          if 0 < r then MixedSupply (Profile C r-1) r else 0 := by
  rw [down_pool_eq_three_pools,
    Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
      ⟨left_cross_disjoint _ _ _,right_cross_disjoint _ _ _⟩),
    Finset.card_union_of_disjoint (left_right_disjoint _ _),
    leftPool_card,rightPool_card,crossPool_card]

theorem validDown_pool_card {C : Finset (Nat × Nat)} (hvalid : ∀ p ∈ C, Valid p) :
    (PrimitivePool (Family (ValidDown C))).card =
      LeftSupply (Profile C 0-1) + LeftSupply (Width C) +
        ∑ r ∈ Finset.range (Width C+1),
          if 0 < r then MixedSupply (Profile C r-1) r else 0 := by
  rw [validDown_primitivePool_eq hvalid, ← down_primitivePool_eq C]
  exact down_pool_card C

def SupplyScore (r i : Nat) : Nat :=
  if i = 0 then 0 else
    if r = 0 then LeftSupply (i-1)
    else MixedSupply (i-1) r + if 3 ≤ r then PrimitivePhi r else 0

theorem leftSupply_zero : LeftSupply 0 = 0 := by simp [LeftSupply]

theorem supplyScore_at_zero (i : Nat) : SupplyScore 0 i = LeftSupply (i-1) := by
  by_cases hi : i = 0
  · simp [SupplyScore,hi,leftSupply_zero]
  · simp [SupplyScore,hi]

theorem columnScore_eq_demand_sub_supply (r i : Nat) :
    ColumnScore r i = DemandScore r i - (SupplyScore r i : Int) := by
  by_cases hi : i = 0
  · simp [ColumnScore,DemandScore,SupplyScore,hi]
  · have hdec : i-1-2 = i-3 := by omega
    have hsucc : i-1+1 = i := by omega
    by_cases hr : r = 0
    · simp [ColumnScore,DemandScore,SupplyScore,hi,hr,hdec]
    · simp [ColumnScore,DemandScore,SupplyScore,hi,hr,hsucc,Nat.cast_add]
      ring

theorem profile_pos_of_positive_le_width (C : Finset (Nat × Nat)) (r : Nat)
    (hr : 0 < r) (hwidth : r ≤ Width C) : 0 < Profile C r :=
  (mem_down_iff_profile C 0 r).mp (positive_width_cell C r hr hwidth)

theorem actual_supplyScore (C : Finset (Nat × Nat)) (r : Nat) (hr : r ≤ Width C) :
    SupplyScore r (Profile C r) =
      (if r = 0 then LeftSupply (Profile C 0-1) else 0) +
      (if 0 < r then MixedSupply (Profile C r-1) r else 0) +
      (if 3 ≤ r then PrimitivePhi r else 0) := by
  by_cases hz : r = 0
  · subst r
    simp [supplyScore_at_zero]
  · have hpos := profile_pos_of_positive_le_width C r (by omega) hr
    simp [SupplyScore,hz,show Profile C r ≠ 0 by omega,show 0 < r by omega]

theorem sum_supplyScore (C : Finset (Nat × Nat)) :
    (∑ r ∈ Finset.range (Width C+1), SupplyScore r (Profile C r)) =
      LeftSupply (Profile C 0-1) + LeftSupply (Width C) +
        ∑ r ∈ Finset.range (Width C+1),
          if 0 < r then MixedSupply (Profile C r-1) r else 0 := by
  have hterm : (∑ r ∈ Finset.range (Width C+1), SupplyScore r (Profile C r)) =
      ∑ r ∈ Finset.range (Width C+1),
        ((if r = 0 then LeftSupply (Profile C 0-1) else 0) +
        (if 0 < r then MixedSupply (Profile C r-1) r else 0) +
        (if 3 ≤ r then PrimitivePhi r else 0)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact actual_supplyScore C r (by have := Finset.mem_range.mp hr; omega)
  rw [hterm,Finset.sum_add_distrib,Finset.sum_add_distrib]
  have hzero : (∑ r ∈ Finset.range (Width C+1),
      if r = 0 then LeftSupply (Profile C 0-1) else 0) = LeftSupply (Profile C 0-1) := by
    simp
  rw [hzero]
  change _ + _ + LeftSupply (Width C) = _
  omega

theorem validDown_pool_card_sum_supplyScore {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    (PrimitivePool (Family (ValidDown C))).card =
      ∑ r ∈ Finset.range (Width C+1), SupplyScore r (Profile C r) := by
  rw [sum_supplyScore]
  exact validDown_pool_card hvalid

theorem validDown_defect_eq_profileScore {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    ((Family (ValidDown C)).card : Int) - (PrimitivePool (Family (ValidDown C))).card =
      ProfileScore ColumnScore (Profile C) (Width C) := by
  rw [validDown_demand_profileScore,validDown_pool_card_sum_supplyScore hvalid]
  simp only [ProfileScore,columnScore_eq_demand_sub_supply,Finset.sum_sub_distrib,Nat.cast_sum]

theorem original_defect_le_profileScore {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) :
    ((Family C).card : Int) - (PrimitivePool (Family C)).card ≤
      ProfileScore ColumnScore (Profile C) (Width C) := by
  rw [← validDown_defect_eq_profileScore hvalid,validDown_primitivePool_eq hvalid]
  exact sub_le_sub_right (Int.ofNat_le.mpr (validDown_demand_mono hvalid)) _

theorem actual_family_defect_bridge (F : Finset (Finset Int))
    (hF : ∀ S ∈ F, ∃ l r : Nat, S = Window l r ∧ 4 ≤ S.card) :
    ∃ C : Finset (Nat × Nat), Family C = F ∧ Antitone (Profile C) ∧
      (F.card : Int) - (PrimitivePool F).card ≤
        ProfileScore ColumnScore (Profile C) (Width C) := by
  obtain ⟨C,hC,hvalid⟩ := exists_coordinates F hF
  refine ⟨C,hC,profile_antitone C,?_⟩
  rw [← hC]
  exact original_defect_le_profileScore hvalid

theorem original_defect_le_of_certificate {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) {cap : Int} {potential : Nat → Nat → Int}
    (cert : Certificate (Width C) (Height C+1) cap ColumnScore potential) :
    ((Family C).card : Int) - (PrimitivePool (Family C)).card ≤ cap := by
  apply (original_defect_le_profileScore hvalid).trans
  apply certificate_sound cert (Profile C)
  · intro r hr
    exact profile_height_bound C r
  · intro r hr
    exact profile_antitone C (by omega)

theorem profileScore_eq_padded (C : Finset (Nat × Nat)) (B : Nat) (hB : Width C ≤ B) :
    ProfileScore ColumnScore (Profile C) (Width C) = ProfileScore ColumnScore (Profile C) B := by
  unfold ProfileScore
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro r hrB hrW
  have hr : Width C < r := by
    have hn : ¬ r < Width C+1 := by simpa only [Finset.mem_range] using hrW
    omega
  rw [profile_zero_of_width_lt C hr]
  simp [ColumnScore]

/-- A first actual-family consequence of the previously checked B=8 table.
The extents, not the number of members or their pair resources, are bounded. -/
theorem original_defect_le_one_eight {C : Finset (Nat × Nat)}
    (hvalid : ∀ p ∈ C, Valid p) (hwidth : Width C ≤ 8) (hheight : Height C ≤ 8) :
    ((Family C).card : Int) - (PrimitivePool (Family C)).card ≤ 1 := by
  apply (original_defect_le_profileScore hvalid).trans
  rw [profileScore_eq_padded C 8 hwidth]
  apply eight_profiles_score_le_one (Profile C)
  · intro r hr
    have hp := profile_height_bound C r
    omega
  · intro r hr
    exact profile_antitone C (by omega)

#print axioms unit_three_isAP
#print axioms negative_unit_isAP
#print axioms mixed_unit_isAP
#print axioms primitive_triple_isAP_iff
#print axioms primitive_pair_iff
#print axioms positive_pair_iff
#print axioms negative_pair_iff
#print axioms mixed_pair_iff
#print axioms ordered_pair_ext
#print axioms mem_sameCoords
#print axioms sameCoords_second_pos
#print axioms sameSlice_card
#print axioms sameCoords_card
#print axioms mem_mixedCoords
#print axioms mixedSupply_zero
#print axioms mixedSlice_card
#print axioms mixedCoords_card
#print axioms leftPool_card
#print axioms rightPool_card
#print axioms crossPool_card
#print axioms sorted_pair_representation
#print axioms primitive_three_types
#print axioms mem_down_pool
#print axioms positive_width_cell
#print axioms leftPool_subset_down_pool
#print axioms rightPool_subset_down_pool
#print axioms crossPool_subset_down_pool
#print axioms down_pool_eq_three_pools
#print axioms leftPool_negative
#print axioms rightPool_positive
#print axioms crossPool_signs
#print axioms left_right_disjoint
#print axioms left_cross_disjoint
#print axioms right_cross_disjoint
#print axioms down_pool_card
#print axioms validDown_pool_card
#print axioms leftSupply_zero
#print axioms supplyScore_at_zero
#print axioms columnScore_eq_demand_sub_supply
#print axioms profile_pos_of_positive_le_width
#print axioms actual_supplyScore
#print axioms sum_supplyScore
#print axioms validDown_pool_card_sum_supplyScore
#print axioms validDown_defect_eq_profileScore
#print axioms original_defect_le_profileScore
#print axioms actual_family_defect_bridge
#print axioms original_defect_le_of_certificate
#print axioms profileScore_eq_padded
#print axioms original_defect_le_one_eight

end JSP233.StaircaseSupply
