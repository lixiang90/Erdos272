module

public import Erdos272.Capacity.N20258.ConcentratedPrice20258
public import Erdos272.Global.N20258.FortyFourFamily20258
public import Erdos272.Global.N20258.FirstSparseCut20258
public import Erdos272.Arithmetic.N20258.PriceChord20258
public import Erdos272.Arithmetic.N20258.StrideQuotients20258

@[expose] public section
namespace JSP233.ConcentratedCut20258
open StarCompletion PrivatePairExistence APClasses88404 IntrinsicTriples208 PaddedSource20258
open FirstSparseCut20258 SparseSmall39 Density41 ResidueCapacity20258
open scoped Classical BigOperators
set_option autoImplicit false

/-- A rectangle in ground size and first cutoff, with one triple price and
one lower bound for the length of an off-list progression. -/
structure Block where
  lo : ℕ
  hi : ℕ
  lowerCut : ℕ
  upperCut : ℕ
  length : ℕ
  price : ℕ
  deriving DecidableEq

def tail (b : Block) := StrideQuotients20258.compactTail (b.hi-1) b.length 160 steps

def total (b : Block) (head debt : ℕ) :=
  let r := b.upperCut
  let n := b.hi-2
  (1+tail b)*b.price+debt+head*(r*n)+(b.price-head)*(((r-1)*r+1)*n)

def Block.Valid (b : Block) (minimum head debt : ℕ) : Prop :=
  20258≤b.lo ∧ b.lo≤b.hi ∧ b.hi<2^16 ∧ 2≤b.lowerCut ∧
  (b.length=1 ∨ 5000*((b.upperCut-1)*b.length+17)≤443*b.lo) ∧
  minimum≤max b.lowerCut (b.length+1) ∧ 0<b.price ∧ head≤b.price ∧
  b.hi-1≤2*b.price ∧ 387679*b.price≤138655*(3*(b.lo-1))+99000 ∧
  (total b head debt:ℚ)≤PriceChord20258.allowance ((b.lo-1:ℕ):ℚ) (b.price:ℚ) ∧
  (total b head debt:ℚ)≤PriceChord20258.allowance ((b.hi-1:ℕ):ℚ) (b.price:ℚ)

instance (b : Block) (s h v : ℕ) : Decidable (b.Valid s h v) := by unfold Block.Valid; infer_instance

/-- Consume an actual triple estimate on the avoiders of the cutoff root.
The head may be below the joint price; only the difference is charged to
the two-transversal population bound. -/
theorem upper {N m s h v : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ} {b : Block}
    (lo : b.lo≤N) (hi : N≤b.hi) (lcut : b.lowerCut≤m) (ucut : m≤b.upperCut)
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (valid : b.Valid s h v)
    (source : ∀ A : Finset (Finset ℤ), Legal (Ground b.hi) A → (∀ S∈A,¬IsAP S) →
      (∀ S∈A,s≤S.card) → h*A.card≤(∑ S∈A,(Pool S).card)+v) : F.card≤B N := by
  classical
  by_contra! counter
  obtain ⟨ground,range,cap,two,length,minima,xpos,covered,span,bend,left,right⟩ := valid
  have sparse := cut.sparse
  let H := CrookedMembers F
  let A := H.filter (fun S => c∉S)
  have hsub : H⊆F := Finset.filter_subset _ _
  have asub : A⊆H := Finset.filter_subset _ _
  have padded : Legal (Ground b.hi) F := by
    refine ⟨fun S hs y hy => ?_,legal.2⟩
    obtain ⟨l,u⟩ := (mem_ground N y).mp (legal.1 S hs hy)
    exact (mem_ground b.hi y).mpr ⟨l,u.trans (by exact_mod_cast hi)⟩
  have long {S : Finset ℤ} (hs : S∈F) (size : 2≤S.card) : b.length<S.card := by
    rcases length with first|enough
    · omega
    by_contra! short
    have product := Nat.mul_le_mul (Nat.sub_le_sub_right ucut 1) short
    have due := (Nat.mul_le_mul_left 5000 (Nat.add_le_add_right product 17)).trans
      (enough.trans (Nat.mul_le_mul_left 443 lo))
    exact (not_lt_of_ge (FortyFourFamily20258.of_member (by omega) (by omega) legal hs cut.crooked due)) counter
  have sizeA (S : Finset ℤ) (hs : S∈A) : s≤S.card := by
    obtain ⟨mem,miss⟩ := Finset.mem_filter.mp hs
    obtain ⟨inside,bad⟩ := Finset.mem_filter.mp mem
    have sc : m≤S.card := by
      by_cases sp : 12*S.card≤N
      · exact cut.minimum S (actual_sparse_membership.mpr ⟨inside,bad,sp⟩) miss
      · omega
    have spanS := long inside (by omega)
    omega
  have subF := asub.trans hsub
  have legalA : Legal (Ground b.hi) A := ⟨fun S hs => padded.1 S (subF hs),
    fun S hs U hu => legal.2 S (subF hs) U (subF hu)⟩
  have pay := source A legalA (fun S hs => (Finset.mem_filter.mp (asub hs)).2) sizeA
  have mass : (∑ S∈A,(Pool S).card)≤∑ S∈F,(Pool S).card :=
    Finset.sum_le_sum_of_subset_of_nonneg subF (fun _ _ _ => Nat.zero_le _)
  have omitter := (actual_sparse_membership.mp cut.omitter).1
  have count := TwoTransversals20258.actual_member (by omega : 2≤N) (by omega : m+1≤N) legal omitter
    (Finset.card_pos.mp (by rw [cut.size]; omega)) cut.crooked
  rw [cut.size] at count
  have countN : H.card≤((b.upperCut-1)*b.upperCut+1)*(b.hi-2) := count.trans
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul (Nat.sub_le_sub_right ucut 1) ucut) 1) (Nat.sub_le_sub_right hi 2))
  have degree := MixedOmitter20258.actual_degree legal omitter cut.misses
  rw [cut.size] at degree
  have standard := degreeBudget_closed N m (by omega) (by omega)
  have rooted : (RootPart H c).card≤b.upperCut*(b.hi-2) := degree.trans
    (((Nat.le_add_right _ _).trans standard.le).trans (Nat.mul_le_mul ucut (Nat.sub_le_sub_right hi 2)))
  have parts : (RootPart H c).card+A.card=H.card := Finset.card_filter_add_card_filter_not (s:=H) _
  have expense : b.price*H.card≤(∑ S∈F,(Pool S).card)+v+h*(b.upperCut*(b.hi-2))+
      (b.price-h)*(((b.upperCut-1)*b.upperCut+1)*(b.hi-2)) := by
    have mix : b.price*H.card=h*(RootPart H c).card+h*A.card+(b.price-h)*H.card := by
      rw [←Nat.mul_add,parts,←Nat.add_mul,Nat.add_sub_of_le covered]
    rw [mix]
    have base := pay.trans (Nat.add_le_add_right mass v)
    have paidRoot := Nat.mul_le_mul_left h rooted
    have paidCount := Nat.mul_le_mul_left (b.price-h) countN
    omega
  have width := ResidueJoint20258.steps_in_ground (by omega : 62≤b.hi)
  have aps := ProgressionPartition20258.actual_AP_partition (by omega : 1≤b.hi) padded steps width
    (fun d _ S hs => long (subset F d hs) (card_two hs))
  have teq : tail b=ProgressionPartition20258.offTail (b.hi-1) b.length steps :=
    StrideQuotients20258.compact_tail_eq (by omega) width
  rw [←teq] at aps
  have apR : ((F.filter IsAP).card:ℝ)≤1+(∑ d∈steps,((StepAP F d).card:ℝ))+(tail b:ℝ) := by exact_mod_cast aps
  have split : ((F.filter IsAP).card:ℝ)+(H.card:ℝ)=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s:=F) IsAP
  let x : ℝ := b.price
  have xp : 0<x := by dsimp only [x]; exact_mod_cast xpos
  have spanN : ((N-1:ℕ):ℝ)≤2*x := by dsimp only [x]; exact_mod_cast (show N-1≤2*b.price by omega)
  have joint := VariablePrice20258.actual (by omega : 62≤N) xp spanN legal
  have cast_end (t : ℕ) (e : (total b h v:ℚ)≤PriceChord20258.allowance (t:ℚ) (b.price:ℚ)) :
      (total b h v:ℝ)≤PriceChord20258.allowance (t:ℝ) x := by
    have z := (Rat.cast_le (K:=ℝ)).mpr e
    unfold PriceChord20258.allowance PriceChord20258.target VariablePrice20258.bound at z ⊢
    push_cast at z; exact z
  have mid := PriceChord20258.between (by exact_mod_cast Nat.sub_le_sub_right lo 1 :
      ((b.lo-1:ℕ):ℝ)≤((N-1:ℕ):ℝ)) (by exact_mod_cast Nat.sub_le_sub_right hi 1 :
      ((N-1:ℕ):ℝ)≤((b.hi-1:ℕ):ℝ)) (x:=x) (K:=(total b h v:ℝ)) (by
    dsimp only [x]
    exact_mod_cast (show 387679*b.price≤138655*((b.lo-1)+(N-1)+(b.hi-1))+99000 by omega))
    (cast_end _ left) (cast_end _ right)
  have target := mul_le_mul_of_nonneg_right (PriceChord20258.target_le (show 1≤N by omega)) xp.le
  have bill : x*(H.card:ℝ)≤(∑ S∈F,((Pool S).card:ℝ))+v+(h:ℝ)*(b.upperCut*((b.hi-2:ℕ):ℝ))+
      (x-h)*((((b.upperCut-1:ℕ):ℝ)*b.upperCut+1)*((b.hi-2:ℕ):ℝ)) := by
    dsimp only [x]; exact_mod_cast expense
  have scaled := mul_le_mul_of_nonneg_right apR xp.le
  have sum := congrArg (fun a : ℝ => a*x) split
  unfold PriceChord20258.allowance total at mid
  push_cast [Nat.cast_sub covered] at mid
  have final : (F.card:ℝ)*x≤(B N:ℝ)*x := by
    dsimp only [x] at *
    nlinarith only [mid,joint,bill,scaled,sum,target]
  exact (not_lt_of_ge (by exact_mod_cast le_of_mul_le_mul_right final xp : F.card≤B N)) counter

#print axioms upper
end JSP233.ConcentratedCut20258
