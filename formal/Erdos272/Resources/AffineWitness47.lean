module

public import Erdos272.Geometry.AffineTrace46
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Chain

@[expose] public section

/-! Sparse, ordinary-kernel witness certificates for every prefix of a block.
Only listed coprime points are checked; no claim about unlisted points is needed. -/
namespace JSP233.AffineWitness47
open scoped Classical
noncomputable section

def BlockCount (m l n : ℕ) : ℕ :=
  ((Finset.Ioc l (l+n)).filter (fun x=>Nat.Coprime x m)).card

def BlockEstimate (m a l n c d : ℕ) : Prop :=
  c≤BlockCount m l n ∧ ∀ k≤n,k≤a*BlockCount m l k+d

def HeadBound (a : ℕ) : ℕ→List ℕ→Bool
  | _,[]=>true
  | d,x::xs=>decide (x≤d+1) && HeadBound a (d+a) xs

def ValidWitness (m a l n d : ℕ) (xs : List ℕ) : Bool :=
  decide (xs.IsChain (·<·)) &&
  xs.all (fun x=>decide (1≤x ∧ x≤n ∧ Nat.Coprime (l+x) m)) &&
  HeadBound a d xs && decide (n≤a*xs.length+d)

theorem block_count_add (m l n t : ℕ) :
    BlockCount m l (n+t)=BlockCount m l n+BlockCount m (l+n) t := by
  have hu : Finset.Ioc l (l+(n+t))=Finset.Ioc l (l+n)∪Finset.Ioc (l+n) ((l+n)+t) := by
    ext x
    simp only [Finset.mem_Ioc,Finset.mem_union]
    omega
  have hd : Disjoint
      ((Finset.Ioc l (l+n)).filter (fun x=>Nat.Coprime x m))
      ((Finset.Ioc (l+n) ((l+n)+t)).filter (fun x=>Nat.Coprime x m)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1
    have hy' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1
    omega
  unfold BlockCount
  rw [hu,Finset.filter_union,Finset.card_union_of_disjoint hd]

theorem block_zero_prefix (m k : ℕ) :
    BlockCount m 0 k=(PrimePrefix35.CoprimePrefix m k).card := by
  unfold BlockCount PrimePrefix35.CoprimePrefix
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_Icc,Nat.zero_add]
  omega

theorem head_bound_prefix (a d n : ℕ) (xs : List ℕ)
    (hh : HeadBound a d xs=true) (he : n≤a*xs.length+d) :
    ∀ k≤n,k≤a*(xs.filter (fun x=>decide (x≤k))).length+d := by
  induction xs generalizing d with
  | nil =>
    intro k hk
    simpa using hk.trans he
  | cons x xs ih =>
    have hh' : x≤d+1 ∧ HeadBound a (d+a) xs=true := by
      simpa only [HeadBound,Bool.and_eq_true,decide_eq_true_eq] using hh
    have he' : n≤a*xs.length+(d+a) := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at he
      omega
    intro k hk
    by_cases hx : x≤k
    · have ht := ih (d+a) hh'.2 he' k hk
      simp only [List.filter_cons,decide_eq_true hx,ite_true,List.length_cons,
        Nat.mul_add,Nat.mul_one]
      omega
    · have hkd : k≤d := by omega
      exact hkd.trans (Nat.le_add_left _ _)

theorem witness_prefix_count_le (m l n k : ℕ) (xs : List ℕ)
    (hn : xs.Nodup)
    (hg : ∀ x∈xs,1≤x ∧ x≤n ∧ Nat.Coprime (l+x) m) :
    (xs.filter (fun x=>decide (x≤k))).length≤BlockCount m l k := by
  let Y := (xs.filter (fun x=>decide (x≤k))).toFinset
  have hy : Y.card=(xs.filter (fun x=>decide (x≤k))).length :=
    List.toFinset_card_of_nodup (hn.filter _)
  have him : (Y.image (fun x=>l+x)).card=Y.card :=
    Finset.card_image_of_injective Y (fun x y h=>Nat.add_left_cancel h)
  have hs : Y.image (fun x=>l+x)⊆(Finset.Ioc l (l+k)).filter (fun x=>Nat.Coprime x m) := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hx' : x∈xs ∧ x≤k := by
      simpa only [Y,List.mem_toFinset,List.mem_filter,decide_eq_true_eq] using hx
    obtain ⟨hx1,_,hcop⟩ := hg x hx'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,hcop⟩
  calc
    _=Y.card := hy.symm
    _=(Y.image (fun x=>l+x)).card := him.symm
    _≤_ := Finset.card_le_card hs

theorem estimate_of_valid (m a l n d : ℕ) (xs : List ℕ)
    (hv : ValidWitness m a l n d xs=true) : BlockEstimate m a l n xs.length d := by
  have hh : xs.IsChain (·<·) ∧
      (∀ x∈xs,1≤x ∧ x≤n ∧ Nat.Coprime (l+x) m) ∧
      HeadBound a d xs=true ∧ n≤a*xs.length+d := by
    simpa only [ValidWitness,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc] using hv
  have hn := (List.isChain_iff_pairwise.mp hh.1).nodup
  have hc := witness_prefix_count_le m l n n xs hn hh.2.1
  have hf : xs.filter (fun x=>decide (x≤n))=xs := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (hh.2.1 x hx).2.1
  refine ⟨by simpa only [hf] using hc,?_⟩
  intro k hk
  exact (head_bound_prefix a d n xs hh.2.2.1 hh.2.2.2 k hk).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left a (witness_prefix_count_le m l n k xs hn hh.2.1)) d)

theorem estimate_join {m a l n t c d e f : ℕ}
    (hL : BlockEstimate m a l n c d) (hR : BlockEstimate m a (l+n) t e f) :
    BlockEstimate m a l (n+t) (c+e) (max d (n+f-a*c)) := by
  refine ⟨?_,?_⟩
  · rw [block_count_add]
    exact Nat.add_le_add hL.1 hR.1
  · intro k hk
    by_cases hkn : k≤n
    · exact (hL.2 k hkn).trans (Nat.add_le_add_left (le_max_left _ _) _)
    · have hsplit : k=n+(k-n) := by omega
      have hkt : k-n≤t := by omega
      have hr := hR.2 (k-n) hkt
      have hm := Nat.mul_le_mul_left a hL.1
      have hd : n+f≤a*c+max d (n+f-a*c) := by
        have hh : n+f-a*c≤max d (n+f-a*c) := le_max_right _ _
        omega
      have hc : BlockCount m l k=BlockCount m l n+BlockCount m (l+n) (k-n) := by
        exact (congrArg (BlockCount m l) hsplit).trans (block_count_add m l n (k-n))
      rw [hc,Nat.mul_add]
      omega

#print axioms block_count_add
#print axioms block_zero_prefix
#print axioms head_bound_prefix
#print axioms witness_prefix_count_le
#print axioms estimate_of_valid
#print axioms estimate_join
end
end JSP233.AffineWitness47
