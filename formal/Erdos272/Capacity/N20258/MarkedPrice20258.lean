module

public import Erdos272.Counting.N20258.MarkedPopulation20258
public import Erdos272.Capacity.N20258.UniformCardPool20258
public import Erdos272.Core.N180000.AnalyticCore180000

@[expose] public section
namespace JSP233.MarkedPrice20258
open StarCompletion APGeometry IntrinsicTriples208 SourceBridge208 MarkedPopulation20258
open scoped BigOperators
set_option autoImplicit false

/-- One fee multiplies the total defects in the indicated cumulative layer. -/
def charge (rows : List (ℕ × ℕ)) (e : ℕ) : ℕ :=
  (rows.map (fun (k,b) => if e≤k then b*e else 0)).sum

def fee (rows : List (ℕ × ℕ)) (n m : ℕ) : ℕ :=
  (rows.map (fun (k,b) => b*budget n (m-1-k) k 216)).sum

def smallPrice (m e : ℕ) : ℕ :=
  let t := m-e
  if e=1 then UniformNumeric84364.value m else e*((27*t*t-150*t)/100)

private theorem analytic {S : Finset ℤ} {m : ℕ} (lo : 78≤m) (hi : m≤100)
    (size : m≤S.card) (top : S.card≤216) (two : 2≤Defect S) (few : Defect S<28) :
    smallPrice m (Defect S)≤(Pool S).card := by
  let t := m-Defect S
  have ht : 51≤t := by dsimp [t]; omega
  have ht' : t≤MaxAPSize S := by
    have h := maxAPSize_le_card S
    dsimp [t,Defect]
    omega
  have pay : 150*t≤27*t*t := by
    have h : 150≤27*t := by omega
    exact Nat.mul_le_mul_right _ h
  have unit : (27*t*t-150*t)/100≤CoreUnionSource200000.UnitBound (MaxAPSize S) := by
    apply AnalyticCore180000.floor_small ht' ((maxAPSize_le_card S).trans (by omega)) (by omega)
    have h := Nat.div_mul_le_self (27*t*t-150*t) 100
    rw [Nat.mul_comm] at h
    omega
  simp only [smallPrice,ite_eq_right (by omega : Defect S≠1)]
  exact (Nat.mul_le_mul_left _ unit).trans (CoreUnionSource200000.actual_union_core_source (by omega))

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem high_table : ∀ i : Fin 139,14000≤
    FastSource208.fastPhysicalK UniformNumeric84364.phi (78+i.val) 28 := by decide +kernel

private theorem high {S : Finset ℤ} (size : 78≤S.card) (top : S.card≤216) (many : 28≤Defect S) :
    14000≤(Pool S).card := by
  let i : Fin 139 := ⟨S.card-78,by omega⟩
  have h := high_table i
  rw [show 78+i.val=S.card by dsimp [i]; omega] at h
  have phi (q : ℕ) (hq : q≤216) : UniformNumeric84364.phi q=q.totient :=
    (UniformBridge84364.phi_eq (by omega)).trans (FastDecode208.phi_correct q (by omega))
  rw [FastSource208.fastPhysicalK_eq phi top] at h
  exact h.trans (actual_source_of_defect (by omega) many)

private theorem one {N m : ℕ} {S : Finset ℤ} (cap : N≤2^18) (ground : S⊆Ground N)
    (bad : ¬IsAP S) (lo : 78≤m) (hi : m≤100) (size : m≤S.card) :
    smallPrice m 1≤(Pool S).card := by
  change UniformNumeric84364.value m≤_
  exact UniformCardPool20258.pool_floor (s:=m) cap ground bad (by omega) (by omega) size le_rfl

private theorem big {N : ℕ} {S : Finset ℤ} (cap : N≤2^18) (ground : S⊆Ground N)
    (bad : ¬IsAP S) (size : 217≤S.card) : 14000≤(Pool S).card :=
  UniformCardPool20258.pool_floor (s:=217) cap ground bad (by decide) (by decide) size (by decide +kernel)

private theorem charges {n m : ℕ} {G : Finset (Finset ℤ)} (rows : List (ℕ × ℕ))
    (legal : Legal (Ground n) G) (large : ∀ S∈G,m≤S.card) (top : ∀ S∈G,S.card≤216)
    (steps : ∀ r∈rows,r.1+2≤m) : ∑ S∈G,charge rows (Defect S)≤fee rows n m := by
  classical
  induction rows with
  | nil => simp [charge,fee]
  | cons r rows ih =>
    obtain ⟨k,b⟩ := r
    have len := steps (k,b) (List.mem_cons_self ..)
    change k+2≤m at len
    let A := G.filter (fun S => Defect S≤k)
    have sub : A⊆G := Finset.filter_subset _ _
    have ha : Legal (Ground n) A :=
      ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht ne => legal.2 S (sub hs) T (sub ht) ne⟩
    have bound := MarkedPopulation20258.actual (a:=m-1-k) ha (by omega)
      (fun S hs => by have := large S (sub hs); omega) (fun S hs => top S (sub hs))
      (fun S hs => (Finset.mem_filter.mp hs).2)
    have head : ∑ S∈G,(if Defect S≤k then b*Defect S else 0)≤b*budget n (m-1-k) k 216 := by
      rw [←Finset.sum_filter,←Finset.mul_sum]
      exact Nat.mul_le_mul_left b bound
    simpa only [charge,fee,List.map_cons,List.sum_cons,Finset.sum_add_distrib] using
      Nat.add_le_add head (ih (fun r hr => steps r (List.mem_cons_of_mem _ hr)))

/-- A single short table indexed by the defect pays every size in the window.
Sizes above 216 and defects above 27 use the same uniform prices for all cuts. -/
theorem family {n m x : ℕ} {A : Finset (Finset ℤ)} (rows : List (ℕ × ℕ))
    (legal : Legal (Ground n) A) (cap : n≤2^18) (lo : 78≤m) (hi : m≤100) (price : x≤14000)
    (large : ∀ S∈A,m≤S.card) (bad : ∀ S∈A,¬IsAP S)
    (steps : ∀ r∈rows,r.1+2≤m)
    (prices : ∀ i : Fin 27,x≤smallPrice m (i.val+1)+charge rows (i.val+1)) :
    x*A.card≤(∑ S∈A,(Pool S).card)+fee rows n m := by
  classical
  let G := A.filter (fun S => S.card≤216)
  have sub : G⊆A := Finset.filter_subset _ _
  have hs : Legal (Ground n) G :=
    ⟨fun S h => legal.1 S (sub h),fun S h T j ne => legal.2 S (sub h) T (sub j) ne⟩
  have pay (S : Finset ℤ) (hsA : S∈A) : x≤(Pool S).card+
      (if S.card≤216 then charge rows (Defect S) else 0) := by
    have inside := legal.1 S hsA
    have sz := large S hsA
    by_cases small : S.card≤216
    · rw [ite_eq_left small]
      by_cases many : 28≤Defect S
      · exact (price.trans (high (by omega) small many)).trans (Nat.le_add_right _ _)
      have pos := MixedCore200000.crooked_defect_positive (by omega : 2≤S.card) (bad S hsA)
      let i : Fin 27 := ⟨Defect S-1,by omega⟩
      have p := prices i
      rw [show i.val+1=Defect S by dsimp [i]; omega] at p
      apply p.trans (Nat.add_le_add_right ?_ _)
      by_cases first : Defect S=1
      · rw [first]
        exact one cap inside (bad S hsA) lo hi sz
      · exact analytic lo hi sz small (by omega) (by omega)
    · simpa only [ite_eq_right small,Nat.add_zero] using price.trans (big cap inside (bad S hsA) (by omega))
  have h := Finset.sum_le_sum pay
  rw [Finset.sum_const,Finset.sum_add_distrib,←Finset.sum_filter] at h
  simpa only [smul_eq_mul,Nat.mul_comm x] using
    h.trans (Nat.add_le_add_left (charges rows hs (fun S h => large S (sub h))
      (fun S h => (Finset.mem_filter.mp h).2) steps) _)

#print axioms family
end JSP233.MarkedPrice20258
