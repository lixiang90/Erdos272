module

public import Erdos272.Counting.N20258.ConcentratedPopulation20258
public import Erdos272.Capacity.N20258.MarkedPrice20258

@[expose] public section
namespace JSP233.ConcentratedPrice20258
open StarCompletion SourceBridge208 IntrinsicTriples208 MarkedPrice20258
open scoped Classical BigOperators
set_option autoImplicit false

structure Plan where
  minimum : ℕ
  top : ℕ
  stop : ℕ
  head : ℕ
  deriving DecidableEq

/-- Backward maxima produce nonnegative charges for cumulative defect layers. -/
def rows (p : Plan) : List (ℕ × ℕ) :=
  ((List.range (p.stop-1)).reverse.foldl (fun (state : ℕ × List (ℕ × ℕ)) i =>
    let e := i+1
    let rate := (p.head-smallPrice p.minimum e+e-1)/e
    if rate≤state.1 then state else (rate,(e,rate-state.1)::state.2)) (0,[])).2

def fee (r : List (ℕ × ℕ)) (n m hi : ℕ) : ℕ :=
  (r.map (fun (k,w) => w*ConcentratedPopulation20258.budget n (m-1-k) k hi)).sum

def Plan.Valid (p : Plan) : Prop :=
  4≤p.minimum ∧ p.minimum≤216 ∧ p.minimum≤p.top ∧ p.top<549 ∧
  2≤p.stop ∧ p.stop+6≤p.minimum ∧ p.head≤UniformNumeric84364.value (p.top+1) ∧
  (∀ i : Fin (p.top+1-p.minimum),p.head≤FastSource208.fastPhysicalK UniformNumeric84364.phi
    (p.minimum+i.val) p.stop) ∧ (∀ r∈rows p,r.1+2≤p.minimum) ∧
  (∀ i : Fin (p.stop-1),p.head≤smallPrice p.minimum (i.val+1)+charge (rows p) (i.val+1))

instance (p : Plan) : Decidable p.Valid := by unfold Plan.Valid; infer_instance

private theorem member_price {N m e : ℕ} {S : Finset ℤ} (cap : N≤2^18) (inside : S⊆Ground N)
    (bad : ¬IsAP S) (sz : m≤S.card) (lo : 4≤m) (hi : m≤216) (coreRoom : e+6≤m)
    (value : Defect S=e) : smallPrice m e≤(Pool S).card := by
  by_cases first : e=1
  · rw [first]
    exact UniformCardPool20258.pool_floor (s:=m) cap inside bad lo (by omega) sz le_rfl
  let t := m-e
  let u := (27*t*t-150*t)/100
  have large : t≤MaxAPSize S := by
    have h := maxAPSize_le_card S
    unfold Defect at value
    dsimp [t]; omega
  have fit : MaxAPSize S≤2^18 := (maxAPSize_le_card S).trans
    ((by simpa only [ground_card] using Finset.card_le_card inside : S.card≤N).trans cap)
  have tl : 6≤t := by dsimp [t]; omega
  have tu : t≤216 := (Nat.sub_le ..).trans hi
  have nonneg : 150*t≤27*t*t := Nat.mul_le_mul_right _ (by omega : 150≤27*t)
  have product := Nat.div_mul_le_self (27*t*t-150*t) 100
  have unit : 100*u+150*t≤27*t*t := by unfold u; omega
  have square := Nat.mul_le_mul tu tu
  have tail : 100*u+525*257≤27*257*257 := by nlinarith only [unit,square]
  have lower := AnalyticCore180000.floor_split large fit (by omega) unit tail
  simp only [smallPrice,ite_eq_right first]
  change e*u≤_
  rw [←value]
  exact (Nat.mul_le_mul_left _ lower).trans (CoreUnionSource200000.actual_union_core_source (by omega))

private theorem bill {n m hi : ℕ} {G : Finset (Finset ℤ)} (r : List (ℕ × ℕ))
    (legal : Legal (Ground n) G) (large : ∀ S∈G,m≤S.card) (size : ∀ S∈G,S.card≤hi)
    (steps : ∀ t∈r,t.1+2≤m) : ∑ S∈G,charge r (Defect S)≤fee r n m hi := by
  classical
  induction r with
  | nil => simp [charge,fee]
  | cons t r ih =>
    obtain ⟨k,w⟩ := t
    have len := steps (k,w) (List.mem_cons_self ..)
    change k+2≤m at len
    let A := G.filter (fun S => Defect S≤k)
    have sub : A⊆G := Finset.filter_subset _ _
    have legalA : Legal (Ground n) A :=
      ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht => legal.2 S (sub hs) T (sub ht)⟩
    have bound := ConcentratedPopulation20258.actual (a:=m-1-k) legalA (by omega)
      (fun S hs => by have := large S (sub hs); omega) (fun S hs => size S (sub hs))
      (fun S hs => (Finset.mem_filter.mp hs).2)
    have head : ∑ S∈G,(if Defect S≤k then w*Defect S else 0)≤w*ConcentratedPopulation20258.budget n (m-1-k) k hi := by
      rw [←Finset.sum_filter,←Finset.mul_sum]; exact Nat.mul_le_mul_left w bound
    simpa only [charge,fee,List.map_cons,List.sum_cons,Finset.sum_add_distrib] using
      Nat.add_le_add head (ih (fun s hs => steps s (List.mem_cons_of_mem _ hs)))

/-- The head times the cardinality is covered by the members' own triple
pools and the sum of the concentrated stride charges. -/
theorem family {n : ℕ} {A : Finset (Finset ℤ)} {p : Plan} (valid : p.Valid)
    (legal : Legal (Ground n) A) (cap : n≤2^18) (large : ∀ S∈A,p.minimum≤S.card)
    (bad : ∀ S∈A,¬IsAP S) : p.head*A.card≤(∑ S∈A,(Pool S).card)+fee (rows p) n p.minimum p.top := by
  classical
  obtain ⟨four,limited,window,top,two,room,tall,physical,steps,prices⟩ := valid
  let G := A.filter (fun S => S.card≤p.top)
  have sub : G⊆A := Finset.filter_subset _ _
  have legalG : Legal (Ground n) G :=
    ⟨fun S hs => legal.1 S (sub hs),fun S hs T ht => legal.2 S (sub hs) T (sub ht)⟩
  have pay (S : Finset ℤ) (hs : S∈A) : p.head≤(Pool S).card+
      (if S.card≤p.top then charge (rows p) (Defect S) else 0) := by
    have size := large S hs
    by_cases small : S.card≤p.top
    · rw [ite_eq_left small]
      by_cases many : p.stop≤Defect S
      · let i : Fin (p.top+1-p.minimum) := ⟨S.card-p.minimum,by omega⟩
        have amount := physical i
        rw [show p.minimum+i.val=S.card by dsimp [i]; omega] at amount
        have phi (q : ℕ) (hq : q≤p.top) : UniformNumeric84364.phi q=q.totient :=
          (UniformBridge84364.phi_eq (by omega)).trans (FastDecode208.phi_correct q (by omega))
        rw [FastSource208.fastPhysicalK_eq phi small] at amount
        exact (amount.trans (actual_source_of_defect (by omega) many)).trans (Nat.le_add_right ..)
      have pos := MixedCore200000.crooked_defect_positive (by omega : 2≤S.card) (bad S hs)
      let i : Fin (p.stop-1) := ⟨Defect S-1,by omega⟩
      have grant := prices i
      rw [show i.val+1=Defect S by dsimp [i]; omega] at grant
      exact grant.trans (Nat.add_le_add_right (member_price cap (legal.1 S hs) (bad S hs) size
        four limited (by omega) rfl) _)
    · rw [ite_eq_right small,Nat.add_zero]
      exact UniformCardPool20258.pool_floor cap (legal.1 S hs) (bad S hs) (by omega)
        (by omega) (by omega) tall
  have h := Finset.sum_le_sum pay
  rw [Finset.sum_const,Finset.sum_add_distrib,←Finset.sum_filter] at h
  simpa only [smul_eq_mul,Nat.mul_comm p.head] using
    h.trans (Nat.add_le_add_left (bill (rows p) legalG (fun S hs => large S (sub hs))
      (fun S hs => (Finset.mem_filter.mp hs).2) steps) _)

#print axioms family
end JSP233.ConcentratedPrice20258
