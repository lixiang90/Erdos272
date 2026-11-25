module

public import Erdos272.Capacity.N20258.PopulationPrice20258
public import Erdos272.Capacity.N20258.ExteriorFamilyPool20258

@[expose] public section
namespace JSP233.NaturalPopulation20258
open StarCompletion PrivatePairExistence SourceBridge208 IntrinsicTriples208 ExteriorStrides20258
open PopulationTariff20258 PopulationPrice20258
open scoped Classical BigOperators
set_option autoImplicit false

def natural (s : ℕ) := (s-1).choose 2-(s-1)/2
def exceptional (S : Finset ℤ) : Prop := Defect S=1 ∧ (Pool S).card<natural S.card

abbrev Extras := List (ℕ × ℕ)
def extra (r : Extras) (s : ℕ) := (r.map (fun (t,w) => if t=s then w else 0)).sum
def weights (r : Extras) := (r.map Prod.snd).sum

private theorem per_size {N s : ℕ} {F A : Finset (Finset ℤ)} (legal : Legal (Ground N) F)
    (sub : A⊆CrookedMembers F) (three : 3≤s) :
    (A.filter (fun S => s=S.card ∧ exceptional S)).card≤4*N := by
  classical
  let E := A.filter (fun S => s=S.card ∧ exceptional S)
  apply four_per_site (G:=E) (m:=s-2) legal ((Finset.filter_subset _ _).trans (sub.trans (Finset.filter_subset _ _)))
  intro S hs
  obtain ⟨mem,eq,one,low⟩ := Finset.mem_filter.mp hs
  obtain full|near := ExteriorDichotomy20258.actual (by omega) (Finset.mem_filter.mp (sub mem)).2 one
  · exact False.elim ((not_le_of_gt low) full)
  · simpa only [eq] using near

private theorem extra_bill {N : ℕ} {F A : Finset (Finset ℤ)} (legal : Legal (Ground N) F)
    (sub : A⊆CrookedMembers F) (r : Extras) (sizes : ∀ z∈r,3≤z.1) :
    (∑ S∈A, if exceptional S then extra r S.card else 0)≤4*N*weights r := by
  classical
  induction r with
  | nil => simp [extra,weights]
  | cons z r ih =>
    obtain ⟨s,w⟩ := z
    have count := per_size legal sub (sizes (s,w) (List.mem_cons_self ..))
    have first : (∑ S∈A, if s=S.card ∧ exceptional S then w else 0)≤4*N*w := by
      rw [←Finset.sum_filter,Finset.sum_const,smul_eq_mul]
      exact Nat.mul_le_mul_right w count
    have expand (S : Finset ℤ) : (if exceptional S then extra ((s,w)::r) S.card else 0)=
        (if s=S.card ∧ exceptional S then w else 0)+(if exceptional S then extra r S.card else 0) := by
      by_cases h : exceptional S <;> by_cases e : s=S.card <;> simp [h,e,extra]
    simpa only [expand,Finset.sum_add_distrib,weights,List.map_cons,List.sum_cons,Nat.mul_add] using
      Nat.add_le_add first (ih (fun z hz => sizes z (List.mem_cons_of_mem _ hz)))

def Good (p : Plan) (r : Extras) : Prop :=
  4≤p.minimum ∧ p.minimum≤p.top ∧ p.top≤256 ∧ 1≤p.stop ∧ 0<p.scale ∧
  (∀ z∈r,3≤z.1) ∧ p.head≤UniformNumeric84364.value (p.top+1) ∧
  (∀ i : Fin (p.top+1-p.minimum),p.head≤IndividualPrice20258.physical (p.minimum+i.val) p.stop) ∧
  (∀ i : Fin (p.top+1-p.minimum),∀ j : Fin (p.stop-1),
    let s := p.minimum+i.val
    let e := j.val+1
    let u := IndividualPrice20258.value s e
    let w := grant p.table s e
    if e=1 then (p.scale*p.head≤p.scale*(max u (natural s))+w ∧ p.scale*p.head≤p.scale*u+w+extra r s)
    else p.scale*p.head≤p.scale*u+w)

instance (p : Plan) (r : Extras) : Decidable (Good p r) := by unfold Good; infer_instance

theorem family {N n m L v : ℕ} {A F : Finset (Finset ℤ)} {p : Plan} {r : Extras} (valid : Good p r)
    (hi : N≤n) (cap : N≤2^18) (two : 2≤N) (room : m+1≤N) (legal : Legal (Ground N) F)
    (sub : A⊆CrookedMembers F) (large : ∀ S∈A,p.minimum≤S.card)
    (omits : ∀ x∈Ground N,∃ S∈CrookedMembers F,x∉S ∧ S.card≤m)
    (many : L*(N-2)<(CrookedMembers F).card) (tests : ∀ t∈p.table,t.1.Valid m L)
    (fee : cost p.table n+4*n*weights r≤p.scale*v) : p.head*A.card≤(∑ S∈A,(Pool S).card)+v := by
  classical
  obtain ⟨four,ok,top,stop,scale,sizes,tall,tail,cell⟩ := valid
  have inside : A⊆F := sub.trans (Finset.filter_subset _ _)
  let reserve (S : Finset ℤ) := if exceptional S then extra r S.card else 0
  have pay (S : Finset ℤ) (hs : S∈A) : p.scale*p.head≤p.scale*(Pool S).card+grant p.table S.card (Defect S)+reserve S := by
    have sz := large S hs
    have bad := (Finset.mem_filter.mp (sub hs)).2
    have ground := legal.1 S (inside hs)
    by_cases low : S.card≤p.top
    · let i : Fin (p.top+1-p.minimum) := ⟨S.card-p.minimum,by omega⟩
      have si : p.minimum+i.val=S.card := by dsimp only [i]; omega
      by_cases high : p.stop≤Defect S
      · have unit := tail i
        rw [si] at unit
        have paid := Nat.mul_le_mul_left p.scale (unit.trans (IndividualPrice20258.physical_le (by omega) (by omega) high))
        omega
      have pos := MixedCore200000.crooked_defect_positive (by omega : 2≤S.card) bad
      let j : Fin (p.stop-1) := ⟨Defect S-1,by omega⟩
      have unit := IndividualPrice20258.actual cap ground bad (by omega) (by omega)
      have mark := cell i j
      dsimp only at mark
      rw [si,show j.val+1=Defect S by dsimp only [j]; omega] at mark
      by_cases one : Defect S=1
      · rw [ite_eq_left one] at mark
        by_cases cheap : exceptional S
        · have paid := Nat.mul_le_mul_left p.scale unit
          simp only [reserve,ite_eq_left cheap]
          omega
        · have highPrice : natural S.card≤(Pool S).card := by
            by_contra! short
            exact cheap ⟨one,short⟩
          have paid := Nat.mul_le_mul_left p.scale (max_le unit highPrice)
          omega
      · rw [ite_eq_right one] at mark
        have paid := Nat.mul_le_mul_left p.scale unit
        omega
    · have unit := UniformCardPool20258.pool_floor cap ground bad (by omega : 4≤p.top+1) (by omega) (by omega) tall
      have paid := Nat.mul_le_mul_left p.scale unit
      omega
  have spent := bill p.table hi two room legal inside omits many tests
  have exceptions := (extra_bill legal sub r sizes).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hi))
  have paid := Finset.sum_le_sum pay
  rw [Finset.sum_const,smul_eq_mul,Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum] at paid
  change (∑ S∈A,reserve S)≤_ at exceptions
  refine Nat.le_of_mul_le_mul_left ?_ scale
  calc
    _ = A.card*(p.scale*p.head) := by ring
    _ ≤ _ := paid
    _ ≤ p.scale*(∑ S∈A,(Pool S).card)+(cost p.table n+4*n*weights r) := by omega
    _ ≤ _ := (Nat.add_le_add_left fee _).trans_eq (Nat.mul_add ..).symm

#print axioms family
end JSP233.NaturalPopulation20258
