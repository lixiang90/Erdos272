module

public import Erdos272.Arithmetic.N118533.SourceQueryFloors118533
public import Erdos272.Arithmetic.N118533.SourceRunFloors118533
public import Erdos272.Counting.N118533.RunFacts118533
public import Erdos272.Resources.N118533.RunSource118533
public import Erdos272.Resources.N130000.RowSources130000
public import Erdos272.Resources.N142758.RowSources142758

@[expose] public section

namespace JSP233.SourceAtlas118533
open StarCompletion SourceBridge208 IntrinsicTriples208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Contract where
  lower : ℕ
  defect : ℕ
  target : ℕ

structure Provider where
  kind : ℕ
  index : ℕ

def demand (i : ℕ) : Contract := (([⟨104,1,2979⟩, ⟨104,4,11156⟩, ⟨198,1,11156⟩, ⟨104,10,24354⟩, ⟨208,2,24354⟩, ⟨298,1,24354⟩, ⟨104,18,36469⟩, ⟨208,4,36469⟩, ⟨362,1,36469⟩, ⟨104,28,44219⟩, ⟨208,4,44219⟩, ⟨397,1,44219⟩, ⟨104,43,52652⟩, ⟨182,6,52652⟩, ⟨433,1,52652⟩, ⟨104,47,60444⟩, ⟨182,7,60444⟩, ⟨462,1,60444⟩, ⟨104,51,68380⟩, ⟨182,8,68380⟩, ⟨491,1,68380⟩, ⟨104,55,75936⟩, ⟨182,9,75936⟩, ⟨517,1,75936⟩, ⟨104,59,83468⟩, ⟨182,10,83468⟩, ⟨520,2,83468⟩, ⟨542,1,83468⟩, ⟨104,63,90874⟩, ⟨156,17,90874⟩, ⟨312,4,90874⟩, ⟨565,1,90874⟩, ⟨104,66,97010⟩, ⟨156,19,97010⟩, ⟨312,4,97010⟩, ⟨583,1,97010⟩, ⟨104,69,102866⟩, ⟨156,20,102866⟩, ⟨312,4,102866⟩, ⟨600,1,102866⟩, ⟨107,1,3169⟩, ⟨107,14,33391⟩, ⟨214,3,33391⟩, ⟨347,1,33391⟩, ⟨107,28,47710⟩, ⟨214,4,47710⟩, ⟨412,1,47710⟩, ⟨107,50,69152⟩, ⟨187,8,69152⟩, ⟨494,1,69152⟩, ⟨107,56,81328⟩, ⟨187,10,81328⟩, ⟨535,1,81328⟩, ⟨107,64,97138⟩, ⟨160,18,97138⟩, ⟨321,4,97138⟩, ⟨583,1,97138⟩, ⟨107,69,107942⟩, ⟨160,20,107942⟩, ⟨321,4,107942⟩, ⟨614,1,107942⟩, ⟨130,1,4732⟩, ⟨130,14,52457⟩, ⟨260,3,52457⟩, ⟨432,1,52457⟩, ⟨130,32,84586⟩, ⟨260,5,84586⟩, ⟨545,1,84586⟩, ⟨130,61,120996⟩, ⟨227,9,120996⟩, ⟨650,1,120996⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def provider (i : ℕ) : Provider := (([⟨1,0⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨1,5⟩, ⟨1,6⟩, ⟨0,0⟩, ⟨1,7⟩, ⟨1,8⟩, ⟨1,9⟩, ⟨1,10⟩, ⟨2,0⟩, ⟨1,11⟩, ⟨1,12⟩, ⟨2,1⟩, ⟨1,13⟩, ⟨1,14⟩, ⟨2,2⟩, ⟨1,15⟩, ⟨1,16⟩, ⟨2,3⟩, ⟨1,17⟩, ⟨1,18⟩, ⟨2,4⟩, ⟨1,19⟩, ⟨1,20⟩, ⟨1,21⟩, ⟨2,5⟩, ⟨1,22⟩, ⟨1,23⟩, ⟨1,24⟩, ⟨2,6⟩, ⟨1,25⟩, ⟨1,26⟩, ⟨1,27⟩, ⟨2,7⟩, ⟨1,28⟩, ⟨1,29⟩, ⟨1,30⟩, ⟨1,31⟩, ⟨1,32⟩, ⟨1,33⟩, ⟨1,34⟩, ⟨1,35⟩, ⟨1,36⟩, ⟨1,37⟩, ⟨2,8⟩, ⟨1,38⟩, ⟨1,39⟩, ⟨2,9⟩, ⟨0,1⟩, ⟨1,40⟩, ⟨2,10⟩, ⟨1,41⟩, ⟨1,42⟩, ⟨1,43⟩, ⟨2,11⟩, ⟨1,44⟩, ⟨1,45⟩, ⟨1,46⟩, ⟨0,2⟩, ⟨1,47⟩, ⟨1,48⟩, ⟨1,49⟩, ⟨1,50⟩, ⟨1,51⟩, ⟨1,52⟩, ⟨2,12⟩, ⟨1,53⟩, ⟨1,54⟩] : List Provider)[i]?).getD ⟨0,0⟩

def oldPlan (i : ℕ) : CorrelatedSource158375.Plan :=
  match i with
  | 0 => SourceQueryData130000.query 313
  | 1 => SourceQueryData142758.query 249
  | 2 => SourceQueryData130000.query 311
  | _ => SourceQueryData130000.query 313

def ofPlan (q : CorrelatedSource158375.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩
def ofRun (q : RunSource118533.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩

def reference (i : ℕ) : Contract :=
  if (provider i).kind=0 then ofPlan (oldPlan (provider i).index) else
  if (provider i).kind=1 then ofPlan (SourceQueryData118533.query (provider i).index) else
    ofRun (RunPlans118533.plan (provider i).index)

def capacity (kind : ℕ) : ℕ := if kind=0 then 3 else if kind=1 then 55 else 13

def Valid (i : ℕ) : Prop :=
  (provider i).kind < 3 ∧ (provider i).index < capacity (provider i).kind ∧
  (reference i).lower ≤ (demand i).lower ∧
  (reference i).defect ≤ (demand i).defect ∧ (demand i).target ≤ (reference i).target

instance (i : ℕ) : Decidable (Valid i) := by unfold Valid; infer_instance

theorem checked : (List.range 71).all (fun i => decide (Valid i)) = true := by decide +kernel

theorem valid {i : ℕ} (hi : i < 71) : Valid i :=
  of_decide_eq_true (List.all_eq_true.mp checked i (List.mem_range.mpr hi))

theorem old_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 3)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (oldPlan i).lower ≤ S.card) (hdefect : (oldPlan i).defect ≤ Defect S) :
    (oldPlan i).target ≤ (Pool S).card := by
  interval_cases i
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 313)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource158375.actual_plan_source (SourceQueryData142758.query 249)
      (SourceQueryData142758.conditions (by decide)) (RowSources142758.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 311)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 71)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hv := valid hi
  have hl := hv.2.2.1.trans hsize
  have he := hv.2.2.2.1.trans hdefect
  by_cases h0 : (provider i).kind=0
  · have hb := old_actual (i := (provider i).index)
      (by simpa [capacity, h0] using hv.2.1) hN hground hS
      (by simpa [reference, h0, ofPlan] using hl)
      (by simpa [reference, h0, ofPlan] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, ofPlan] using hb)
  by_cases h1 : (provider i).kind=1
  · have hiq : (provider i).index < 55 := by simpa [capacity, h1] using hv.2.1
    have hb := CorrelatedSource118533.actual_plan_source (SourceQueryData118533.query (provider i).index)
      (SourceQueryData118533.conditions hiq) (SourceQueryFloors118533.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, ofPlan] using hl)
      (by simpa [reference, h0, h1, ofPlan] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, ofPlan] using hb)
  have hiq : (provider i).index < 13 := by simpa [capacity, h0, h1] using hv.2.1
  have hb := RunSource118533.actual_run_plan_source (RunPlans118533.plan (provider i).index)
    (RunFacts118533.conditions hiq) (SourceRunFloors118533.floors hiq) hN hground hS
    (by simpa [reference, h0, h1, ofRun] using hl)
    (by simpa [reference, h0, h1, ofRun] using he)
  exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, ofRun] using hb)

#print axioms checked
#print axioms valid
#print axioms old_actual
#print axioms actual_source
end
end JSP233.SourceAtlas118533
