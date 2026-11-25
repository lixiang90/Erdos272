module

public import Erdos272.Arithmetic.N109474.SourceQueryFloors109474
public import Erdos272.Arithmetic.N109474.SourceRunFloors109474
public import Erdos272.Counting.N109474.RunFacts109474
public import Erdos272.Resources.N109474.RunSource109474
public import Erdos272.Resources.N109474.CorrelatedSource109474
public import Erdos272.Resources.N130000.RowSources130000
public import Erdos272.Resources.N118533.SourceAtlas118533

@[expose] public section

namespace JSP233.SourceAtlas109474
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

def ofPlan (q : CorrelatedSource158375.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩
def ofRun (q : RunSource109474.Plan) : Contract := ⟨q.lower,q.defect,q.target⟩

def oldContract (i : ℕ) : Contract :=
  match i with
  | 0 => ofPlan (SourceQueryData130000.query 313)
  | 1 => ofPlan (SourceQueryData130000.query 264)
  | 2 => ofPlan (SourceQueryData130000.query 321)
  | 3 => ofPlan (SourceQueryData130000.query 116)
  | 4 => ofPlan (SourceQueryData130000.query 87)
  | 5 => ofPlan (SourceQueryData130000.query 221)
  | 6 => ofPlan (SourceQueryData130000.query 123)
  | 7 => ⟨(SourceAtlas118533.demand 61).lower,(SourceAtlas118533.demand 61).defect,(SourceAtlas118533.demand 61).target⟩
  | _ => ofPlan (SourceQueryData130000.query 0)

def hybridPlan (i : ℕ) : CorrelatedSource109474.Plan := SourceQueryData109474.query (125+i)

def highIndex (i : ℕ) : ℕ :=
  match i with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 6
  | 7 => 7
  | 8 => 16
  | 9 => 18
  | 10 => 26
  | 11 => 27
  | 12 => 28
  | 13 => 29
  | 14 => 30
  | 15 => 42
  | 16 => 43
  | 17 => 44
  | 18 => 45
  | 19 => 57
  | 20 => 58
  | _ => 0

def HybridValid (i : ℕ) : Prop :=
  highIndex i < 60 ∧
  (RunPlans109474.plan (highIndex i)).lower ≤ (hybridPlan i).lower ∧
  (RunPlans109474.plan (highIndex i)).defect ≤ (hybridPlan i).cutoff ∧
  (hybridPlan i).target ≤ (RunPlans109474.plan (highIndex i)).target

instance (i : ℕ) : Decidable (HybridValid i) := by unfold HybridValid; infer_instance

theorem hybrid_checked : (List.range 21).all (fun i => decide (HybridValid i)) = true := by decide +kernel

theorem hybrid_valid {i : ℕ} (hi : i < 21) : HybridValid i :=
  of_decide_eq_true (List.all_eq_true.mp hybrid_checked i (List.mem_range.mpr hi))

theorem hybrid_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 21)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (hybridPlan i).lower ≤ S.card) (hdefect : (hybridPlan i).defect ≤ Defect S) :
    (hybridPlan i).target ≤ (Pool S).card := by
  have hl := hybrid_valid hi
  apply CorrelatedSource109474.actual_plan_source_of_high (hybridPlan i)
    (SourceQueryData109474.conditions (i := 125+i) (by omega)) hN hground hS hsize hdefect
  intro hhigh
  have hb := RunSource109474.actual_run_plan_source (RunPlans109474.plan (highIndex i))
    (RunFacts109474.conditions hl.1) (SourceRunFloors109474.floors hl.1) hN hground hS
    (hl.2.1.trans hsize) (hl.2.2.1.trans hhigh)
  exact hl.2.2.2.trans hb

def demand (i : ℕ) : Contract := (([⟨100,1,2761⟩, ⟨100,4,10239⟩, ⟨190,1,10239⟩, ⟨100,7,16800⟩, ⟨200,2,16800⟩, ⟨242,1,16800⟩, ⟨100,10,22373⟩, ⟨200,2,22373⟩, ⟨286,1,22373⟩, ⟨100,14,28519⟩, ⟨200,3,28519⟩, ⟨321,1,28519⟩, ⟨100,18,33220⟩, ⟨200,3,33220⟩, ⟨346,1,33220⟩, ⟨100,22,36560⟩, ⟨200,4,36560⟩, ⟨362,1,36560⟩, ⟨100,26,38970⟩, ⟨200,4,38970⟩, ⟨373,1,38970⟩, ⟨100,31,40533⟩, ⟨200,4,40533⟩, ⟨381,1,40533⟩, ⟨100,41,45906⟩, ⟨175,6,45906⟩, ⟨404,1,45906⟩, ⟨100,43,49886⟩, ⟨175,7,49886⟩, ⟨421,1,49886⟩, ⟨100,45,54134⟩, ⟨175,7,54134⟩, ⟨438,1,54134⟩, ⟨100,47,57892⟩, ⟨175,8,57892⟩, ⟨453,1,57892⟩, ⟨100,49,61460⟩, ⟨175,8,61460⟩, ⟨466,1,61460⟩, ⟨100,51,64982⟩, ⟨175,9,64982⟩, ⟨479,1,64982⟩, ⟨100,53,68396⟩, ⟨175,9,68396⟩, ⟨491,1,68396⟩, ⟨100,54,69838⟩, ⟨175,9,69838⟩, ⟨496,1,69838⟩, ⟨100,55,72108⟩, ⟨150,14,72108⟩, ⟨300,3,72108⟩, ⟨504,1,72108⟩, ⟨100,57,75294⟩, ⟨175,10,75294⟩, ⟨500,2,75294⟩, ⟨515,1,75294⟩, ⟨100,59,78476⟩, ⟨150,16,78476⟩, ⟨300,4,78476⟩, ⟨526,1,78476⟩, ⟨100,61,82230⟩, ⟨150,17,82230⟩, ⟨300,4,82230⟩, ⟨538,1,82230⟩, ⟨100,63,85822⟩, ⟨150,18,85822⟩, ⟨300,4,85822⟩, ⟨549,1,85822⟩, ⟨100,64,87678⟩, ⟨150,19,87678⟩, ⟨300,4,87678⟩, ⟨555,1,87678⟩, ⟨100,65,89390⟩, ⟨150,19,89390⟩, ⟨300,4,89390⟩, ⟨560,1,89390⟩, ⟨100,66,91072⟩, ⟨150,20,91072⟩, ⟨300,4,91072⟩, ⟨565,1,91072⟩, ⟨101,1,2815⟩, ⟨101,4,10519⟩, ⟨193,1,10519⟩, ⟨101,10,22860⟩, ⟨202,2,22860⟩, ⟨289,1,22860⟩, ⟨101,16,31697⟩, ⟨202,3,31697⟩, ⟨338,1,31697⟩, ⟨101,22,37698⟩, ⟨202,4,37698⟩, ⟨368,1,37698⟩, ⟨101,30,41472⟩, ⟨202,4,41472⟩, ⟨385,1,41472⟩, ⟨101,42,48338⟩, ⟨176,6,48338⟩, ⟨415,1,48338⟩, ⟨101,46,56770⟩, ⟨176,8,56770⟩, ⟨449,1,56770⟩, ⟨101,49,62162⟩, ⟨176,8,62162⟩, ⟨469,1,62162⟩, ⟨101,52,68008⟩, ⟨176,9,68008⟩, ⟨490,1,68008⟩, ⟨101,54,70292⟩, ⟨176,9,70292⟩, ⟨498,1,70292⟩, ⟨101,56,74808⟩, ⟨176,10,74808⟩, ⟨505,2,74808⟩, ⟨513,1,74808⟩, ⟨101,58,78320⟩, ⟨151,16,78320⟩, ⟨303,4,78320⟩, ⟨525,1,78320⟩, ⟨101,60,81502⟩, ⟨151,17,81502⟩, ⟨303,4,81502⟩, ⟨535,1,81502⟩, ⟨101,62,85106⟩, ⟨151,18,85106⟩, ⟨303,4,85106⟩, ⟨547,1,85106⟩, ⟨101,64,88700⟩, ⟨151,19,88700⟩, ⟨303,4,88700⟩, ⟨558,1,88700⟩, ⟨101,66,92726⟩, ⟨151,20,92726⟩, ⟨303,4,92726⟩, ⟨570,1,92726⟩, ⟨102,1,2869⟩, ⟨102,4,10729⟩, ⟨195,1,10729⟩, ⟨102,10,23353⟩, ⟨204,2,23353⟩, ⟨292,1,23353⟩, ⟨102,16,32593⟩, ⟨204,3,32593⟩, ⟨342,1,32593⟩, ⟨102,23,39466⟩, ⟨204,4,39466⟩, ⟨376,1,39466⟩, ⟨102,30,42620⟩, ⟨204,4,42620⟩, ⟨390,1,42620⟩, ⟨102,41,47576⟩, ⟨178,6,47576⟩, ⟨411,1,47576⟩, ⟨102,45,55024⟩, ⟨178,7,55024⟩, ⟨442,1,55024⟩, ⟨102,49,63368⟩, ⟨178,8,63368⟩, ⟨473,1,63368⟩, ⟨102,53,71058⟩, ⟨178,9,71058⟩, ⟨501,1,71058⟩, ⟨102,55,73870⟩, ⟨178,10,73870⟩, ⟨510,1,73870⟩, ⟨102,57,77234⟩, ⟨178,10,77234⟩, ⟨510,2,77234⟩, ⟨521,1,77234⟩, ⟨102,59,81120⟩, ⟨153,16,81120⟩, ⟨306,4,81120⟩, ⟨534,1,81120⟩, ⟨102,61,84302⟩, ⟨153,17,84302⟩, ⟨306,4,84302⟩, ⟨544,1,84302⟩, ⟨102,63,87906⟩, ⟨153,18,87906⟩, ⟨306,4,87906⟩, ⟨555,1,87906⟩, ⟨102,65,92448⟩, ⟨153,19,92448⟩, ⟨306,4,92448⟩, ⟨569,1,92448⟩, ⟨102,67,95702⟩, ⟨153,20,95702⟩, ⟨306,4,95702⟩, ⟨579,1,95702⟩, ⟨130,1,4732⟩, ⟨130,16,57962⟩, ⟨260,4,57962⟩, ⟨453,1,57962⟩, ⟨130,33,86189⟩, ⟨260,5,86189⟩, ⟨550,1,86189⟩, ⟨130,55,102588⟩, ⟨227,8,102588⟩, ⟨599,1,102588⟩] : List Contract)[i]?).getD ⟨0,0,0⟩

def provider (i : ℕ) : Provider := (([⟨3,0⟩, ⟨1,0⟩, ⟨1,1⟩, ⟨3,1⟩, ⟨1,2⟩, ⟨3,2⟩, ⟨3,3⟩, ⟨1,3⟩, ⟨1,4⟩, ⟨3,4⟩, ⟨1,5⟩, ⟨1,6⟩, ⟨3,5⟩, ⟨1,7⟩, ⟨1,8⟩, ⟨1,9⟩, ⟨0,0⟩, ⟨1,10⟩, ⟨3,6⟩, ⟨0,0⟩, ⟨1,11⟩, ⟨3,7⟩, ⟨1,12⟩, ⟨0,1⟩, ⟨2,8⟩, ⟨1,13⟩, ⟨1,14⟩, ⟨2,9⟩, ⟨1,15⟩, ⟨1,16⟩, ⟨2,10⟩, ⟨1,17⟩, ⟨1,18⟩, ⟨2,11⟩, ⟨1,19⟩, ⟨1,20⟩, ⟨2,12⟩, ⟨1,21⟩, ⟨1,22⟩, ⟨2,13⟩, ⟨1,23⟩, ⟨1,24⟩, ⟨2,14⟩, ⟨1,25⟩, ⟨1,26⟩, ⟨2,15⟩, ⟨3,8⟩, ⟨1,27⟩, ⟨2,17⟩, ⟨3,9⟩, ⟨1,28⟩, ⟨1,29⟩, ⟨2,19⟩, ⟨1,30⟩, ⟨0,2⟩, ⟨1,31⟩, ⟨2,20⟩, ⟨1,32⟩, ⟨1,33⟩, ⟨1,34⟩, ⟨2,21⟩, ⟨1,35⟩, ⟨1,36⟩, ⟨1,37⟩, ⟨2,22⟩, ⟨1,38⟩, ⟨1,39⟩, ⟨1,40⟩, ⟨2,23⟩, ⟨1,41⟩, ⟨1,42⟩, ⟨0,3⟩, ⟨2,24⟩, ⟨1,43⟩, ⟨1,44⟩, ⟨1,45⟩, ⟨2,25⟩, ⟨1,46⟩, ⟨1,47⟩, ⟨1,48⟩, ⟨1,49⟩, ⟨3,10⟩, ⟨1,50⟩, ⟨3,11⟩, ⟨1,51⟩, ⟨1,52⟩, ⟨3,12⟩, ⟨1,53⟩, ⟨1,54⟩, ⟨3,13⟩, ⟨0,0⟩, ⟨1,55⟩, ⟨3,14⟩, ⟨1,56⟩, ⟨1,57⟩, ⟨2,31⟩, ⟨1,58⟩, ⟨1,59⟩, ⟨2,32⟩, ⟨1,60⟩, ⟨1,61⟩, ⟨2,33⟩, ⟨1,62⟩, ⟨1,63⟩, ⟨2,34⟩, ⟨1,64⟩, ⟨1,65⟩, ⟨2,35⟩, ⟨1,66⟩, ⟨0,4⟩, ⟨2,36⟩, ⟨1,67⟩, ⟨0,2⟩, ⟨1,68⟩, ⟨2,37⟩, ⟨1,69⟩, ⟨1,70⟩, ⟨1,71⟩, ⟨2,38⟩, ⟨1,72⟩, ⟨1,73⟩, ⟨1,74⟩, ⟨2,39⟩, ⟨1,75⟩, ⟨1,76⟩, ⟨0,5⟩, ⟨2,40⟩, ⟨1,77⟩, ⟨1,78⟩, ⟨1,79⟩, ⟨2,41⟩, ⟨1,80⟩, ⟨1,81⟩, ⟨0,6⟩, ⟨1,82⟩, ⟨3,15⟩, ⟨1,83⟩, ⟨1,84⟩, ⟨1,85⟩, ⟨1,86⟩, ⟨3,16⟩, ⟨1,87⟩, ⟨1,88⟩, ⟨3,17⟩, ⟨0,0⟩, ⟨1,89⟩, ⟨3,18⟩, ⟨1,90⟩, ⟨1,91⟩, ⟨2,46⟩, ⟨1,92⟩, ⟨1,93⟩, ⟨2,47⟩, ⟨1,94⟩, ⟨1,95⟩, ⟨2,48⟩, ⟨1,96⟩, ⟨1,97⟩, ⟨2,49⟩, ⟨1,98⟩, ⟨1,99⟩, ⟨2,50⟩, ⟨1,100⟩, ⟨1,101⟩, ⟨2,51⟩, ⟨1,102⟩, ⟨0,2⟩, ⟨1,103⟩, ⟨2,52⟩, ⟨1,104⟩, ⟨1,105⟩, ⟨1,106⟩, ⟨2,53⟩, ⟨1,107⟩, ⟨1,108⟩, ⟨1,109⟩, ⟨2,54⟩, ⟨1,110⟩, ⟨1,111⟩, ⟨1,112⟩, ⟨2,55⟩, ⟨1,113⟩, ⟨1,114⟩, ⟨1,115⟩, ⟨2,56⟩, ⟨1,116⟩, ⟨1,117⟩, ⟨1,118⟩, ⟨0,7⟩, ⟨3,19⟩, ⟨1,119⟩, ⟨1,120⟩, ⟨3,20⟩, ⟨1,121⟩, ⟨1,122⟩, ⟨2,59⟩, ⟨1,123⟩, ⟨1,124⟩] : List Provider)[i]?).getD ⟨0,0⟩

def reference (i : ℕ) : Contract :=
  if (provider i).kind=0 then oldContract (provider i).index else
  if (provider i).kind=1 then ofPlan (SourceQueryData109474.query (provider i).index) else
  if (provider i).kind=2 then ofRun (RunPlans109474.plan (provider i).index) else
    ofPlan (hybridPlan (provider i).index)

def capacity (kind : ℕ) : ℕ := if kind=0 then 8 else if kind=1 then 125 else if kind=2 then 60 else 21

def Valid (i : ℕ) : Prop :=
  (provider i).kind < 4 ∧ (provider i).index < capacity (provider i).kind ∧
  (reference i).lower ≤ (demand i).lower ∧
  (reference i).defect ≤ (demand i).defect ∧ (demand i).target ≤ (reference i).target

instance (i : ℕ) : Decidable (Valid i) := by unfold Valid; infer_instance

theorem checked : (List.range 198).all (fun i => decide (Valid i)) = true := by decide +kernel

theorem valid {i : ℕ} (hi : i < 198) : Valid i :=
  of_decide_eq_true (List.all_eq_true.mp checked i (List.mem_range.mpr hi))

theorem old_actual {N i : ℕ} {S : Finset ℤ} (hi : i < 8)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (oldContract i).lower ≤ S.card) (hdefect : (oldContract i).defect ≤ Defect S) :
    (oldContract i).target ≤ (Pool S).card := by
  interval_cases i
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 313)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 264)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 321)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 116)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 87)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 221)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact CorrelatedSource130000.actual_plan_source (SourceQueryData130000.query 123)
      (SourceQueryData130000.conditions (by decide)) (RowSources130000.floors (by decide))
      hN hground hS hsize hdefect
  · exact SourceAtlas118533.actual_source (i := 61) (by decide)
      hN hground hS hsize hdefect

theorem actual_source {N i : ℕ} {S : Finset ℤ} (hi : i < 198)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (hsize : (demand i).lower ≤ S.card) (hdefect : (demand i).defect ≤ Defect S) :
    (demand i).target ≤ (Pool S).card := by
  have hv := valid hi
  have hl := hv.2.2.1.trans hsize
  have he := hv.2.2.2.1.trans hdefect
  by_cases h0 : (provider i).kind=0
  · have hb := old_actual (i := (provider i).index)
      (by simpa [capacity, h0] using hv.2.1) hN hground hS
      (by simpa [reference, h0] using hl) (by simpa [reference, h0] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0] using hb)
  by_cases h1 : (provider i).kind=1
  · have hiq : (provider i).index < 125 := by simpa [capacity, h1] using hv.2.1
    have hb := CorrelatedSource118533.actual_plan_source (SourceQueryData109474.query (provider i).index)
      (SourceQueryData109474.conditions (by omega : (provider i).index < 146))
      (SourceQueryFloors109474.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, ofPlan] using hl)
      (by simpa [reference, h0, h1, ofPlan] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, ofPlan] using hb)
  by_cases h2 : (provider i).kind=2
  · have hiq : (provider i).index < 60 := by simpa [capacity, h2] using hv.2.1
    have hb := RunSource109474.actual_run_plan_source (RunPlans109474.plan (provider i).index)
      (RunFacts109474.conditions hiq) (SourceRunFloors109474.floors hiq) hN hground hS
      (by simpa [reference, h0, h1, h2, ofRun] using hl)
      (by simpa [reference, h0, h1, h2, ofRun] using he)
    exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, h2, ofRun] using hb)
  have hiq : (provider i).index < 21 := by simpa [capacity, h0, h1, h2] using hv.2.1
  have hb := hybrid_actual hiq hN hground hS
    (by simpa [reference, h0, h1, h2, ofPlan] using hl)
    (by simpa [reference, h0, h1, h2, ofPlan] using he)
  exact hv.2.2.2.2.trans (by simpa [reference, h0, h1, h2, ofPlan] using hb)

#print axioms hybrid_checked
#print axioms hybrid_valid
#print axioms hybrid_actual
#print axioms checked
#print axioms valid
#print axioms old_actual
#print axioms actual_source
end
end JSP233.SourceAtlas109474
