module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source099
public import Erdos272.Arithmetic.N20258.Sources.Source103
public import Erdos272.Arithmetic.N20258.Sources.Source105
public import Erdos272.Arithmetic.N20258.Sources.Source106
public import Erdos272.Arithmetic.N20258.Sources.Source107
public import Erdos272.Arithmetic.N20258.Sources.Source109

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests61_107_0 : ∀ z∈source107.plan.table,z.1.Valid 61 0 := by decide +kernel
private theorem fee61_107_20973 :
    PopulationFees20258.bill (n:=20973) (PopulationFees20258.tabulate (20973-1) 256) source107.plan.table+
      4*20973*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*188970424212 := by decide +kernel
private theorem range61From20258To2944 : Segment 61 20258 20973 0 2944 :=
  paid (pc:=69) (v:=188970424212) (by decide) source107_valid tests61_107_0 fee61_107_20973 (by decide +kernel)

private theorem tests61_107_2944 : ∀ z∈source107.plan.table,z.1.Valid 61 2944 := by decide +kernel
private theorem range61From20258To2988 : Segment 61 20258 20973 2944 2988 :=
  paid (pc:=69) (v:=188970424212) (by decide) source107_valid tests61_107_2944 fee61_107_20973 (by decide +kernel)

private theorem tests61_099_2988 : ∀ z∈source099.plan.table,z.1.Valid 61 2988 := by decide +kernel
private theorem fee61_099_20973 :
    PopulationFees20258.bill (n:=20973) (PopulationFees20258.tabulate (20973-1) 256) source099.plan.table+
      4*20973*NaturalPopulation20258.weights source099.extras≤source099.plan.scale*249262258216 := by decide +kernel
private theorem range61From20258To3003 : Segment 61 20258 20973 2988 3003 :=
  paid (pc:=69) (v:=249262258216) (by decide) source099_valid tests61_099_2988 fee61_099_20973 (by decide +kernel)

private theorem tests61_103_3003 : ∀ z∈source103.plan.table,z.1.Valid 61 3003 := by decide +kernel
private theorem fee61_103_20973 :
    PopulationFees20258.bill (n:=20973) (PopulationFees20258.tabulate (20973-1) 256) source103.plan.table+
      4*20973*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*238246583519 := by decide +kernel
private theorem range61From20258To3167 : Segment 61 20258 20973 3003 3167 :=
  paid (pc:=67) (v:=238246583519) (by decide) source103_valid tests61_103_3003 fee61_103_20973 (by decide +kernel)

private theorem tests61_105_3167 : ∀ z∈source105.plan.table,z.1.Valid 61 3167 := by decide +kernel
private theorem fee61_105_20973 :
    PopulationFees20258.bill (n:=20973) (PopulationFees20258.tabulate (20973-1) 256) source105.plan.table+
      4*20973*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*261198289297 := by decide +kernel
private theorem range61From20258To3661 : Segment 61 20258 20973 3167 3661 :=
  paid (pc:=61) (v:=261198289297) (by decide) source105_valid tests61_105_3167 fee61_105_20973 (by decide +kernel)

private theorem range61From20258 : Win 61 20258 20973 :=
  complete (by decide) (by decide) (join_population (join_population range61From20258To2944 range61From20258To2988) (join_population range61From20258To3003 (join_population range61From20258To3167 range61From20258To3661)))

private theorem fee61_107_21645 :
    PopulationFees20258.bill (n:=21645) (PopulationFees20258.tabulate (21645-1) 256) source107.plan.table+
      4*21645*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*199959927459 := by decide +kernel
private theorem range61From20974To2964 : Segment 61 20974 21645 0 2964 :=
  paid (pc:=70) (v:=199959927459) (by decide) source107_valid tests61_107_0 fee61_107_21645 (by decide +kernel)

private theorem tests61_107_2964 : ∀ z∈source107.plan.table,z.1.Valid 61 2964 := by decide +kernel
private theorem range61From20974To3002 : Segment 61 20974 21645 2964 3002 :=
  paid (pc:=70) (v:=199959927459) (by decide) source107_valid tests61_107_2964 fee61_107_21645 (by decide +kernel)

private theorem tests61_103_3002 : ∀ z∈source103.plan.table,z.1.Valid 61 3002 := by decide +kernel
private theorem fee61_103_21645 :
    PopulationFees20258.bill (n:=21645) (PopulationFees20258.tabulate (21645-1) 256) source103.plan.table+
      4*21645*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*252177316285 := by decide +kernel
private theorem range61From20974To3135 : Segment 61 20974 21645 3002 3135 :=
  paid (pc:=69) (v:=252177316285) (by decide) source103_valid tests61_103_3002 fee61_103_21645 (by decide +kernel)

private theorem tests61_105_3135 : ∀ z∈source105.plan.table,z.1.Valid 61 3135 := by decide +kernel
private theorem fee61_105_21645 :
    PopulationFees20258.bill (n:=21645) (PopulationFees20258.tabulate (21645-1) 256) source105.plan.table+
      4*21645*NaturalPopulation20258.weights source105.extras≤source105.plan.scale*276477600521 := by decide +kernel
private theorem range61From20974To3661 : Segment 61 20974 21645 3135 3661 :=
  paid (pc:=63) (v:=276477600521) (by decide) source105_valid tests61_105_3135 fee61_105_21645 (by decide +kernel)

private theorem range61From20974 : Win 61 20974 21645 :=
  complete (by decide) (by decide) (join_population (join_population range61From20974To2964 range61From20974To3002) (join_population range61From20974To3135 range61From20974To3661))

private theorem fee61_107_22321 :
    PopulationFees20258.bill (n:=22321) (PopulationFees20258.tabulate (22321-1) 256) source107.plan.table+
      4*22321*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*211571551497 := by decide +kernel
private theorem range61From21646To2968 : Segment 61 21646 22321 0 2968 :=
  paid (pc:=71) (v:=211571551497) (by decide) source107_valid tests61_107_0 fee61_107_22321 (by decide +kernel)

private theorem tests61_107_2968 : ∀ z∈source107.plan.table,z.1.Valid 61 2968 := by decide +kernel
private theorem range61From21646To3001 : Segment 61 21646 22321 2968 3001 :=
  paid (pc:=71) (v:=211571551497) (by decide) source107_valid tests61_107_2968 fee61_107_22321 (by decide +kernel)

private theorem tests61_107_3001 : ∀ z∈source107.plan.table,z.1.Valid 61 3001 := by decide +kernel
private theorem range61From21646To3002 : Segment 61 21646 22321 3001 3002 :=
  paid (pc:=71) (v:=211571551497) (by decide) source107_valid tests61_107_3001 fee61_107_22321 (by decide +kernel)

private theorem fee61_103_22321 :
    PopulationFees20258.bill (n:=22321) (PopulationFees20258.tabulate (22321-1) 256) source103.plan.table+
      4*22321*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*266622407782 := by decide +kernel
private theorem range61From21646To3102 : Segment 61 21646 22321 3002 3102 :=
  paid (pc:=70) (v:=266622407782) (by decide) source103_valid tests61_103_3002 fee61_103_22321 (by decide +kernel)

private theorem tests61_106_3102 : ∀ z∈source106.plan.table,z.1.Valid 61 3102 := by decide +kernel
private theorem fee61_106_22321 :
    PopulationFees20258.bill (n:=22321) (PopulationFees20258.tabulate (22321-1) 256) source106.plan.table+
      4*22321*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*298050780232 := by decide +kernel
private theorem range61From21646To3625 : Segment 61 21646 22321 3102 3625 :=
  paid (pc:=65) (v:=298050780232) (by decide) source106_valid tests61_106_3102 fee61_106_22321 (by decide +kernel)

private theorem tests61_109_3625 : ∀ z∈source109.plan.table,z.1.Valid 61 3625 := by decide +kernel
private theorem fee61_109_22321 :
    PopulationFees20258.bill (n:=22321) (PopulationFees20258.tabulate (22321-1) 256) source109.plan.table+
      4*22321*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*237884241213 := by decide +kernel
private theorem range61From21646To3661 : Segment 61 21646 22321 3625 3661 :=
  paid (pc:=63) (v:=237884241213) (by decide) source109_valid tests61_109_3625 fee61_109_22321 (by decide +kernel)

private theorem range61From21646 : Win 61 21646 22321 :=
  complete (by decide) (by decide) (join_population (join_population range61From21646To2968 (join_population range61From21646To3001 range61From21646To3002)) (join_population range61From21646To3102 (join_population range61From21646To3625 range61From21646To3661)))

private theorem fee61_107_23027 :
    PopulationFees20258.bill (n:=23027) (PopulationFees20258.tabulate (23027-1) 256) source107.plan.table+
      4*23027*NaturalPopulation20258.weights source107.extras≤source107.plan.scale*223864065782 := by decide +kernel
private theorem range61From22322To2972 : Segment 61 22322 23027 0 2972 :=
  paid (pc:=72) (v:=223864065782) (by decide) source107_valid tests61_107_0 fee61_107_23027 (by decide +kernel)

private theorem tests61_107_2972 : ∀ z∈source107.plan.table,z.1.Valid 61 2972 := by decide +kernel
private theorem range61From22322To3001 : Segment 61 22322 23027 2972 3001 :=
  paid (pc:=72) (v:=223864065782) (by decide) source107_valid tests61_107_2972 fee61_107_23027 (by decide +kernel)

private theorem range61From22322To3002 : Segment 61 22322 23027 3001 3002 :=
  paid (pc:=72) (v:=223864065782) (by decide) source107_valid tests61_107_3001 fee61_107_23027 (by decide +kernel)

private theorem fee61_103_23027 :
    PopulationFees20258.bill (n:=23027) (PopulationFees20258.tabulate (23027-1) 256) source103.plan.table+
      4*23027*NaturalPopulation20258.weights source103.extras≤source103.plan.scale*282018517335 := by decide +kernel
private theorem range61From22322To3079 : Segment 61 22322 23027 3002 3079 :=
  paid (pc:=71) (v:=282018517335) (by decide) source103_valid tests61_103_3002 fee61_103_23027 (by decide +kernel)

private theorem tests61_106_3079 : ∀ z∈source106.plan.table,z.1.Valid 61 3079 := by decide +kernel
private theorem fee61_106_23027 :
    PopulationFees20258.bill (n:=23027) (PopulationFees20258.tabulate (23027-1) 256) source106.plan.table+
      4*23027*NaturalPopulation20258.weights source106.extras≤source106.plan.scale*315264272106 := by decide +kernel
private theorem range61From22322To3475 : Segment 61 22322 23027 3079 3475 :=
  paid (pc:=68) (v:=315264272106) (by decide) source106_valid tests61_106_3079 fee61_106_23027 (by decide +kernel)

private theorem tests61_109_3475 : ∀ z∈source109.plan.table,z.1.Valid 61 3475 := by decide +kernel
private theorem fee61_109_23027 :
    PopulationFees20258.bill (n:=23027) (PopulationFees20258.tabulate (23027-1) 256) source109.plan.table+
      4*23027*NaturalPopulation20258.weights source109.extras≤source109.plan.scale*251755096477 := by decide +kernel
private theorem range61From22322To3661 : Segment 61 22322 23027 3475 3661 :=
  paid (pc:=65) (v:=251755096477) (by decide) source109_valid tests61_109_3475 fee61_109_23027 (by decide +kernel)

private theorem range61From22322 : Win 61 22322 23027 :=
  complete (by decide) (by decide) (join_population (join_population range61From22322To2972 (join_population range61From22322To3001 range61From22322To3002)) (join_population range61From22322To3079 (join_population range61From22322To3475 range61From22322To3661)))

theorem cut61From20258 : Win 61 20258 23027 :=
  (join_ground (join_ground range61From20258 range61From20974) (join_ground range61From21646 range61From22322))

end JSP233.FiniteCutRanges20258
