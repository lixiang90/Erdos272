module

public import Erdos272.Global.N20258.PopulationRanges20258
public import Erdos272.Arithmetic.N20258.Sources.Source018
public import Erdos272.Arithmetic.N20258.Sources.Source026
public import Erdos272.Arithmetic.N20258.Sources.Source028
public import Erdos272.Arithmetic.N20258.Sources.Source030
public import Erdos272.Arithmetic.N20258.Sources.Source031
public import Erdos272.Arithmetic.N20258.Sources.Source032
public import Erdos272.Arithmetic.N20258.Sources.Source033
public import Erdos272.Arithmetic.N20258.Sources.Source034
public import Erdos272.Arithmetic.N20258.Sources.Source035

@[expose] public section
namespace JSP233.FiniteCutRanges20258
open PopulationRanges20258 PopulationSources20258
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 5000000

private theorem tests50_028_0 : ∀ z∈source028.plan.table,z.1.Valid 50 0 := by decide +kernel
private theorem fee50_028_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source028.plan.table+
      4*20454*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*89209149446 := by decide +kernel
private theorem range50From20258To2153 : Segment 50 20258 20454 0 2153 :=
  paid (pc:=79) (v:=89209149446) (by decide) source028_valid tests50_028_0 fee50_028_20454 (by decide +kernel)

private theorem tests50_030_2153 : ∀ z∈source030.plan.table,z.1.Valid 50 2153 := by decide +kernel
private theorem fee50_030_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source030.plan.table+
      4*20454*NaturalPopulation20258.weights source030.extras≤source030.plan.scale*159987252207 := by decide +kernel
private theorem range50From20258To2243 : Segment 50 20258 20454 2153 2243 :=
  paid (pc:=79) (v:=159987252207) (by decide) source030_valid tests50_030_2153 fee50_030_20454 (by decide +kernel)

private theorem tests50_018_2243 : ∀ z∈source018.plan.table,z.1.Valid 50 2243 := by decide +kernel
private theorem fee50_018_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source018.plan.table+
      4*20454*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*156157964048 := by decide +kernel
private theorem range50From20258To2266 : Segment 50 20258 20454 2243 2266 :=
  paid (pc:=78) (v:=156157964048) (by decide) source018_valid tests50_018_2243 fee50_018_20454 (by decide +kernel)

private theorem tests50_031_2266 : ∀ z∈source031.plan.table,z.1.Valid 50 2266 := by decide +kernel
private theorem fee50_031_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source031.plan.table+
      4*20454*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*148076784808 := by decide +kernel
private theorem range50From20258To2312 : Segment 50 20258 20454 2266 2312 :=
  paid (pc:=78) (v:=148076784808) (by decide) source031_valid tests50_031_2266 fee50_031_20454 (by decide +kernel)

private theorem tests50_032_2312 : ∀ z∈source032.plan.table,z.1.Valid 50 2312 := by decide +kernel
private theorem fee50_032_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source032.plan.table+
      4*20454*NaturalPopulation20258.weights source032.extras≤source032.plan.scale*192416218560 := by decide +kernel
private theorem range50From20258To2325 : Segment 50 20258 20454 2312 2325 :=
  paid (pc:=78) (v:=192416218560) (by decide) source032_valid tests50_032_2312 fee50_032_20454 (by decide +kernel)

private theorem tests50_034_2325 : ∀ z∈source034.plan.table,z.1.Valid 50 2325 := by decide +kernel
private theorem fee50_034_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source034.plan.table+
      4*20454*NaturalPopulation20258.weights source034.extras≤source034.plan.scale*183435605573 := by decide +kernel
private theorem range50From20258To2381 : Segment 50 20258 20454 2325 2381 :=
  paid (pc:=77) (v:=183435605573) (by decide) source034_valid tests50_034_2325 fee50_034_20454 (by decide +kernel)

private theorem tests50_033_2381 : ∀ z∈source033.plan.table,z.1.Valid 50 2381 := by decide +kernel
private theorem fee50_033_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source033.plan.table+
      4*20454*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*182628592411 := by decide +kernel
private theorem range50From20258To2387 : Segment 50 20258 20454 2381 2387 :=
  paid (pc:=77) (v:=182628592411) (by decide) source033_valid tests50_033_2381 fee50_033_20454 (by decide +kernel)

private theorem tests50_026_2387 : ∀ z∈source026.plan.table,z.1.Valid 50 2387 := by decide +kernel
private theorem fee50_026_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source026.plan.table+
      4*20454*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*179786364226 := by decide +kernel
private theorem range50From20258To2405 : Segment 50 20258 20454 2387 2405 :=
  paid (pc:=77) (v:=179786364226) (by decide) source026_valid tests50_026_2387 fee50_026_20454 (by decide +kernel)

private theorem tests50_035_2405 : ∀ z∈source035.plan.table,z.1.Valid 50 2405 := by decide +kernel
private theorem fee50_035_20454 :
    PopulationFees20258.bill (n:=20454) (PopulationFees20258.tabulate (20454-1) 256) source035.plan.table+
      4*20454*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*171967053079 := by decide +kernel
private theorem range50From20258To2451 : Segment 50 20258 20454 2405 2451 :=
  paid (pc:=77) (v:=171967053079) (by decide) source035_valid tests50_035_2405 fee50_035_20454 (by decide +kernel)

private theorem range50From20258 : Win 50 20258 20454 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range50From20258To2153 range50From20258To2243) (join_population range50From20258To2266 range50From20258To2312)) (join_population (join_population range50From20258To2325 range50From20258To2381) (join_population range50From20258To2387 (join_population range50From20258To2405 range50From20258To2451))))

private theorem fee50_028_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source028.plan.table+
      4*20688*NaturalPopulation20258.weights source028.extras≤source028.plan.scale*91067910868 := by decide +kernel
private theorem range50From20455To2160 : Segment 50 20455 20688 0 2160 :=
  paid (pc:=79) (v:=91067910868) (by decide) source028_valid tests50_028_0 fee50_028_20688 (by decide +kernel)

private theorem tests50_030_2160 : ∀ z∈source030.plan.table,z.1.Valid 50 2160 := by decide +kernel
private theorem fee50_030_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source030.plan.table+
      4*20688*NaturalPopulation20258.weights source030.extras≤source030.plan.scale*163289089940 := by decide +kernel
private theorem range50From20455To2248 : Segment 50 20455 20688 2160 2248 :=
  paid (pc:=79) (v:=163289089940) (by decide) source030_valid tests50_030_2160 fee50_030_20688 (by decide +kernel)

private theorem tests50_018_2248 : ∀ z∈source018.plan.table,z.1.Valid 50 2248 := by decide +kernel
private theorem fee50_018_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source018.plan.table+
      4*20688*NaturalPopulation20258.weights source018.extras≤source018.plan.scale*159506291096 := by decide +kernel
private theorem range50From20455To2269 : Segment 50 20455 20688 2248 2269 :=
  paid (pc:=78) (v:=159506291096) (by decide) source018_valid tests50_018_2248 fee50_018_20688 (by decide +kernel)

private theorem tests50_031_2269 : ∀ z∈source031.plan.table,z.1.Valid 50 2269 := by decide +kernel
private theorem fee50_031_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source031.plan.table+
      4*20688*NaturalPopulation20258.weights source031.extras≤source031.plan.scale*151135594644 := by decide +kernel
private theorem range50From20455To2314 : Segment 50 20455 20688 2269 2314 :=
  paid (pc:=78) (v:=151135594644) (by decide) source031_valid tests50_031_2269 fee50_031_20688 (by decide +kernel)

private theorem tests50_032_2314 : ∀ z∈source032.plan.table,z.1.Valid 50 2314 := by decide +kernel
private theorem fee50_032_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source032.plan.table+
      4*20688*NaturalPopulation20258.weights source032.extras≤source032.plan.scale*196364913950 := by decide +kernel
private theorem range50From20455To2325 : Segment 50 20455 20688 2314 2325 :=
  paid (pc:=78) (v:=196364913950) (by decide) source032_valid tests50_032_2314 fee50_032_20688 (by decide +kernel)

private theorem fee50_034_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source034.plan.table+
      4*20688*NaturalPopulation20258.weights source034.extras≤source034.plan.scale*187211481437 := by decide +kernel
private theorem range50From20455To2380 : Segment 50 20455 20688 2325 2380 :=
  paid (pc:=77) (v:=187211481437) (by decide) source034_valid tests50_034_2325 fee50_034_20688 (by decide +kernel)

private theorem tests50_033_2380 : ∀ z∈source033.plan.table,z.1.Valid 50 2380 := by decide +kernel
private theorem fee50_033_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source033.plan.table+
      4*20688*NaturalPopulation20258.weights source033.extras≤source033.plan.scale*186400906821 := by decide +kernel
private theorem range50From20455To2386 : Segment 50 20455 20688 2380 2386 :=
  paid (pc:=77) (v:=186400906821) (by decide) source033_valid tests50_033_2380 fee50_033_20688 (by decide +kernel)

private theorem tests50_026_2386 : ∀ z∈source026.plan.table,z.1.Valid 50 2386 := by decide +kernel
private theorem fee50_026_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source026.plan.table+
      4*20688*NaturalPopulation20258.weights source026.extras≤source026.plan.scale*183652561595 := by decide +kernel
private theorem range50From20455To2403 : Segment 50 20455 20688 2386 2403 :=
  paid (pc:=77) (v:=183652561595) (by decide) source026_valid tests50_026_2386 fee50_026_20688 (by decide +kernel)

private theorem tests50_026_2403 : ∀ z∈source026.plan.table,z.1.Valid 50 2403 := by decide +kernel
private theorem range50From20455To2404 : Segment 50 20455 20688 2403 2404 :=
  paid (pc:=77) (v:=183652561595) (by decide) source026_valid tests50_026_2403 fee50_026_20688 (by decide +kernel)

private theorem tests50_035_2404 : ∀ z∈source035.plan.table,z.1.Valid 50 2404 := by decide +kernel
private theorem fee50_035_20688 :
    PopulationFees20258.bill (n:=20688) (PopulationFees20258.tabulate (20688-1) 256) source035.plan.table+
      4*20688*NaturalPopulation20258.weights source035.extras≤source035.plan.scale*175524305854 := by decide +kernel
private theorem range50From20455To2451 : Segment 50 20455 20688 2404 2451 :=
  paid (pc:=77) (v:=175524305854) (by decide) source035_valid tests50_035_2404 fee50_035_20688 (by decide +kernel)

private theorem range50From20455 : Win 50 20455 20688 :=
  complete (by decide) (by decide) (join_population (join_population (join_population range50From20455To2160 range50From20455To2248) (join_population range50From20455To2269 (join_population range50From20455To2314 range50From20455To2325))) (join_population (join_population range50From20455To2380 range50From20455To2386) (join_population range50From20455To2403 (join_population range50From20455To2404 range50From20455To2451))))

theorem cut50From20258 : Win 50 20258 20688 :=
  (join_ground range50From20258 range50From20455)

end JSP233.FiniteCutRanges20258
